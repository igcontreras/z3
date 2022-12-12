#include "qe/qe_mbp_tg.h"
#include "ast/array_decl_plugin.h"
#include "ast/ast.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "qe/mbp/mbp_term_graph.h"
#include "qe/mbp/mbp_arrays.h"
#include "util/debug.h"
#include "util/tptr.h"
#include "util/vector.h"
#include "ast/rewriter/var_subst.h"
#include "ast/ast_pp.h"

namespace check_uninterp_consts_ns {
  struct found {};
  struct proc {
    app_ref_vector &m_vars;
    proc(app_ref_vector &vars) : m_vars(vars) {}
    void operator()(expr *n) const {}
    void operator()(app *n) {
      if (is_uninterp_const(n) && m_vars.contains(n)) throw found();
    }
  };
} // namespace check_uninterp_consts_ns

// check if e contains any apps from vars
bool contains_vars(expr *e, app_ref_vector &vars) {
  check_uninterp_consts_ns::proc proc(vars);
  try {
    for_each_expr(proc, e);
  }
  catch (const check_uninterp_consts_ns::found &) { return true; }
  return false;
}

bool contains_var(expr *e, app_ref var) {
  app_ref_vector vars(var.get_manager());
  vars.push_back(var);
  check_uninterp_consts_ns::proc proc(vars);
  try {
    for_each_expr(proc, e);
  }
  catch (const check_uninterp_consts_ns::found &) { return true; }
  return false;
}

class qe_mbp_tg::impl {
private:
  ast_manager& m;
  array_util m_array_util;
  //TODO: change this, only keep a reference
  app_ref_vector m_vars;
  
  bool is_arr_write(expr* t) {
    if (!m_array_util.is_store(t)) return false;
    return contains_vars(to_app(t)->get_arg(0), m_vars);
  }

  bool is_rd_wr(expr* t) {
    if (!m_array_util.is_select(t) || !m_array_util.is_store(to_app(t)->get_arg(0))) return false;
    return contains_vars(to_app(to_app(t)->get_arg(0))->get_arg(0), m_vars);
  }

  bool has_arr_var(expr* t) {
    return contains_vars(t, m_vars);
  }
  
  void preprocess(expr_ref_vector& fml) {
    int j = 0;
    vector<expr_ref_vector> empty;
    for(expr* e : fml) {
      if (m.is_eq(e) && m_array_util.is_array(to_app(e)->get_arg(0)) && (has_arr_var(to_app(e)->get_arg(0)) || has_arr_var(to_app(e)->get_arg(1)))) {
        peq pe(to_app(e)->get_arg(1), to_app(e)->get_arg(0), empty, m);
	fml[j] = pe.mk_peq();
      }
      j++;
    }
    j = 0;
    for(expr* e : fml) {
      if (is_app(e) && is_partial_eq(to_app(e)) && (is_arr_write(to_app(e)->get_arg(1)) && !is_arr_write(to_app(e)->get_arg(0)))) {
	peq ex(to_app(e), m);
	vector<expr_ref_vector> result;
	ex.get_diff_indices(result);
	peq pe(ex.rhs(), ex.lhs(), result, m);
	fml[j] = pe.mk_peq();
      }
      j++;
    }
  }
public:
  impl(ast_manager &m, params_ref const &p)
    : m(m), m_array_util(m), m_vars(m) {}

  void operator()(app_ref_vector &vars, expr_ref &e, model& mdl) {
    if (vars.empty())
      return;
    for(auto v : vars) m_vars.push_back(v);
    expr_ref_vector fml(m);
    flatten_and(e, fml);
    TRACE("mbp_tg", tout << "Before preprocess " << mk_and(fml););
    preprocess(fml);
    TRACE("mbp_tg", tout << "After preprocess " << mk_and(fml););
    mbp::term_graph tg(m);
    tg.set_prop_ground(true);
    tg.set_vars(vars, true /*exclude*/);    
    expr_ref_vector todo(m);
    expr* f;
    for(expr *e : fml) {
      if(is_app(e) && is_partial_eq(to_app(e))) {
	todo.push_back(e);
      }
      else if (m.is_not(e, f) && is_app(f) && is_partial_eq(to_app(f))) {
	todo.push_back(f);
      }
      tg.add_lit(e);
    }
    vector<expr_ref_vector> indices;

    //ElimWrEq begin 
    while(!todo.empty()) {
      expr* e = todo.back();
      todo.pop_back();
      SASSERT(is_app(e) && is_partial_eq(to_app(e)));
      TRACE("mbp_tg", tout << "processing " << expr_ref(e, m););
      peq p(to_app(e), m);
      tg.add_lit(p.mk_peq());
      if (is_arr_write(p.lhs())) {
	expr* j = to_app(p.lhs())->get_arg(1);
	bool in = false;
	indices.reset();
	p.get_diff_indices(indices);
	expr* eq;
	expr_ref_vector deq(m);
	for(expr_ref_vector& e : indices) {
	  for (expr* i : e) {
	    if (mdl.is_true(m.mk_eq(j, i))) {
	      in = true;
	      eq = m.mk_eq(j, i);
	    }
	    else deq.push_back(i);
	  }
	}
	if (in) {
	  peq p_new(to_app(p.lhs())->get_arg(0), p.rhs(), indices, m);
	  tg.add_lit(p_new.mk_peq());
	  tg.add_eq(p.mk_peq(), p_new.mk_peq());
	  tg.add_lit(eq);
	}
	else {
	  for(expr* d : deq) {
	    tg.add_lit(m.mk_not(m.mk_eq(j, d)));
	  }
	  if (indices.empty()) {
	    expr_ref_vector setOne(m);
	    setOne.push_back(j);
	    indices.push_back(setOne);
	  }
	  else
	    indices.back().push_back(j);
	  peq p_new(to_app(p.lhs())->get_arg(0), p.rhs(), indices, m);
	  tg.add_lit(p_new.mk_peq());
	  expr* args[2] = {p.rhs(), j}; 
	  expr* rd = m_array_util.mk_select(2, args);
	  eq = m.mk_eq(rd, to_app(p.lhs())->get_arg(2));
	  tg.add_lit(eq);
	  tg.add_eq(p.mk_peq(), p_new.mk_peq());
	}
      }
    }
    //ElimWreq end

    //ElimEq begin
    for (expr * lit : tg.get_lits()) {
      if (is_app(lit) && is_partial_eq(to_app(lit))) {
	peq p(to_app(lit), m);
	if (is_uninterp_const(p.lhs()) && has_arr_var(p.lhs()) && !contains_var(p.rhs(), app_ref(to_app(p.lhs()), m))) {
	  app_ref_vector aux_consts(m);
	  expr_ref eq(m);
	  eq = p.mk_eq(aux_consts, true);
	  for(app* a : aux_consts) m_vars.push_back(a);
	  tg.add_vars(aux_consts);
	  tg.add_lit(eq);
	  tg.add_lit(m.mk_true());
	  tg.add_eq(p.mk_peq(), m.mk_true());
	  TRACE("mbp_tg", tout << "added lit  " << eq;);
	}
      }
    }
    //ElimEq End

    expr_ref_vector terms(m), rdTerms(m);
    tg.get_terms(terms);
    for (expr* term : terms) {
      if (is_rd_wr(term)) {
	expr* wr_ind = to_app(to_app(term)->get_arg(0))->get_arg(1);
	expr* rd_ind = to_app(term)->get_arg(1);
	expr* eq = m.mk_eq(wr_ind, rd_ind);
	if (mdl.is_true(eq)) {
	  tg.add_lit(eq);
	  tg.add_lit(m.mk_eq(term, to_app(to_app(term)->get_arg(0))->get_arg(2)));
	}
	else {
	  tg.add_lit(m.mk_not(eq));
	  expr* args[2] = {to_app(to_app(term)->get_arg(0))->get_arg(0), to_app(term)->get_arg(1)};
	  expr* rdTerm = m_array_util.mk_select(2, args);
	  tg.add_lit(m.mk_eq(term, rdTerm));
	}
      }
      else if (m_array_util.is_select(term) && contains_vars(to_app(term)->get_arg(0), m_vars)) {
	rdTerms.push_back(term);
      }
    }

    for (unsigned i = 0; i < rdTerms.size(); i++) {
      for (unsigned j = i+1; j < rdTerms.size(); j++) {
	expr* e1 = rdTerms.get(i);
	expr* e2 = rdTerms.get(j);
	expr* a1 = to_app(e1)->get_arg(0);
	expr* a2 = to_app(e2)->get_arg(0);
	expr* i1 = to_app(e1)->get_arg(1);
	expr* i2 = to_app(e2)->get_arg(1);
	expr* eq = m.mk_eq(i1, i2);
	if (a1 == a2) {
	  if (mdl.is_true(eq))
	    tg.add_eq(i1, i2);
	  else
	    tg.add_lit(m.mk_not(eq));
	}
      }
    }

    TRACE("mbp_tg", tout << "mbp tg " << mk_and(tg.get_lits()););
    tg.compute_non_ground<true>(m_vars);
    e = tg.to_ground_expr();
    TRACE("mbp_tg", tout << "after mbp tg " << e;);
  }

};

qe_mbp_tg::qe_mbp_tg(ast_manager &m, params_ref const &p) {
  m_impl = alloc(impl, m, p);
}

qe_mbp_tg::~qe_mbp_tg() { dealloc(m_impl); }

void qe_mbp_tg::operator()(app_ref_vector &vars, expr_ref &fml, model& mdl) {
  (*m_impl)(vars, fml, mdl);
}

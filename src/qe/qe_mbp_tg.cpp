#include "qe/qe_mbp_tg.h"
#include "ast/array_decl_plugin.h"
#include "ast/ast.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "qe/mbp/mbp_term_graph.h"
#include "qe/mbp/mbp_arrays.h"
#include "util/debug.h"
#include "util/vector.h"
#include "ast/rewriter/var_subst.h"

namespace check_uninterp_consts_ns {
struct proc {
  app_ref_vector &m_vars;
  bool res;
  proc(app_ref_vector &vars) : m_vars(vars), res(false) {}
  void operator()(expr *n) const {}
  void operator()(app *n) {
    if (!res && is_uninterp_const(n) && m_vars.contains(n)) res = true;
  }
};
} // namespace check_uninterp_consts_ns

// check if e contains any apps from vars
bool contains_vars(expr *e, app_ref_vector &vars) {
    check_uninterp_consts_ns::proc proc(vars);
    for_each_expr(proc, e);
    return proc.res;
}

class qe_mbp_tg::impl {
private:
  ast_manager& m;
  array_util m_array_util;
  app_ref_vector vars;
  
  bool is_arr_write(expr* t) {
    if (!m_array_util.is_store(t)) return false;
    return contains_vars(to_app(t)->get_arg(0), vars);
  }
  
  bool has_arr_term(expr* t) {
    return contains_vars(t, vars);
  }
  
  void preprocess(expr_ref_vector& fml) {
    int j = 0;
    vector<expr_ref_vector> empty;
    for(expr* e : fml) {
      if (m.is_eq(e) && (has_arr_term(to_app(e)->get_arg(0)) || has_arr_term(to_app(e)->get_arg(1)))) {
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
    : m(m), m_array_util(m), vars(m) {}

  void operator()(app_ref_vector &vars, expr_ref &e, model& mdl) {
    if (vars.empty())
      return;
    expr_ref_vector fml(m);
    flatten_and(e, fml);
    preprocess(fml);

    mbp::term_graph tg(m);
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
    }
    vector<expr_ref_vector> indices;
    
    while(!todo.empty()) {
      expr* e = todo.back();
      todo.pop_back();
      SASSERT(is_app(e) && is_partial_eq(to_app(e)));
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
    tg.qe_lite(vars, e);
  }

};

qe_mbp_tg::qe_mbp_tg(ast_manager &m, params_ref const &p) {
  m_impl = alloc(impl, m, p);
}

qe_mbp_tg::~qe_mbp_tg() { dealloc(m_impl); }

void qe_mbp_tg::operator()(app_ref_vector &vars, expr_ref &fml, model& mdl) {
  (*m_impl)(vars, fml, mdl);
}

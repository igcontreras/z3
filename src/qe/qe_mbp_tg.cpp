#include "qe/qe_mbp_tg.h"
#include "ast/array_decl_plugin.h"
#include "ast/ast.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "model/model.h"
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
    app_ref_vector const &m_vars;
    bool m_only_arr;
    array_util m_arr;
    proc(app_ref_vector const &vars, bool only_arr = false) : m_vars(vars), m_only_arr(only_arr), m_arr(m_vars.get_manager()) {}
    void operator()(expr *n) const {}
    void operator()(app *n) {
      if (is_uninterp_const(n) && m_vars.contains(n) && (!m_only_arr || m_arr.is_array(n))) throw found();
    }
  };
} // namespace check_uninterp_consts_ns

// check if e contains any apps from vars
bool contains_vars(expr *e, app_ref_vector const &vars, bool only_arr = false) {
  check_uninterp_consts_ns::proc proc(vars, only_arr);
  try {
    for_each_expr(proc, e);
  }
  catch (const check_uninterp_consts_ns::found &) { return true; }
  return false;
}

bool contains_var(expr *e, app_ref var, bool only_arr = false) {
  app_ref_vector vars(var.get_manager());
  vars.push_back(var);
  check_uninterp_consts_ns::proc proc(vars, only_arr);
  try {
    for_each_expr(proc, e);
  }
  catch (const check_uninterp_consts_ns::found &) { return true; }
  return false;
}

namespace collect_arrInd_ns {
struct proc {
  app_ref_vector const& m_vars;
  app_ref_vector &m_out;
  ast_manager& m;
  array_util m_array_util;
  expr* ind;
  proc(app_ref_vector const& vars, app_ref_vector &out) : m_vars(vars), m_out(out), m(out.get_manager()), m_array_util(m) {}
  void operator()(expr *n) const {}
  void operator()(app *n) {
    if (m_array_util.is_select(n) || m_array_util.is_store(n)) {
      ind = to_app(n)->get_arg(1);
      for (auto v : m_vars) {
	if (ind->get_id() == v->get_id())
	  m_out.push_back(v);
      }
    }
  }
};
} // namespace collect_arrInd_ns

// Return all variables in vars that are used to index arrays in fml
void collect_array_indices(expr *fml, app_ref_vector const& vars, app_ref_vector &out) {
  collect_arrInd_ns::proc proc(vars, out);
  for_each_expr(proc, fml);
}
void remove_peq(expr* inp, expr_ref& op) {
  ast_manager& m = op.get_manager();
  expr_ref_vector fml(m);
  flatten_and(inp, fml);
  unsigned i = 0, j = fml.size();
  expr *lit, *lhs, *rhs;
  auto is_peq = [] (expr* e) {
    return is_app(e) && is_partial_eq(to_app(e));
  };
  for (;i < j;) {
    lit = fml.get(i);
    if ( is_peq(lit) || (m.is_eq(lit, lhs, rhs) && (is_peq(lhs) || is_peq(rhs))) )
      fml[i] = fml.get(--j);
    else
      i++;
  }
  fml.shrink(j);
  op = mk_and(fml);
}
class qe_mbp_tg::impl {
private:
  ast_manager& m;
  array_util m_array_util;
  datatype_util m_dt_util;
  //TODO: change this, only keep a reference
  app_ref_vector m_vars;
  bool m_reduce_all_selects;
  
  bool is_arr_write(expr* t) {
    if (!m_array_util.is_store(t)) return false;
    return contains_vars(to_app(t)->get_arg(0), m_vars);
  }

  bool is_rd_wr(expr* t) {
    if (!m_array_util.is_select(t) || !m_array_util.is_store(to_app(t)->get_arg(0))) return false;
    return m_reduce_all_selects || contains_vars(to_app(to_app(t)->get_arg(0))->get_arg(0), m_vars);
  }

  bool has_var(expr* t) {
    return contains_vars(t, m_vars);
  }

  bool has_arr_var(expr* t) {
    return contains_vars(t, m_vars, true);
  }

  bool is_var(expr* t) {
    return is_uninterp_const(t) && has_var(t);
  }

  bool is_constructor(expr* t) {
    return is_app(t) && m_dt_util.is_constructor(to_app(t)->get_decl()) && has_var(t);
  }

  app_ref new_var(sort* s) {
    return app_ref(m.mk_fresh_const("mbptg", s), m);
  }

  bool is_wr_on_rhs(expr* e) {
    return is_app(e) && is_partial_eq(to_app(e)) && is_wr_on_rhs(to_app(e)->get_arg(0), to_app(e)->get_arg(1));
  }

  bool is_wr_on_rhs(expr* lhs, expr* rhs) {
    return (is_arr_write(rhs) && !is_arr_write(lhs));
  }

  bool should_create_peq(expr* e) {
    return m.is_eq(e) && should_create_peq(to_app(e)->get_arg(0), to_app(e)->get_arg(1));
  }

  bool should_create_peq(expr* lhs, expr* rhs) {
    return m_array_util.is_array(lhs) && m_array_util.is_array(rhs) && (has_var(lhs) || has_var(rhs));
  }

  peq mk_peq(expr* e1, expr* e2) {
    vector<expr_ref_vector> empty;
    return mk_peq(e1, e2, empty);
  }

  peq mk_peq(expr* e1, expr* e2, vector<expr_ref_vector>& indices) {
    expr* n_lhs, *n_rhs;
    if (is_wr_on_rhs(e1, e2)) {
	n_lhs = e2;
	n_rhs = e1;
      }
      else {
	n_lhs = e1;
	n_rhs = e2;
      }
      return peq(n_lhs, n_rhs, indices, m);
  }

  void elimwreq(peq p, mbp::term_graph &tg, model& mdl, bool is_neg) {
    SASSERT(is_arr_write(p.lhs()));
    TRACE("mbp_tg", tout << "processing " << expr_ref(p.mk_peq(), m););
    vector<expr_ref_vector> indices;
    expr* j = to_app(p.lhs())->get_arg(1);
    bool in = false;
    p.get_diff_indices(indices);
    expr* eq;
    expr_ref_vector deq(m);
    for(expr_ref_vector& e : indices) {
      for (expr* i : e) {
	if (mdl.is_true(m.mk_eq(j, i))) {
	  in = true;
	  eq = m.mk_eq(j, i);
	  break;
	}
	else deq.push_back(i);
      }
    }
    if (in) {
      peq p_new = mk_peq(to_app(p.lhs())->get_arg(0), p.rhs(), indices);
      tg.add_lit(p_new.mk_peq());
      tg.add_eq(p.mk_peq(), p_new.mk_peq());
      tg.add_lit(eq);
      expr* p_new_expr = is_neg ? m.mk_not(p_new.mk_peq()) : p_new.mk_peq();
      tg.add_lit(p_new_expr);
    }
    else {
      for(expr* d : deq) {
	eq = m.mk_not(m.mk_eq(j, d));
	tg.add_lit(eq);
      }
      expr_ref_vector setOne(m);
      setOne.push_back(j);
      indices.push_back(setOne);
      peq p_new = mk_peq(to_app(p.lhs())->get_arg(0), p.rhs(), indices);
      expr* args[2] = {p.rhs(), j};
      expr* rd = m_array_util.mk_select(2, args);
      eq = m.mk_eq(rd, to_app(p.lhs())->get_arg(2));
      if (!is_neg) {
	tg.add_lit(p_new.mk_peq());
	tg.add_lit(eq);
	tg.add_eq(p.mk_peq(), p_new.mk_peq());
      }
      else {
	SASSERT(mdl.is_false(p_new.mk_peq()) || mdl.is_false(eq));
	if (mdl.is_false(p_new.mk_peq())) {
	  tg.add_lit(mk_not(p_new.mk_peq()));
	  tg.add_eq(p.mk_peq(), p_new.mk_peq());
	}
	if (mdl.is_false(eq)) {
	  tg.add_lit(m.mk_not(eq));
	}
      }
    }
  }

  void add_rdVar(expr* rd, mbp::term_graph &tg, app_ref_vector& vars, model& mdl) {
    //do not assign new variable if rd is already equal to a value
    if (tg.has_val_in_class(rd)) return;
    app_ref u = new_var(to_app(rd)->get_sort());
    if (m_dt_util.is_datatype(u->_get_sort()) || m_array_util.is_array(u)) {
	m_vars.push_back(u);
	tg.add_var(u);
    }
    else
      vars.push_back(u);
    expr* eq = m.mk_eq(u, rd);
    tg.add_lit(eq);
    mdl.register_decl(u->get_decl(), mdl(rd));
  }

  void elimeq(peq p, mbp::term_graph &tg, app_ref_vector& vars, model& mdl) {
    app_ref_vector aux_consts(m);
    expr_ref eq(m);
    expr_ref store(m);
    eq = p.mk_eq(aux_consts, true);
    vector<expr_ref_vector> indices;
    p.get_diff_indices(indices);
    vector<expr_ref_vector>::iterator itr = indices.begin();
    unsigned i = 0;
    for(app* a : aux_consts) {
      if (m_dt_util.is_datatype(a->_get_sort()) || m_array_util.is_array(a)) {
	m_vars.push_back(a);
	tg.add_var(a);
      }
      else
	vars.push_back(a);
      auto const& indx =  std::next(itr, i);
      SASSERT(indx->size() == 1);
      expr *args[2] = {to_app(p.lhs()), to_app(indx->get(0))};
      store = m_array_util.mk_select(2, args);
      mdl.register_decl(a->get_decl(), 	mdl(store));
      i++;
    }
    tg.add_lit(eq);
    tg.add_lit(m.mk_true());
    tg.add_eq(p.mk_peq(), m.mk_true());
    TRACE("mbp_tg", tout << "added lit  " << eq;);
  }

  void elimrdwr(expr* term, mbp::term_graph &tg, model& mdl) {
    SASSERT(is_rd_wr(term));
    expr* wr_ind = to_app(to_app(term)->get_arg(0))->get_arg(1);
    expr* rd_ind = to_app(term)->get_arg(1);
    expr *eq = m.mk_eq(wr_ind, rd_ind);
    expr_ref e(m);
    if (mdl.is_true(eq)) {
      tg.add_lit(eq);
      e =  to_app(to_app(term)->get_arg(0))->get_arg(2);
    }
    else {
      tg.add_lit(m.mk_not(eq));
      expr* args[2] = {to_app(to_app(term)->get_arg(0))->get_arg(0), to_app(term)->get_arg(1)};
      e = m_array_util.mk_select(2, args);
    }
    tg.add_lit(m.mk_eq(term, e));
  }

  bool is_constructor_app(expr* e, expr* &cons, expr* &rhs) {
    if (!m.is_eq(e, cons, rhs)) return false;
    //TODO: does it matter whether vars in cons appear in rhs?
    if (is_constructor(cons)) {
      return true;
    }
    else if (is_constructor(rhs)) {
      cons = rhs;
      rhs = to_app(e)->get_arg(0);
      return true;
    }
    return false;
  }

  void rm_select(expr* term, mbp::term_graph& tg, model& mdl, app_ref_vector& vars) {
    SASSERT(is_app(term) && m_dt_util.is_accessor(to_app(term)->get_decl()) && is_var(to_app(term)->get_arg(0)));
    expr* v = to_app(term)->get_arg(0), *sel, *eq;
    app_ref u(m);
    app_ref_vector new_vars(m);
    func_decl* cons = m_dt_util.get_accessor_constructor(to_app(term)->get_decl());
    ptr_vector<func_decl> const* accessors =  m_dt_util.get_constructor_accessors(cons);
    for (unsigned i = 0; i < accessors->size(); i++) {
      func_decl* d = accessors->get(i);
      u = new_var(d->get_range());
      if (m_dt_util.is_datatype(u->_get_sort()) || m_array_util.is_array(u)) {
	m_vars.push_back(u);
	tg.add_var(u);
      }
      else
	vars.push_back(u);
      new_vars.push_back(u);
      sel = m.mk_app(d, v);
      eq = m.mk_eq(sel, u);
      tg.add_lit(eq);
      tg.mark2(u);
      tg.mark2(sel);
      mdl.register_decl(u->get_decl(), mdl(sel));
    }
    eq = m.mk_eq(v, m.mk_app(cons, new_vars));
    tg.add_lit(eq);
    tg.mark2(eq);
  }

  void deconstruct_eq(expr* cons, expr* rhs, mbp::term_graph& tg) {
    ptr_vector<func_decl> const* accessors = m_dt_util.get_constructor_accessors(to_app(cons)->get_decl());
    for (unsigned i = 0; i < accessors->size(); i++) {
      app* a = m.mk_app(accessors->get(i), rhs);
      expr* newRhs = to_app(cons)->get_arg(i);
      tg.add_lit(m.mk_eq(a, newRhs));
    }
    func_decl* is_cons = m_dt_util.get_constructor_recognizer(to_app(cons)->get_decl());
    tg.add_lit(m.mk_app(is_cons, rhs));
  }

  void deconstruct_neq(expr* cons, expr* rhs, mbp::term_graph& tg, model& mdl) {
    ptr_vector<func_decl> const* accessors = m_dt_util.get_constructor_accessors(to_app(cons)->get_decl());
    func_decl* is_cons = m_dt_util.get_constructor_recognizer(to_app(cons)->get_decl());
    expr* a = m.mk_app(is_cons, rhs);
    if (mdl.is_false(a)) {
      tg.add_lit(m.mk_not(a));
      return;
    }
    tg.add_lit(a);

    for (unsigned i = 0; i < accessors->size(); i++) {
      app* a = m.mk_app(accessors->get(i), rhs);
      expr* newRhs = to_app(cons)->get_arg(i);
      expr* eq = m.mk_eq(a, newRhs);
      if (mdl.is_false(eq)) {
	tg.add_lit(m.mk_not(eq));
      }
    }
  }

  //todo are the literals to be processed
  // progress indicates whether mbp_arr added terms to the term graph
  bool mbp_adt(expr_ref_vector& fml, mbp::term_graph& tg, model& mdl, app_ref_vector &vars) {
    expr* cons, *rhs, *f;
    expr_ref_vector terms(m);
    unsigned sz = 0;
    bool progress = false;
    do {
      TRACE("mbp_tg", tout << "Iterating over terms of tg";);
      progress = false;
      tg.get_terms(terms, !m_reduce_all_selects);
      sz = sz == 0? terms.size() : sz;
      for (unsigned i = 0; i < terms.size(); i++) {
	expr* term = terms.get(i);
	if (tg.is_marked2(term)) continue;
	if (is_app(term) && m_dt_util.is_accessor(to_app(term)->get_decl()) && is_var(to_app(term)->get_arg(0))) {
	  tg.mark2(term);
	  progress = true;
	  rm_select(term, tg, mdl, vars);
	  continue;
	}
	if (is_constructor_app(term, cons, rhs)) {
	  tg.mark2(term);
	  progress = true;
	  deconstruct_eq(cons, rhs, tg);
	  continue;
	}
	if (m.is_not(term, f) && is_constructor_app(f, cons, rhs)) {
	  tg.mark2(term);
          progress = true;
	  deconstruct_neq(cons, rhs, tg, mdl);
	  continue;
	}
      }
    } while(progress);
    return sz < terms.size();;
  }

  // todo are the literals to be processed
  // progress indicates whether mbp_arr added terms to the term graph
  bool mbp_arr(expr_ref_vector& todo, mbp::term_graph& tg, model& mdl, app_ref_vector &vars) {
    vector<expr_ref_vector> indices;
    expr_ref_vector terms(m), rdTerms(m);
    expr_ref e(m), rdEq(m), rdDeq(m);
    expr* nt, *term;
    bool progress = false, is_neg = false;
    unsigned sz = 0;
    do {
      TRACE("mbp_tg", tout << "Iterating over terms of tg";);
      progress = false;
      terms.reset();
      rdTerms.reset();
      tg.get_terms(terms, !m_reduce_all_selects);
      // initialize sz in first iteration
      sz = sz == 0 ? terms.size() : sz;
      for (unsigned i = 0; i < terms.size(); i++) {
	term = terms.get(i);
	if (tg.is_marked2(term)) continue;
	TRACE("mbp_tg", tout << "processing " << expr_ref(term, m););
	if (should_create_peq(term)) {
	  // rewrite array eq as peq
	  tg.mark2(term);
	  progress = true;
	  e = mk_peq(to_app(term)->get_arg(0), to_app(term)->get_arg(1)).mk_peq();
	  tg.add_lit(e);
	  continue;
	}
	nt = term;
	is_neg = m.is_not(term, nt);
	if (is_app(nt) && is_partial_eq(to_app(nt))) {
	  TRACE("mbp_tg", tout << "processing " << expr_ref(nt, m););
	  peq p(to_app(nt), m);
	  if (is_arr_write(p.lhs())) {
	    tg.mark2(nt);
	    tg.mark2(term);
	    progress = true;
	    elimwreq(p, tg, mdl, is_neg);
	    continue;
	  }
	  if (is_var(p.lhs()) && !contains_var(p.rhs(), app_ref(to_app(p.lhs()), m))) {
	    tg.mark2(nt);
	    tg.mark2(term);
	    progress = true;
	    elimeq(p, tg, vars, mdl);
	    continue;
	  }
	}
	if (is_rd_wr(term)) {
	  tg.mark2(term);
	  progress = true;
	  elimrdwr(term, tg, mdl);
	  continue;
	}
      }

      // iterate over term graph again to collect read terms
      // irrespective of whether they have been marked or not
      for (unsigned i = 0; i < terms.size(); i++) {
	term = terms.get(i);
	if (m_array_util.is_select(term) && contains_vars(to_app(term)->get_arg(0), m_vars)) {
          rdTerms.push_back(term);
	  if (tg.is_marked2(term)) continue;
          add_rdVar(term, tg, vars, mdl);
	  tg.mark2(term);
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
	  if (a1->get_id() == a2->get_id()) {
	    rdEq = m.mk_eq(i1, i2);
	    if (!tg.is_marked2(rdEq) && mdl.is_true(rdEq)) {
	      progress = true;
	      tg.add_lit(rdEq);
              tg.mark2(rdEq);
	      continue;
	    }
	    rdDeq = m.mk_not(rdEq);
	    if (!tg.is_marked2(rdDeq) && mdl.is_true(rdDeq)) {
	      progress = true;
	      tg.add_lit(rdDeq);
              tg.mark2(rdDeq);
	      continue;
	    }
	  }
	}
      }
    } while(progress);
    return sz < terms.size();
  }

public:
  impl(ast_manager &m, params_ref const &p)
    : m(m), m_array_util(m), m_dt_util(m), m_vars(m), m_reduce_all_selects(false) {}

  void operator()(app_ref_vector &vars, expr_ref &inp, model& mdl, bool reduce_all_selects = false) {
    if (!reduce_all_selects && vars.empty())
      return;
    m_reduce_all_selects = reduce_all_selects;
    app_ref_vector arrIndices(m);
    collect_array_indices(inp, vars, arrIndices);
    // m_vars are array and ADT variables to be projected vars are
    // variables that cannot be eliminated after MBP. These are
    // variables of other sorts introduced by the MBP
    // procedure. e.g. when eliminating arrays, new variables of index
    // type are created and added to vars
    app_ref_vector other_vars(m);
    for(auto v : vars) {
      if (!m_dt_util.is_datatype(v->_get_sort()) && !m_array_util.is_array(v))
	other_vars.push_back(v);
      else if (!arrIndices.contains(v))
	m_vars.push_back(v);
    }
    vars.reset();
    for (auto v : arrIndices)
      vars.push_back(v);
    for (auto v : other_vars)
      vars.push_back(v);
    expr_ref_vector fml(m);
    mbp::term_graph tg(m);
    tg.add_vars(m_vars);
    flatten_and(inp, fml);
    for(expr *e : fml) {
      tg.add_lit(e);
    }
    bool progress1 = false, progress2 = false;
    do {
      progress1 = mbp_arr(fml, tg, mdl, vars);
      progress2 = mbp_adt(fml, tg, mdl, vars);
    } while(progress1 || progress2);
    TRACE("mbp_tg", tout << "mbp tg " << mk_and(tg.get_lits()););
    inp = tg.to_ground_expr();
    SASSERT(!contains_vars(inp, m_vars));
    remove_peq(inp, inp);
    TRACE("mbp_tg", tout << "after mbp tg " << inp;);
  }
};

qe_mbp_tg::qe_mbp_tg(ast_manager &m, params_ref const &p) {
  m_impl = alloc(impl, m, p);
}

qe_mbp_tg::~qe_mbp_tg() { dealloc(m_impl); }

void qe_mbp_tg::operator()(app_ref_vector &vars, expr_ref &fml, model& mdl, bool reduce_all_selects) {
  (*m_impl)(vars, fml, mdl, reduce_all_selects);
}

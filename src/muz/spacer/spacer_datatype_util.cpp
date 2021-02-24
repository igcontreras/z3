/*++
  Copyright (c) 2020 Arie Gurfinkel

  Module Name:

  spacer_datatype_util.cpp

  Abstract:

  Helper functions for handling datatypes in Spacer

  Author:

  Hari Govind V K
  Arie Gurfinkel


  --*/

#include "muz/spacer/spacer_datatype_util.h"
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/expr_abstract.h"
#include "ast/for_each_expr.h"

namespace spacer {

void get_selector_total_axioms(ast_manager &m, const sort_ref_vector &sorts,
                               expr_ref_vector &res) {
    datatype_util u(m);
    for (auto s : sorts) {
        SASSERT(u.is_datatype(s));
        get_selector_total_axioms(m, s, res);
    }
}

void get_selector_total_axioms(ast_manager &m, sort *s, expr_ref_vector &res) {
    datatype_util u(m);
    unsigned sz = u.get_datatype_num_constructors(s);
    // if (u.datatype_params(s).size() > 0) NOT_IMPLEMENTED_YET();
    ptr_vector<func_decl> const *cnstrs = u.get_datatype_constructors(s);
    for (unsigned i = 0; i < sz; i++) {
        func_decl *cnstr = cnstrs->get(i);
        get_selector_total_axioms(m, s, cnstr, res);
    }
}

void get_selector_total_axioms(ast_manager &m, sort *s, func_decl *cnstr,
                               expr_ref_vector &res) {
    datatype_util u(m);
    ptr_vector<func_decl> const *accessors = u.get_constructor_accessors(cnstr);
    ptr_vector<func_decl> const *cnstrs = u.get_datatype_constructors(s);
    unsigned num_sel = cnstr->get_arity();
    unsigned sz = u.get_datatype_num_constructors(s);
    func_decl *o_cnstr, *accessor;
    for (unsigned i = 0; i < num_sel; i++) {
        accessor = accessors->get(i);
        for (unsigned j = 0; j < sz; j++) {
            o_cnstr = cnstrs->get(j);
            if (u.get_accessor_constructor(accessor) == o_cnstr) continue;
            if (o_cnstr->get_arity() != 0) mk_non_null_axiom(o_cnstr, accessor, m, res);
            else mk_null_axiom(o_cnstr, accessor, m, res);
           }
    }
}

//given a nullary constructor \p cnstr and a non matching \p accessor, add
//accessor(cnstr) = fresh_value to \p res
void mk_null_axiom(func_decl* cnstr, func_decl* accessor, ast_manager& m, expr_ref_vector& res) {
    SASSERT(cnstr->get_arity() == 0);
    expr_ref sel_app(m), eq(m), rhs(m);
    sel_app = m.mk_app(accessor, to_expr(m.mk_const(cnstr)));
    sort *r = accessor->get_range();
    rhs = m.get_some_value(r);
    eq = m.mk_eq(sel_app, rhs);
    res.push_back(eq);
}

// given a non nullary constructor \p cnstr and a non matching \p accessor, add
// \forall \vd. accessor(cnstr(\vd)) = fresh_value to \p res
void mk_non_null_axiom(func_decl *cnstr, func_decl *accessor, ast_manager &m,
                   expr_ref_vector &res) {
    SASSERT(cnstr->get_arity() != 0);
    expr_ref sel_app(m), eq(m), rhs(m), cnstr_app(m), q_body(m), q_app(m);
    unsigned sz = cnstr->get_arity();
    ptr_buffer<sort> sorts;
    sort* s;
    svector<symbol> names;
    expr_ref_vector vars(m);
    expr* var;
    for(unsigned i = 0; i < sz; i++) {
        s = cnstr->get_domain(i);
        sorts.push_back(s);
        var = m.mk_fresh_const(cnstr->get_name(), s);
        vars.push_back(var);
        names.push_back(to_app(var)->get_decl()->get_name());
    }
    cnstr_app = m.mk_app(cnstr, vars);
    sel_app = m.mk_app(accessor, cnstr_app);
    sort *r = accessor->get_range();
    rhs = m.get_some_value(r);
    eq = m.mk_eq(sel_app, rhs);
    q_body = expr_abstract(m, 0, vars.size(), vars.c_ptr(), eq);
    q_app = m.mk_forall(sz, sorts.c_ptr(), names.c_ptr(), q_body);
    res.push_back(q_app);
}

namespace get_dt_ns {
struct found {};
struct get_dt_proc {
    ast_manager &m;
    datatype_util m_dt;
    sort_ref_vector &m_sorts;
    get_dt_proc(ast_manager &a_m, sort_ref_vector &res)
        : m(a_m), m_dt(m), m_sorts(res) {}
    void operator()(expr *n) const {}
    void operator()(app *n) {
        sort *s = n->get_sort();
        if (m_dt.is_datatype(s) && !m_sorts.contains(s)) m_sorts.push_back(s);
    }
};
} // namespace get_dt_ns

void get_datatype_sorts(expr_ref e, sort_ref_vector &s) {
    get_dt_ns::get_dt_proc t(e.get_manager(), s);
    for_each_expr(t, e);
}
} // namespace spacer

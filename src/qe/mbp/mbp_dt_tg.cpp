/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    mbp_dt_tg.cpp

Abstract:

    Apply rules for model based projection for datatypes on a term graph

Author:

    Hari Govind V K (hgvk94) 2023-03-07

Revision History:

--*/
#include "qe/mbp/mbp_dt_tg.h"
#include "qe/mbp/mbp_qel_util.h"

void mbp_dt_tg::rm_select(expr* term) {
    SASSERT(is_app(term) && m_dt_util.is_accessor(to_app(term)->get_decl()) && is_var(to_app(term)->get_arg(0)));
    TRACE("mbp_tg", tout << "applying rm_select on " << expr_ref(term, m););
    expr* v = to_app(term)->get_arg(0), *sel, *eq;
    app_ref u(m);
    app_ref_vector new_vars(m);
    func_decl* cons = m_dt_util.get_accessor_constructor(to_app(term)->get_decl());
    ptr_vector<func_decl> const* accessors =  m_dt_util.get_constructor_accessors(cons);
    for (unsigned i = 0; i < accessors->size(); i++) {
        func_decl* d = accessors->get(i);
        sel = m.mk_app(d, v);
        u = m_tg.get_const_in_class(sel);
        if (u) {
            new_vars.push_back(u);
            continue;
        }
        u = new_var(d->get_range(), m);
        m_new_vars.push_back(u);
        m_tg.add_var(u);
        new_vars.push_back(u);
        eq = m.mk_eq(sel, u);
        m_tg.add_lit(eq);
        m_mdl.register_decl(u->get_decl(), m_mdl(sel));
    }
    eq = m.mk_eq(v, m.mk_app(cons, new_vars));
    m_tg.add_lit(eq);
}

void mbp_dt_tg::deconstruct_eq(expr* cons, expr* rhs) {
    TRACE("mbp_tg", tout << "applying deconstruct_eq on " << expr_ref(cons, m););
    ptr_vector<func_decl> const* accessors = m_dt_util.get_constructor_accessors(to_app(cons)->get_decl());
    for (unsigned i = 0; i < accessors->size(); i++) {
        app* a = m.mk_app(accessors->get(i), rhs);
        expr* newRhs = to_app(cons)->get_arg(i);
        m_tg.add_lit(m.mk_eq(a, newRhs));
    }
    func_decl* is_cons = m_dt_util.get_constructor_recognizer(to_app(cons)->get_decl());
    m_tg.add_lit(m.mk_app(is_cons, rhs));
}

void mbp_dt_tg::deconstruct_neq(expr* cons, expr* rhs) {
    TRACE("mbp_tg", tout << "applying deconstruct_neq on " << expr_ref(cons, m););
    ptr_vector<func_decl> const* accessors = m_dt_util.get_constructor_accessors(to_app(cons)->get_decl());
    func_decl* is_cons = m_dt_util.get_constructor_recognizer(to_app(cons)->get_decl());
    expr* a = m.mk_app(is_cons, rhs);
    if (m_mdl.is_false(a)) {
      m_tg.add_lit(m.mk_not(a));
      return;
    }
    m_tg.add_lit(a);

    for (unsigned i = 0; i < accessors->size(); i++) {
        app* a = m.mk_app(accessors->get(i), rhs);
        expr* newRhs = to_app(cons)->get_arg(i);
        expr* eq = m.mk_eq(a, newRhs);
        if (m_mdl.is_false(eq)) {
            m_tg.add_lit(m.mk_not(eq));
            break;
        }
    }
}

bool mbp_dt_tg::operator()() {
    expr *cons, *rhs, *f, *term;
    bool progress = false;
    m_new_vars.reset();
    TRACE("mbp_tg", tout << "Iterating over terms of tg";);
    //Not resetting terms because get_terms calls resize on terms
    m_tg.get_terms(terms, false);
    for (unsigned i = 0; i < terms.size(); i++) {
        term = terms.get(i);
        SASSERT(!m.is_distinct(term));
        if (is_seen(term)) continue;
        if (m_tg.is_cgr(term)) continue;
        if (is_app(term) && m_dt_util.is_accessor(to_app(term)->get_decl()) && is_var(to_app(term)->get_arg(0))) {
            mark_seen(term);
            progress = true;
            rm_select(term);
            continue;
        }
        if (is_constructor_app(term, cons, rhs)) {
            mark_seen(term);
            progress = true;
            deconstruct_eq(cons, rhs);
            continue;
        }
        if (m_use_mdl && m.is_not(term, f) && is_constructor_app(f, cons, rhs)) {
          mark_seen(term);
          progress = true;
          deconstruct_neq(cons, rhs);
          continue;
        }
    }
    return progress;
}

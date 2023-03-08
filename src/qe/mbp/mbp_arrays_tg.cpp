/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    mbp_arrays_tg.cpp

Abstract:

    Apply rules for model based projection for arrays on a term graph

Author:

    Hari Govind V K (hgvk94) 2023-03-07

Revision History:

--*/

#include "qe/mbp/mbp_arrays_tg.h"
#include "qe/mbp/mbp_qel_util.h"
#include "qe/mbp/mbp_arrays.h"
#include "util/obj_hashtable.h"
#include "util/obj_pair_hashtable.h"

peq mbp_array_tg::mk_peq(expr* e1, expr* e2, vector<expr_ref_vector>& indices) {
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

void mbp_array_tg::elimwreq(peq p, bool is_neg) {
    SASSERT(is_arr_write(p.lhs()));
    TRACE("mbp_tg", tout << "applying elimwreq on " << expr_ref(p.mk_peq(), m););
    vector<expr_ref_vector> indices;
    expr* j = to_app(p.lhs())->get_arg(1);
    bool in = false;
    p.get_diff_indices(indices);
    expr* eq;
    expr_ref_vector deq(m);
    for(expr_ref_vector& e : indices) {
        for (expr* i : e) {
            if (m_mdl.is_true(m.mk_eq(j, i))) {
                in = true;
                eq = m.mk_eq(j, i);
                break;
            }
            else deq.push_back(i);
        }
    }
    if (in) {
        peq p_new = mk_peq(to_app(p.lhs())->get_arg(0), p.rhs(), indices);
        m_tg.add_lit(eq);
        expr* p_new_expr = is_neg ? m.mk_not(p_new.mk_peq()) : p_new.mk_peq();
        m_tg.add_lit(p_new_expr);
        m_tg.add_lit(m.mk_eq(p_new_expr, p.mk_peq()));
    }
    else {
        for(expr* d : deq) {
            eq = m.mk_not(m.mk_eq(j, d));
            m_tg.add_lit(eq);
        }
        expr_ref_vector setOne(m);
        setOne.push_back(j);
        indices.push_back(setOne);
        peq p_new = mk_peq(to_app(p.lhs())->get_arg(0), p.rhs(), indices);
        expr* args[2] = {p.rhs(), j};
        expr* rd = m_array_util.mk_select(2, args);
        eq = m.mk_eq(rd, to_app(p.lhs())->get_arg(2));
        if (!is_neg) {
            m_tg.add_lit(p_new.mk_peq());
            m_tg.add_lit(eq);
            m_tg.add_eq(p.mk_peq(), p_new.mk_peq());
        }
        else {
            SASSERT(m_mdl.is_false(p_new.mk_peq()) || m_mdl.is_false(eq));
            if (m_mdl.is_false(p_new.mk_peq())) {
                m_tg.add_lit(mk_not(p_new.mk_peq()));
                m_tg.add_eq(p.mk_peq(), p_new.mk_peq());
            }
            if (m_mdl.is_false(eq)) {
                m_tg.add_lit(m.mk_not(eq));
            }
        }
    }
}

void mbp_array_tg::add_rdVar(expr* rd) {
    //do not assign new variable if rd is already equal to a value
    if (m_tg.has_val_in_class(rd)) return;
    TRACE("mbp_tg", tout << "applying add_rdVar on " << expr_ref(rd, m););
    app_ref u = new_var(to_app(rd)->get_sort(), m);
    m_new_vars.push_back(u);
    m_tg.add_var(u);
    expr* eq = m.mk_eq(u, rd);
    m_tg.add_lit(eq);
    m_mdl.register_decl(u->get_decl(), m_mdl(rd));
}

void mbp_array_tg::elimeq(peq p) {
    TRACE("mbp_tg", tout << "applying elimeq on " << expr_ref(p.mk_peq(), m););
    app_ref_vector aux_consts(m);
    expr_ref eq(m);
    expr_ref sel(m);
    eq = p.mk_eq(aux_consts, true);
    vector<expr_ref_vector> indices;
    p.get_diff_indices(indices);
    vector<expr_ref_vector>::iterator itr = indices.begin();
    unsigned i = 0;
    for(app* a : aux_consts) {
        m_new_vars.push_back(a);
        m_tg.add_var(a);
        auto const& indx =  std::next(itr, i);
        SASSERT(indx->size() == 1);
        expr *args[2] = {to_app(p.lhs()), to_app(indx->get(0))};
        sel = m_array_util.mk_select(2, args);
        m_mdl.register_decl(a->get_decl(), m_mdl(sel));
        i++;
    }
    m_tg.add_lit(eq);
    m_tg.add_lit(m.mk_true());
    m_tg.add_eq(p.mk_peq(), m.mk_true());
    TRACE("mbp_tg", tout << "added lit  " << eq;);
}

void mbp_array_tg::elimrdwr(expr* term) {
    SASSERT(is_rd_wr(term, true));
    TRACE("mbp_tg", tout << "applying elimrdwr on " << expr_ref(term, m););
    expr* wr_ind = to_app(to_app(term)->get_arg(0))->get_arg(1);
    expr* rd_ind = to_app(term)->get_arg(1);
    expr *eq = m.mk_eq(wr_ind, rd_ind);
    expr_ref e(m);
    if (m_mdl.is_true(eq)) {
        m_tg.add_lit(eq);
        e =  to_app(to_app(term)->get_arg(0))->get_arg(2);
    }
    else {
        m_tg.add_lit(m.mk_not(eq));
        expr* args[2] = {to_app(to_app(term)->get_arg(0))->get_arg(0), to_app(term)->get_arg(1)};
        e = m_array_util.mk_select(2, args);
    }
    m_tg.add_lit(m.mk_eq(term, e));
}

// iterate through all terms in m_tg and apply all array MBP rules once
// returns true if any rules were applied
bool mbp_array_tg::operator()() {
    TRACE("mbp_tg", tout << "Iterating over terms of tg";);
    indices.reset();
    rdTerms.reset();
    m_new_vars.reset();
    expr_ref e(m), rdEq(m), rdDeq(m);
    expr* nt, *term;
    bool progress = false, is_neg = false;

    //Not resetting terms because get_terms calls resize on terms
    m_tg.get_terms(terms, !m_reduce_all_selects);
    for (unsigned i = 0; i < terms.size(); i++) {
        term = terms.get(i);
        SASSERT(!m.is_distinct(term));
        if (m_seen.is_marked(term)) continue;
        TRACE("mbp_tg", tout << "processing " << expr_ref(term, m););
        if (should_create_peq(term)) {
            // rewrite array eq as peq
            mark_seen(term);
            progress = true;
            e = mk_peq(to_app(term)->get_arg(0), to_app(term)->get_arg(1)).mk_peq();
            m_tg.add_lit(e);
            m_tg.add_lit(m.mk_eq(term, e));
            continue;
        }
        nt = term;
        is_neg = m.is_not(term, nt);
        if (is_app(nt) && is_partial_eq(to_app(nt))) {
            peq p(to_app(nt), m);
            if (m_use_mdl && is_arr_write(p.lhs())) {
                mark_seen(nt);
                mark_seen(term);
                progress = true;
                elimwreq(p, is_neg);
                continue;
            }
            if (is_var(p.lhs()) && !contains_var(p.rhs(), app_ref(to_app(p.lhs()), m), m)) {
                mark_seen(nt);
                mark_seen(term);
                progress = true;
                elimeq(p);
                continue;
            }
            //eliminate eq when the variable is on the rhs
            if (is_var(p.rhs()) && !contains_var(p.lhs(), app_ref(to_app(p.rhs()), m), m)) {
                p.get_diff_indices(indices);
                peq p_new = mk_peq(p.rhs(), p.lhs(), indices);
                mark_seen(nt);
                mark_seen(term);
                progress = true;
                elimeq(p_new);
                continue;
            }
        }
        if (m_use_mdl && is_rd_wr(term, m_reduce_all_selects)) {
            mark_seen(term);
            progress = true;
            elimrdwr(term);
            continue;
        }
    }

    // iterate over term graph again to collect read terms
    // irrespective of whether they have been marked or not
    rdTerms.reset();
    for (unsigned i = 0; i < terms.size(); i++) {
        term = terms.get(i);
        if (m_array_util.is_select(term) && has_var(to_app(term)->get_arg(0))) {
            rdTerms.push_back(term);
            if (is_seen(term)) continue;
            add_rdVar(term);
            mark_seen(term);
        }
    }
    if (!m_use_mdl) return progress;
    expr *e1, *e2, *a1, *a2, *i1, *i2;
    for (unsigned i = 0; i < rdTerms.size(); i++) {
        e1 = rdTerms.get(i);
        a1 = to_app(e1)->get_arg(0);
        i1 = to_app(e1)->get_arg(1);
        for (unsigned j = i+1; j < rdTerms.size(); j++) {
            e2 = rdTerms.get(j);
            a2 = to_app(e2)->get_arg(0);
            i2 = to_app(e2)->get_arg(1);
            if (!is_seen(e1, e2) && a1->get_id() == a2->get_id()) {
                mark_seen(e1, e2);
                rdEq = m.mk_eq(i1, i2);
                if (m_mdl.is_true(rdEq)) {
                    progress = true;
                    m_tg.add_lit(rdEq);
                    continue;
                }
                rdDeq = m.mk_not(rdEq);
                if (m_mdl.is_true(rdDeq)) {
                    progress = true;
                    m_tg.add_lit(rdDeq);
                    continue;
                }
            }
        }
    }
    return progress;
}

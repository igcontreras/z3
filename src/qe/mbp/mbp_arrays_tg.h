/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    mbp_arrays_tg.h

Abstract:

    Apply rules for model based projection for arrays on a term graph

Author:

    Hari Govind V K (hgvk94) 2023-03-07

Revision History:

--*/


#pragma once

#include "qe/mbp/mbp_arrays.h"
#include "qe/mbp/mbp_qel_util.h"
#include "qe/mbp/mbp_term_graph.h"
#include "util/obj_hashtable.h"
#include "util/obj_pair_hashtable.h"

class mbp_array_tg {
    typedef std::pair<expr *, expr *> expr_pair;
    ast_manager& m;
    array_util m_array_util;
    mbp::term_graph& m_tg;
    //TODO: cache mdl evaluation eventhough we extend m_mdl
    model& m_mdl;

    //set of all variables in the formula. To make contains check faster
    obj_hashtable<app> &m_vars_set;
    // vector of all variables in the formula. For final output
    //TODO: merge m_tg_project_vars and m_all_vars
    app_ref_vector &m_vars;

    expr_sparse_mark &m_seen;
    obj_pair_hashtable<expr, expr> m_seenp;

    bool m_reduce_all_selects;

    // variables required for applying rules
    vector<expr_ref_vector> indices;
    expr_ref_vector terms, rdTerms;

    bool has_var(expr* t) {
        return contains_vars(t, m_vars_set, m);
    }

    bool has_arr_var(expr* t) {
        return contains_vars(t, m_vars_set, m, true);
    }

    bool is_var(expr* t) {
        return is_uninterp_const(t) && has_var(t);
    }

    bool is_wr_on_rhs(expr* e) {
        return is_app(e) && is_partial_eq(to_app(e)) && is_wr_on_rhs(to_app(e)->get_arg(0), to_app(e)->get_arg(1));
    }

    bool is_wr_on_rhs(expr* lhs, expr* rhs) {
        return (is_arr_write(rhs) && !is_arr_write(lhs));
    }

    bool is_arr_write(expr* t) {
        if (!m_array_util.is_store(t)) return false;
        return contains_vars(to_app(t), m_vars_set, m);
    }

    bool is_rd_wr(expr* t, bool all = false) {
        if (!m_array_util.is_select(t) || !m_array_util.is_store(to_app(t)->get_arg(0))) return false;
        return all || contains_vars(to_app(to_app(t)->get_arg(0))->get_arg(0), m_vars_set, m);
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

    peq mk_peq(expr* e1, expr* e2, vector<expr_ref_vector>& indices);

    void elimwreq(peq p, bool is_neg);

    void add_rdVar(expr* rd);

    void elimeq(peq p);

    void elimrdwr(expr* term);

    void mark_seen(expr* t) { m_seen.mark(t); }
    bool is_seen(expr* t) { return m_seen.is_marked(t); }
    void mark_seen(expr* t1, expr* t2) { m_seenp.insert(expr_pair(t1, t2)); }
    bool is_seen(expr* t1, expr* t2) { return m_seenp.contains(expr_pair(t1, t2)) || m_seenp.contains(expr_pair(t2, t1)); }

    public:
        mbp_array_tg(ast_manager& man, mbp::term_graph& tg, model& mdl, obj_hashtable<app> &vars_set, app_ref_vector &vars, expr_sparse_mark &seen):
            m(man), m_array_util(m), m_tg(tg), m_mdl(mdl), m_vars_set(vars_set), m_vars(vars), m_seen(seen), m_reduce_all_selects(false), terms(m), rdTerms(m) {}

        void set_reduce_all_selects() { m_reduce_all_selects = true; }

        // iterate through all terms in m_tg and apply all array MBP rules once
        // returns true if any rules were applied
        bool operator()();
        void reset() {
            m_seen.reset();
            m_vars_set.reset();
            //Not resetting terms because get_terms calls resize on terms
        }
};

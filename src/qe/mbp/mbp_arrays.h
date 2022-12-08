/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    mbp_arrays.h

Abstract:

    Model based projection for arrays

Author:

    Nikolaj Bjorner (nbjorner) 2015-06-13

Revision History:

--*/


#pragma once

#include "ast/array_decl_plugin.h"
#include "qe/mbp/mbp_plugin.h"

namespace {
    bool is_partial_eq (app* a);

    /**
     * \brief utility class for partial equalities
     *
     * A partial equality (a ==I b), for two arrays a,b and a finite set of indices I holds
     *   iff (Forall i. i \not\in I => a[i] == b[i]); in other words, it is a
     *   restricted form of the extensionality axiom
     *
     * using this class, we denote (a =I b) as f(a,b,i0,i1,...)
     *   where f is an uninterpreted predicate with name PARTIAL_EQ and
     *   I = {i0,i1,...}
     */

    // TBD: make work for arrays with multiple arguments.
    class peq {
        ast_manager&        m;
        expr_ref            m_lhs;
        expr_ref            m_rhs;
        vector<expr_ref_vector>  m_diff_indices;
        func_decl_ref       m_decl;     // the partial equality declaration
        app_ref             m_peq;      // partial equality application
        app_ref             m_eq;       // equivalent std equality using def. of partial eq
        array_util          m_arr_u;

    public:
        static const char* PARTIAL_EQ;

        peq (app* p, ast_manager& m):
            m (m),
            m_lhs (p->get_arg (0), m),
            m_rhs (p->get_arg (1), m),
            m_decl (p->get_decl (), m),
            m_peq (p, m),
            m_eq (m),
            m_arr_u (m)
        {
            VERIFY (is_partial_eq (p));
            SASSERT (m_arr_u.is_array (m_lhs) &&
                     m_arr_u.is_array (m_rhs) &&
                m_lhs->get_sort() == m_rhs->get_sort());
            unsigned arity = get_array_arity(m_lhs->get_sort());
            for (unsigned i = 2; i < p->get_num_args (); i += arity) {
                SASSERT(arity + i <= p->get_num_args());
                expr_ref_vector vec(m);
                vec.append(arity, p->get_args() + i);
                m_diff_indices.push_back (vec);
            }
        }

        peq (expr* lhs, expr* rhs, vector<expr_ref_vector> const& diff_indices, ast_manager& m):
            m (m),
            m_lhs (lhs, m),
            m_rhs (rhs, m),
            m_diff_indices (diff_indices),
            m_decl (m),
            m_peq (m),
            m_eq (m),
            m_arr_u (m) {
            SASSERT (m_arr_u.is_array (lhs) &&
                     m_arr_u.is_array (rhs) &&
                     lhs->get_sort() == rhs->get_sort());
            ptr_vector<sort> sorts;
            sorts.push_back (m_lhs->get_sort ());
            sorts.push_back (m_rhs->get_sort ());
            for (auto const& v : diff_indices) {
                SASSERT(v.size() == get_array_arity(m_lhs->get_sort()));
                for (expr* e : v)
                    sorts.push_back (e->get_sort());
            }
            m_decl = m.mk_func_decl (symbol (PARTIAL_EQ), sorts.size (), sorts.data (), m.mk_bool_sort ());
        }

        expr_ref lhs () { return m_lhs; }

        expr_ref rhs () { return m_rhs; }

        void get_diff_indices (vector<expr_ref_vector>& result) { result.append(m_diff_indices); }

        app_ref mk_peq () {
            if (!m_peq) {
                ptr_vector<expr> args;
                args.push_back (m_lhs);
                args.push_back (m_rhs);
                for (auto const& v : m_diff_indices) {
                    args.append (v.size(), v.data());
                }
                m_peq = m.mk_app (m_decl, args.size (), args.data ());
            }
            return m_peq;
        }

        app_ref mk_eq (app_ref_vector& aux_consts, bool stores_on_rhs = true) {
            if (!m_eq) {
                expr_ref lhs (m_lhs, m), rhs (m_rhs, m);
                if (!stores_on_rhs) {
                    std::swap (lhs, rhs);
                }
                // lhs = (...(store (store rhs i0 v0) i1 v1)...)
                sort* val_sort = get_array_range (lhs->get_sort());
                for (expr_ref_vector const& diff : m_diff_indices) {
                    ptr_vector<expr> store_args;
                    store_args.push_back (rhs);
                    store_args.append (diff.size(), diff.data());
                    app_ref val(m.mk_fresh_const ("diff", val_sort), m);
                    store_args.push_back (val);
                    aux_consts.push_back (val);
                    rhs = m_arr_u.mk_store (store_args);
                }
                m_eq = m.mk_eq (lhs, rhs);
            }
            return m_eq;
        }
    };

    const char* peq::PARTIAL_EQ = "!partial_eq";

    bool is_partial_eq (app* a) {
        return a->get_decl ()->get_name () == peq::PARTIAL_EQ;
    }
}

namespace mbp {

    class array_project_plugin : public project_plugin {
        struct imp;
        imp* m_imp;
    public:
        array_project_plugin(ast_manager& m);
        ~array_project_plugin() override;
        bool operator()(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) override;
        bool solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) override;
        void operator()(model& model, app_ref_vector& vars, expr_ref& fml, app_ref_vector& aux_vars, bool reduce_all_selects);
        family_id get_family_id() override;
        bool project(model& model, app_ref_vector& vars, expr_ref_vector& lits, vector<def>& defs) override;
        void saturate(model& model, func_decl_ref_vector const& shared, expr_ref_vector& lits) override;

    };

};


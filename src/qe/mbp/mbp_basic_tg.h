/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    mbp_basic_tg.h

Abstract:

    Apply rules for model based projection for basic types, on a term graph

Author:

    Hari Govind V K (hgvk94) 2023-03-07

Revision History:

--*/
#pragma once

#include "qe/mbp/mbp_qel_util.h"
#include "qe/mbp/mbp_term_graph.h"
#include "qe/mbp/mbp_tg_plugins.h"
#include "util/obj_hashtable.h"

class mbp_basic_tg: public mbp_tg_plugin {
    ast_manager& m;
    mbp::term_graph& m_tg;
    //TODO: cache mdl evaluation eventhough we extend m_mdl
    model& m_mdl;

    //set of variables on which to apply MBP rules
    obj_hashtable<app> &m_vars_set;

    //variables created in the last iteration of MBP application
    app_ref_vector m_new_vars;

    expr_sparse_mark &m_seen;

    expr_ref_vector terms;
    bool m_use_mdl;

    void mark_seen(expr* t) { m_seen.mark(t); }
    bool is_seen(expr* t) { return m_seen.is_marked(t); }


    public:
        mbp_basic_tg(ast_manager& man, mbp::term_graph& tg, model& mdl, obj_hashtable<app> &vars_set, expr_sparse_mark &seen):
            m(man), m_tg(tg), m_mdl(mdl), m_vars_set(vars_set), m_new_vars(m), m_seen(seen), terms(m), m_use_mdl(false) {}
        // iterate through all terms in m_tg and apply all basic MBP rules once
        // returns true if any rules were applied
        bool apply() override;
        ~mbp_basic_tg() override = default;
        void use_model() override { m_use_mdl = true; }
        void get_new_vars(app_ref_vector*& t) override { t = &m_new_vars; }
        family_id get_family_id() const override { return m.get_basic_family_id(); }

};

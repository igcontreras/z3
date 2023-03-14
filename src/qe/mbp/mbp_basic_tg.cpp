/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    mbp_basic_tg.cpp

Abstract:

    Apply rules for model based projection for basic types, on a term graph

Author:

    Hari Govind V K (hgvk94) 2023-03-07

Revision History:

--*/

#include "qe/mbp/mbp_basic_tg.h"
#include "ast/ast.h"
#include "ast/expr_functors.h"
#include "util/debug.h"

bool mbp_basic_tg::apply() {
    if (!m_use_mdl) return false;
    expr *term, *c, *th, *el;
    expr_ref nterm(m);
    bool progress = false;
    TRACE("mbp_tg", tout << "Iterating over terms of tg";);
    //Not resetting terms because get_terms calls resize on terms
    m_tg.get_terms(terms, false);
    for (unsigned i = 0; i < terms.size(); i++) {
        term = terms.get(i);
        //Unsupported operators
        SASSERT(!m.is_and(term));
        SASSERT(!m.is_or(term));
        SASSERT(!m.is_distinct(term));
        SASSERT(!m.is_implies(term));

        if (is_seen(term)) continue;
        if (m_tg.is_cgr(term)) continue;
        if (m.is_ite(term, c, th, el)) {
            mark_seen(term);
            progress = true;
            if (m_mdl.is_true(c)) {
                m_tg.add_lit(c);
                m_tg.add_eq(term, th);
            }
            else {
                if (m.is_not(c)) nterm = to_app(c)->get_arg(0);
                else nterm = m.mk_not(c);
                m_tg.add_lit(nterm);
                m_tg.add_eq(term, el);
            }
            continue;
        }
    }
    return progress;
}

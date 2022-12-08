/*++

  Module Name:

    qe_mbp_tg.h

Abstract:

    Model Based Projection based on term graph

Author:

    Hari Govind V K (hgvk94) 2022-07-12

Revision History:


--*/

#pragma once

#include "ast/ast.h"
#include "util/params.h"
#include "model/model.h"

class qe_mbp_tg {
    class impl;
    impl * m_impl;
public:

    qe_mbp_tg(ast_manager& m, params_ref const & p);

    ~qe_mbp_tg();

    /**
       Do model based projection
    */
  void operator()(app_ref_vector& vars, expr_ref& fml, model& mdl);
};

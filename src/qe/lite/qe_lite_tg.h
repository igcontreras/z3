/*++

  Module Name:

    qe_lite_tg.h

Abstract:

    Light weight partial quantifier-elimination for cubes using term graphs

Author:

    Isabel Garcia (igcontreras)

Revision History:


--*/

#pragma once

#include "ast/ast.h"
#include "util/uint_set.h"
#include "util/params.h"

class qe_lite_tg {
    class impl;
    impl * m_impl;
public:

    qe_lite_tg(ast_manager& m, params_ref const & p, bool use_array_der = true);

    ~qe_lite_tg();

    /**
       \brief Applies light-weight elimination of `vars` provided as vector
       of expressions to the cube `fml`. Returns the updated formula and updated
       set of variables that were not eliminated.
    */
    void operator()(app_ref_vector& vars, expr_ref& fml);
};

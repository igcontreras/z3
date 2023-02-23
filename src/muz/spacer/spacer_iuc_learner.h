/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_iuc_learner.h

Abstract:

    itp cores

Author:
    Isabel Garcia

Revision History:


--*/
#pragma once

#include "ast/ast.h"
#include "muz/spacer/spacer_util.h"
#include "muz/spacer/spacer_proof_utils.h"
#include "muz/spacer/spacer_iuc_proof.h"

#include "muz/spacer/spacer_unsat_core_learner.h"

#include "qe/mbp/mbp_term_graph.h" // for euf iuc

namespace spacer {

  class unsat_core_plugin;
  class iuc_proof;
  class iuc_learner : public unsat_core_learner {

    mbp::term_graph m_iuc_eg;

  public:
    iuc_learner(ast_manager &m, iuc_proof &pr) : unsat_core_learner(m,pr), m_iuc_eg(m){};
    virtual ~iuc_learner();

    void compute_unsat_core(expr_ref_vector& unsat_core) override;
    void add_lemma_to_core(expr* lemma) override;

    };

} // namespace spacer

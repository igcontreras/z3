/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_iuc_learner.cpp

Abstract:
   itp cores

Author:
    Isabel Garcia

Revision History:


--*/

#include "ast/for_each_expr.h"
#include "ast/proofs/proof_utils.h"
#include "muz/spacer/spacer_iuc_learner.h"
#include "muz/spacer/spacer_unsat_core_plugin.h"
#include "muz/spacer/spacer_iuc_proof.h"
#include "muz/spacer/spacer_util.h"


namespace spacer {

  // returns true if the literal is syntactically good for
  static bool is_iuc_lit(proof *step, ast_manager &m){
    if(m.is_asserted(step))
      return true;

    expr *fact = m.get_fact(step);

    return spacer::is_literal(m, fact) &&
      !(m.is_eq(fact) && m.is_eq(to_app(fact)->get_arg(0))); // not like (= (= a b) (= b a))
  }

  iuc_learner::~iuc_learner() {}

  void iuc_learner::compute_unsat_core(expr_ref_vector &unsat_core) {

    // std::ofstream ofs;
    // ofs.open("/tmp/proof.dot");
    // m_pr.display_dot(ofs);
    // ofs.close();

    proof_visitor it(m_pr.get(), m); // proof pre visitor

    while (it.hasNext()) {
        proof* curr = it.next();

        if (!is_b_open(curr)) continue;

        // verbose_stream() << "Visiting: " << expr_ref(m.get_fact(curr), m)
        //                  << "\n";

        // TODO: is_b_pure checks that the node is not colored A. But it could
        // be colorable by both in this case the check does not hold. We
        // shouldn't even look at nodes that are fully colorable as A
        if (is_b_pure(curr) && is_iuc_lit(curr, m)) {
            add_lemma_to_core(m.get_fact(curr));
            set_closed(curr, true);
        }
        // try to get an unsat core from a node that mixes A-reasoning and
        // B-reasoning
        else if (is_a(curr) && is_b(curr)) {
            compute_partial_core(curr);
        }

        // an unsat core could not be obtained just by looking at this node, the
        // children have to be visited
        if(!is_closed(curr)) {
          it.visit_parents();
          // close because eventually the unsat core for the children will be
          // computed and the node does not need to be visited again
          set_closed(curr, true);
        }
    }

    finalize();

    m_iuc_eg.to_expr(unsat_core);
}

void iuc_learner::add_lemma_to_core(expr* lemma) {
    m_iuc_eg.add_lit(lemma);
}

}

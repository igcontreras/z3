/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_unsat_core_plugin.h

Abstract:
   plugin for itp cores

Author:
    Bernhard Gleiss

Revision History:


--*/
#pragma once

#include "ast/ast.h"
#include "util/min_cut.h"
#include "ast/proofs/proof_utils.h" // ugly?

namespace spacer {

    class unsat_core_learner;


    class unsat_core_plugin {
    protected:
        typedef vector<std::pair<rational, app*>> coeff_lits_t;
        ast_manager& m;
    public:
        unsat_core_plugin(unsat_core_learner& learner);
        virtual ~unsat_core_plugin() = default;
        virtual void compute_partial_core(proof* step) = 0;
        virtual void finalize(){};

        unsat_core_learner& m_ctx;
    };

    class unsat_core_plugin_lemma : public unsat_core_plugin {
    public:
        unsat_core_plugin_lemma(unsat_core_learner& learner) : unsat_core_plugin(learner){};
        void compute_partial_core(proof* step) override;
    private:
        void add_lowest_split_to_core(proof* step) const;
    };

    class unsat_core_plugin_farkas_lemma : public unsat_core_plugin {
    public:
        unsat_core_plugin_farkas_lemma(unsat_core_learner& learner,
                                       bool split_literals,
                                       bool use_constant_from_a=true) :
            unsat_core_plugin(learner),
            m_split_literals(split_literals),
            m_use_constant_from_a(use_constant_from_a) {};
        void compute_partial_core(proof* step) override;
    private:
        bool m_split_literals;
        bool m_use_constant_from_a;
        /*
         * compute linear combination of literals 'literals' having coefficients 'coefficients' and save result in res
         */
        expr_ref compute_linear_combination(const coeff_lits_t& coeff_lits);
    };

    class unsat_core_plugin_farkas_lemma_optimized : public unsat_core_plugin {
    public:
        unsat_core_plugin_farkas_lemma_optimized(unsat_core_learner& learner, ast_manager& m) : unsat_core_plugin(learner) {};
        void compute_partial_core(proof* step) override;
        void finalize() override;
    protected:
        vector<coeff_lits_t> m_linear_combinations;
        /*
         * compute linear combination of literals 'literals' having coefficients 'coefficients' and save result in res
         */
        expr_ref compute_linear_combination(const coeff_lits_t& coeff_lits);
    };

    class unsat_core_plugin_farkas_lemma_bounded : public unsat_core_plugin_farkas_lemma_optimized {
    public:
        unsat_core_plugin_farkas_lemma_bounded(unsat_core_learner& learner, ast_manager& m) : unsat_core_plugin_farkas_lemma_optimized(learner, m) {};
        void finalize() override;
    };

    class unsat_core_plugin_min_cut : public unsat_core_plugin {
    public:
        unsat_core_plugin_min_cut(unsat_core_learner& learner, ast_manager& m);
        void compute_partial_core(proof* step) override;
        void finalize() override;
    private:
        ast_mark m_visited; // saves for each node i whether the subproof with root i has already been added to the min-cut-problem
        obj_map<proof, unsigned> m_proof_to_node_minus; // maps proof-steps to the corresponding minus-nodes (the ones which are closer to source)
        obj_map<proof, unsigned> m_proof_to_node_plus; // maps proof-steps to the corresponding plus-nodes (the ones which are closer to sink)
        void advance_to_lowest_partial_cut(proof* step, ptr_vector<proof>& todo);
        void add_edge(proof* i, proof* j);

        vector<expr*> m_node_to_formula; // maps each node to the corresponding formula in the original proof
        ast_mark m_connected_to_s; // remember which nodes have already been connected to the supersource, in order to avoid multiple edges.

        min_cut m_min_cut;
    };

    class unsat_core_plugin_euf : public unsat_core_plugin {
      public:
        unsat_core_plugin_euf(unsat_core_learner &learner, ast_manager &m)
          : unsat_core_plugin(learner){};
        void compute_partial_core(proof *step) override;
    };

  class replay_plugin : public unsat_core_plugin {

  public:
    replay_plugin(unsat_core_learner &learner, ast_manager &m)
        : unsat_core_plugin(learner), m_b(m), m_b_lemmas(m), m_a(m),
          m_a_lemmas(m), m_h(m){};
    void compute_partial_core(proof *step) override;

  private:
    // B literals (except for proxy)
    expr_ref_vector m_b;
    // B lemmas (in a language useful for spacer itps)
    expr_ref_vector m_b_lemmas;
    // A clauses
    expr_ref_vector m_a;
    // A lemmas (derived from A in any language)
    expr_ref_vector m_a_lemmas;
    // hypotheses (that make A a cube, not the ones used to derive lemmas)
    expr_ref_vector m_h;

    void reset();
    void store_step(proof *pr, bool store_hyp);
    // extract data from proof
    void extract_from_proof(proof_visitor &pit, bool store_hyp);
    bool understands_proof(proof *pf); // should be plugin interface function
  };
}

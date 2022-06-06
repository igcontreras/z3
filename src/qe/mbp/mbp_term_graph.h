/**++
Copyright (c) Arie Gurfinkel

Module Name:

    mbp_term_graph.h

Abstract:

    Equivalence graph of terms

Author:

    Arie Gurfinkel

Notes:

--*/
#pragma once

#include "ast/ast.h"
#include "ast/is_variable_test.h"
#include "util/plugin_manager.h"
#include "qe/mbp/mbp_solve_plugin.h"
#include "model/model.h"

namespace mbp {

    class term;

    class term_graph {
        class projector;
        class cover;

        class is_variable_proc : public ::is_variable_proc {
            bool m_exclude;
            obj_hashtable<func_decl> m_decls, m_solved;
        public:
            bool operator()(const expr *e) const override;
            bool operator()(const term &t) const;

            void set_decls(const func_decl_ref_vector &decls, bool exclude);
            void mark_solved(const expr *e);
            void reset_solved() {m_solved.reset();}
            void reset() {m_decls.reset(); m_solved.reset(); m_exclude = true;}
            bool contains(func_decl *f) {
              return m_decls.contains(f) == m_exclude;
            }
        };

        struct term_hash { unsigned operator()(term const* t) const; };
        struct term_eq { bool operator()(term const* a, term const* b) const; };
        ast_manager &     m;
        ptr_vector<term>  m_terms;
        expr_ref_vector   m_lits; // NSB: expr_ref_vector?
        u_map<term* >     m_app2term;
        ast_ref_vector    m_pinned;
        projector*        m_projector;
        cover*            m_cover;
        u_map<expr *> m_term2app;
        plugin_manager<solve_plugin> m_plugins;
        ptr_hashtable<term, term_hash, term_eq> m_cg_table;
        vector<std::pair<term*,term*>> m_merge;
        bool             m_prop_ground = false;
        ptr_vector<term> m_gr_to_prop; // list of terms that now have a gr representative

        term_graph::is_variable_proc m_is_var;

        void merge(term &t1, term &t2);
        void propagate_gr(term &t);
        void merge_flush();

        term *mk_term(expr *t);
        term *get_term(expr *t);
        term *get_term(func_decl *f);

        term *internalize_term(expr *t);
        void internalize_eq(expr *a1, expr *a2);
        void internalize_lit(expr *lit);
        void internalize_distinct(expr *d);
        void internalize_deq(expr *a1, expr *a2);

        bool is_internalized(expr *a);

        bool term_lt(term const &t1, term const &t2);
        void pick_root (term &t);
        void pick_roots();

        void reset_marks();
        bool marks_are_clear();

        expr* mk_app_core(expr* a);
        expr_ref mk_app(term const &t);
        expr* mk_pure(term& t);
        expr_ref mk_app(expr *a);
        void mk_equalities(term const &t, expr_ref_vector &out);
        void mk_all_equalities(term const &t, expr_ref_vector &out);
        void display(std::ostream &out);

        bool is_pure_def(expr* atom, expr *& v);

        // variables (or terms?) to eliminate
        // useful to not pick roots that are in this vector if possible
        ptr_vector<term> m_elim;

      public:
        term_graph(ast_manager &m);
        ~term_graph();

        void set_vars(func_decl_ref_vector const& decls, bool exclude);

        ast_manager& get_ast_manager() const { return m;}

        void add_lit(expr *lit);
        void add_lits(expr_ref_vector const &lits) { for (expr* e : lits) add_lit(e); }
        void add_eq(expr* a, expr* b) { internalize_eq(a, b); }

        void reset();

        // deprecate?
        void to_lits(expr_ref_vector &lits, bool all_equalities = false,
                     bool repick_roots = true);
        expr_ref to_expr(bool repick_roots = true);

        /**
         * Return literals obtained by projecting added literals
         * onto the vocabulary of decls (if exclude is false) or outside the
         * vocabulary of decls (if exclude is true).
         */
        expr_ref_vector project();
        expr_ref_vector solve();
        expr_ref_vector project(model &mdl);

      /**
       * Return disequalities to ensure that disequalities between
       * excluded functions are preserved.
       * For example if f(a) = b, f(c) = d, and b and d are not
       * congruent, then produce the disequality a != c.
       */
      expr_ref_vector get_ackerman_disequalities();

        /**
         * Produce model-based disequality 
         * certificate corresponding to 
         * definition in BGVS 2020.
         * A disequality certificate is a reduced set of 
         * disequalities, true under mdl, such that the literals
         * can be satisfied when non-shared symbols are projected.
         */
      expr_ref_vector dcert(model& mdl, expr_ref_vector const& lits);

        /**
         * Produce a model-based partition.
         */
      vector<expr_ref_vector> get_partition(model& mdl);

        /**
         * Extract shared occurrences of terms whose sort are 
         * fid, but appear in a context that is not fid.
         * for example f(x + y) produces the shared occurrence
         * x + y when f is uninterpreted and x + y has sort Int or Real.
         */
        expr_ref_vector shared_occurrences(family_id fid);

        /**
         * Map expression that occurs in added literals into representative if it exists.
         */
        void  add_model_based_terms(model& mdl, expr_ref_vector const& terms);
        expr* rep_of(expr* e);

      // new methods by IG
        using deqs = bit_vector;
        struct add_deq_proc {
          uint64_t m_deq_cnt =
              0; // TODO: how can I declare a type for a very big number?
                 //       is this a bad idea?
          void operator()(term *t1, term *t2);
          void operator()(ptr_vector<term> &ts);
        };

        // -- disequalities added for output
        vector<std::pair<term*,term*>> m_deq_pairs;
        // -- maybe they are not necessary since they are in the original formula
        vector<ptr_vector<term>> m_deq_distinct;

        void mark_non_ground(func_decl_ref_vector &vars);
        void set_prop_gr(bool v) { m_prop_ground = v;}
        expr_ref_vector non_gr_terms();
        void gr_terms_to_lits(expr_ref_vector &lits, bool all_equalities);
        void mk_gr_equalities(term const &t, expr_ref_vector &out);
        void mk_all_gr_equalities(term const &t, expr_ref_vector &out);
        expr_ref to_gr_expr();
        void mb_cover(model& mdl);
        void add_deq_terms(term *t1, term *t2);
        void add_deq_terms(ptr_vector<term> &ts);

      private:
        void push_parents_propagate_gr(term &t);
        add_deq_proc m_add_deq;
    };
}

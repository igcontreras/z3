/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_summary.h

Abstract:

    summaries for EUF IUCs

Author:

    Isabel Garcia Contreras

Notes:


--*/

#pragma once

#include "ast/ast_smt2_pp.h" // TODO: remove
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_justification.h"
#include <unordered_map>

namespace euf {

class euf_summarizer {

  struct congr_sum {
    expr_ref_vector m_left_args;
    expr_ref_vector m_right_args;
    bool m_colorable = 0;

    congr_sum(ast_manager &m) : m_left_args(m), m_right_args(m){};
    void set_colorable() { m_colorable = true; }
    bool is_colorable() const { return m_colorable; }
    void reset() {
      m_left_args.reset();
      m_right_args.reset();
    }
  };

  struct sum_manager {
    ast_manager &m;
    expr_ref_vector &m_sum;
    expr_ref m_begin;
    expr * m_first_expr;
    expr_ref &m_first_sum;
    bool begins_colorable = false;

    sum_manager(expr_ref_vector &sum, expr * first_expr, expr_ref &first_sum)
        : m(sum.get_manager()), m_sum(sum), m_begin(sum.get_manager()),
          m_first_expr(first_expr), m_first_sum(first_sum) {
      m_begin = nullptr;
    }

    expr_ref open(expr_ref begin) {
      // verbose_stream() << "open: " << begin << "\n";
      SASSERT(begin);
      if(begin == m_first_expr) // do not push in the summary, store in m_first_sum when closing
        begins_colorable = true;
      else
        m_begin = begin;

      return begin;
    }
    void close(expr_ref end) {
      // verbose_stream() << "close: " << end << "\n";
      SASSERT(end);
      if (begins_colorable) {
        m_first_sum = end;
        begins_colorable = false;
      } else {
        if (m_begin != end) {
          m_sum.push_back(m.mk_eq(m_begin, end));
        }
      }
    }
  };

  // cache for congruences that have been summarized
  std::unordered_map<justification *, congr_sum>
      m_ccsum;
  egraph &m_eg;
  expr_ref_vector &m_sum;
  ast_manager &m;

  void summarize_trans(enode *a, enode *b, expr_ref &a_sum, expr_ref &b_sum);
  // summarizes a congruence edge if not already summarized,
  // adds a summary in `m_sum` for each argument. If the step is
  // colorable, it does not add anything and it marks the justification as
  // colorable
  const euf_summarizer::congr_sum &summarize_congr(enode *c);
  expr_ref summarize_branch(enode *n, enode *lca, expr_ref &first_sum);

public:
  euf_summarizer(egraph &eg, expr_ref_vector &sum)
      : m_eg(eg), m_sum(sum), m(eg.get_manager()){};
  void sum_eq(enode *a, enode *b);
};


} // namespace euf

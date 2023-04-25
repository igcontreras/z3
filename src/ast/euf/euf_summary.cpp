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

#include "ast/euf/euf_summary.h"

namespace euf {

  expr_ref rewrite_args(expr * e, const expr_ref_vector &args) {

    ast_manager &m = args.get_manager();

    SASSERT(is_app(e));
    app * a = to_app(e);

    return expr_ref(
        m.mk_app(a->get_decl(), args.size(), args.data()),
        m);
  }

  expr_ref euf_summarizer::summarize_branch(enode *n, enode *lca, expr_ref &first_sum) {

    expr_ref r(nullptr, m); // beginning of summary

    if(n == lca)
      return r;

    const congr_sum *csum = nullptr;
    sum_manager sm(m_sum, n->get_expr(), first_sum);

    while (n != lca) {
      justification &j = n->m_justification;
      if (j.is_congruence() && !j.is_marked()) {
        csum = &summarize_congr(n); // marks j if colorable

        if (!j.is_marked()) {
          if (r) { // summary started, close
            sm.close(rewrite_args(n->get_expr(), csum->m_left_args));
          } else { // open and close
            sm.open(expr_ref(n->get_expr(),m));
            sm.close(rewrite_args(n->get_expr(), csum->m_left_args));
          }
          // open for the next one
          r = sm.open(rewrite_args(n->m_target->get_expr(), csum->m_right_args));
        }
      }
      if (!r && j.is_marked()) { // new summary starts
        r = sm.open(expr_ref(n->get_expr(), m));
      } else if (r && !j.is_marked() && !j.is_congruence()) {
        sm.close(expr_ref(n->get_expr(),m));
        r = nullptr;
      }

      SASSERT(n->m_target);
      n = n->m_target;
    }
    return r;
  }

  void euf_summarizer::summarize_trans(enode *a, enode *b, expr_ref &a_sum,
                                       expr_ref &b_sum) {
    enode *lca = m_eg.find_lca(a, b);
    // verbose_stream() << "trans: " << m_eg.bpp(a) << " " << m_eg.bpp(b) << " "
    //                  << m_eg.bpp(lca) << std::endl;
    expr_ref lhs(m);
    lhs = summarize_branch(a, lca, a_sum);
    // verbose_stream() << "br(a_sum): " << a_sum << " br(lhs): " << expr_ref(lhs,m) << std::endl;
    // partially summarized a--->lca, we do not know how b reaches lca
    expr_ref rhs(m);
    rhs = summarize_branch(b, lca, b_sum);

    // if lhs or rhs are null, the (possibly empty) summaries are closed for that branch
    // if this is the case, if one of them is not null, the summary needs to be closed at lca
    if (!lhs)
      lhs = lca->get_expr();
    if (!rhs)
      rhs = lca->get_expr();

    // since we want to store the summary in the variables `a_sum`/`b_sum` if it
    // starts on the ends, we first check if we are in this case before pushing a new equality to
    // the summary
    if (lhs == a->get_expr() && a_sum == nullptr)
      a_sum = rhs;
    if (rhs == b->get_expr() && b_sum == nullptr)
      b_sum = lhs;

    if (lhs != a->get_expr() && rhs != b->get_expr() && lhs != rhs) {
      m_sum.push_back(m.mk_eq(lhs, rhs));
    }
    verbose_stream() << "sum-trans: a " << m_eg.bpp(a) << " -- " << a_sum << " b "
                     << m_eg.bpp(b) << " -- " << b_sum << std::endl;
  }

  const euf_summarizer::congr_sum &euf_summarizer::summarize_congr(enode *c) {

    SASSERT(c->m_justification.is_congruence());

    verbose_stream() << "congr: " << m_eg.bpp(c) << " " << m_eg.bpp(c->m_target) << std::endl;

    justification &j = c->m_justification;
    if (m_ccsum.count(&j) > 0)
      return m_ccsum.find(&j)->second;

    m_ccsum.emplace(&j, m); // create new entry in the cache
    congr_sum &csum = m_ccsum.find(&j)->second;

    bool all_blue = true;

    expr_ref a_sum(m), b_sum(m);
    unsigned init_sz = m_sum.size();
    unsigned last_sz = init_sz;

    auto ach = enode_args(c);
    auto bch = enode_args(c->m_target);
    // justify each of the arguments, caches colorable end summaries
    for (auto a_it = ach.begin(), b_it = bch.begin(); a_it != ach.end();
         ++a_it, ++b_it) {
      enode *an = *a_it;
      enode *bn = *b_it;

      a_sum = nullptr;
      b_sum = nullptr;

      if (an != bn) {
        summarize_trans(an, bn, a_sum, b_sum);
        if (m_sum.size() == last_sz) {
          // arg explanation may be colorable
          if (a_sum != bn->get_expr() || b_sum != an->get_expr()) {
            all_blue = false;
          } else {
            // colorable, choose a representative: rhs
            a_sum = b_sum;
          }
        } else {
          all_blue = false;
        }
        last_sz = m_sum.size();
      }
      csum.m_left_args.push_back(a_sum ? a_sum : an->get_expr());
      csum.m_right_args.push_back(b_sum ? b_sum : bn->get_expr());
    }

    if (all_blue) {
      csum.reset();
      csum.set_colorable();
      c->m_justification.set_mark(true);
      m_sum.shrink(init_sz); // all arguments can be colored, we do not
      // need each explanation
    }
    return csum;
  }

  // assumes that justifications belonging to the part that needs to be
  // summarized have been marked using the general purpose mark
  void euf_summarizer::sum_eq(enode *a, enode *b) {
    SASSERT(a->get_root() == b->get_root());

    expr_ref a_sum(m), b_sum(m);
    summarize_trans(a, b, a_sum, b_sum);
    if (a_sum && a_sum != a->get_expr()) // the second condition may happen for congr. sum
      m_sum.push_back(m.mk_eq(a->get_expr(),a_sum));
    if (b_sum && b_sum != b->get_expr() // can happen for congr. sum
        && a_sum != b->get_expr()) // avoids duplicated equality if the path is
                                    // fully colorable
      m_sum.push_back(m.mk_eq(b->get_expr(), b_sum));
  }
} // namespace euf

/*++

  Module Name:

    qe_lite_tg.cpp

Abstract:

    Light weight partial quantifier-elimination for cubes using term graphs

Author:

    Isabel Garcia (igcontreras)
    Hari Govind V K (hgvk94)

Revision History:


--*/
#include "qe/lite/qe_lite_tg.h"
#include "qe/mbp/mbp_term_graph.h"

class qe_lite_tg::impl {
private:
    ast_manager& m;

public:
  impl(ast_manager &m, params_ref const &p)
      : m(m) {}

  void operator()(app_ref_vector &vars, expr_ref &fml) {
    if (vars.empty())
      return;

    mbp::term_graph tg(m);
    tg.set_vars(vars, true /*exclude*/);

    expr_ref_vector lits(m);
    flatten_and(fml, lits);
    tg.add_lits(lits);
    tg.qe_lite(vars, fml);
    }

};

qe_lite_tg::qe_lite_tg(ast_manager &m, params_ref const &p) {
  m_impl = alloc(impl, m, p);
}

qe_lite_tg::~qe_lite_tg() { dealloc(m_impl); }

void qe_lite_tg::operator()(app_ref_vector &vars, expr_ref &fml) {
  (*m_impl)(vars, fml);
}

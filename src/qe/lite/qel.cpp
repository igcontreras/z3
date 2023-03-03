/*++

  Module Name:

    qel.cpp

Abstract:

    Light weight partial quantifier-elimination for cubes using term graphs

Author:

    Isabel Garcia (igcontreras)
    Hari Govind V K (hgvk94)

Revision History:


--*/
#include "qe/lite/qel.h"
#include "qe/mbp/mbp_term_graph.h"

class qel::impl {
private:
    ast_manager& m;
    params_ref m_params;
public:
  impl(ast_manager &m, params_ref const &p)
      : m(m), m_params(p) {}

  void operator()(app_ref_vector &vars, expr_ref &fml) {
    if (vars.empty())
      return;

    mbp::term_graph tg(m, p);
    tg.set_vars(vars);

    expr_ref_vector lits(m);
    flatten_and(fml, lits);
    tg.add_lits(lits);
    tg.qel(vars, fml);
    }

};

qel::qel(ast_manager &m, params_ref const &p) {
  m_impl = alloc(impl, m, p);
}

qel::~qel() { dealloc(m_impl); }

void qel::operator()(app_ref_vector &vars, expr_ref &fml) {
  (*m_impl)(vars, fml);
}

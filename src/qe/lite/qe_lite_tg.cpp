#include "qe/lite/qe_lite_tg.h"
#include "qe/mbp/mbp_term_graph.h"

class qe_lite_tg::impl {
private:
    ast_manager& m;

    bool m_use_array_der;

public:
  impl(ast_manager &m, params_ref const &p, bool use_array_der)
      : m(m), m_use_array_der(use_array_der) {}

  void operator()(app_ref_vector &vars, expr_ref &fml) {
    if (vars.empty())
      return;

    mbp::term_graph tg(m);
    tg.set_vars(vars, true /*exclude*/);

    if(m.is_and(fml)) {
      for (expr *lit : *to_app(fml))
        tg.add_lit(lit);
    }
    else {
      tg.add_lit(fml);
    }

    tg.qe_lite(vars, fml);
    }

};

qe_lite_tg::qe_lite_tg(ast_manager &m, params_ref const &p, bool use_array_der) {
  m_impl = alloc(impl, m, p, use_array_der);
}

qe_lite_tg::~qe_lite_tg() { dealloc(m_impl); }

void qe_lite_tg::operator()(app_ref_vector &vars, expr_ref &fml) {
  (*m_impl)(vars, fml);
}

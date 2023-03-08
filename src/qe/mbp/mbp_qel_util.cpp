#include "qe/mbp/mbp_qel_util.h"
#include "ast/array_decl_plugin.h"
#include "ast/ast.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/pp.h"
#include "ast/ast_pp.h"

namespace check_uninterp_consts_ns {
  struct found {};
  struct proc {
    obj_hashtable<app> const &m_vars;
    bool m_only_arr;
    array_util m_arr;
    proc(obj_hashtable<app> const &vars, ast_manager& man,bool only_arr = false) : m_vars(vars), m_only_arr(only_arr), m_arr(man) {}
    void operator()(expr *n) const {}
    void operator()(app *n) {
      if (is_uninterp_const(n) && m_vars.contains(n) && (!m_only_arr || m_arr.is_array(n))) throw found();
    }
  };
} // namespace check_uninterp_consts_ns

// check if e contains any apps from vars
bool contains_vars(expr *e, obj_hashtable<app> const &vars, ast_manager& man, bool only_arr) {
  check_uninterp_consts_ns::proc proc(vars, man, only_arr);
  try {
    for_each_expr(proc, e);
  }
  catch (const check_uninterp_consts_ns::found &) { return true; }
  return false;
}

app_ref new_var(sort* s, ast_manager& m) {
    return app_ref(m.mk_fresh_const("mbptg", s), m);
}

bool contains_var(expr *e, app_ref var, ast_manager& man, bool only_arr) {
  obj_hashtable<app> vars;
  vars.insert(var);
  check_uninterp_consts_ns::proc proc(vars, man, only_arr);
  try {
    for_each_expr(proc, e);
  }
  catch (const check_uninterp_consts_ns::found &) { return true; }
  return false;
}

namespace collect_uninterp_consts_ns {
struct proc {
    obj_hashtable<app> &m_out;
    proc(obj_hashtable<app> &out) : m_out(out) {}
    void operator()(expr *n) const {}
    void operator()(app *n) {
        if (is_uninterp_const(n)) m_out.insert(n);
    }
};
} // namespace collect_uninterp_consts_ns

// Return all uninterpreted constants of \p q
void collect_uninterp_consts(expr *e, obj_hashtable<app> &out) {
    collect_uninterp_consts_ns::proc proc(out);
    for_each_expr(proc, e);
}

namespace collect_selstore_vars_ns {
  struct proc {
    ast_manager& m;
    obj_hashtable<app>& m_vars;
    array_util m_array_util;
    proc(obj_hashtable<app>& vars, ast_manager& man) : m(man), m_vars(vars), m_array_util(m) {}
    void operator()(expr *n) const {}
    void operator()(app *n) {
      if (m_array_util.is_select(n)) {
        collect_uninterp_consts(n->get_arg(1), m_vars);
      }
      else if (m_array_util.is_store(n)) {
        collect_uninterp_consts(n->get_arg(1), m_vars);
        collect_uninterp_consts(n->get_arg(2), m_vars);
      }
    }
  };
} // namespace is_selstore_vars_ns

// collect all uninterpreted consts used as array indices or values
void collect_selstore_vars(expr *fml, obj_hashtable<app>&  vars, ast_manager& man) {
  collect_selstore_vars_ns::proc proc(vars, man);
  quick_for_each_expr(proc, fml);
}

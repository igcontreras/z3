/*++

  Module Name:

    mbp_qel.cpp

Abstract:

    Model Based Projection based on term graph

Author:

    Hari Govind V K (hgvk94) 2022-07-12

Revision History:


--*/
#include "ast/array_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "model/model.h"
#include "qe/mbp/mbp_term_graph.h"
#include "qe/mbp/mbp_arrays.h"
#include "qe/mbp/mbp_arrays_tg.h"
#include "qe/mbp/mbp_dt_tg.h"
#include "qe/mbp/mbp_qel.h"
#include "util/obj_hashtable.h"

class mbp_qel::impl {
private:
  ast_manager& m;
  array_util m_array_util;
  datatype_util m_dt_util;
  obj_hashtable<app> m_vars_set; //set of variables to be projected to make contains_check faster

  //Utilities to keep track of which terms have been processed
  expr_sparse_mark m_seen;
  void mark_seen(expr* t) { m_seen.mark(t); }
  bool is_seen(expr* t) { return m_seen.is_marked(t); }

public:
  impl(ast_manager &m, params_ref const &p)
    : m(m), m_array_util(m), m_dt_util(m) { }

  void operator()(app_ref_vector &vars, expr_ref &inp, model& mdl, bool reduce_all_selects = false) {
    if (!reduce_all_selects && vars.empty())
      return;

    //create vars_set to speed up contains check
    for(auto v : vars) m_vars_set.insert(v);

    mbp::term_graph tg(m);
    // mark vars as non-ground.
    tg.add_vars(vars);
    // treat eq literals as term in the egraph
    tg.set_explicit_eq();

    expr_ref_vector fml(m);
    flatten_and(inp, fml);
    tg.add_lits(fml);

    mbp_array_tg m_array_project(m, tg, mdl, m_vars_set, vars, m_seen);
    mbp_dt_tg m_dt_project(m, tg, mdl, m_vars_set, vars, m_seen);

    //Apply MBP rules till saturation
    bool progress1 = true, progress2 = true;
    unsigned sz = 0;
    do {
      sz = tg.size();
      //apply both rules until fixed point
      //TODO: add option to toggle model based splitting so that we split lazily
      while(progress1) progress1 = m_array_project();
      while(progress2) progress2 = m_dt_project();
    } while(tg.size() > sz);
    TRACE("mbp_tg", tout << "mbp tg " << mk_and(tg.get_lits()) << " and vars " << vars;);
    TRACE("mbp_tg_verbose",
          obj_hashtable<app> vars_tmp;
          collect_uninterp_consts(mk_and(tg.get_lits()), vars_tmp);
          for(auto a : vars_tmp) tout << mk_pp(a->get_decl(), m) << "\n";
          for(auto b : tg.get_lits()) tout << expr_ref(b, m) << "\n";
          for(auto a : vars) tout << expr_ref(a, m) << " " ;);

    // apply the read_over_write rule to all terms, including those without
    // variables DOES not always remove the original read_over_write term but
    // introduces equalities and disequalities where necessary
    if (reduce_all_selects) {
      m_array_project.set_reduce_all_selects();
      //resets m_vars_set
      m_array_project.reset();
      bool progress = true;
      while(progress) progress = m_array_project();
    }

    // 1. Apply qe_lite to remove all c-ground variables
    // 2. Collect all core variables in the output (variables used as array indices/values)
    // 3. Re-apply qe_lite to remove non-core variables

    //Step 1.
    tg.qel(vars, inp);

    //Step 2.
    // Variables that appear as array indices or values cannot be eliminated if
    // they are not c-ground. They are core variables
    // All other Array/ADT variables can be eliminated, they are redundant.
    obj_hashtable<app> core_vars;
    collect_selstore_vars(inp, core_vars, m);
    std::function<bool(app*)> is_red =
            [&](app* v) {
              if (!m_dt_util.is_datatype(v->get_sort()) && !m_array_util.is_array(v)) return false;
              return !core_vars.contains(v);
            };
    expr_sparse_mark red_vars;
    for (auto v : vars) if (is_red(v)) red_vars.mark(v);
    CTRACE("mbp_tg", !core_vars.empty(),
           tout << "vars not redundant ";
           for (auto v : core_vars) tout << " " << app_ref(v, m); tout <<"\n";);

    std::function<bool(expr*)> non_core = [&] (expr* e) {
      array_util m_array(m);
      if (is_app(e) && is_partial_eq(to_app(e))) return true;
      if (reduce_all_selects && m_array.is_select(e) && m_array.is_store(to_app(e)->get_arg(0))) return true;
      return red_vars.is_marked(e);
    };

    //Step 3.
    tg.qel(vars, inp, &non_core);
  }
};

mbp_qel::mbp_qel(ast_manager &m, params_ref const &p) {
  m_impl = alloc(impl, m, p);
}

mbp_qel::~mbp_qel() { dealloc(m_impl); }

void mbp_qel::operator()(app_ref_vector &vars, expr_ref &fml, model& mdl, bool reduce_all_selects) {
  (*m_impl)(vars, fml, mdl, reduce_all_selects);
}

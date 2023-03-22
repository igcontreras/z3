/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    dbg_cmds.cpp

Abstract:
    SMT2 front-end commands for debugging purposes.

Author:

    Leonardo (leonardo) 2011-04-01

Notes:

--*/
#include<iomanip>
#include "ast/ast.h"
#include "cmd_context/cmd_context.h"
#include "cmd_context/cmd_util.h"
#include "ast/rewriter/rewriter.h"
#include "ast/shared_occs.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/ast_lt.h"
#include "cmd_context/simplify_cmd.h"
#include "ast/ast_smt2_pp.h"
#include "ast/simplifiers/bound_manager.h"
#include "ast/used_vars.h"
#include "ast/rewriter/var_subst.h"
#include "ast/ast_util.h"
#include "util/gparams.h"
#include "qe/qe_mbp.h"
#include "qe/qe_mbi.h"
#include "qe/mbp/mbp_term_graph.h"
#include "qe/mbp/mbp_qel.h"
#include "qe/lite/qe_lite_tactic.h"
#include "qe/lite/qel.h"

#include "sat/sat_solver.h"
#include "ast/euf/euf_egraph.h"
#include "ast/arith_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "sat/smt/euf_solver.h"
#include "smt/params/theory_arith_params.h"

#include "ast/euf/euf_justification.h"

    BINARY_SYM_CMD(
        get_quantifier_body_cmd, "dbg-get-qbody", "<symbol> <quantifier>",
        "store the body of the quantifier in the global variable <symbol>",
        CPK_EXPR, expr *, {
          if (!is_quantifier(arg))
            throw cmd_exception("invalid command, term must be a quantifier");
          store_expr_ref(ctx, m_sym, to_quantifier(arg)->get_expr());
        });

BINARY_SYM_CMD(set_cmd,
               "dbg-set",
               "<symbol> <term>",
               "store <term> in the global variable <symbol>",
               CPK_EXPR,
               expr *, {
    store_expr_ref(ctx, m_sym, arg);
});


UNARY_CMD(pp_var_cmd, "dbg-pp-var", "<symbol>", "pretty print a global variable that references an AST", CPK_SYMBOL, symbol const &, {
    expr * t = get_expr_ref(ctx, arg);
    SASSERT(t != 0);
    ctx.display(ctx.regular_stream(), t);
    ctx.regular_stream() << std::endl;
});

BINARY_SYM_CMD(shift_vars_cmd,
               "dbg-shift-vars",
               "<symbol> <uint>",
               "shift the free variables by <uint> in the term referenced by the global variable <symbol>, the result is stored in <symbol>",
               CPK_UINT,
               unsigned, {
    expr * t = get_expr_ref(ctx, m_sym);
    expr_ref r(ctx.m());
    var_shifter s(ctx.m());
    s(t, arg, r);
    store_expr_ref(ctx, m_sym, r.get());
});


UNARY_CMD(assert_not_cmd, "assert-not", "<term>", "assert negation", CPK_EXPR, expr *, {
    expr_ref ne(ctx.m().mk_not(arg), ctx.m());
    ctx.assert_expr(ne);
});


UNARY_CMD(size_cmd, "dbg-size", "<term>", "return the size of the given term", CPK_EXPR, expr *, {
    ctx.regular_stream() << get_num_exprs(arg) << std::endl;
});

class subst_cmd : public cmd {
    unsigned         m_idx;
    expr *           m_source;
    symbol           m_target;
    ptr_vector<expr> m_subst;
public:
    subst_cmd():cmd("dbg-subst") {}
    char const * get_usage() const override { return "<symbol> (<symbol>*) <symbol>"; }
    char const * get_descr(cmd_context & ctx) const override { return "substitute the free variables in the AST referenced by <symbol> using the ASTs referenced by <symbol>*"; }
    unsigned get_arity() const override { return 3; }
    void prepare(cmd_context & ctx) override { m_idx = 0; m_source = nullptr; }
    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override {
        if (m_idx == 1) return CPK_SYMBOL_LIST;
        return CPK_SYMBOL;
    }
    void set_next_arg(cmd_context & ctx, symbol const & s) override {
        if (m_idx == 0) {
            m_source = get_expr_ref(ctx, s);
        }
        else {
            m_target = s;
        }
        m_idx++;
    }
    void set_next_arg(cmd_context & ctx, unsigned num, symbol const * s) override {
        m_subst.reset();
        unsigned i = num;
        while (i > 0) {
            --i;
            m_subst.push_back(get_expr_ref(ctx, s[i]));
        }
        m_idx++;
    }
    void execute(cmd_context & ctx) override {
        beta_reducer p(ctx.m());
        expr_ref r = p(m_source, m_subst.size(), m_subst.data());
        store_expr_ref(ctx, m_target, r.get());
    }
};

UNARY_CMD(bool_rewriter_cmd, "dbg-bool-rewriter", "<term>", "apply the Boolean rewriter to the given term", CPK_EXPR, expr *, {
    expr_ref t(ctx.m());
    params_ref p;
    p.set_bool("flat", false);
    SASSERT(p.get_bool("flat", true) == false);
    bool_rewriter_star r(ctx.m(), p);
    r(arg, t);
    ctx.display(ctx.regular_stream(), t);
    ctx.regular_stream() << std::endl;
});

UNARY_CMD(bool_frewriter_cmd, "dbg-bool-flat-rewriter", "<term>", "apply the Boolean (flattening) rewriter to the given term", CPK_EXPR, expr *, {
    expr_ref t(ctx.m());
    {
        params_ref p;
        p.set_bool("flat", true);
        bool_rewriter_star r(ctx.m(), p);
        r(arg, t);
    }
    ctx.display(ctx.regular_stream(), t);
    ctx.regular_stream() << std::endl;
});

UNARY_CMD(elim_and_cmd, "dbg-elim-and", "<term>", "apply the Boolean rewriter (eliminating AND operator and flattening) to the given term", CPK_EXPR, expr *, {
    expr_ref t(ctx.m());
    {
        params_ref p;
        p.set_bool("flat", true);
        p.set_bool("elim_and", true);
        bool_rewriter_star r(ctx.m(), p);
        r(arg, t);
    }
    ctx.display(ctx.regular_stream(), t);
    ctx.regular_stream() << std::endl;
});

class lt_cmd : public cmd {
    expr *           m_t1;
    expr *           m_t2;
public:
    lt_cmd():cmd("dbg-lt") {}
    char const * get_usage() const override { return "<term> <term>"; }
    char const * get_descr(cmd_context & ctx) const override { return "return true if the first term is smaller than the second one in the internal Z3 total order on terms."; }
    unsigned get_arity() const override { return 2; }
    void prepare(cmd_context & ctx) override { m_t1 = nullptr; }
    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override { return CPK_EXPR; }
    void set_next_arg(cmd_context & ctx, expr * arg) override {
        if (m_t1 == nullptr)
            m_t1 = arg;
        else
            m_t2 = arg;
    }
    void execute(cmd_context & ctx) override {
        bool r = lt(m_t1, m_t2);
        ctx.regular_stream() << (r ? "true" : "false") << std::endl;
    }
};


UNARY_CMD(some_value_cmd, "dbg-some-value", "<sort>", "retrieve some value of the given sort", CPK_SORT, sort *, {
    ast_manager & m = ctx.m();
    expr_ref val(m);
    val = m.get_some_value(arg);
    ctx.display(ctx.regular_stream(), val);
    ctx.regular_stream() << std::endl;
});

void tst_params(cmd_context & ctx) {
    params_ref p1;
    params_ref p2;
    p1.set_uint("val", 100);
    p2.append(p1);
    SASSERT(p2.get_uint("val", 0) == 100);
    p2.set_uint("val", 200);
    SASSERT(p2.get_uint("val", 0) == 200);
    SASSERT(p1.get_uint("val", 0) == 100);
    p2.append(p1);
    SASSERT(p2.get_uint("val", 0) == 100);
    SASSERT(p1.get_uint("val", 0) == 100);
    ctx.regular_stream() << "worked" << std::endl;
}

ATOMIC_CMD(params_cmd, "dbg-params", "test parameters", tst_params(ctx););


UNARY_CMD(translator_cmd, "dbg-translator", "<term>", "test AST translator", CPK_EXPR, expr *, {
    ast_manager & m = ctx.m();
    scoped_ptr<ast_manager> m2 = alloc(ast_manager, m.proof_mode());
    ast_translation proc(m, *m2);
    expr_ref s(m);
    expr_ref t(*m2);
    s = arg;
    t = proc(s.get());
    ctx.regular_stream() << mk_ismt2_pp(s, m) << "\n--->\n" << mk_ismt2_pp(t, *m2) << std::endl;
});

UNARY_CMD(sexpr_cmd, "dbg-sexpr", "<sexpr>", "display an s-expr", CPK_SEXPR, sexpr *, {
    arg->display(ctx.regular_stream());
    ctx.regular_stream() << std::endl;
});


#define GUARDED_CODE(CODE) try { CODE } catch (z3_error & ex) { throw ex; } catch (z3_exception & ex) { ctx.regular_stream() << "(error \"" << escaped(ex.msg()) << "\")" << std::endl; }

UNARY_CMD(set_next_id, "dbg-set-next-id", "<unsigned>", "set the next expression id to be at least the given value", CPK_UINT, unsigned, {
    ctx.m().set_next_expr_id(arg);
});


UNARY_CMD(used_vars_cmd, "dbg-used-vars", "<expr>", "test used_vars functor", CPK_EXPR, expr *, {
    used_vars proc;
    if (is_quantifier(arg))
        arg = to_quantifier(arg)->get_expr();
    proc(arg);
    ctx.regular_stream() << "(vars";
    for (unsigned i = 0; i < proc.get_max_found_var_idx_plus_1(); i++) {
        sort * s = proc.get(i);
        ctx.regular_stream() << "\n  (" << std::left << std::setw(6) << i << " ";
        if (s != 0)
            ctx.display(ctx.regular_stream(), s, 10);
        else
            ctx.regular_stream() << "<not-used>";
        ctx.regular_stream() << ")";
    }
    ctx.regular_stream() << ")" << std::endl;
});

UNARY_CMD(elim_unused_vars_cmd, "dbg-elim-unused-vars", "<expr>", "eliminate unused vars from a quantifier", CPK_EXPR, expr *, {
    if (!is_quantifier(arg)) {
        ctx.display(ctx.regular_stream(), arg);
        return;
    }
    expr_ref r = elim_unused_vars(ctx.m(), to_quantifier(arg), gparams::get_ref());
    SASSERT(!is_quantifier(r) || !to_quantifier(r)->may_have_unused_vars());
    ctx.display(ctx.regular_stream(), r);
    ctx.regular_stream() << std::endl;
});

class instantiate_cmd_core : public cmd {
protected:
    quantifier *     m_q;
    ptr_vector<expr> m_args;
public:
    instantiate_cmd_core(char const * name):cmd(name) {}
    char const * get_usage() const override { return "<quantifier> (<symbol>*)"; }
    char const * get_descr(cmd_context & ctx) const override { return "instantiate the quantifier using the given expressions."; }
    unsigned get_arity() const override { return 2; }
    void prepare(cmd_context & ctx) override { m_q = nullptr; m_args.reset(); }

    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override {
        if (m_q == nullptr) return CPK_EXPR;
        else return CPK_EXPR_LIST;
    }

    void set_next_arg(cmd_context & ctx, expr * s) override {
        if (!is_quantifier(s))
            throw cmd_exception("invalid command, quantifier expected.");
        m_q = to_quantifier(s);
    }

    void set_next_arg(cmd_context & ctx, unsigned num, expr * const * ts) override {
        if (num != m_q->get_num_decls())
            throw cmd_exception("invalid command, mismatch between the number of quantified variables and the number of arguments.");
        unsigned i = num;
        while (i-- > 0) {
            sort * s = ts[i]->get_sort();
            if (s != m_q->get_decl_sort(i)) {
                std::ostringstream buffer;
                buffer << "invalid command, sort mismatch at position " << i;
                throw cmd_exception(buffer.str());
            }
        }
        m_args.append(num, ts);
    }

    void execute(cmd_context & ctx) override {
        expr_ref r = instantiate(ctx.m(), m_q, m_args.data());
        ctx.display(ctx.regular_stream(), r);
        ctx.regular_stream() << std::endl;
    }
};

class instantiate_cmd : public instantiate_cmd_core {
public:
    instantiate_cmd():instantiate_cmd_core("dbg-instantiate") {}
};

class instantiate_nested_cmd : public instantiate_cmd_core {
public:
    instantiate_nested_cmd():instantiate_cmd_core("dbg-instantiate-nested") {}

    char const * get_descr(cmd_context & ctx) const override { return "instantiate the quantifier nested in the outermost quantifier, this command is used to test the instantiation procedure with quantifiers that contain free variables."; }

    void set_next_arg(cmd_context & ctx, expr * s) override {
        instantiate_cmd_core::set_next_arg(ctx, s);
        if (!is_quantifier(m_q->get_expr()))
            throw cmd_exception("invalid command, nested quantifier expected");
        m_q = to_quantifier(m_q->get_expr());
    }
};

class print_dimacs_cmd : public cmd {
public:
    print_dimacs_cmd():cmd("display-dimacs") {}
    char const * get_usage() const override { return ""; }
    char const * get_descr(cmd_context & ctx) const override { return "print benchmark in DIMACS format"; }
    unsigned get_arity() const override { return 0; }
    void prepare(cmd_context & ctx) override {}
    void execute(cmd_context & ctx) override { ctx.display_dimacs(); }
};

class mbp_cmd : public cmd {
    expr* m_fml;
    ptr_vector<expr> m_vars;
public:
    mbp_cmd():cmd("mbp") {}
    char const * get_usage() const override { return "<expr> (<vars>)"; }
    char const * get_descr(cmd_context & ctx) const override { return "perform model based projection"; }
    unsigned get_arity() const override { return 2; }
    cmd_arg_kind next_arg_kind(cmd_context& ctx) const override {
        if (m_fml == nullptr) return CPK_EXPR; 
        return CPK_EXPR_LIST;
    }
    void set_next_arg(cmd_context& ctx, expr * arg) override { m_fml = arg; }
    void set_next_arg(cmd_context & ctx, unsigned num, expr * const * ts) override {
        m_vars.append(num, ts);
    }
    void prepare(cmd_context & ctx) override { m_fml = nullptr; m_vars.reset(); }
    void execute(cmd_context & ctx) override { 
        ast_manager& m = ctx.m();
        app_ref_vector vars(m);
        model_ref mdl;
        if (!ctx.is_model_available(mdl) || !ctx.get_check_sat_result()) {
            throw cmd_exception("model is not available");
        }
        for (expr* v : m_vars) {
            if (!is_uninterp_const(v)) {
                throw cmd_exception("invalid variable argument. Uninterpreted variable expected");
            }
            vars.push_back(to_app(v));
        }
        qe::mbproj mbp(m);
        expr_ref fml(m_fml, m);
        mbp.spacer(vars, *mdl.get(), fml);
        ctx.regular_stream() << fml << "\n";
    }
};

class get_interpolant_cmd : public cmd {
    scoped_ptr<expr_ref> m_a;
    scoped_ptr<expr_ref> m_b;
public:
    get_interpolant_cmd():cmd("get-interpolant") {}
    char const * get_usage() const override { return "<expr> <expr>"; }
    char const * get_descr(cmd_context & ctx) const override { return "perform model based interpolation"; }
    unsigned get_arity() const override { return 2; }
    cmd_arg_kind next_arg_kind(cmd_context& ctx) const override {
        return CPK_EXPR; 
    }
    void set_next_arg(cmd_context& ctx, expr * arg) override { 
        ast_manager& m = ctx.m();
        if (!m.is_bool(arg))
            throw default_exception("argument to interpolation is not Boolean");
        if (!m_a) 
            m_a = alloc(expr_ref, arg, m); 
        else 
            m_b = alloc(expr_ref, arg, m); 
    }
    void prepare(cmd_context & ctx) override { m_a = nullptr; m_b = nullptr;  }
    void execute(cmd_context & ctx) override { 
        ast_manager& m = ctx.m();
        qe::interpolator mbi(m);
        if (!m_a || !m_b)
            throw default_exception("interpolation requires two arguments");
        if (!m.is_bool(*m_a) || !m.is_bool(*m_b))
            throw default_exception("interpolation requires two Boolean arguments");
        expr_ref itp(m);
        lbool r = mbi.pogo(ctx.get_solver_factory(), *m_a, *m_b, itp);
        switch (r) {
        case l_true:
            ctx.regular_stream() << "sat\n";
            break;
        case l_undef:
            ctx.regular_stream() << "unknown\n";
            break;
        case l_false:
            ctx.regular_stream() << itp << "\n";
            break;
        }
    }
};



class mbi_cmd : public cmd {
    expr* m_a;
    expr* m_b;
    ptr_vector<func_decl> m_vars;
public:
    mbi_cmd():cmd("mbi") {}
    char const * get_usage() const override { return "<expr> <expr> (vars)"; }
    char const * get_descr(cmd_context & ctx) const override { return "perform model based interpolation"; }
    unsigned get_arity() const override { return 3; }
    cmd_arg_kind next_arg_kind(cmd_context& ctx) const override {
        if (m_a == nullptr) return CPK_EXPR; 
        if (m_b == nullptr) return CPK_EXPR; 
        return CPK_FUNC_DECL_LIST;
    }
    void set_next_arg(cmd_context& ctx, expr * arg) override { 
        if (m_a == nullptr) 
            m_a = arg; 
        else 
            m_b = arg; 
    }
    void set_next_arg(cmd_context & ctx, unsigned num, func_decl * const * ts) override {
        m_vars.append(num, ts);
    }
    void prepare(cmd_context & ctx) override { m_a = nullptr; m_b = nullptr; m_vars.reset(); }
    void execute(cmd_context & ctx) override { 
        ast_manager& m = ctx.m();
        func_decl_ref_vector vars(m);
        for (func_decl* v : m_vars) {
            vars.push_back(v);
        }
        qe::interpolator mbi(m);
        expr_ref a(m_a, m);
        expr_ref b(m_b, m);
        expr_ref itp(m);
        solver_factory& sf = ctx.get_solver_factory();
        params_ref p;
        solver_ref sA = sf(m, p, false /* no proofs */, true, true, symbol::null);
        solver_ref sB = sf(m, p, false /* no proofs */, true, true, symbol::null);
        sA->assert_expr(a);
        sB->assert_expr(b);
        qe::prop_mbi_plugin pA(sA.get());
        qe::prop_mbi_plugin pB(sB.get());
        pA.set_shared(vars);
        pB.set_shared(vars);
        lbool res = mbi.pingpong(pA, pB, itp);
        ctx.regular_stream() << res << " " << itp << "\n";
    }
};


class eufi_cmd : public cmd {
    expr* m_a;
    expr* m_b;
    ptr_vector<func_decl> m_vars;
public:
    eufi_cmd():cmd("eufi") {}
    char const * get_usage() const override { return "<expr> <expr> (vars)"; }
    char const * get_descr(cmd_context & ctx) const override { return "perform model based interpolation"; }
    unsigned get_arity() const override { return 3; }
    cmd_arg_kind next_arg_kind(cmd_context& ctx) const override {
        if (m_a == nullptr) return CPK_EXPR; 
        if (m_b == nullptr) return CPK_EXPR; 
        return CPK_FUNC_DECL_LIST;
    }
    void set_next_arg(cmd_context& ctx, expr * arg) override { 
        if (m_a == nullptr) 
            m_a = arg; 
        else 
            m_b = arg; 
    }
    void set_next_arg(cmd_context & ctx, unsigned num, func_decl * const * ts) override {
        m_vars.append(num, ts);
    }
    void prepare(cmd_context & ctx) override { m_a = nullptr; m_b = nullptr; m_vars.reset(); }
    void execute(cmd_context & ctx) override { 
        ast_manager& m = ctx.m();
        func_decl_ref_vector vars(m);
        for (func_decl* v : m_vars) {
            vars.push_back(v);
        }
        qe::interpolator mbi(m);
        expr_ref a(m_a, m);
        expr_ref b(m_b, m);
        expr_ref itp(m);
        solver_factory& sf = ctx.get_solver_factory();
        params_ref p;
        solver_ref sA = sf(m, p, false /* no proofs */, true, true, symbol::null);
        solver_ref sB = sf(m, p, false /* no proofs */, true, true, symbol::null);
        solver_ref sNotA = sf(m, p, false /* no proofs */, true, true, symbol::null);
        solver_ref sNotB = sf(m, p, false /* no proofs */, true, true, symbol::null);
        sA->assert_expr(a);
        sB->assert_expr(b);
        qe::uflia_mbi pA(sA.get(), sNotA.get());
        qe::prop_mbi_plugin pB(sB.get());
        pA.set_shared(vars);
        pB.set_shared(vars);
        lbool res = mbi.pogo(pA, pB, itp);
        ctx.regular_stream() << res << " " << itp << "\n";
    }
};


class euf_project_cmd : public cmd {
    unsigned              m_arg_index;
    ptr_vector<expr>      m_lits;
    ptr_vector<func_decl> m_vars;
public:
    euf_project_cmd():cmd("euf-project") {}
    char const * get_usage() const override { return "(exprs) (vars)"; }
    char const * get_descr(cmd_context & ctx) const override { return "perform congruence projection"; }
    unsigned get_arity() const override { return 2; }
    cmd_arg_kind next_arg_kind(cmd_context& ctx) const override {
        if (m_arg_index == 0) return CPK_EXPR_LIST;
        return CPK_FUNC_DECL_LIST;
    }
    void set_next_arg(cmd_context& ctx, unsigned num, expr * const* args) override { 
        m_lits.append(num, args);
        m_arg_index = 1;
    }
    void set_next_arg(cmd_context & ctx, unsigned num, func_decl * const * ts) override {
        m_vars.append(num, ts);
    }
    void prepare(cmd_context & ctx) override { m_arg_index = 0; m_lits.reset(); m_vars.reset(); }
    void execute(cmd_context & ctx) override { 
        ast_manager& m = ctx.m();
        func_decl_ref_vector vars(m);
        expr_ref_vector lits(m);
        for (func_decl* v : m_vars) vars.push_back(v);
        for (expr* e : m_lits) lits.push_back(e);
        flatten_and(lits);
        solver_factory& sf = ctx.get_solver_factory();
        params_ref pa;
        solver_ref s = sf(m, pa, false, true, true, symbol::null);
        solver_ref se = sf(m, pa, false, true, true, symbol::null);
        s->assert_expr(lits);
        lbool r = s->check_sat();
        if (r != l_true) {
            ctx.regular_stream() << "sat check " << r << "\n";
            return;
        }
        model_ref mdl;
        s->get_model(mdl);
        qe::uflia_mbi plugin(s.get(), se.get());
        plugin.set_shared(vars);
        plugin.project(mdl, lits);
        ctx.regular_stream() << lits << "\n";
    }

};


class tg_mbp_cmd : public cmd {
    unsigned              m_arg_index;
    ptr_vector<expr>      m_lits;
    ptr_vector<expr> m_vars;
public:
  tg_mbp_cmd() : cmd("mbp-tg") {};
  char const *get_usage() const override { return "(exprs) (vars)"; }
  char const *get_descr(cmd_context &ctx) const override {
    return "Model based projection using e-graphs"; }
    unsigned get_arity() const override { return 2; }
    cmd_arg_kind next_arg_kind(cmd_context& ctx) const override {
        return CPK_EXPR_LIST;
    }
    void set_next_arg(cmd_context& ctx, unsigned num, expr * const* args) override {
      if(m_arg_index == 0) {
        m_lits.append(num, args);
        m_arg_index = 1;
      }
      else {
	 m_vars.append(num, args);
      }
    }
    void prepare(cmd_context & ctx) override { m_arg_index = 0; m_lits.reset(); m_vars.reset(); }
    void execute(cmd_context & ctx) override {
      ast_manager &m = ctx.m();
      app_ref_vector vars(m);
      expr_ref fml(m);
      expr_ref_vector lits(m);
      for (expr *v : m_vars) vars.push_back(to_app(v));
      for (expr *e : m_lits) lits.push_back(e);
      fml = mk_and(lits);
      solver_factory &sf = ctx.get_solver_factory();
      params_ref pa;
      solver_ref s = sf(m, pa, false, true, true, symbol::null);
      s->assert_expr(fml);
      lbool r = s->check_sat();
      if (r != l_true) {
	return;
      }
      model_ref mdl;
      s->get_model(mdl);
      mbp_qel mbptg(m, pa);
      mbptg(vars, fml, *mdl.get());

      ctx.regular_stream() << "------------------------------ " << std::endl;
      ctx.regular_stream() << "Orig tg: " << mk_and(lits) << std::endl;
      ctx.regular_stream() << "To elim: ";
      for (expr *v : m_vars) {
        ctx.regular_stream() << to_app(v)->get_decl()->get_name() << " ";
      }
      ctx.regular_stream() << std::endl;
      ctx.regular_stream() << "output " << fml << std::endl;
    }
};

class qe_lite_tg_cmd : public cmd {
    unsigned              m_arg_index;
    ptr_vector<expr>      m_lits;
    ptr_vector<func_decl> m_vars;
public:
  qe_lite_tg_cmd() : cmd("qe-lite-tg"){};
  char const *get_usage() const override { return "(lits) (vars)"; }
  char const *get_descr(cmd_context &ctx) const override {
    return "QE lite over e-graphs"; }
    unsigned get_arity() const override { return 2; }
    cmd_arg_kind next_arg_kind(cmd_context& ctx) const override {
        if (m_arg_index == 0) return CPK_EXPR_LIST;
        return CPK_FUNC_DECL_LIST;
    }
    void set_next_arg(cmd_context& ctx, unsigned num, expr * const* args) override {
        m_lits.append(num, args);
        m_arg_index = 1;
    }
    void set_next_arg(cmd_context & ctx, unsigned num, func_decl * const * ts) override {
        m_vars.append(num, ts);
    }
    void prepare(cmd_context & ctx) override { m_arg_index = 0; m_lits.reset(); m_vars.reset(); }
    void execute(cmd_context & ctx) override {
      ast_manager &m = ctx.m();
      func_decl_ref_vector vars(m);
      app_ref_vector vars_apps(m);
      expr_ref_vector lits(m);

      ctx.regular_stream() << "------------------------------ " << std::endl;

      for (func_decl *v : m_vars) {
        vars.push_back(v);
        vars_apps.push_back(m.mk_const(v));
      }
      for (expr *e : m_lits)
        lits.push_back(e);


      expr_ref fml(m.mk_and(lits), m);
      ctx.regular_stream() << "[tg] Before: " << fml << std::endl
                           << "[tg] Vars: ";
      for (app *a : vars_apps)
        ctx.regular_stream() << app_ref(a,m) << " ";

      ctx.regular_stream() << std::endl;

      params_ref pa;

      // the following is the same code as in qe_mbp in spacer
      qel qe(m, pa);
      qe(vars_apps, fml);
      ctx.regular_stream() << "[tg] After: " << fml << std::endl
                           << "[tg] Vars: ";
      for (app *a : vars_apps)
        ctx.regular_stream() << app_ref(a, m) << " ";

      ctx.regular_stream() << std::endl;
    }
};


class qe_lite_der_cmd : public cmd {
    unsigned              m_arg_index;
    ptr_vector<expr>      m_lits;
    ptr_vector<func_decl> m_vars;
public:
  qe_lite_der_cmd() : cmd("qe-lite-der"){};
  char const *get_usage() const override { return "(lits) (vars)"; }
  char const *get_descr(cmd_context &ctx) const override {
    return "QE lite over e-graphs"; }
    unsigned get_arity() const override { return 2; }
    cmd_arg_kind next_arg_kind(cmd_context& ctx) const override {
        if (m_arg_index == 0) return CPK_EXPR_LIST;
        return CPK_FUNC_DECL_LIST;
    }
    void set_next_arg(cmd_context& ctx, unsigned num, expr * const* args) override {
        m_lits.append(num, args);
        m_arg_index = 1;
    }
    void set_next_arg(cmd_context & ctx, unsigned num, func_decl * const * ts) override {
        m_vars.append(num, ts);
    }
    void prepare(cmd_context & ctx) override { m_arg_index = 0; m_lits.reset(); m_vars.reset(); }
    void execute(cmd_context & ctx) override {
      ast_manager &m = ctx.m();
      func_decl_ref_vector vars(m);
      app_ref_vector vars_apps(m);
      expr_ref_vector lits(m);

      ctx.regular_stream() << "------------------------------ " << std::endl;

      for (func_decl *v : m_vars) {
        vars.push_back(v);
        vars_apps.push_back(m.mk_const(v));
      }
      for (expr *e : m_lits)
        lits.push_back(e);

      expr_ref fml(m.mk_and(lits), m);
      ctx.regular_stream() << "[der] Before: " << fml << std::endl
                           << "[der] Vars: ";
      for (app *a : vars_apps)
        ctx.regular_stream() << app_ref(a,m) << " ";

      ctx.regular_stream() << std::endl;

      params_ref pa;
      // the following is the same code as in qe_mbp in spacer
      qe_lite qe(m, pa, false);
      qe(vars_apps, fml);
      ctx.regular_stream() << "[der] After: " << fml << std::endl
                           << "[der] Vars: ";
      for (app *a : vars_apps)
        ctx.regular_stream() << app_ref(a, m) << " ";

      ctx.regular_stream() << std::endl;
    }
};

struct dummy_si : public sat::sat_internalizer {
public:
  dummy_si() {}
  ~dummy_si() override {}
  bool is_bool_op(expr *e) const override { return false; }
  sat::literal internalize(expr *e) override {
    return sat::literal();
  }
  bool is_cached(app *t, sat::literal l) const override {
    return false;
  }
  sat::bool_var to_bool_var(expr *e) override { return sat::null_bool_var; }
  sat::bool_var add_bool_var(expr *e) override { return sat::null_bool_var; }
  void cache(app *t, sat::literal l) override {}
  void uncache(sat::literal l) override {}
  void push() override {}
  void pop(unsigned n) override {}
  void set_expr2var_replay(obj_map<expr, sat::bool_var> *r) override {}
};

class euf_solver_eq : public cmd {
  expr *m_euf_cube;   // axioms (and l1 l2 ... ln)
  expr *m_euf_eq;     // equality to justify

public:
  euf_solver_eq() : cmd("euf-explain-eq"){};
  char const *get_usage() const override { return "(euf-cube) (eq)"; }
  char const *get_descr(cmd_context &ctx) const override {
    return "Equality proof for an EUF cube";
  }

  unsigned get_arity() const override { return 2; }
  cmd_arg_kind next_arg_kind(cmd_context &ctx) const override {
    return CPK_EXPR;
  }
  void set_next_arg(cmd_context &ctx, expr *arg) override {
    if (m_euf_cube == nullptr)
      m_euf_cube = arg;
    else
      m_euf_eq = arg;
  }
  void prepare(cmd_context &ctx) override {
    m_euf_cube = nullptr;
    m_euf_eq = nullptr;
  }

  // copied from euf_solver for justifications
  size_t *to_ptr(sat::literal l) {
    return TAG(size_t *, reinterpret_cast<size_t *>((size_t)(l.index() << 4)),
               1);
  }
  void execute(cmd_context &ctx) override {

    ast_manager &m = ctx.m();
    reg_decl_plugins(m);
    arith_util a(m);

    expr_ref phi(m_euf_cube, m);
    expr_ref eq(m_euf_eq, m);

    dummy_si dsi;

    euf::solver euf_s = euf::solver(m, dsi);

    euf::egraph &g = euf_s.get_egraph();

    // euf::ext_justification_idx justifications[5] = {1, 2, 3, 4, 5};
    expr *lhs, *rhs;
    euf::enode *e1, *e2;
    ctx.regular_stream() << "------------------------------ " << std::endl;
    for (auto l : *to_app(phi)) {
      ctx.regular_stream() << expr_ref(l,m) << " ";
      SASSERT(m.is_eq(l));
      m.is_eq(l, lhs, rhs);

      e1 = euf_s.e_internalize(lhs);
      e2 = euf_s.e_internalize(rhs);
      g.merge(e1, e2, to_ptr(sat::literal(e1->bool_var())));
      g.propagate(); // can this be delayed?
    }

    SASSERT(!g.inconsistent());

    m.is_eq(m_euf_eq,lhs,rhs);
    e1 = g.find(lhs);
    e2 = g.find(rhs);

    ctx.regular_stream() << "\nexplain: "
                         << expr_ref(e1->get_expr(), m) << " = " << expr_ref(e2->get_expr(), m) << "\n";

    SASSERT(e1->get_root() == e2->get_root());

    ptr_vector<size_t> js;
    g.begin_explain();
    g.explain_eq<size_t>(js, nullptr, e1, e2);
    g.end_explain();

    ctx.regular_stream() << "justification size: " << js.size() << "\n";
  }
};


class euf_solver_iuc : public cmd {
  expr *m_A;   // A(x,y) (and l1 l2 ... ln)
  expr *m_B;   // B(y)   assumptions
  expr *m_eq;   // equality to justify

public:
  euf_solver_iuc() : cmd("euf-iuc"){};
  char const *get_usage() const override {
    return "(A-cube) (B-cube) (eq)";
  }
  char const *get_descr(cmd_context &ctx) const override {
    return "Interpolating Unsat Core for two A(x,y) and B(x) cubes";
  }

  unsigned get_arity() const override { return 3; }
  cmd_arg_kind next_arg_kind(cmd_context &ctx) const override {
    return CPK_EXPR;
  }
  void set_next_arg(cmd_context &ctx, expr *arg) override {
    if (m_A == nullptr)
      m_A = arg;
    else if (m_B == nullptr)
      m_B = arg;
    else
      m_eq = arg;
  }
  void prepare(cmd_context &ctx) override {
    m_A = nullptr;
    m_B = nullptr;
    m_eq = nullptr;
  }

  // copied from euf_solver for justifications
  size_t *to_ptr(sat::literal l) {
    return TAG(size_t *, reinterpret_cast<size_t *>((size_t)(l.index() << 4)),
               1);
  }
  void execute(cmd_context &ctx) override {

    ast_manager &m = ctx.m();
    reg_decl_plugins(m);
    arith_util a(m);

    expr_ref A(m_A, m);
    SASSERT(m.is_and(m_A));
    expr_ref B(m_B, m);
    SASSERT(m.is_and(m_B));
    expr_ref eq(m_eq, m);

    dummy_si dsi;

    euf::solver euf_s = euf::solver(m, dsi);

    euf::egraph &g = euf_s.get_egraph();

    // vector<euf::justification> justifications;
    expr *lhs, *rhs;
    euf::enode *e1, *e2;
    ctx.regular_stream() << "-------------------------------------------------- " << std::endl << "A: ";
    for (auto l : *to_app(A)) {
      ctx.regular_stream() << expr_ref(l,m) << " ";
      SASSERT(m.is_eq(l));
      m.is_eq(l, lhs, rhs);

      e1 = euf_s.e_internalize(lhs);
      e2 = euf_s.e_internalize(rhs);
      g.merge(e1, e2,
              to_ptr(sat::literal(
                  e1->bool_var()))); // creates an external justification
    }
    g.propagate();
    ctx.regular_stream() << std::endl
                         << "B: ";

    for (auto l : *to_app(B)) {
      ctx.regular_stream() << expr_ref(l, m) << " ";
      SASSERT(m.is_eq(l));
      m.is_eq(l, lhs, rhs);

      e1 = euf_s.e_internalize(lhs);
      e2 = euf_s.e_internalize(rhs);
      euf::justification j =
          euf::justification::external(to_ptr(sat::literal(e1->bool_var())));
      j.set_mark(true);   // mark edges in proof tree
      g.merge(e1, e2, j); // creates an external justification
    }
    g.propagate();

    SASSERT(!g.inconsistent());

    ENSURE(m.is_eq(m_eq, lhs, rhs)); // to check: ENSURE always gets executed
    e1 = g.find(lhs);
    e2 = g.find(rhs);

    ctx.regular_stream() << "\nexplain: "
                         << expr_ref(e1->get_expr(), m) << " = " << expr_ref(e2->get_expr(), m) << "\n";

    SASSERT(e1->get_root() == e2->get_root());

    expr_ref_vector iuc(m);
    g.explain_eq_sum(e1, e2, iuc);

    ctx.regular_stream() << "IUC: " << iuc << "\n";

    ctx.regular_stream() << "graph: \n";
    ctx.regular_stream() << g;
  }
};


#if 0

#define MAXJ 100
class euf_iuc : public cmd {
  expr *m_euf_cube;   // axioms  (and l1 l2 ... ln)
  expr *m_euf_assums; // assumptions (and a1 a2 ... am)
  expr *m_euf_eq;     // equality to justify

  struct summarizer {
    ast_manager &m_m;
    ptr_vector<int> &m_js;
    int m_offset;
    app *m_asserted;
    app *m_assumed;

    summarizer(ast_manager &m, ptr_vector<int> &js, int offset, app *asserted,
               app *assumed)
        : m_m(m), m_js(js), m_offset(offset), m_asserted(asserted),
          m_assumed(assumed) {}

    // \brief if `e1` and `e2` share a term (syntactic), `l` and `r` point to
    // the non-shared terms of e1 and e2 respectively and returns true.
    // otherwise returns false.
    bool get_ends(expr *e1, expr *e2, expr **l, expr **r) {
      expr *e1lhs, *e1rhs, *e2lhs, *e2rhs;
      m_m.is_eq(e1, e1lhs, e1rhs);
      m_m.is_eq(e2, e2lhs, e2rhs);

      // is there a call to simplify?
      if (e1lhs == e2lhs) {
        *l = e1rhs;
        *r = e2rhs;
      } else if (e1lhs == e2rhs) {
        *l = e1rhs;
        *r = e2lhs;
      } else if (e1rhs == e2lhs) {
        *l = e1lhs;
        *r = e2rhs;
      } else if (e1rhs == e2rhs) {
        *l = e1lhs;
        *r = e2lhs;
      } else {
        return false;
      }
      return true;
    }

    expr *get_js_expr(int idx) {
      if (*m_js[idx] < m_offset)
        return m_asserted->get_arg(*m_js[idx]);
      else
        return m_assumed->get_arg(*m_js[idx] - m_offset);
    }

    void summarize(int begin, int end, expr_ref_vector &summary){
      if (begin == end) {
        summary.push_back(get_js_expr(begin));
      } else {
        expr *lhs, *rhs;
        get_ends(get_js_expr(begin), get_js_expr(begin + 1), &lhs, &rhs);
        if (end - begin > 1) {
          expr *dummy;
          get_ends(get_js_expr(end - 1), get_js_expr(end), &dummy, &rhs);
        }
        summary.push_back(m_m.mk_eq(lhs, rhs));
      }
    }

    // summarizes consecutive equalities of the same color
    void horizontal_summarize(int (*color)(int,int), expr_ref_vector &summary) {
      int curr_color = color(m_offset, *m_js[0]);
      int begin_curr = 0, end_curr = 0;

      expr *prev = get_js_expr(0), *curr;
      expr *l, *r;

      for (int i = 1; i < m_js.size(); ++i) {
        curr = get_js_expr(i);
        int c = color(m_offset, *m_js[i]);
        if (c == curr_color && get_ends(prev, curr, &l, &r)) { // same sequence
          // get_ends is never executed the first iteration of the loop
          end_curr = i;
        } else { // current sequence ended, either because of color change or
                 // because of justification cut
          summarize(begin_curr, end_curr, summary);
          curr_color = c;
          begin_curr = end_curr = i;
        }
        prev = curr;
      }
      summarize(begin_curr, end_curr, summary);
    }
  };

public : euf_iuc() : cmd("euf-iuc"){};
  char const *get_usage() const override { return "(euf-cube) (assums) (eq)"; }
  char const *get_descr(cmd_context &ctx) const override {
    return "Interpolating congruence closure for 2 EUF cubes";
  }

  unsigned get_arity() const override { return 3; }
  cmd_arg_kind next_arg_kind(cmd_context &ctx) const override {
    return CPK_EXPR;
  }
  void set_next_arg(cmd_context &ctx, expr *arg) override {
    if (m_euf_cube == nullptr)
      m_euf_cube = arg;
    else if (m_euf_assums == nullptr)
      m_euf_assums = arg;
    else
      m_euf_eq = arg;
  }
  void prepare(cmd_context &ctx) override {
    m_euf_cube = nullptr;
    m_euf_assums = nullptr;
    m_euf_eq = nullptr;
  }

  void execute(cmd_context &ctx) override {

    // enable_trace("euf_verbose");
    // enable_trace("euf");

    ast_manager &m = ctx.m();
    reg_decl_plugins(m);
    arith_util a(m);

    expr_ref phi(m_euf_cube, m);
    expr_ref assums(m_euf_assums, m);
    expr_ref eq(m_euf_eq, m);

    euf::egraph g(m);

    int justifications[MAXJ];
    for(int i = 0; i < MAXJ ; ++i) {
      justifications[i] = i;
    }

    int n = 0;
    expr *lhs, *rhs;
    euf::enode *e1, *e2;

    // insert formula
    SASSERT(m.is_and(phi));
    app *phi_app = to_app(phi);
    ctx.regular_stream() << "------------------------------------------------------------\n";
    ctx.regular_stream() << "Phi: ";
    for (auto l : *phi_app) {
      ctx.regular_stream() << expr_ref(l,m) << " ";
      SASSERT(m.is_eq(l));
      m.is_eq(l, lhs, rhs);

      e1 = g.rec_mk(lhs,0 /* generation */);
      e2 = g.rec_mk(rhs,0);
      g.merge(e1, e2, &justifications[n]);
      ++n;
      g.propagate();
    }
    int phi_n_lits = n;
    // insert assumptions
    SASSERT(m.is_and(assums));
    app *assums_app = to_app(assums);
    ctx.regular_stream() << "\nAssums: ";
    for (auto l : *assums_app) {
      ctx.regular_stream() << expr_ref(l, m) << " ";

      if(!m.is_eq(l, lhs, rhs))
        continue;

      e1 = g.rec_mk(lhs, 0);
      e2 = g.rec_mk(rhs, 0);
      g.merge(e1, e2, &justifications[n]);
      ++n;
      g.propagate();
    }

    SASSERT(!g.inconsistent());

    SASSERT(m.is_eq(m_euf_eq));
    m.is_eq(m_euf_eq,lhs,rhs);
    e1 = g.find(lhs);
    SASSERT(e1 && "term not internalized");
    ctx.regular_stream() << "\nJustify " << expr_ref(e1->get_expr(), m) << " = ";
    e2 = g.find(rhs);
    SASSERT(e2 && "term not internalized");
    ctx.regular_stream() << expr_ref(e2->get_expr(), m) << ":\n";

    ptr_vector<int> js;
    g.begin_explain();
    g.explain_eq<int>(js, nullptr, e1, e2);
    g.end_explain();

    ctx.regular_stream() << "\tfull:  ";
    for (int *j : js) {
      if (*j >= phi_n_lits) {
        ctx.regular_stream()
            << expr_ref(assums_app->get_arg(*j - phi_n_lits), m) << ", ";
      }
      else {
        ctx.regular_stream()
            << expr_ref(phi_app->get_arg(*j), m) << ", ";
      }
    }
    ctx.regular_stream() << "\n\tassumptions only: ";
    for (int *j : js) {
      if (*j >= phi_n_lits) {
        ctx.regular_stream()
            << expr_ref(assums_app->get_arg(*j - phi_n_lits), m) << ", ";
      }
    }
    ctx.regular_stream() << "\n";

    auto color = [](int th, int n) {return n < th ? 0 : 1;};
    summarizer sum(m,js,phi_n_lits,phi_app,assums_app);

    expr_ref_vector summary(m);
    sum.horizontal_summarize(color, summary);

    // this is sumarized, not filtered!
    ctx.regular_stream() << "\nSummarized: ";
    for (auto e : summary)
      ctx.regular_stream() << expr_ref(e, m) << ", ";

    ctx.regular_stream() << "\n";

    // ctx.regular_stream() << "graph: \n";
    // ctx.regular_stream() << g;
  }
};

#endif


void install_dbg_cmds(cmd_context & ctx) {
    ctx.insert(alloc(print_dimacs_cmd));
    ctx.insert(alloc(get_quantifier_body_cmd));
    ctx.insert(alloc(set_cmd));
    ctx.insert(alloc(pp_var_cmd));
    ctx.insert(alloc(shift_vars_cmd));
    ctx.insert(alloc(assert_not_cmd));
    ctx.insert(alloc(size_cmd));
    ctx.insert(alloc(subst_cmd));
    ctx.insert(alloc(bool_rewriter_cmd));
    ctx.insert(alloc(bool_frewriter_cmd));
    ctx.insert(alloc(elim_and_cmd));
    install_simplify_cmd(ctx, "dbg-th-rewriter");
    ctx.insert(alloc(lt_cmd));
    ctx.insert(alloc(some_value_cmd));
    ctx.insert(alloc(params_cmd));
    ctx.insert(alloc(translator_cmd));
    ctx.insert(alloc(sexpr_cmd));
    ctx.insert(alloc(used_vars_cmd));
    ctx.insert(alloc(elim_unused_vars_cmd));
    ctx.insert(alloc(instantiate_cmd));
    ctx.insert(alloc(instantiate_nested_cmd));
    ctx.insert(alloc(set_next_id));
    ctx.insert(alloc(get_interpolant_cmd));
    ctx.insert(alloc(mbp_cmd));
    ctx.insert(alloc(tg_mbp_cmd));
    ctx.insert(alloc(mbi_cmd));
    ctx.insert(alloc(euf_project_cmd));
    ctx.insert(alloc(eufi_cmd));
    ctx.insert(alloc(qe_lite_tg_cmd));
    ctx.insert(alloc(qe_lite_der_cmd));
    ctx.insert(alloc(euf_solver_eq));
    ctx.insert(alloc(euf_solver_iuc));
}

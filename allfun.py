#!/usr/bin/env python3
"""Basic ideas for all fun."""

# File:  allfun.py
# Author:  mikolas
# Created on:  Sat Jul 13 14:47:01 CEST 2024
# Copyright (C) 2024, Mikolas Janota

import argparse
import itertools
import json
import multiprocessing
import os
import sys
import typing
from collections.abc import Iterable
from pathlib import Path
from io import StringIO

import pysmt
import pysmt.environment
import pysmt.shortcuts
import pysmt.smtlib.commands as smtcmd
import pysmt.smtlib.parser
import sympy
from pysmt.fnode import FNode
from pysmt.shortcuts import FALSE, And, Equals, ForAll, Not, Or, Symbol
from pysmt.substituter import FunctionInterpretation
from pysmt.typing import REAL
from sympy import Expr

import external
import mirek
import mirek_term
from external import call_tarski, make_query, portfolio_solve
from solvers import call_portfolio
from stats import Stats
from translate import Converter, TranslateAllFunException
from util import (
    ConstOracle,
    Interpret,
    check_add,
    find_index,
    flatten_and,
    get_arguments,
    get_fixed,
    powerset,
    warning,
)


def sz(v: FNode):
    return v.size()


def sz_id(v: FNode):
    return (v.size(), v.node_id())


def smaller(a: FNode, b: FNode) -> bool:
    """Compare two formulas in order to break symmetries for commutative
    things."""
    return a.node_id() < b.node_id()


def mkmult(a: FNode, b: FNode) -> FNode:
    """Make pysmt mult and simplify."""
    rv = (a * b) if smaller(a, b) else (b * a)
    return rv.simplify()


def mkplus(a: FNode, b: FNode) -> FNode:
    """Make pysmt plus and simplify."""
    rv = (a + b) if smaller(a, b) else (b + a)
    return rv.simplify()


def mkeq(a: FNode, b: FNode) -> FNode:
    """Make pysmt equality and simplify."""
    if not smaller(a, b):
        b, a = a, b
    return Equals(a, b).simplify()


def show(message, formula: FNode):
    """Show message with a formula."""
    print(message, formula.serialize(), flush=True)


def show_all(loglevel, message, formulas: Iterable[FNode]):
    """Show message with a formula."""
    if loglevel > VERBOSE:
        return
    print(message, flush=True)
    for f in formulas:
        print(" ", f.serialize(), flush=True)


class AllFunException(Exception):
    """exception."""


def check(condition, message):
    """Throw an exception if condition not verified."""
    if not condition:
        raise AllFunException(message)


VERBOSE = 1


def showl(lev, message, formula: FNode):
    """Show message with a formula under a verbosity condition."""
    if not lev <= VERBOSE:
        return
    print(message, formula.serialize(), flush=True)


def log(lev, *args, **kwargs):
    """Like print, but only if lev > VERBOSE."""
    if not lev <= VERBOSE:
        return
    print(*args, **kwargs, flush=True)


class Quantifier:
    """Class handling as a single quantified expression."""

    def __init__(self, fla: FNode, parent):
        self.fla = fla
        self.matrix: FNode = self.fla.args()[0]
        self.quant_vars = self.fla.quantifier_vars()
        self.parent = parent
        self.con = parent.con.create_copy()
        self.x: FNode = parent.x
        for v in self.quant_vars:
            log(2, "adding:", v)
            self.con.add_var(v)
        self.templated: FNode | None = None
        # check(self.parent.is_qf(self.fla_without_quant), "expecting prenex assertions")
        log(2, "Quant vars:", self.quant_vars)
        showl(2, "Matrix:", self.matrix)

    def make_templated(self, template):
        """Create a templated version of this quantifier."""
        self.templated = template.apply(self)
        log(2, "== templated", self.templated)
        return self.templated

    def nice_instantiations(self) -> typing.Set[FNode] | None:
        """Attempts to create some nice instantiations."""

        def get_subs_light(args_sy: typing.List[Expr]):
            """Set everything to 0 accept for one, which is set to x."""
            x = self.con.smt2sy(self.x)
            for i, asy in enumerate(args_sy):
                rest = args_sy[:i] + args_sy[i + 1 :]
                to_solve = [sympy.Eq(a, sympy.S.Zero) for a in rest] + [
                    sympy.Eq(asy, x)
                ]
                print("to_solve:", to_solve)
                yield sympy.solve(to_solve, quant_vars_sy, dict=True, warn=True)

        def get_subs_heavy(args_sy: typing.List[Expr]):
            """For every subset s set 0 and the rest to x."""
            x = self.con.smt2sy(self.x)
            for s in powerset(args_sy):
                to_solve = [sympy.Eq(a, sympy.S.Zero) for a in s] + [
                    sympy.Eq(a, x) for a in args_sy if a not in s
                ]
                print("to_solve:", to_solve)
                yield sympy.solve(to_solve, quant_vars_sy, dict=True, warn=True)

        def sysol_to_pysmt(sol):
            """Convert sympy solution to pysmt subtitution."""
            rv = {}
            # def_value = sympy.S.Zero
            for syv in quant_vars_sy:
                # syval = sol.get(syv, def_value)
                if syv in sol:
                    syval = sol[syv]
                    val = self.con.sy2smt(syval)
                    v = self.con.sy2smt(syv)
                    rv[v] = val
                else:
                    log(3, f"independent var in solution {syv}")
            return rv

        if not self.parent.is_qf(self.matrix):
            return None
        log(2, "== nice_instantiations", self.matrix)
        args = get_arguments(self.matrix, self.parent.fname)
        log(3, "fun args", args)
        # convert to sympy
        args_sy: typing.List[Expr] = [
            asy for a in args if (asy := self.con.smt2sy(a)).is_polynomial()
        ]
        quant_vars_sy = [self.con.smt2sy(x) for x in self.quant_vars]

        # calculate instantiations
        rv: typing.Set[FNode] = set()
        get_subs = get_subs_heavy if self.parent.opts.nice_heavy else get_subs_light
        try:
            qvars = self.quant_vars + (self.x,)
            for solutions in get_subs(args_sy):
                print("Solutions:", solutions)
                for s in solutions:
                    subs: FNode = self.matrix.substitute(sysol_to_pysmt(s))
                    new_instance = ForAll(qvars, subs).simplify()
                    if not new_instance.is_true() and check_add(rv, new_instance):
                        show("nice instance: ", new_instance)
        except Exception as e:
            warning(f"Something when wrong in nice instantiations: {e}")
        log(2, "== done nice_instantiations", self.matrix)
        return rv


class AllFun:
    """Basic ideas for all fun."""

    def __init__(self, opts, script):
        self.opts = opts
        self.script = script
        self.spec_fla = None
        self.quantifiers = []
        self.background = set()  # set of background axioms
        self.redundant_facts = set()  # we add nice instantions here
        self.fname = None  # name of the function
        self.con = Converter()  # conversion between smt and sympy
        self.const_oracle = ConstOracle()
        self.skolems = []
        self.negations = dict()
        self.x = self.con.add_var(
            Symbol("_x", REAL)
        )  # we use this var to construct the definition f
        self.original_function = (
            None  # description of the function from the original problem, if available
        )
        self.init_terms: list[FNode] = []
        self.derived_facts: list[FNode] = []
        self.stats = Stats()

    def zero(self):
        return self.con.mgr.Real(0)

    def one(self):
        return self.con.mgr.Real(1)

    def build_domain_constraints(self, c: FNode):
        """Build a domain constraint over c for for the function being solved
        as SMT, from the original problem formulation."""
        assert self.original_function is not None
        f, t, _attrs = self.original_function
        check(
            f == self.fname.symbol_name(),
            "the original problem function name does not match the SMT one",
        )
        if t is None:
            return None
        x = mirek_term.VariableTerm(c.symbol_name())
        rv = pysmt.shortcuts.And([a.to_pysmt() for a in t.domain.assumptions(x)])
        log(2, "domain constraint:", rv)
        # log(2, "domain constraint", mirek.SMT.reduce_and(t.domain.assumptions(x)))
        return rv
    
    def build_domain_constraints_num(self, num: int):
        assert self.original_function is not None
        f, t, _attrs = self.original_function
        check(
            f == self.fname.symbol_name(),
                "the original problem function name does not match the SMT one",
        )
        if t is None:
            return None
        x = mirek_term.NumericTerm(num)
        rv = pysmt.shortcuts.And([a.to_pysmt() for a in t.domain.assumptions(x)])
        log(2, "domain constraint num:", rv)
        # log(2, "domain constraint", mirek.SMT.reduce_and(t.domain.assumptions(x)))
        return rv    

    def add_original_problem(self, original_filename):
        """Register the original problem."""
        spec_funs = mirek.parse_file("mirek_special_functions.txt", mirek.SpecFuncPack)
        problems = mirek.parse_file(
            original_filename, lambda lines: mirek.parse_problem(lines, spec_funs)
        )
        check(
            len(problems) == 1,
            "expecting a single problem in the original problem formulation",
        )
        problem = problems[0]
        log(2, f"read original problem {problem.title}")
        check(
            len(problem.header.functions) == 1,
            "expecting a single function in the original problem formulation",
        )
        self.original_function = problem.header.functions[0]
        log(2, f"original function '{self.original_function[0]}'")

    def get_constants(self) -> typing.Set[FNode]:
        """Extract constants name."""
        rv: typing.Set[FNode] = set()
        for fs in self.script.get_declared_symbols():
            ft = fs.symbol_type()
            if ft.is_function_type():
                continue
            check(ft.is_real_type(), "only real constants expected")
            rv.add(fs)
        return rv

    def get_function_name(self):
        """Extract function name."""
        rv = None
        for fs in self.script.get_declared_symbols():
            ft = fs.symbol_type()
            if not ft.is_function_type() or len(ft.param_types) == 0:
                continue
            check(rv is None, "expected only one function declaration")
            check(
                ft.is_function_type()
                and ft.return_type.is_real_type()
                and len(ft.param_types) == 1
                and ft.param_types[0].is_real_type(),
                "expected only function from reals to reals",
            )
            rv = fs
        check(rv is not None, "expected function declaration")
        return rv

    def solve(self):
        """Attempt to solve allfun."""
        self.fname = self.get_function_name()
        self.con.add_fun(self.fname)
        for c in self.get_constants():
            self.con.add_const(c)
        self.spec_fla = self.script.get_last_formula()

        # split formula into quantifiers and others
        for asr in self.script.filter_by_command_name(smtcmd.ASSERT):
            afla: FNode = asr.args[0]
            if afla.is_forall():
                self.quantifiers.append(Quantifier(afla, self))
            else:
                showl(2, "fact:", afla)
                self.background.add(afla)

        if self.opts.nice_instantiations:
            # create nice instantiations
            for q in self.quantifiers:
                if (nc := q.nice_instantiations()) is not None:
                    log(3, nc)
                    self.stats.nice_insts.inc(len(nc))
                    self.redundant_facts |= nc

        showl(1, "fla:", self.spec_fla)
        log(1, "fname:", self.fname)

        if (sols := self.template_solve()) is not None:
            return sols
        return None

    def mk_skolem(self):
        """Create a new skolem constant.

        Currently we're not careful about name collision.
        """
        nm = f"SK{len(self.skolems)}"
        rv = Symbol(nm, REAL)
        self.con.add_const(rv)
        self.skolems.append(rv)
        return rv

    def neg_sol(self, s: FNode):
        """Say that the given solution is not a solution."""
        if s in self.negations:
            return self.negations[s]
        sk = self.mk_skolem()
        inner = Not(s.substitute({self.x: sk}))
        if self.original_function is not None:
            dc = self.build_domain_constraints(sk)
            if dc is not None and not dc.is_true():
                inner = And(dc, inner)

        self.negations[s] = inner
        return inner

    def mk_coeffs_vals(self, solution: typing.Dict[Expr, Expr], cfs: typing.List[Expr]):
        """Create (symbolic) coefficient values based on partial values.

        For a quadratic poylynomial f(x) = c2x^2+c1x+c0 we have f(1) =
        c2+c1+c0, f(0)=c0, and f(-1)=c2-c1+c0, which lets us rewrite the
        coefficients symbolically, if there are no concrete values for
        them.
        """
        assert len(cfs) == 3
        # make sure that the inputs to f are in its domain
        f = self.con.smt2sy(self.fname)
        c0, c1, c2 = cfs[0], cfs[1], cfs[2]
        rv = [None for _ in range(3)]
        if c0 in solution:
            rv[0] = solution[c0]
        else:
            # Is f(0) allowed here?
            dc0 = self.build_domain_constraints_num(0)
            if dc0 is not None and not dc0.simplify().is_true():
                log(2, f"Domain constraint {dc0} does not allow f(0) to be evaluated, using f(1), f(2), f(3).")

                # Try f(1), f(2), f(3).
                # TODO: Fix for other restricted domains.
                dc1 = self.build_domain_constraints_num(1)
                dc2 = self.build_domain_constraints_num(2)
                dc3 = self.build_domain_constraints_num(3)
                assert dc1 is not None and dc1.simplify().is_true(), (dc1)
                assert dc2 is not None and dc2.simplify().is_true(), (dc2)
                assert dc3 is not None and dc3.simplify().is_true(), (dc3)

                rv[0] = ((3 * f(1)) - (3 * f(2)) + f(3))
            else:
                rv[0] = f(0)

        if c2 in solution:
            rv[2] = solution[c2]
        else:
            # Is f(1) and f(-1) allowed here?
            dc1 = self.build_domain_constraints_num(1)
            dcm1 = self.build_domain_constraints_num(-1)
            if (dc1 is not None and not dc1.simplify().is_true()) or (dcm1 is not None and not dcm1.simplify().is_true()):
                log(2, f"Domain constraints {dc1} or {dcm1} do not allow f(1) or f(-1) to be evaluated, using f(1), f(2), f(3).")
                # Assume f(1) and try f(2) and f(3).
                dc2 = self.build_domain_constraints_num(2)
                dc3 = self.build_domain_constraints_num(3)
                assert dc1 is not None and dc1.simplify().is_true(), (dc1)
                assert dc2 is not None and dc2.simplify().is_true(), (dc2)
                assert dc3 is not None and dc3.simplify().is_true(), (dc3)

                rv[2] = ((f(1) / 2) - f(2) + (f(3) / 2))
            else:
                rv[2] = ((f(1) + f(-1)) / 2 - rv[0])

        if c1 in solution:
            rv[1] = solution[c1]
        else:
            # Is f(1) allowed here?
            dc1 = self.build_domain_constraints_num(1)
            assert dc1 is not None and dc1.simplify().is_true(), (dc1)
            rv[1] = (f(1) - rv[2] - rv[0])

        return rv

    def mk_coeff_sol(
        self, solution: typing.Dict[Expr, Expr], cfs_sy: typing.List[Expr]
    ):
        """Create a function representation ouf of coefficient values."""
        assert len(cfs_sy) == 3
        sy_vals = self.mk_coeffs_vals(solution, cfs_sy)
        vals = [self.con.sy2smt(v).simplify() for v in sy_vals]
        x = self.x
        rv = (vals[0] + vals[1] * x + vals[2] * x * x).simplify()
        log(1, f"sol: lambda {x}:", rv)
        # TODO: condition by domain of x
        return Equals(self.fname(x), rv)

    def mk_constr_sol(self, fixed: typing.Dict[Expr, Expr], constraint: Expr, template):
        """Create a function representation ouf of constraints and
        coefficients."""
        assert len(template.cfs_sy) == 3
        log(3, "mk_constr_sol", fixed, constraint)
        cfx = get_fixed(constraint, set(template.cfs_sy))
        log(3, "get_fixed", cfx)
        fixed = fixed | cfx
        log(2, "mk_constr_sol", fixed, constraint)
        sy_vals = self.mk_coeffs_vals(fixed, template.cfs_sy)
        subs = {template.cfs_sy[deg]: val for deg, val in enumerate(sy_vals)}
        constraint_vals_sy = constraint.subs(subs)
        constraint_vals = self.con.sy2smt(constraint_vals_sy)
        showl(2, "constraint_vals", constraint_vals)
        x = self.x
        f = self.fname
        vals: typing.List[FNode] = [self.con.sy2smt(v).simplify() for v in sy_vals]
        rv = And(
            constraint_vals, Equals(f(x), vals[0] + vals[1] * x + vals[2] * x * x)
        ).simplify()
        print("sol:", rv)
        return rv

    def get_coeffs_eq(self, q: Quantifier):
        """A polynomial is equal to 0 iff all its coeffs equal to 0.

        This routine collects all coeffs and equates them to 0.
        """
        assert q.templated is not None and q.templated.is_equals()
        t = q.con.smt2sy(q.templated)
        a, b = t.args
        log(2, f"== template_solve_eq {a} = {b}")
        lhs: Expr = (a - b).simplify(rational=True)
        if not lhs.is_polynomial():
            log(2, f"{lhs} is not polynomial")
            return None
        log(2, f"{lhs} is polynomial")
        quant_vars_sy = [q.con.smt2sy(x) for x in q.quant_vars]
        lhs = sympy.polys.polytools.poly(lhs, quant_vars_sy)
        log(2, "polynomial", lhs, lhs.coeffs())
        return {sympy.Eq(c, sympy.S.Zero) for c in lhs.coeffs()}

    def test_sols(self, sols, use_original_constraint, additional_id=None):
        """Test solutions if they cover everything."""
        log(2, "== test_sols", sols)
        show_all(3, "derived_facts", self.derived_facts)
        show_all(3, "redundant_facts", self.redundant_facts)

        tests = (
            list(self.derived_facts)
            + list(self.redundant_facts)
            + list(map(self.mk_test, sols))
        )
        if use_original_constraint:
            tests += [self.spec_fla]

        test_formula: FNode = And(tests)
        test_result = portfolio_solve(test_formula, self.con)
        show(
            f"test_formula -> {test_result}",
            test_formula,
        )
        if test_result is False and self.opts.smt_output_path is not None:
            Path(self.opts.smt_output_path).mkdir(parents=True, exist_ok=True)
            flas = flatten_and(test_formula)
            query = external.make_query(flas, self.con)
            filename = os.path.basename(self.opts.filename).removesuffix(".smt2")
            if additional_id is not None:
                filename += "_" + additional_id
            outfile_path = os.path.join(self.opts.smt_output_path, filename + ".smt2")
            with open(outfile_path, "w", encoding="utf-8") as outfile:
                outfile.write(query)
        return test_result is False

    def find_irredundant(self, new_facts, sols):
        """Return a subset of new_facts by removing redundant facts."""
        rv = []
        for fact in sorted(new_facts, key=sz):
            pruning_fact = self.find_provable(
                sols,
                [fact],
                # verbose=args.verbose,
                timeout=1,
                only_check=True,
            )
            if pruning_fact:
                log(2, f"Pruned fact: {fact}")
            else:
                log(2, f"Added fact: {fact}")
                self.derived_facts.append(fact)
                rv.append(fact)
        return rv

    def find_provable(self, sols, formulae, timeout=5, only_check=False):
        """Test formulae if they are provable."""
        log(2, "== find_provable", len(formulae))

        if only_check:
            tests = list(self.derived_facts)
        else:
            tests = (
                list(self.derived_facts)
                + list(self.redundant_facts)
                + list(map(self.mk_test, sols))
            )
            if not self.opts.subst_constraints_remove:
                tests += [self.spec_fla]

        results = call_portfolio(
            [make_query([And((tests + [Not(f)]))], self.con) for f in formulae],
            timeout=timeout,
            only_check=only_check,
            threads=self.opts.threads,
            verbose=self.opts.external_VERBOSE > 1,
        )

        new_facts = set()

        for i, j, r in results:
            if r is False:
                if not only_check:
                    log(2, "Found fact: ", i, j, formulae[i])
                new_facts.add(formulae[i])
            elif r is True:
                if not only_check:
                    log(2, "!!! Found a model: ", i, j, formulae[i])

        return list(new_facts)

    def mk_test(self, sol):
        """Create a test formula for a single solution by negating the
        solution."""
        log(2, "== test_sol", sol)
        if VERBOSE > 1:
            show(f"sol: lambda {self.x}:", sol)
        return self.neg_sol(sol)

    class PolyTemplate:
        """Polynomial template for a function."""

        def __init__(self, con: Converter, fname: FNode):
            """TODO: to be defined."""
            self.fname = fname
            self.con = con
            self.cfs: typing.List[FNode] = [
                self.con.add_const(Symbol(f"C{i}", REAL)) for i in range(3)
            ]
            self.cfs_sy: typing.List[Expr] = [self.con.smt2sy(c) for c in self.cfs]

        def apply(self, q: Quantifier) -> FNode:
            """Create a pysmt expression that corresponds to templated fname in
            fla."""
            showl(3, "apply in ", q.matrix)
            for c in self.cfs:
                q.con.add_const(c)
            x = Symbol("_x", REAL)
            i = FunctionInterpretation(
                [x],
                x * x * self.cfs[2] + x * self.cfs[1] + self.cfs[0],
                allow_free_vars=True,
            )
            rv = q.matrix.substitute({}, interpretations={self.fname: i}).simplify()
            showl(3, "apply out", rv)
            return rv

        def apply_general(self, g: FNode) -> FNode:
            """Create a pysmt expression that corresponds to templated fname in
            g."""
            showl(3, "apply_general in ", g)
            x = Symbol("_x", REAL)
            # i = FunctionInterpretation(
            #     [x],
            #     x * x * self.cfs[2] + x * self.cfs[1] + self.cfs[0],
            #     allow_free_vars=True,
            # )
            body = x * x * self.cfs[2] + x * self.cfs[1] + self.cfs[0]
            i = Interpret(self.con.env, self.fname, x, body)
            rv = i.walk(g)
            # rv =  g.substitute({}, interpretations={self.fname: i}).simplify()
            showl(3, "apply_general out", rv)
            return rv

    def create_terms(self, depth=1):
        """Create a set of terms of given depths, self.init_terms are used for
        the base case."""
        assert depth > 0

        if depth == 1:
            return self.init_terms

        smaller_terms = {i: self.create_terms(depth=i) for i in range(1, depth)}

        # application of f
        new_terms = {self.fname(t) for t in smaller_terms[depth - 1]}

        # create binary ops on terms
        for t1 in smaller_terms[depth - 1]:
            for i in range(1, depth):
                for t2 in smaller_terms[i]:
                    if i == depth - 1 and not smaller(t1, t2):
                        continue
                    if self.zero() not in (t1, t2):  # +
                        new_terms.add(mkplus(t1, t2))
                    if self.zero() not in (t1, t2) and self.one() not in (t1, t2):  # *
                        new_terms.add(mkmult(t1, t2))
                    if t1 != t2:  # -
                        if t1 != self.zero():
                            new_terms.add(t2 - t1)
                        if t2 != self.zero():
                            new_terms.add(t1 - t2)

        return {x.simplify() for x in new_terms}

    def mk_newfacts(self, sols, d1: int, d2: int):
        """Derive new equalities of fixed depths."""
        d1_terms = self.create_terms(depth=d1)
        d2_terms = self.create_terms(depth=d2)

        log(2, f"Checking {d1} [{len(d1_terms)}] x {d2} [{len(d2_terms)}].")

        tested_facts = set()

        if self.opts.abc and (d1 == 1) and (d2 == 1):
            try:
                # Fails for example for the restricted domains.
                log(2, "=== abc solutions.")
                f0_sols = []
                f1_sols = []
                f_1_sols = []
                c_sols = []
                b_sols = []
                a_sols = []

                for sol in sols:
                    f0_sol = sol.substitute({self.x: self.zero()}).simplify()
                    f1_sol = sol.substitute({self.x: self.one()}).simplify()
                    f_1_sol = sol.substitute(
                        {self.x: (self.zero() - self.one())}
                    ).simplify()

                    tested_facts.add(f0_sol)
                    f0_sols.append(f0_sol)
                    tested_facts.add(f1_sol)
                    f1_sols.append(f1_sol)
                    tested_facts.add(f_1_sol)
                    f_1_sols.append(f_1_sol)

                    # TODO: Addapt this and more for restricted domains
                    sol_f0 = sol.substitute({self.x: self.zero()}).arg(1).simplify()
                    sol_f1 = sol.substitute({self.x: self.one()}).arg(1).simplify()
                    sol_f_1 = (
                        sol.substitute({self.x: (self.zero() - self.one())})
                        .arg(1)
                        .simplify()
                    )

                    f0 = self.fname(self.zero())
                    f1 = self.fname(self.one())
                    f_1 = self.fname(self.zero() - self.one())

                    c_sol = mkeq(f0, sol_f0).simplify()
                    b_sol = mkeq((f1 - f_1) / 2, (sol_f1 - sol_f_1) / 2).simplify()
                    a_sol = mkeq(
                        ((f1 + f_1) / 2) - f0, ((sol_f1 + sol_f_1) / 2) - sol_f0
                    ).simplify()

                    tested_facts.add(c_sol)
                    c_sols.append(c_sol)
                    tested_facts.add(b_sol)
                    b_sols.append(b_sol)
                    tested_facts.add(a_sol)
                    a_sols.append(a_sol)

                tested_facts.add(Or(f0_sols).simplify())
                tested_facts.add(Or(f1_sols).simplify())
                tested_facts.add(Or(f_1_sols).simplify())
                tested_facts.add(Or(c_sols).simplify())
                tested_facts.add(Or(b_sols).simplify())
                tested_facts.add(Or(a_sols).simplify())
            except Exception as e:
                warning(f"Something went wrong in abc (restricted domain?): {e}")

        or_sols_num = 0

        for t1 in d1_terms:
            if (d2 == 1) and self.opts.or_sol:
                or_sols = []

                for sol in sols:
                    or_sol = sol.substitute({self.x: t1}).simplify()
                    or_sols.append(or_sol)

                    if self.opts.or_sol_split:
                        tested_facts.add(or_sol)
                        or_sols_num += 1

                tested_facts.add(Or(or_sols).simplify())
                or_sols_num += 1

            for t2 in d2_terms:
                if t1 == t2:
                    continue
                tested_fact = mkeq(t1, t2)
                if (
                    not tested_fact.is_false()
                    and not tested_fact.is_true()
                    and tested_fact not in self.derived_facts
                ):
                    tested_facts.add(tested_fact)

        log(
            2,
            f"There are {len(tested_facts)} tested facts of depth ({d1},{d2}) including {or_sols_num} or sols.",
        )

        facts_to_prune = self.find_provable(
            sols, list(tested_facts), timeout=1, only_check=True
        )
        pruned_tested_facts = tested_facts - set(facts_to_prune)

        log(2, f"Pruned tested facts {len(pruned_tested_facts)}.")

        new_facts = self.find_irredundant(
            self.find_provable(
                sols, list(pruned_tested_facts), timeout=self.opts.timeout
            ),
            sols,
        )
        log(3, f"New facts tested facts {new_facts}.")
        # self.derived_facts.extend(new_facts)
        self.stats.new_facts.inc(len(new_facts))
        return len(new_facts) > 0

    def basic_instances(self) -> set[FNode]:
        """Greedy instantiantion by terms in the formula."""
        assert self.opts.subst_constraints_depth >= 1
        assert self.opts.subst_constraints_numvar >= 1

        used_terms = set()

        for d in range(1, self.opts.subst_constraints_depth + 1):
            used_terms.update(self.create_terms(depth=d))

        new_subst_instances = set()

        for q in self.quantifiers:
            vars_tuples = itertools.combinations(
                q.quant_vars,
                min(len(q.quant_vars), self.opts.subst_constraints_numvar),
            )

            for vars_tuple in vars_tuples:
                for terms_tuple in itertools.product(
                    used_terms, repeat=len(vars_tuple)
                ):
                    subst = dict(zip(vars_tuple, terms_tuple))
                    new_fla = ForAll(
                        q.quant_vars, q.matrix.substitute(subst)
                    ).simplify()
                    new_subst_instances.add(new_fla)

        if VERBOSE > 2:
            for f in new_subst_instances:
                show("new_subst_instances", f)
        return new_subst_instances

    def simple_terms(self, sols: set[FNode]):
        """Solving using simple substitutions into formulae."""
        log(1, "== simple_terms")

        # Different solutions can produce different facts (skolems + chain of derivations), hence we should clear.
        self.derived_facts.clear()

        # assert len(self.skolems) == len(sols)

        # Collect all the constants that appear anywhere including skolems, also add 0, 1
        test_flas = list(map(self.mk_test, sols))
        init_terms_set = (
            {self.zero(), self.one()}
            | self.const_oracle.get_consts(self.spec_fla)
            | set(
                itertools.chain.from_iterable(
                    map(self.const_oracle.get_consts, test_flas)
                )
            )
        )
        self.init_terms: FNode = list(init_terms_set)
        self.init_terms.sort(key=sz_id)  # sort to improve reproducibility

        log(2, "init_terms", self.init_terms)
        # log(2, "init_terms (2)", self.create_terms(depth=2))

        if self.opts.subst_constraints or self.opts.subst_constraints_remove:
            # this overrides original nice instantiations
            self.redundant_facts = self.basic_instances()

        repeat = True

        count = 0
        while repeat:
            count += 1
            log(1, f"Round of facts {count}")
            self.stats.st_rounds.set_val(count)
            repeat = False

            if self.test_sols(
                sols,
                use_original_constraint=not self.opts.subst_constraints_remove,
                additional_id=f"rs{count}",
            ):
                return sols  # sols verified, done

            for d1 in range(1, self.opts.depth1 + 1):
                for d2 in range(1, min(d1 + 1, self.opts.depth2 + 1)):
                    repeat = self.mk_newfacts(sols, d1, d2)
                    if repeat:
                        break
                if repeat:
                    break

        return None

    def template_solve_eq(self, template):
        """Solve equalities with template-based approach."""
        if not all(map(lambda q: q.templated.is_equals(), self.quantifiers)):
            return None
        to_solve = set()
        # collect equations from each quantifier, if possible
        for q in self.quantifiers:
            if (to_solve_q := self.get_coeffs_eq(q)) is None:
                return None
            to_solve |= to_solve_q

        # solve by sympy
        log(2, "eq to_solve:", to_solve)
        eq_sols = sympy.solve(to_solve, template.cfs_sy, dict=True, warn=True)
        log(2, "eq solutions:", eq_sols)

        if eq_sols is None:
            return None
        # make actual solutions and test if they cover everything
        sols = {self.mk_coeff_sol(s, template.cfs_sy) for s in eq_sols}

        if self.test_sols(sols, use_original_constraint=True):
            return sols

        # failed to prove, try simple_terms method
        if self.opts.simple_terms:
            return self.simple_terms(sols)

        return None

    def template_solve(self):
        """Solving the whole problem based on the (polynomial) template
        approach."""
        log(1, "== template_solve")
        template = AllFun.PolyTemplate(self.con, self.fname)

        for q in self.quantifiers:
            q.make_templated(template)

        if (
            self.opts.eq_solving
            and not self.background
            and (sols := self.template_solve_eq(template)) is not None
        ):
            return sols

        return self.tarski(template)

    def tarski(self, template: PolyTemplate):
        """Run tarsi on the giving template."""
        log(1, "== tarski qe")

        # tarski_range = reversed(range(3)) if self.opts.reversed_tarski else range(3)
        # for deg in tarski_range:
        #     if (rv := self.tarski_deg(deg, template)) is not None:
        #         return rv

        if self.opts.reversed_tarski:
            sols = self.tarski_reversed(2, template)

            if sols is not None:
                if self.test_sols(sols, use_original_constraint=True):
                    return sols

                # failed to prove, try simple_terms method
                if self.opts.simple_terms:
                    return self.simple_terms(sols)
        else:
            for deg in range(3):
                if (rv := self.tarski_deg(deg, template)) is not None:
                    return rv
        return None

    def fish_qe_solutions(self, f: Expr, template: PolyTemplate):
        """Try to fish exact coefficients from QEed formula."""
        log(2, f"== solution fishing {f}")
        rv = self.fish_qe_solutions_core(f, template)
        log(2, f"== solution fishing {f} -> {rv}")
        return rv

    def fish_qe_solutions_core(self, f: Expr, template: PolyTemplate):
        """Try to fish exact coefficients from QEed formula (inner method)."""
        if f.func == sympy.Eq:
            return sympy.solve([f], template.cfs_sy, dict=True, warn=True)

        if f.func == sympy.logic.boolalg.BooleanFalse:
            return []

        if f.func == sympy.Or:
            ops = f.args
            rv: typing.List[typing.Dict[Expr, Expr]] = []
            for op in ops:
                if (op_solution := self.fish_qe_solutions(op, template)) is None:
                    return None
                rv = rv + op_solution
            return rv

        if f.func == sympy.And:
            ops = f.args
            if all(map(lambda x: isinstance(x, sympy.core.relational.Eq), ops)):
                return sympy.solve(f.args, template.cfs_sy, dict=True, warn=True)
            if all(map(lambda x: isinstance(x, sympy.core.relational.Relational), ops)):
                return [f]
            di, d = find_index(ops, lambda x: isinstance(x, sympy.Or))
            if di is not None:
                ops1 = list(ops[:di] + ops[di + 1 :])
                dops = d.args
                rv = []
                for dop in dops:
                    # ands = self.con.smt2sy(self.con.sy2smt(sympy.And(*([dop] + ops1))).simplify())
                    dop_solution = self.fish_qe_solutions(
                        sympy.And(*([dop] + ops1)).simplify(rational=True),
                        template,
                    )
                    if dop_solution is None:
                        return None
                    rv = rv + dop_solution
                return rv

        return None

    def is_qf(self, formula: FNode):
        """Check if the given formulas quantifier free."""
        return self.con.env.qfo.is_qf(formula)

    def tarski_deg(self, deg: int, template: PolyTemplate):
        """Run tarski on limited degree of the polynomial."""
        log(2, f"== tarski_deg {deg}")
        self.derived_facts.clear()
        # cs forces portion of the coefficients to 0
        cs = {c: self.zero() for d, c in enumerate(template.cfs) if d > deg}
        rv = None
        if (rv := self.try_tarski_restricted(cs, template)) is not None:
            return rv

        if self.opts.restricted_tarski:
            # try placing zeros into lower degrees to simplify the problem
            for d in reversed(range(deg)):
                cs[template.cfs[d]] = self.zero()
                self.derived_facts.clear()
                if (rv := self.try_tarski_restricted(cs, template)) is not None:
                    return rv

        return None

    def tarski_reversed(self, deg: int, template: PolyTemplate):
        """Run tarski on limited degree of the polynomial in the reversed
        mode."""
        log(2, f"== tarski_deg {deg}")
        self.derived_facts.clear()
        # cs forces portion of the coefficients to 0
        cs = {c: self.zero() for d, c in enumerate(template.cfs) if d > deg}
        rv = None
        if (
            rv := self.try_tarski_restricted(cs, template, only_tarski=True)
        ) is not None:
            log(2, "== tarski the most general reversed solution")
            return rv

        # If not a solution to the most general then return the union of all the less general
        log(2, "== tarski failed for the most general reversed solution")
        union_rv = None

        for ndeg in reversed(range(deg + 1)):
            # cs forces portion of the coefficients to 0
            cs = {c: self.zero() for d, c in enumerate(template.cfs) if d > ndeg}

            if ndeg != deg:
                if (
                    rv := self.try_tarski_restricted(cs, template, only_tarski=True)
                ) is not None:
                    if union_rv is None:
                        union_rv = rv
                    else:
                        union_rv = union_rv.union(rv)

            if self.opts.restricted_tarski:
                # try placing zeros into lower degrees to simplify the problem
                for d in reversed(range(ndeg)):
                    cs[template.cfs[d]] = self.zero()
                    self.derived_facts.clear()
                    if (
                        rv := self.try_tarski_restricted(cs, template, only_tarski=True)
                    ) is not None:
                        if union_rv is None:
                            union_rv = rv
                        else:
                            union_rv = union_rv.union(rv)

        log(2, f"=== Union of solutions: {union_rv}")

        return union_rv

    def try_tarski_restricted(
        self,
        cs: typing.Dict[Expr, Expr],
        template: PolyTemplate,
        only_tarski=False,
    ):
        """Run tarski_restricted, None if there's an exception in
        translation."""
        rv = None
        try:
            rv = self.tarski_restricted(cs, template, only_tarski=only_tarski)
        except TranslateAllFunException as e:
            warning(f"EXCEPTION: something when wrong in tarski_deg: {e}")
        return rv

    def tarski_quant(self, q: FNode, qq: Quantifier) -> FNode:
        """Try to help tarski with quantifiers when the quantified formula is
        an equality of polynomials."""
        if not q.is_forall():
            return q
        matrix: Expr = qq.con.smt2sy(q.args()[0])
        log(3, "tarski_quant matrix", matrix)
        if not matrix.is_Equality:
            return q
        a, b = matrix.args
        lhs = (a - b).simplify(rational=True)
        if not lhs.is_polynomial():
            return q
        quant_vars_sy = [qq.con.smt2sy(x) for x in qq.quant_vars]
        lhs = sympy.polys.polytools.poly(lhs, quant_vars_sy)
        log(3, "q polynomial", lhs, lhs.coeffs())
        eqs = {sympy.Eq(c, sympy.S.Zero) for c in lhs.coeffs()}
        log(3, "q eqs", eqs)
        rv = And([self.con.sy2smt(eq) for eq in eqs]).simplify()
        log(2, q, "->", rv)
        return rv

    def tarski_restricted(
        self, cs: typing.Dict[Expr, Expr], template: PolyTemplate, only_tarski=False
    ):
        """Run tarski on a restricted set of coefficients."""
        log(2, f"== tarski_restricted {cs}")
        qs = []
        cs_sy = {self.con.smt2sy(v): self.con.smt2sy(cs[v]) for v in cs}
        for q in self.quantifiers:
            templated1 = q.templated.substitute(cs)
            showl(2, "restricted quant:", templated1)
            q1 = self.tarski_quant(ForAll(q.quant_vars, templated1).simplify(), q)
            qs.append(q1)
            log(2, "restricted q:", q1)
        for b in self.background:
            templated = template.apply_general(b)
            templated1 = templated.substitute(cs)
            log(
                2,
                "restricted background:",
                b.serialize(),
                " ... ",
                templated1.serialize(),
            )
            qs.append(templated1)

        if any(map(lambda x: x.is_false(), qs)):
            log(2, "trivially false")
            qe_const = FALSE()
        else:
            if (qe_const := call_tarski(qs)) is None:
                return None
        show("solution qe:", qe_const)
        qe_const = qe_const.simplify()
        show("solution qe simpl:", qe_const)
        if qe_const.is_false():
            sols = set()  # no solutions
        else:
            # fish for solutions
            qe_const_sy = self.con.smt2sy(qe_const).simplify(rational=True)
            log(2, "solution qe:", qe_const_sy)
            if (fished_sols := self.fish_qe_solutions(qe_const_sy, template)) is None:
                return None
            log(1, "fished solutions qe:", fished_sols)
            sols = set()
            sols_coef = [s for s in fished_sols if isinstance(s, dict)]
            for s in sols_coef:
                s.update(cs_sy)
            log(2, "sols coef:", sols_coef)
            sols.update({self.mk_coeff_sol(s, template.cfs_sy) for s in sols_coef})
            # other constraints, not simple coefficients
            sols_constr = {
                self.mk_constr_sol(cs_sy, s, template)
                for s in fished_sols
                if not isinstance(s, dict)
            }
            log(2, "sols constr:", sols_constr)
            sols.update(sols_constr)

        if only_tarski:
            return sols
        else:
            if self.test_sols(sols, use_original_constraint=True):
                return sols

            rv = None

            # failed to prove, try simple_terms method
            if self.opts.simple_terms:
                rv = self.simple_terms(sols)

            return rv


def run_main():
    """Run the whole program."""
    multiprocessing.set_start_method("fork")
    parser = argparse.ArgumentParser(description="All Fun.")
    parser.add_argument("filename")

    def bool_opt(name, default, help_msg, dest=None):
        """Create a boolean option with a no option."""
        if dest is None:
            dest = name.replace("-", "_")
        parser.add_argument(
            f"--{name}",
            help=help_msg,
            default=default,
            dest=dest,
            action=argparse.BooleanOptionalAction,
        )

    # Old version of python
    # def bool_opt(name, default, help, dest=None):
    #     parser.add_argument(
    #         f"--{name}", help=help, default=default, dest=dest, action="store_true"
    #     )
    #     parser.add_argument(
    #         f"--no-{name}", help=f"turn off {name}", dest=dest, action="store_false"
    #     )

    bool_opt(
        "nice-instantiations",
        default=True,
        dest="nice_instantiations",
        help_msg="use nice instantiations",
    )

    bool_opt(
        "nice-instantiations-heavy",
        default=True,
        dest="nice_heavy",
        help_msg="be more aggressive in nice instantiations",
    )

    parser.add_argument(
        "--original-problem",
        dest="original_problem",
        help="provide original problem formulation in Mirek's notation",
        type=str,
    )

    bool_opt(
        "filename-is-original-problem",
        dest="filename_is_original_problem",
        default=False,
        help_msg="filename is the original problem formulation in Mirek's notation",
    )

    bool_opt(
        "eq-solving",
        dest="eq_solving",
        default=True,
        help_msg="use equality-solving solving",
    )
    parser.add_argument(
        "--external-verbosity",
        dest="external_VERBOSE",
        default=1,
        type=int,
        help="verbosity level for external module",
    )
    parser.add_argument(
        "--verbosity",
        dest="VERBOSE",
        default=1,
        type=int,
        help="verbosity level for main module",
    )
    bool_opt(
        "reversed-tarski",
        dest="reversed_tarski",
        default=True,
        help_msg="use reversed tarski (start from degree 2)",
    )
    bool_opt(
        "restricted-tarski",
        dest="restricted_tarski",
        default=True,
        help_msg="use restricted tarski (some coefs to 0)",
    )
    bool_opt(
        "simple-terms",
        dest="simple_terms",
        default=True,
        help_msg="try to substitute simple terms",
    )
    parser.add_argument(
        "--depth1", type=int, default=3, help="The max depth of the first term."
    )
    parser.add_argument(
        "--depth2", type=int, default=2, help="The max depth of the second term."
    )
    bool_opt(
        "subst-constraints",
        dest="subst_constraints",
        default=True,
        help_msg="Substitute terms into the constraints (subst_constraints_numvar variables).",
    )
    parser.add_argument(
        "--subst_constraints_depth",
        type=int,
        default=1,
        help="The depth of substitute terms into the constraints is 1...this.",
    )
    parser.add_argument(
        "--subst_constraints_numvar",
        type=int,
        default=1,
        help="The number of vars we want to instantiate in simple terms.",
    )
    bool_opt(
        "subst-constraints-remove",
        dest="subst_constraints_remove",
        default=False,
        help_msg="Substitute terms into the constraints (subst_constraints_numvar variables) (and remove the original).",
    )
    bool_opt(
        "abc",
        dest="abc",
        default=False,
        help_msg="Try to use a b c coefficients.",
    )
    bool_opt(
        "or-sol",
        dest="or_sol",
        default=True,
        help_msg="Use OR of the solutions and substitute terms of the size depth1 (when you first encouter depth1)",
    )
    bool_opt(
        "or-sol-split",
        dest="or_sol_split",
        default=True,
        help_msg="When using or-sol, try also individual equalities.",
    )
    parser.add_argument(
        "--threads",
        type=int,
        default=8,
        help="The number of threads for simple terms.",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=5,
        help="Timeout for solvers in seconds for simple terms.",
    )
    parser.add_argument(
        "--smt-output-path",
        dest="smt_output_path",
        type=str,
        default=None,
        help="Save SMT files that led to successful calls on proving there are no more solutions.",
    )

    opts = parser.parse_args()
    global VERBOSE
    VERBOSE, external.VERBOSE = opts.VERBOSE, opts.external_VERBOSE

    with open("config.json", encoding="utf-8") as cfgf:
        external.CFG = json.load(cfgf)

    print("# VERBOSE ", VERBOSE)
    print("# EXTERNAL VERBOSE ", external.VERBOSE)

    smt_parser = pysmt.smtlib.parser.SmtLibParser()
    if opts.filename_is_original_problem:
        spec_funs = mirek.parse_file("mirek_special_functions.txt", mirek.SpecFuncPack)
        problems = mirek.parse_file(opts.filename, lambda lines: mirek.parse_problem(lines, spec_funs))

        assert len(problems) == 1, (opts.filename, "expecting a single problem in the original problem formulation")

        problem = problems[0]

        assert len(problem.header.functions) == 1, (opts.filename, problem.header.functions, "expecting a single function in the original problem formulation")

        smt_problem = problem.to_smt(negate_solutions=False)

        if 'status sat' in smt_problem:
            smt_problem = f"{smt_problem}(get-model)\n"
        else:
            smt_problem = f"{smt_problem}"

        # string to file object
        f = StringIO(smt_problem)
        script = smt_parser.get_script(f)
        solver = AllFun(opts, script)
        solver.add_original_problem(opts.filename)
    else:
        with open(opts.filename, encoding="utf8") as f:
            script = smt_parser.get_script(f)
        solver = AllFun(opts, script)
        if opts.original_problem is not None:
            solver.add_original_problem(opts.original_problem)

    sols = solver.solve()
    print("== STATS ==")
    for s in solver.stats.all():
        print("STAT:", s.descr, s.val)
    print("== END STATS ==")
    if sols is not None:
        print("== SOLVED ==")
        if not sols:
            print("== UNSAT ==")
        for s in sols:
            show("", s)
        print("== DONE ==")


if __name__ == "__main__":
    run_main()
    sys.exit(0)

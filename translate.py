#!/usr/bin/env python3
# File:  translate.py
# Author:  mikolas
# Created on:  Sat Jul 13 14:47:37 CEST 2024
# Copyright (C) 2024, Mikolas Janota
import sys

import pysmt
import sympy
from pysmt.fnode import FNode
from pysmt.shortcuts import FunctionType, Symbol
from pysmt.typing import REAL
from pysmt.walkers.dag import DagWalker
from sympy import sympify


class TranslateAllFunException(Exception):
    """exception"""


def check(condition, message):
    """throw an exception if condition not verified"""
    if not condition:
        raise TranslateAllFunException(message)


class SymipfyWalker(DagWalker):
    """walker to sympify"""

    def __init__(self, symbols, env=None, invalidate_memoization=None):
        DagWalker.__init__(self, env, invalidate_memoization)
        self.symbols = symbols

    def walk_symbol(self, f, args, **kwargs):
        check(f in self.symbols, "undeclared symbol " + f.symbol_name())
        return self.symbols[f]

    def walk_times(self, _f, args, **kwargs):
        return sympy.Mul(*args)

    def walk_iff(self, f, args, **kwargs):
        check(len(args) == 2, f"{f} expects two arguments")
        return sympy.Equivalent(*args)

    def walk_or(self, _f, args, **kwargs):
        return sympy.Or(*args)

    def walk_and(self, _f, args, **kwargs):
        return sympy.And(*args)

    def walk_plus(self, _f, args, **kwargs):
        return sympy.Add(*args)

    def walk_minus(self, _f, args, **kwargs):
        check(len(args) == 2, "equals expects two arguments")
        return args[0] - args[1]

    def walk_not(self, f, args, **kwargs):
        check(len(args) == 1, f"{f} expects 1 argument")
        return sympy.Not(args[0])

    def walk_div(self, f, args, **kwargs):
        check(len(args) == 2, f"{f} expects 2 argument")
        return args[0] / args[1]

    def walk_implies(self, f, args, **kwargs):
        check(len(args) == 2, f"{f} expects 2 argument")
        return sympy.Implies(args[0], args[1])

    def walk_equals(self, _f, args, **kwargs):
        check(len(args) == 2, "equals expects two arguments")
        return sympy.Eq(args[0], args[1])

    def walk_function(self, f, args, **kwargs):
        fn = f.function_name()
        check(fn in self.symbols, "undeclared function " + fn.symbol_name())
        sfn = self.symbols[fn]
        return sfn(*args)

    def walk_real_constant(self, f, args, **kwargs):
        return sympify(str(f))

    def walk_bool_constant(self, f, args, **kwargs):
        return sympify(f.constant_value())

    def walk_le(self, f: FNode, args, **kwargs):
        check(len(args) == 2, f"{f} expects two arguments")
        return args[0] <= args[1]

    def walk_lt(self, f, args, **kwargs):
        check(len(args) == 2, f"{f} expects two arguments")
        return args[0] < args[1]


class Converter:
    """Converter between pysmt and sympy."""

    def create_copy(self):
        """creates a copy of self"""
        rv = Converter(self.env)
        rv.smt2sy_symbols.update(self.smt2sy_symbols)
        rv.sy2smt_symbols.update(self.sy2smt_symbols)
        return rv

    def __init__(self, env=None):
        if env is None:
            env = pysmt.environment.get_env()

        self.env = env
        self.smt2sy_symbols = {}
        self.sy2smt_symbols = {}
        self.smt2_walker = SymipfyWalker(self.smt2sy_symbols, env)
        self.mgr = self.env.formula_manager
        self.synumerals = {
            sympy.core.numbers.NegativeOne: self.mgr.Real(-1),
            sympy.core.numbers.One: self.mgr.Real(1.0),
            sympy.core.numbers.Zero: self.mgr.Real(0),
            sympy.core.numbers.Half: self.mgr.Div(self.mgr.Real(1), self.mgr.Real(2)),
        }
        self.sqrt = Symbol("SQRT", FunctionType(REAL, [REAL]))

    def smt2sy(self, f) -> sympy.Expr:
        """convert given SMT to sympy"""
        return self.smt2_walker.walk(f)

    def add_const(self, c):
        """add SMT constant symbol"""
        assert c not in self.smt2sy_symbols
        csy = sympy.Symbol("c" + str(c), real=True)
        self.smt2sy_symbols[c] = csy
        self.sy2smt_symbols[csy] = c
        return c

    def add_var(self, v):
        """add SMT variable symbol"""
        assert v not in self.smt2sy_symbols
        vsy = sympy.Symbol("v" + str(v), real=True)
        self.smt2sy_symbols[v] = vsy
        self.sy2smt_symbols[vsy] = v
        return v

    def add_fun(self, f):
        """Add SMT function symbol."""
        assert f not in self.smt2sy_symbols
        fsy = sympy.Function(f.symbol_name())
        self.smt2sy_symbols[f] = fsy
        self.sy2smt_symbols[fsy] = f
        return f

    def pysmt_pow(self, a: FNode, e0: sympy.Expr):
        """Attempt to convert the power operator."""
        check(e0.is_constant(), "expecting constant powers")
        check(
            not a.is_zero() or (e0.is_negative is False and e0.is_zero is False),
            "offending power of zero",
        )
        e = sympy.Rational(e0)
        if e.p == 0:
            return self.mgr.Real(1)
        if e.p > 0 and e.q == 1:
            return self.mgr.Times([a] * abs(e.p))
        if e.p < 0 and e.q == 1:
            return self.mgr.Div(self.mgr.Real(1), self.mgr.Times([a] * -e.p))
        if e.p == 1 and e.q == 2:
            return self.sqrt(a)
        check(False, f"unsupported exponent {e0}")
        return None

    def sy2smt(self, f: sympy.Expr):
        """Convert given sympy to SMT."""
        op = f.func
        args = f.args
        rec = lambda x: self.sy2smt(x)
        if op in self.synumerals:
            return self.synumerals[op]
        if op == sympy.Mul:
            return self.mgr.Times([rec(a) for a in args])
        if op == sympy.Add:
            return self.mgr.Plus([rec(a) for a in args])
        if op == sympy.Rational:
            return self.mgr.Div(self.mgr.Real(f.p), self.mgr.Real(f.q))
        if op == sympy.Float:
            return rec(sympy.Rational(f))
        if op == sympy.core.numbers.Integer:
            return self.mgr.Real(int(f))
        if op == sympy.core.power.Pow:
            assert len(args) == 2
            return self.pysmt_pow(rec(args[0]), args[1])
        if op == sympy.Symbol:
            check(
                f in self.sy2smt_symbols,
                f"unknown sympy symbol '{f}'",
            )
            return self.sy2smt_symbols[f]
        if op in self.sy2smt_symbols:  # let's assume it's function application
            return self.mgr.Function(self.sy2smt_symbols[op], [rec(a) for a in args])
        if op == sympy.logic.boolalg.BooleanTrue:
            return self.mgr.TRUE()
        if op == sympy.logic.boolalg.BooleanFalse:
            return self.mgr.FALSE()
        if op == sympy.logic.boolalg.Or:
            return self.mgr.Or([rec(a) for a in args])
        if op == sympy.logic.boolalg.And:
            return self.mgr.And([rec(a) for a in args])
        if op == sympy.logic.boolalg.Not:
            assert len(args) == 1
            return self.mgr.Not(rec(args[0]))
        if op == sympy.logic.boolalg.Implies:
            assert len(args) == 2
            return self.mgr.Implies(rec(args[0]), rec(args[1]))
        if op == sympy.core.relational.Unequality:
            assert len(args) == 2
            return self.mgr.Not(self.mgr.Equals(rec(args[0]), rec(args[1])))
        if isinstance(f, sympy.core.relational.Relational):
            tr = {
                sympy.core.relational.Equality: self.mgr.Equals,
                sympy.core.relational.GreaterThan: self.mgr.GE,
                sympy.core.relational.StrictGreaterThan: self.mgr.GT,
                sympy.core.relational.LessThan: self.mgr.LE,
                sympy.core.relational.StrictLessThan: self.mgr.LT,
            }
            assert len(args) == 2
            return tr[op](rec(args[0]), rec(args[1]))

        check(False, "unknown operator '" + str(f) + "' " + str(op))


def run_main():
    """For testing purposes only."""
    f = Symbol("f", FunctionType(REAL, [REAL]))
    x = Symbol("x", REAL)
    con = Converter()
    con.add_var(x)
    con.add_fun(f)
    sx = con.smt2sy(x)
    sf = con.smt2sy(f)
    se = sympy.Eq(sf(sx), sx * 1 / 4)
    e = con.sy2smt(se)
    print(se, e)


if __name__ == "__main__":
    run_main()
    sys.exit(0)

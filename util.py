#!/usr/bin/env python3
# File:  util.py
# Author:  mikolas
# Created on:  Tue Jul 16 12:55:09 CEST 2024
# Copyright (C) 2024, Mikolas Janota
import itertools
import sys
from io import StringIO

import pysmt
import pysmt.operators as ops
import sympy
from pysmt import walkers
from pysmt.fnode import FNode
from sympy import Expr


def warning(*args, **kwargs):
    print(*args, **kwargs, file=sys.stderr, flush=True)


# Operators for which Args is an FNode
DEPENDENCIES_SIMPLE_ARGS = set(ops.ALL_TYPES) - (
    set([ops.SYMBOL, ops.FUNCTION]) | ops.QUANTIFIERS | ops.CONSTANTS
)


class ConstOracle(pysmt.walkers.DagWalker):

    def get_consts(self, formula):
        """Returns the set of consts appearing in the formula."""
        return self.walk(formula)

    @walkers.handles(DEPENDENCIES_SIMPLE_ARGS)
    def walk_simple_args(self, formula, args, **kwargs):
        # pylint: disable=unused-argument
        res = set()
        for arg in args:
            res.update(arg)
        return frozenset(res)

    def walk_symbol(self, formula, args, **kwargs):
        # pylint: disable=unused-argument
        # print("walk_symbol", formula)
        ft = formula.symbol_type()
        is_const = not ft.is_function_type() or len(ft.param_types) == 0
        return frozenset([formula]) if is_const else frozenset()

    @walkers.handles(ops.CONSTANTS)
    def walk_constant(self, formula, args, **kwargs):
        # pylint: disable=unused-argument
        return frozenset([formula])

    @walkers.handles(ops.QUANTIFIERS)
    def walk_quantifier(self, formula, args, **kwargs):
        # pylint: disable=unused-argument
        return args[0].difference(formula.quantifier_vars())

    def walk_function(self, formula: Expr, args, **kwargs):
        # pylint: disable=unused-argument
        fn = formula.function_name()
        ft = fn.symbol_type()
        assert ft.is_function_type()
        is_const = len(ft.param_types) == 0
        res = set([formula.function_name()]) if is_const else set()
        for arg in args:
            res.update(arg)
        return frozenset(res)


def get_fixed(f: Expr, vs: set[Expr]) -> set[Expr, Expr]:
    """Try to figure out that vs have a fixed value in f."""

    def is_good_rhs(rhs: Expr) -> bool:
        return rhs.is_constant() or len(rhs.atoms()) <= 1

    if f.func == sympy.And:
        rv: dict[Expr, Expr] = {}
        for op in f.args:
            rv |= get_fixed(op, vs)
        return rv
    if f.func == sympy.Eq:
        a, b = f.args
        if a in vs and is_good_rhs(b):
            return {a: b}
        if b in vs and is_good_rhs(a):
            return {b: a}
    return {}


def find_index(ls, pred):
    """Find a value satisfying a predicate, return its index and the value."""
    for i, v in enumerate(ls):
        if pred(v):
            return i, v
    return None, None


# https://docs.python.org/3/library/itertools.html
def powerset(iterable):
    "powerset([1,2,3]) → () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return itertools.chain.from_iterable(
        itertools.combinations(s, r) for r in range(len(s) + 1)
    )


def get_arguments(fla: FNode, fname):
    """Get argument of the function fname from fla."""
    # Top most
    if fla.is_function_application() and fla.function_name() == fname:
        assert len(fla.args()) == 1
        return set(fla.args())
    return set().union(*[get_arguments(x, fname) for x in fla.args()])


class SmtPrinterFix(pysmt.smtlib.printers.SmtPrinter):
    """Our own printing for SMT formulas fixing the issue of rationals not
    printing floats."""

    def __init__(self, stream, print_floats=True, annotations=None):
        super().__init__(stream, annotations)
        self.print_floats = print_floats

    def walk_real_constant(self, formula: pysmt.formula.FNode):
        c = formula.constant_value()
        template = "(- %s)" if c < 0 else "%s"

        n: int
        d: int
        n, d = abs(c.numerator), c.denominator
        if self.print_floats:
            if d != 1:
                res = template % ("(/ " + str(n) + ".0 " + str(d) + ".0)")
            else:
                res = template % (str(n) + ".0")
        else:
            if d != 1:
                res = template % ("(/ " + str(n) + str(d) + ")")
            else:
                res = template % (str(n))

        self.write(res)


class Interpret(pysmt.walkers.IdentityDagWalker):
    def __init__(self, env, f, x, body):
        pysmt.walkers.IdentityDagWalker.__init__(self, env=env)
        self.f = f
        self.x = x
        self.body = body

    def walk_function(self, formula, args, **kwargs):
        f = formula.function_name()
        if f != self.f:
            return pysmt.walkers.IdentityDagWalker.super(
                self, formula, args=args, **kwargs
            )
        assert len(args) == 1
        return self.body.substitute({self.x: args[0]})


def flatten_and(f: FNode) -> list[FNode]:
    """Returns a list of formulas corresponding to the arguments of f,
    recursively.

    If f isn't an AND, a singleton list is returned.
    """
    if not f.is_and():
        return [f]
    rv = []
    for a in f.args():
        rv += flatten_and(a)
    return rv


def to_smtlib(formula, print_floats=True):
    """Our own printing for SMT formulas fixing the issue of rationals not
    printing floats."""
    buf = StringIO()
    p = SmtPrinterFix(buf, print_floats)
    p.printer(formula)
    res = buf.getvalue()
    buf.close()
    return res


def check_add(s, e):
    """Add element e to s, return true if and only if the element was really
    added."""
    old_length = len(s)
    s.add(e)
    return len(s) > old_length

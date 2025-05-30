import itertools

from mirek_parser import Parser
from mirek_term import *


class NumType:
    def __init__(self, base="R", lbound=None, ubound=None, removed=()):
        self.base = base
        self.lbound = lbound
        self.ubound = ubound
        self.removed = removed

    def assumptions(self, term):
        assumptions = []
        if self.base == "Q":
            assumptions.append(IsRationalTerm(term))
        else:
            assert self.base == "R"
        if self.lbound is not None:
            b, strict = self.lbound
            if strict:
                op = ">"
            else:
                op = ">="
            assumptions.append(BinOpTerm(op, term, NumericTerm(b), False, True))
        if self.ubound is not None:
            b, strict = self.ubound
            if strict:
                op = "<"
            else:
                op = "<="
            assumptions.append(BinOpTerm(op, term, NumericTerm(b), False, True))
        for x in self.removed:
            assumptions.append(BinOpTerm("!=", term, NumericTerm(x), False, True))
        return assumptions


class FunType:
    def __init__(self, domain, codomain):
        assert isinstance(domain, NumType)
        assert isinstance(codomain, NumType)
        self.domain = domain
        self.codomain = codomain


def parse_type(desc):
    if "->" in desc:
        domain, codomain = desc.split("->")
        domain = parse_type(domain)
        codomain = parse_type(codomain)
        return FunType(domain, codomain)
    else:
        removed = ()
        lbound = None
        ubound = None
        if desc[0] in ("(", "[") and desc[-1] in (")", "]"):
            base = "R"
            lbound_strict = desc[0] == "("
            ubound_strict = desc[-1] == ")"
            lbound_val, ubound_val = desc[1:-1].split(",")
            if lbound_val == "-inf":
                assert lbound_strict
            else:
                lbound = int(lbound_val), lbound_strict
            if ubound_val == "inf":
                assert ubound_strict
            else:
                ubound = int(ubound_val), ubound_strict
        else:
            base = desc[0]
            assert base in ("R", "Q"), base
            if len(desc) > 1:
                if desc[1:] == "+":
                    lbound = 0, True
                elif desc[1:] == "+0":
                    lbound = 0, False
                else:
                    assert desc[1] == "-"
                    removed = tuple(map(int, desc[2:].split(",")))
        return NumType(base, lbound, ubound, removed)


class SMT:
    @staticmethod
    def reduce_and(terms):
        smt_terms = [x.to_smt() for x in terms]
        if not smt_terms:
            return None
        elif len(smt_terms) == 1:
            return smt_terms[0]
        else:
            return "(and " + " ".join(smt_terms) + ")"

    @staticmethod
    def quantify(quantifier, assump_conn, vs, ts, body):
        if not vs:
            return body
        if not all(isinstance(t, NumType) for t in ts):
            raise Exception("Cannot quantify over a type not derived from Reals")
        assumptions = itertools.chain.from_iterable(
            t.assumptions(v) for v, t in zip(vs, ts)
        )
        assumption = SMT.reduce_and(assumptions)
        if assumption is not None:
            body = f"({assump_conn} {assumption} {body})"
        smt_typing = " ".join(f"({v.name} Real)" for v in vs)
        return f"({quantifier} ({smt_typing}) {body})"

    @staticmethod
    def forall(vs, ts, body):
        return SMT.quantify("forall", "=>", vs, ts, body)

    @staticmethod
    def exists(vs, ts, body):
        return SMT.quantify("exists", "and", vs, ts, body)

    @staticmethod  # forall x:domain. f(x) in codomain
    def codomain_constraint(f, t):
        assert f != "x"
        if not isinstance(t.codomain, NumType):
            raise Exception(f"Only real-based codomains are supported")
        x = VariableTerm("x")
        body = SMT.reduce_and(t.codomain.assumptions(FunAppTerm(f, x)))
        if body is None:
            return None
        res = SMT.forall([x], [t.domain], body)
        return res

    @staticmethod  # forall x,y:domain. in_rel(x,y) => out_rel(f(x),f(y))
    def compatibility_constraint(f, t, in_rel, out_rel):
        assert f not in ("x", "y")
        res = f"(=> ({in_rel} x y) ({out_rel} ({f} x) ({f} y)))"
        res = SMT.forall(
            [VariableTerm("x"), VariableTerm("y")], [t.domain, t.domain], res
        )
        return res

    @staticmethod  # forall y:codomain. exists x. f(x) = y
    def surjective_constraint(f, t):
        assert f not in ("x", "y")
        res = f"(= ({f} x) y)"
        res = SMT.exists([VariableTerm("x")], [t.domain], res)
        res = SMT.forall([VariableTerm("y")], [t.codomain], res)
        return res

    @staticmethod  # exists y:Real. forall x:domain. -b <= f(x) <= b
    def bounded_constraint(f, t):
        assert f not in ("x", "y")
        res = f"(<= (- y) ({f} x) y)"
        res = SMT.forall([VariableTerm("x")], [t.domain], res)
        res = SMT.exists([VariableTerm("y")], [NumType()], res)
        return res

    @staticmethod
    def finitely_many_roots_constraint(f, t):
        assert f not in ("x", "roots", "roots_bound")
        x = VariableTerm("x")
        res = f"(=> (= ({f} x) 0.0) (exists ((k Int)) (and (<= 0 k roots_bound) (= x (roots k)))))"
        res = SMT.exists([x], [t.domain], res)
        return res

    @staticmethod
    def attr_constraint(f, t, attr):
        if attr == "INJECTIVE":
            return SMT.compatibility_constraint(f, t, "distinct", "distinct")
        elif attr == "INCREASING":
            return SMT.compatibility_constraint(f, t, "<", "<")
        elif attr == "DECREASING":
            return SMT.compatibility_constraint(f, t, "<", ">")
        elif attr == "NONINCREASING":
            return SMT.compatibility_constraint(f, t, "<", ">=")
        elif attr == "NONDECREASING":
            return SMT.compatibility_constraint(f, t, "<", "<=")
        elif attr == "MONOTONIC":
            inc = SMT.compatibility_constraint(f, t, "<", "<=")
            dec = SMT.compatibility_constraint(f, t, "<", ">=")
            return f"(or {inc} {dec})"
        elif attr == "SURJECTIVE":
            return SMT.surjective_constraint(f, t)
        elif attr == "BOUNDED":
            return SMT.bounded_constraint(f, t)
        elif attr == "FINITELY_MANY_ROOTS":
            return SMT.finitely_many_roots_constraint(f, t)
        else:
            raise Exception(f"Unexpected constraint: '{attr}'")


class Header:
    def __init__(self):
        self.functions = []
        self.constants = []
        self.variables = []

    def add_variable(self, v, t):
        assert isinstance(v, VariableTerm)
        assert isinstance(t, NumType)
        self.variables.append((v, t))

    def add_constant(self, c, t):
        assert isinstance(c, ConstantTerm)
        assert isinstance(t, NumType)
        self.constants.append((c, t))

    def add_function(self, f, t, attrs):
        assert isinstance(f, str)
        assert isinstance(t, FunType)
        self.functions.append((f, t, attrs))

    def add_to_parser(self, parser, skip_vars=False):
        for f, _, _ in self.functions:
            parser.add_function(f)
        for c, _ in self.constants:
            parser.add_constant(c)
        if not skip_vars:
            for v, _ in self.variables:
                parser.add_constant(v)

    def get_parser(self):
        parser = Parser()
        self.add_to_parser(parser)
        return parser

    def __add__(self, other):
        res = Header()
        res.functions = self.functions + other.functions
        res.constants = self.constants + other.constants
        res.variables = self.variables + other.variables
        return res

    def to_smt(self):
        res = []
        if any("FINITELY_MANY_ROOTS" in attrs for f, t, attrs in self.functions):
            res.append("(declare-fun roots (Int) Real)")
            res.append("(declare-const roots_bound Int)")
        for c, t in self.constants:
            res.append(f"(declare-const {c.name} Real)")
            for assump in t.assumptions(c):
                res.append(f"(assert {assump.to_smt()})")
        for f, t, attrs in self.functions:
            res.append(f"(declare-fun {f} (Real) Real)")
            assump = SMT.codomain_constraint(f, t)
            if assump is not None:
                res.append(f"(assert {assump})")
            for attr in attrs:
                res.append(f"(assert {SMT.attr_constraint(f,t,attr)}) ; {attr.lower()}")
        return res

    def smt_forall_closure(self, constraint):
        vs_names = set(v.name for v in constraint.variables())
        ts = []
        vs = []
        for v, t in self.variables:
            if v.name in vs_names:
                vs.append(v)
                ts.append(t)
                vs_names.remove(v.name)
        assert not vs_names
        return SMT.forall(vs, ts, constraint.to_smt())


class SpecFuncPack:
    def __init__(self, lines):
        self.header = Header()
        self.constraints = []
        self.has_power = False
        for line in lines:
            if " " in line:
                cmd, content = line.split(" ", 1)
            else:
                cmd, content = line, ""
            if cmd == "DECLARE_POWER":
                self.has_power = True
                assert not content
            elif cmd in ("ALL", "DECLARE"):
                name, t = content.split(":")
                t = parse_type(t)
                if cmd == "ALL":
                    assert isinstance(t, NumType)
                    self.header.add_variable(VariableTerm(name), t)
                else:
                    if isinstance(t, NumType):
                        self.header.add_constant(ConstantTerm(name), t)
                    else:
                        self.header.add_function(name, t, ())
            else:
                parser = self.header.get_parser()
                constraint = parser(line)
                assert not constraint.is_num, constraint
                self.constraints.append(constraint)

    def has_used_name(self, names):
        return (
            any(f in names for f, t, _ in self.header.functions)
            or any(c.name in names for c, t in self.header.constants)
            or self.has_power
            and "^" in names
        )

    def to_smt(self):
        res = []
        if self.has_power:
            res.append("(declare-fun power (Real Real) Real)")
        res.extend(self.header.to_smt())
        res.extend(
            f"(assert {self.header.smt_forall_closure(constraint)})"
            for constraint in self.constraints
        )
        return res

    @staticmethod
    def get_parser(spec_funs):
        parser = Parser()
        for pack in spec_funs:
            pack.header.add_to_parser(parser, skip_vars=True)
        return parser

    @staticmethod
    def used_to_smt(spec_funs, terms):
        names = set()
        for term in terms:
            for subterm in term.subterms_rec():
                if isinstance(subterm, FunAppTerm):
                    names.add(subterm.f)
                elif isinstance(subterm, ConstantTerm):
                    names.add(subterm.name)
                elif isinstance(subterm, BinOpTerm) and subterm.op == "^":
                    names.add("^")
        res = []
        for pack in spec_funs:
            if pack.has_used_name(names):
                res.extend(pack.to_smt())
        if not res:
            return ""
        else:
            return "; Special functions\n" + "\n".join(res) + "\n\n"


class Problem:
    def __init__(self, title, header, constraints, spec_funs):
        self.title = title
        self.header = header
        self.constraints = constraints
        self.spec_funs = spec_funs

    def base_to_smt(self, sat=False, terms_from_solutions=True):
        if sat:
            status = "sat"
        else:
            status = "unsat"
        vejtek_sources = []
        ori_sources = []
        for name in self.title:
            if name[0] in ("U", "C") and name[1:].isnumeric():
                if name[0] == "U":
                    cz = "Úloha"
                elif name[0] == "C":
                    cz = "Cvičení"
                vejtek_sources.append(cz + " " + name[1:])
            else:
                ori_sources.append(name)
        sources = []
        if vejtek_sources:
            sources.append("Problem number: " + ", ".join(vejtek_sources) + "\n")
        if ori_sources:
            sources.append("Original source: " + ", ".join(ori_sources) + "\n")
        sources = "".join(sources)
        smt_header = f"""(set-info :smt-lib-version 2.6)
(set-logic AUFNIRA)
(set-info :source |
Generated by: Mirek Olšák, Mikoláš Janota, Chad E. Brown
Generated on: 2024-04-14
Application: Mathematics challenges involving function synthesis
From a collection by: Vít Musil
Source url: https://prase.cz/library/FunkcionalniRovniceVM/FunkcionalniRovniceVM.pdf
{sources}|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "crafted")
(set-info :status {status})
"""

        header = "; Header\n" + "\n".join(self.header.to_smt())
        if terms_from_solutions:
            terms = self.constraints + self.get_extra_terms()
        else:
            terms = self.constraints
        spec_funs = SpecFuncPack.used_to_smt(self.spec_funs, terms)
        constraints = "\n".join(
            f"(assert {self.header.smt_forall_closure(constraint)})"
            for constraint in self.constraints
        )
        return f"{smt_header}\n{spec_funs}{header}\n\n; Equations\n{constraints}"


class FindProblem(Problem):
    def __init__(
        self,
        title,
        header,
        constraints,
        spec_funs,
        functions_to_find,
        solutions,
        find_one,
    ):
        super().__init__(title, header, constraints, spec_funs)
        self.functions_to_find = functions_to_find
        self.solutions = solutions
        self.find_one = find_one

    def get_extra_terms(self):
        if self.solutions is None:
            return []
        else:
            return list(
                itertools.chain.from_iterable(
                    constraints for header, constraints in self.solutions
                )
            )

    def to_smt(self, negate_solutions=True):
        base = self.base_to_smt(sat=not negate_solutions, terms_from_solutions=negate_solutions)
        if self.find_one:
            find_task = "; Find an example of " + " ".join(self.functions_to_find)
        else:
            find_task = "; Find all possible " + " ".join(self.functions_to_find)

        if not negate_solutions:
            if self.solutions is None or len(self.solutions) > 0:
                return base + "\n\n" + find_task + "\n\n(check-sat)\n(exit)\n"
            else:
                # Create an SMT even if there are no solutions
                assert self.solutions == []
                base = self.base_to_smt(sat=False, terms_from_solutions=negate_solutions)
                return base + "\n\n" + find_task + "\n\n(check-sat)\n(exit)\n"

        if self.solutions is None:
            solutions = "; Solutions Unknown"
        elif not self.solutions:
            solutions = "; No Solutions"
        else:
            solutions = ["; Solutions"]
            for header, constraints in self.solutions:
                full_header = self.header + header
                constraints = [
                    full_header.smt_forall_closure(constraint)
                    for constraint in constraints
                ]
                if not constraints:
                    raise Exception("Solution with no equations")
                if len(constraints) == 1:
                    [solution] = constraints
                else:
                    solution = (
                        "(and\n"
                        + "\n".join("  " + constraint for constraint in constraints)
                        + ")"
                    )
                if header.constants:
                    vs, ts = zip(*header.constants)
                    solution = SMT.exists(vs, ts, solution)
                solution = f"(assert (not {solution}))"
                solutions.append(solution)
            solutions = "\n\n".join(solutions)

        return (
            base + "\n\n" + find_task + "\n\n" + solutions + "\n\n(check-sat)\n(exit)\n"
        )


class ProveProblem(Problem):
    def __init__(self, title, header, constraints, spec_funs, goal):
        super().__init__(title, header, constraints, spec_funs)
        self.goal = goal

    def get_extra_terms(self):
        return [self.goal]

    def to_smt(self):
        base = self.base_to_smt()
        goal = f"; Negated Goal\n(assert (not {self.header.smt_forall_closure(self.goal)}))"
        return base + "\n\n" + goal + "\n\n(check-sat)\n(exit)\n"


class CheckSolProblem(Problem):
    def __init__(self, find_problem, index):
        self.find_problem = find_problem
        self.solution_index = index

        solution_header, solution_constraints = find_problem.solutions[index]
        header = find_problem.header + solution_header
        self.target_constraints = []
        for i, (f, t, attrs) in enumerate(header.functions):
            constraint = SMT.codomain_constraint(f, t)
            if constraint is not None:
                self.target_constraints.append(constraint)
            for attr in attrs:
                if attr == "FINITELY_MANY_ROOTS":
                    continue
                self.target_constraints.append(SMT.attr_constraint(f, t, attr))
            # neutralize constraints
            header.functions[i] = f, FunType(NumType("R"), NumType("R")), ()

        solution_constraints = list(solution_constraints)
        for constraint in find_problem.constraints:
            fs = set(find_problem.functions_to_find)
            used = constraint.used_constants()
            if fs & used:
                self.target_constraints.append(header.smt_forall_closure(constraint))
            else:
                solution_constraints.append(constraint)

        super().__init__(
            find_problem.title, header, solution_constraints, find_problem.spec_funs
        )

    def to_smt(self):
        base = self.base_to_smt()
        res = [base, ""]

        res.append("; Negated constraints")
        add_and = (" (and", ")") if len(self.target_constraints) > 1 else ("", "")
        res.append("(assert (not" + add_and[0])
        for constraint in self.target_constraints:
            res.append("  " + constraint)
        res.append("))" + add_and[1])
        res.append("")
        res.append("(check-sat)")
        res.append("(exit)")
        res.append("")
        return "\n".join(res)

    def get_extra_terms(self):
        return self.find_problem.constraints


def parse_problem(lines, spec_funs):
    title = None
    header = Header()
    constraints = []
    sol_header = Header()
    sol_mode = False
    solutions = None
    goal = None
    functions_to_find = []
    find_one = False

    def get_parser():
        parser = SpecFuncPack.get_parser(spec_funs)
        header.add_to_parser(parser)
        sol_header.add_to_parser(parser)
        return parser

    for line in lines:
        try:
            if " " in line:
                cmd, content = line.split(" ", 1)
            else:
                cmd, content = line, ""
            if cmd == "TITLE":
                assert title is None
                title = content.split()
                continue
            elif cmd in ("GIVEN", "FIND", "FIND1", "ALL"):
                if cmd == "FIND1":
                    cmd = "FIND"
                    find_one = True
                content = content.split()
                name, t = content[0].split(":")
                t = parse_type(t)
                if cmd == "FIND":
                    functions_to_find.append(name)
                    cmd = "GIVEN"
                attrs = content[1:]

                if sol_mode:
                    cur_header = sol_header
                else:
                    cur_header = header

                if cmd == "ALL":
                    assert isinstance(t, NumType)
                    assert not attrs
                    cur_header.add_variable(VariableTerm(name), t)
                else:
                    assert cmd == "GIVEN"
                    if isinstance(t, NumType):
                        assert not attrs
                        cur_header.add_constant(ConstantTerm(name), t)
                    else:
                        assert not sol_mode
                        cur_header.add_function(name, t, attrs)

            elif cmd == "PROVE":
                assert goal is None
                assert not sol_mode
                parser = get_parser()
                goal = parser(content)
                assert not goal.is_num, goal
            elif cmd == "SOLUTION:":
                assert not content
                if sol_mode:
                    solutions.append((sol_header, sol_constraints))
                else:
                    assert solutions is None
                    solutions = []
                sol_header = Header()
                sol_constraints = []
                sol_mode = True
            elif cmd == "NO_SOLUTION":
                solutions = []
            else:  # no command, just a constraint
                parser = get_parser()
                constraint = parser(line)
                assert not constraint.is_num, constraint
                if sol_mode:
                    sol_constraints.append(constraint)
                else:
                    constraints.append(constraint)
        except:
            print("--->", line)
            raise

    if sol_mode:
        solutions.append((sol_header, sol_constraints))

    assert bool(functions_to_find) == (
        goal is None
    ), f"functions_to_find: {functions_to_find}, goal: {goal}"
    if functions_to_find:
        return FindProblem(
            title,
            header,
            constraints,
            spec_funs,
            functions_to_find,
            solutions,
            find_one=find_one,
        )
    else:
        return ProveProblem(title, header, constraints, spec_funs, goal)


def parse_file(fname, block_export):
    problems = []
    start = None
    lines = []
    with open(fname) as f:
        for line_i, line in enumerate(f):
            line = line.strip()
            line_i = line_i + 1
            if line.startswith("#"):
                continue
            if line == "":
                if start is None:
                    continue
                else:
                    try:
                        problem = block_export(lines)
                        problems.append(problem)
                    except:
                        print(f"Error on lines: {start} -- {line_i-1}")
                        raise
                    start = None
                    lines = []
            else:
                if start is None:
                    start = line_i
                lines.append(line)
        if start is not None:
            try:
                problem = block_export(lines)
                problems.append(problem)
            except:
                print(f"Error on lines: {start} -- {line_i-1}")
                raise

    return problems

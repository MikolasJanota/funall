import pysmt.shortcuts as ps
from translate import check


class Term:
    def __repr__(self):
        return f"Term({str(self)})"

    def subterms(self):
        return ()

    def subterms_rec(self):
        res = set()
        self.collect_subterms_rec(res)
        return res

    def collect_subterms_rec(self, out):
        out.add(self)
        for subterm in self.subterms():
            subterm.collect_subterms_rec(out)

    def variables(self):
        return set(filter(lambda x: isinstance(x, VariableTerm), self.subterms_rec()))

    def used_constants(self):
        res = set()
        for term in self.subterms_rec():
            if isinstance(term, FunAppTerm):
                res.add(term.f)
            elif isinstance(term, ConstantTerm):
                res.add(term.name)
        return res


class IsRationalTerm(Term):
    def __init__(self, q):
        assert q.is_num
        self.q = q
        self.is_num = False

    def to_smt(self):
        return f"(exists ((numerator Int) (denominator Int)) (and (distinct denominator 0) (= (/ (to_real numerator) (to_real denominator)) {self.q.to_smt()})))"

    def subterms(self):
        return (self.q,)


class UMinusTerm(Term):
    def __init__(self, body: Term):
        assert body.is_num, body
        self.body = body
        self.is_num = True

    def __str__(self):
        return "-" + str(self.body)

    def subterms(self):
        return (self.body,)

    def to_smt(self):
        return f"(- {self.body.to_smt()})"

    def to_pysmt(self):
        return -self.body.to_pysmt()


class NumericTerm(Term):
    def __init__(self, n: int):
        self.n = n
        self.is_num = True

    def __str__(self):
        return str(self.n)

    def to_smt(self):
        if self.n >= 0:
            return str(float(self.n))
        else:
            return f"(- {float(-self.n)})"

    def to_pysmt(self):
        return ps.Real(self.n)


class ConstantTerm(Term):
    def __init__(self, name: str, is_num: bool = True):
        self.name = name
        self.is_num = is_num

    def __str__(self):
        return self.name

    def to_smt(self):
        return self.name

    def to_pysmt(self):
        return ps.Symbol(self.name, ps.REAL)


class VariableTerm(Term):
    def __init__(self, name: str, is_num: bool = True):
        self.name = name
        self.is_num = is_num

    def __str__(self):
        return self.name

    def to_smt(self):
        return self.name

    def to_pysmt(self):
        return ps.Symbol(self.name, ps.REAL)


class FunAppTerm(Term):
    def __init__(self, f: str, arg: Term, is_num: bool = True, arg_is_num: bool = True):
        assert arg.is_num == arg_is_num, (arg, arg_is_num)
        self.f = f
        self.arg = arg
        self.is_num = is_num

    def __str__(self):
        return f"{self.f}({self.arg})"

    def subterms(self):
        return (self.arg,)

    def to_smt(self):
        if self.f == "floor":
            return f"(to_real (to_int {self.arg.to_smt()}))"
        else:
            return f"({self.f} {self.arg.to_smt()})"


class BinOpTerm(Term):
    def __init__(self, op: str, arg1: Term, arg2: Term, is_num: bool, arg_is_num: bool):
        assert arg1.is_num == arg_is_num, (op, arg1, arg_is_num)
        assert arg2.is_num == arg_is_num, (op, arg2, arg_is_num)
        self.op = op
        self.arg1 = arg1
        self.arg2 = arg2
        self.is_num = is_num

    def __str__(self):
        return f"({self.arg1} {self.op} {self.arg2})"

    def subterms(self):
        return (self.arg1, self.arg2)

    def to_smt(self):
        if self.op == "||":
            smt_op = "or"
        elif self.op == "&&":
            smt_op = "and"
        elif self.op == "!=":
            smt_op = "distinct"
        elif self.op == "^":
            smt_op = "power"
        else:
            smt_op = self.op
        return f"({smt_op} {self.arg1.to_smt()} {self.arg2.to_smt()})"

    def to_pysmt(self):
        opm = {
            "+": ps.Plus,
            "-": ps.Minus,
            "*": ps.Times,
            "/": ps.Div,
            "||": ps.Or,
            "&&": ps.And,
            "!=": ps.AllDifferent,
            ">=": ps.GE,
            ">": ps.GT,
            "<": ps.LT,
            "<=": ps.LE,
            "=>": ps.Implies,
            "=": ps.Equals,
        }
        check(self.op in opm, f"unknown operator '{self.op}'")
        smt_op = opm[self.op]
        return smt_op(self.arg1.to_pysmt(), self.arg2.to_pysmt())


class NatPowerTerm(Term):
    def __init__(self, base: Term, power: int):
        assert base.is_num, base
        self.base = base
        self.power = power
        assert power >= 2
        self.is_num = True

    def __str__(self):
        return f"{self.base}^{self.power}"

    def subterms(self):
        return (self.base,)

    def to_smt(self):
        base = self.base.to_smt()
        return "(* " + " ".join([base] * self.power) + ")"

from icecream import ic
from mirek_term import *


class Token:
    def __init__(self, line, start, end):
        assert end <= len(line)
        self.s = line[start:end]
        self.line = line
        self.start = start
        self.end = end

    @property
    def in_line(self):
        return self.line + "\n" + " " * self.start + "^" * (self.end - self.start)

    def __str__(self):
        return self.s

    def __repr__(self):
        return f"Token({self.s}"


def lexer(available_tokens, line):
    res = []
    i = 0
    while i < len(line):
        if line[i].isspace():
            i += 1
        elif line[i].isdecimal():
            j = i + 1
            while j < len(line) and line[j].isdigit():
                j += 1
            res.append(Token(line, i, j))
            i = j
        else:
            for t in available_tokens:
                if line[i : i + len(t)] == t:
                    res.append(Token(line, i, i + len(t)))
                    i += len(t)
                    break
            else:
                print(Token(line, i, i + 1).in_line)
                raise Exception("Lexer Error: unknown character")
    return res


class Parser:
    def __init__(self):
        self.const_to_term = dict()
        self.functions = set()
        self.operators = dict()

        self.add_constant(ConstantTerm("false", is_num=False))
        self.add_function("floor")
        # self.add_constant(ConstantTerm('pi'))
        # self.add_function("abs")
        # self.add_function("sqrt")
        # self.add_function("log")
        # self.add_function("exp")
        # self.add_function("sin")
        # self.add_function("cos")

        self.add_operator("=>", 0, False, False)

        self.add_operator("&&", 1, False, False)
        self.add_operator("||", 1, False, False)

        self.add_operator("=", 2, False)
        self.add_operator("!=", 2, False)
        self.add_operator("<=", 2, False)
        self.add_operator(">=", 2, False)
        self.add_operator("<", 2, False)
        self.add_operator(">", 2, False)

        self.add_operator("+", 3)
        self.add_operator("-", 3)

        self.add_operator("/", 4)
        self.add_operator("*", 4)

        self.add_operator("^", 5)

        self.max_precedence = self.operators["^"][0] + 1

    @property
    def available_tokens(self):
        res = {"(", ")"}
        res.update(self.const_to_term.keys())
        res.update(self.operators.keys())
        res.update(self.functions)
        res = list(res)
        res.sort(key=len, reverse=True)
        return res

    def add_constant(self, c):
        assert c.name not in self.const_to_term, c
        assert c.name not in self.functions, c
        assert c.name not in self.operators, c
        self.const_to_term[c.name] = c

    def add_function(self, f):
        assert f not in self.const_to_term, f
        assert f not in self.functions, f
        assert f not in self.operators, f
        self.functions.add(f)

    def add_operator(self, symbol, precedence, is_num=True, arg_is_num=True):
        assert isinstance(
            precedence, int
        ), f"Precedence must be an integer, got {precedence}"
        assert symbol not in self.const_to_term
        assert symbol not in self.functions
        assert symbol not in self.operators
        self.operators[symbol] = precedence, is_num, arg_is_num

    def __call__(self, line):
        tokens = lexer(self.available_tokens, line)
        if not tokens:
            raise Exception(f"No token in line: '{line}'")
        i, res = self._parse_tokens(tokens=tokens, index=0, precedence=0)
        if i != len(tokens):
            print(tokens[i].in_line)
            raise Exception("Premature end of parsing")
        return res

    def _require_token(self, tokens, index, token):
        if index >= len(tokens):
            print(tokens[-1].in_line)
            raise Exception(f"End of tokens, expected: '{token}'")
        if tokens[index].s != token:
            print(tokens[index].in_line)
            raise Exception(f"Wrong token, expected: '{token}'")

    def _parse_tokens(self, tokens, index, precedence):
        s = tokens[index].s

        # first term

        last_prec = self.max_precedence
        if s == "(":
            index, res = self._parse_tokens(tokens, index + 1, 0)
            self._require_token(tokens, index, ")")
            index += 1
        elif s == "-":  # unary minus
            last_prec = self.operators[s][0]
            index, res = self._parse_tokens(
                tokens, index + 1, max(precedence, last_prec + 1)
            )
            res = UMinusTerm(res)
        elif s.isdecimal():
            res = NumericTerm(int(s))
            index += 1
        elif s in self.const_to_term:
            res = self.const_to_term[s]
            index += 1
        elif s in self.functions:
            index += 1
            self._require_token(tokens, index, "(")
            index, res = self._parse_tokens(tokens, index + 1, 0)
            self._require_token(tokens, index, ")")
            index += 1
            res = FunAppTerm(s, res)
        else:
            print(tokens[index].in_line)
            raise Exception(f"Expecting start of a term, got '{s}'")

        # adding operators

        while True:
            if index == len(tokens) or tokens[index].s == ")":
                break
            op = tokens[index].s
            if op not in self.operators:
                op = "*"
                index2 = index
            else:
                index2 = index + 1
            last_prec, is_num, arg_is_num = self.operators[op]
            if last_prec < precedence:
                break
            if op == "^" and index2 < len(tokens) and tokens[index2].s.isdecimal():
                power = int(tokens[index2].s)
                index = index2 + 1
                res = NatPowerTerm(res, power)
            else:
                index, res2 = self._parse_tokens(
                    tokens, index2, max(precedence, last_prec + 1)
                )
                res = BinOpTerm(op, res, res2, is_num, arg_is_num)

        return index, res


if __name__ == "__main__":
    parser = Parser()
    parser.add_constant(ConstantTerm("x"))
    parser.add_constant(ConstantTerm("y"))
    print(parser("x^2y^2"))

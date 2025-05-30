#!/usr/bin/env python3

"""Communication with external solvers."""
# File:  external.py
# Author:  mikolas
# Created on:  Sun Jul 14 10:21:54 CEST 2024
# Copyright (C) 2024, Mikolas Janota

import io
import json
import sys
import tempfile
from multiprocessing import Manager, Process
from subprocess import PIPE, Popen

import psutil
import pysmt
import pysmt.smtlib.commands as smtcmd
from pysmt.fnode import FNode
from pysmt.shortcuts import And, Equals, Exists, ForAll, FunctionType, Not, Symbol
from pysmt.typing import REAL

import translate
from util import flatten_and, to_smtlib

CFG = {}
VERBOSE = 1


def showl(lev, message, formula: FNode):
    """Show message with a formula."""
    if not lev <= VERBOSE:
        return
    print(message, formula.to_smtlib(daggify=False), flush=True)


class ExternalAllFunException(Exception):
    """exception."""


def log(lev, *args, **kwargs):
    """Like print, but only if lev > VERBOSE."""
    if not lev <= VERBOSE:
        return
    print(*args, **kwargs, flush=True)


def check(condition, message):
    """Throw an exception if condition not verified."""
    if not condition:
        raise ExternalAllFunException(message)


def show(message, formula: FNode):
    """Show message with a formula."""
    print(message, formula.serialize(), flush=True)


def make_query(
    flas: list[FNode], con: translate.Converter | None, print_floats=True
) -> str:
    """Create an SMT query based on the given formulas."""
    free = set().union(*[f.get_free_variables() for f in flas])
    header = ["(set-logic AUFNIRA)"] + [
        f"(declare-fun {s} {s.symbol_type().as_smtlib()})" for s in free
    ]

    if con is not None and con.sqrt in free:
        log(2, "adding axioms for sqrt")
        sq = con.sqrt.symbol_name()
        header.append(
            f"(assert (forall ((x Real)) (=> (>= x 0.0) (= (* ({sq} x) ({sq} x)) x))))"
        )

    lines = (
        header
        + [f"(assert {to_smtlib(fla, print_floats)})" for fla in flas]
        + ["(check-sat)"]
        + ["(exit)"]
    )
    rv = "\n".join(lines)
    log(3, f"smt query\n{rv}")
    return rv


def portfolio_solve(f: FNode, con):
    """Solve by a portfolio mode.

    Result is True, False or None.
    """
    run_parallel = int(CFG.get("parallel", 0)) > 0
    return call_parallel(f, con) if run_parallel else call_sequential(f, con)


def call_tarski(flas: list[FNode]):
    """Tarski tool for QE."""
    solver_id = "tarski"
    check(solver_id in CFG, f"full path of {solver_id} needs to be in config.json")
    tarski = CFG[solver_id]
    log(1, "tarski")
    smt2 = make_query(flas, None, print_floats=False)
    log(2, "tarski on ==", smt2, "============", sep="\n")
    params = [tarski]
    with tempfile.NamedTemporaryFile(delete=False) as fp_in:
        with tempfile.NamedTemporaryFile(delete=False) as fp_out:
            fp_in.write(smt2.encode())
            fp_in.close()  # the file is closed, but not removed
            tarski_input = (
                f'(def F0 (smtlib-load "{fp_in.name}"))\n'
                f"(def F1 (make-prenex F0))\n"
                f"(def F2 (dnf F1))\n"
                f'(smtlib-store (qepcad-qe F2) "{fp_out.name}")'
            )
            log(2, "tarski in ==", tarski_input, "============", sep="\n")
            with Popen(params, stdout=PIPE, stdin=PIPE, stderr=PIPE, text=True) as p:
                stdout_data, stderr_data = p.communicate(input=tarski_input)
                ec = p.returncode
            log(1, f"tarksi ec {ec}")
            if ec != 0:
                print(f"tarksi ec {ec}\n{stdout_data}\n{stderr_data}", file=sys.stderr)
                return None

            if VERBOSE > 2:
                outlines = stdout_data.splitlines()
                errlines = stderr_data.splitlines()
                log(2, f"{solver_id} stdout")
                for ol in outlines:
                    log(2, " ", ol)
                log(2, f"{solver_id} stderr\n")
                for el in errlines:
                    log(2, " ", el)
            with open(fp_out.name, mode="rb") as outf:
                t_out = outf.read().decode()
                log(2, "== qe tarksi\n" + t_out + "\n==")
    parser = pysmt.smtlib.parser.SmtLibParser()
    script = parser.get_script(io.StringIO(t_out))
    log(2, script)
    if not script.contains_command(smtcmd.CHECK_SAT):
        print(
            "tarksi's SMT didn't contain check-sat",
            file=sys.stderr,
        )
        return None
    qe = script.get_last_formula()
    log(1, qe, qe.get_free_variables())
    return qe


def call_sequential(f: FNode, con: translate.Converter):
    """Run a sequential portfolio of solvers with increasing timeout."""
    showl(2, "call:", f)
    smt2 = make_query([f], con)
    to = 2000  # cvc5 timeout
    log(2, smt2)
    for _ in range(4):
        for strategy in [
            ["--enum-inst"],
            ["--no-e-matching", "--enum-inst"],
            ["--simplification=none", "--enum-inst"],
            ["--mbqi"],
            ["--no-e-matching", "--no-cbqi", "--enum-inst"],
        ]:
            rv = call_cvc5(smt2, strategy, timeout=to)
            if rv is not None:
                return rv
        rv = call_vampire(smt2, timeout=to // 1000)
        if rv is not None:
            return rv
        to = to * 2

    return None


def call_vampire(smt2: str, timeout=2000):
    """Call vampire's SMT tactic."""
    solver_id = "vampire"
    if solver_id not in CFG:
        print(f"full path of {solver_id} needs to be in config.json to run it")
        return None
    vampire = CFG[solver_id]
    params = [
        vampire,
        "-t",
        f"{timeout}",
        "--input_syntax",
        "smtlib2",
        "--mode",
        "portfolio",
        "--schedule",
        "smtcomp_2018",
        "--cores",
        "1",
    ]
    log(1, "vampire portfolio", f"TO={timeout}")
    log(2, "vampire args", " ".join(params))
    with Popen(params, stdout=PIPE, stdin=PIPE, stderr=PIPE, text=True) as p:
        stdout_data, stderr_data = p.communicate(input=smt2)
    outline = stdout_data.splitlines()

    if VERBOSE >= 2:
        for ln in outline:
            log(2, "vam", ln)
        for ln in stderr_data.splitlines():
            log(2, "vam err", ln)
    for ol in outline:
        if ol.startswith("% SZS status Satisfiable"):
            return True
        if ol.startswith("% SZS status Unsatisfiable"):
            return False
    return None


def call_z3(smt2: str, args: list[str], timeout):
    """Run one invocation of z3."""
    solver_id = "z3"
    check(solver_id in CFG, f"full path of {solver_id} needs to be in config.json")
    solver_path = CFG[solver_id]
    params = [
        solver_path,
        f"-T:{timeout}",
        "-memory:32768",
        "-smt2",
        "--in",
    ] + args
    log(1, f"{solver_id} call", args, f"TO={timeout}")
    with Popen(params, stdout=PIPE, stdin=PIPE, stderr=PIPE, text=True) as p:
        stdout_data, stderr_data = p.communicate(input=smt2)
    outline = stdout_data.splitlines()

    log(2, f"{solver_id} stdout", outline)
    log(2, f"{solver_id} stderr\n", stderr_data)
    for ol in outline:
        if ol == "sat":
            return True
        if ol == "unsat":
            return False
    return None


def call_cvc5(smt2: str, args: list[str], timeout=2000):
    """Run one invocation of cvc5."""
    solver_id = "cvc5"
    check(solver_id in CFG, f"full path of {solver_id} needs to be in config.json")
    cvc5 = CFG[solver_id]
    params = [
        cvc5,
        f"--tlimit={timeout}",
        "-Lsmtlib2.6",
        "--no-incremental",
        "--no-type-checking",
        "--no-interactive",
    ] + args
    log(1, "cvc5 strategy", args, f"TO={timeout}")
    with Popen(params, stdout=PIPE, stdin=PIPE, stderr=PIPE, text=True) as p:
        stdout_data, stderr_data = p.communicate(input=smt2)
    outline = stdout_data.splitlines()

    log(2, "cvc5 stdout", outline)
    log(2, "cvc5 stderr\n", stderr_data)
    for ol in outline:
        if ol == "sat":
            return True
        if ol == "unsat":
            return False
    return None


def call_z3_q(q, smt2: str, args: list[str], timeout):
    """Queue-wrapper for z3."""
    q.put((call_z3(smt2, args, timeout), "z3 " + ",".join(args)))


def call_cvc5_q(q, smt2: str, args: list[str], timeout=30000):
    """Queue-wrapper for cvc5."""
    q.put((call_cvc5(smt2, args, timeout), "cvc " + ",".join(args)))


def call_vampire_q(q, smt2: str, timeout=30):
    """Queue-wrapper for vampire."""
    q.put((call_vampire(smt2, timeout), "vampire"))


def parallel_portfolio(smt2):
    """Run solvers in parallel until one solves."""
    strs = [
        ["--enum-inst"],
        ["--no-e-matching", "--enum-inst"],
        ["--simplification=none", "--enum-inst"],
        ["--mbqi"],
        ["--no-e-matching", "--no-cbqi", "--enum-inst"],
    ]
    res = None
    key = "parallel_timeout"
    timeout = CFG.get(key, 30)
    with Manager() as manager:
        # create the shared queue
        shared_queue = manager.Queue()
        processes = (
            [
                Process(
                    target=call_cvc5_q, args=(shared_queue, smt2, args, timeout * 1000)
                )
                for args in strs
            ]
            + [Process(target=call_vampire_q, args=(shared_queue, smt2, timeout))]
            + [Process(target=call_z3_q, args=(shared_queue, smt2, [], timeout))]
        )
        # start all processes
        for process in processes:
            process.start()
        # read data from the queue
        for _ in range(len(processes)):
            # pop result from the queue
            res, solver = shared_queue.get()
            print(f"got {res} from {solver}")
            if res is not None:
                break
        for p in processes:
            try:
                for child in psutil.Process(p.pid).children(recursive=True):
                    child.terminate()
                p.terminate()
                p.join()
            except:
                pass
    return res


def call_parallel(f: FNode, con):
    """Queue-wrapper for parallel_portfolio."""
    showl(2, "call:", f)
    return parallel_portfolio(make_query(flatten_and(f), con))
    # return parallel_portfolio(make_query([f], con))


def run_main():
    """For testing purposes only."""
    global CFG
    with open("config.json", encoding="utf-8") as cfgf:
        CFG = json.load(cfgf)

    f = Symbol("f", FunctionType(REAL, [REAL]))
    x = Symbol("x", REAL)
    f = And(ForAll([x], Equals(f(x), x)), Exists([x], Not(Equals(f(x), x))))
    # assert call_str(f) is False
    assert call_parallel(f, None) is False

    a = Symbol("a", REAL)
    b = Symbol("b", REAL)
    f1 = Exists([x], And(a < x, x < b))
    call_tarski(f1)


if __name__ == "__main__":
    run_main()
    sys.exit(0)

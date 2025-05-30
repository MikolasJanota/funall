import functools
import itertools
from concurrent.futures import ThreadPoolExecutor
from subprocess import PIPE, Popen
from typing import List

import external


def check(condition, message):
    """Throw an exception if condition not verified."""
    if not condition:
        raise external.ExternalAllFunException(message)


def logprint(*args, **kwargs):
    print(*args, **kwargs, flush=True)


def call_vampire(smt2: str, timeout=5, verbose=False):
    """Call vampire's SMT tactic."""
    solver_id = "vampire"
    check(
        solver_id in external.CFG,
        f"full path of {solver_id} needs to be in config.json to run it",
    )
    vampire = external.CFG[solver_id]
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

    if verbose:
        logprint("vampire portfolio", f"TO={timeout}")
    with Popen(params, stdout=PIPE, stdin=PIPE, stderr=PIPE, text=True) as p:
        stdout_data, stderr_data = p.communicate(input=smt2)
    outline = stdout_data.splitlines()

    if verbose:
        logprint("vampire stdout", outline)
        logprint("vampire stderr\n", stderr_data)

    for ol in outline:
        if ol.startswith("% SZS status Satisfiable"):
            return True
        if ol.startswith("% SZS status Unsatisfiable"):
            return False
    return None


def call_cvc5(smt2: str, args: List[str], timeout=5000, verbose=False):
    """Run one invocation of cvc5."""
    solver_id = "cvc5"
    check(
        solver_id in external.CFG,
        f"full path of {solver_id} needs to be in config.json",
    )
    cvc5 = external.CFG[solver_id]
    params = [
        cvc5,
        f"--tlimit={timeout}",
        "-Lsmtlib2.6",
        "--no-incremental",
        "--no-type-checking",
        "--no-interactive",
    ] + args

    if verbose:
        logprint("cvc5 strategy", args, f"TO={timeout}")

    with Popen(params, stdout=PIPE, stdin=PIPE, stderr=PIPE, text=True) as p:
        stdout_data, stderr_data = p.communicate(input=smt2)
    outline = stdout_data.splitlines()

    if verbose:
        logprint("cvc5 stdout", outline)
        logprint("cvc5 stderr\n", stderr_data)

    for ol in outline:
        if ol == "sat":
            return True
        if ol == "unsat":
            return False
    return None


def get_solvers(timeout=5, verbose=False):
    solvers = [lambda x: call_vampire(x, timeout=timeout, verbose=verbose)]

    for strategy in [
        ["--enum-inst"],
        ["--no-e-matching", "--enum-inst"],
        ["--simplification=none", "--enum-inst"],
        ["--mbqi"],
        ["--no-e-matching", "--no-cbqi", "--enum-inst"],
    ]:
        solvers.append(
            functools.partial(
                call_cvc5, args=strategy, verbose=verbose, timeout=int(timeout * 1000)
            )
            # lambda x: call_cvc5(x, args=strategy, verbose=verbose, timeout=int(timeout * 1000))
        )

    return solvers


def call_cvc5_q(q, i, j, smt2, args: List[str], timeout=5000, verbose=False):
    """queue-wrapper for cvc5"""
    q.put((i, j, call_cvc5(smt2, args, timeout=timeout, verbose=verbose)))


def call_vampire_q(q, i, j, smt2: str, timeout=5, verbose=False):
    """queue-wrapper for vampire"""
    q.put((i, j, call_vampire(smt2, timeout=timeout, verbose=verbose)))


def get_solvers_q(timeout=5, verbose=False):
    solvers = [
        lambda q, i, j, x: call_vampire_q(q, i, j, x, timeout=timeout, verbose=verbose)
    ]

    for strategy in [
        ["--enum-inst"],
        ["--no-e-matching", "--enum-inst"],
        ["--simplification=none", "--enum-inst"],
        ["--mbqi"],
        ["--no-e-matching", "--no-cbqi", "--enum-inst"],
    ]:
        solvers.append(
            lambda q, i, j, x: call_cvc5_q(
                q, i, j, x, strategy, verbose=verbose, timeout=int(timeout * 1000)
            )
        )

    return solvers


def call_solver(t):
    (i, p), (j, s) = t
    return i, j, s(p)


def call_portfolio(problems, timeout=5, threads=16, only_check=False, verbose=False):
    solvers = get_solvers(timeout=timeout, verbose=verbose)

    if only_check:
        solvers = solvers[-1:]

    pairs = itertools.product(enumerate(problems), enumerate(solvers))

    with ThreadPoolExecutor(threads) as p:
        results = p.map(call_solver, pairs)
        return list(results)

# AllFun

## Installation

The tool has only been tested on Linux and MacOs. Bulk of the code is written
in python but it requires other tools (solvers) to run.

For `allfun.py` to run, `config.json` needs to exist, the script `mk_config.sh`
tries to create it using the `which` command. The config can
look like this.

The key `parallel_timeout` is the timeout, in seconds, for the parallel portfolio.
The key `parallel` runs portfolio of SMT solvers rather than sequentially.
```
{
    "parallel_timeout" : 120,
    "parallel": 1,
    "z3" : "/usr/bin/z3",
    "cvc5" : "/home/mikolas/bin/cvc5",
    "tarski" : "/home/mikolas/bin/tarski",
    "vampire" : "/home/mikolas/bin/vampire"
}
```

To prevent `tarski` from getting stuck, we also wrap it in `tarski.sh`, which
kills it after 10s, so put `pwd tarski.sh`, in `config.json` and modify
`tarski.sh` according to your location of `tarski`.

For our experiments, we used the following versions of the solvers

- Z3 version 4.12.1 - 64 bit
- cvc5 version 1.1.3-dev.72.2b4ca00c2 [git 2b4ca00c2 on branch main]
- tarski 1.37
- Vampire 4.8 (commit 8d999c135 on 2023-07-12 16:43:10 +0000) Linked with Z3 4.9.1.0 6ed071b44407cf6623b8d3c0dceb2a8fb7040cee z3-4.8.4-6427-g6ed071b44

### Python dependencies

It also requires the following Python packages: `sympy`, `pysmt`, `psutil`, and `icecream`,
which can be installed using `pip`.

```shell
pip install sympy
pip install pysmt
pip install psutil
pip install icecream
```

## Run

To solve a problem, for example, U10 run it as follows.

```shell
python allfun.py --no-nice-instantiations Musil/problem_U10.smt2 --original-problem Musil/problem_U10.txt
```

The original problem option is only important for problems that have a domain
different from reals, e.g. R+.

See `python allfun.py -h` for  more options.

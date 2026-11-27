# Formal knowledge model for AI-assisted SBOM generation

This repository holds a small, mechanically verified mathematical model of
the knowledge built up while investigating a C/C++ repository's external
components. The investigation is done by deterministic tools, an AI and
human reviewers. The model is meant as the foundation for a future SBOM
generator. **It does not include the generator.**

| Deliverable | File |
|---|---|
| 1. Mathematical domain specification | [`docs/DOMAIN.md`](docs/DOMAIN.md) |
| 2. Executable formal specification | [`spec/kmodel.py`](spec/kmodel.py) (model and mutants), [`spec/obligations.py`](spec/obligations.py) (verification obligations and witnesses), [`spec/cases.py`](spec/cases.py) (challenge cases A–E with negative controls), [`spec/run_all.py`](spec/run_all.py) (runner) |
| 3. Verification and critical-review report | [`docs/REPORT.md`](docs/REPORT.md); raw output of the last run is in [`results/verification_results.md`](results/verification_results.md) |

The specification is written as quantifier-free SMT formulas, built with the
z3 Python API over finite enumerated sorts. Every check is therefore decidable
and complete within its bound. For each obligation, a counterexample (a
concrete state) is printed whenever one exists.

## Reproducing

```bash
python3 -m pip install -r requirements.txt
```

```bash
python3 spec/run_all.py --quick
```

```bash
python3 spec/run_all.py
```

```bash
python3 spec/run_all.py --smt2 results/smt2
```

- `--quick` uses small scopes and takes about 5 minutes.
- Running with no flags uses the scopes reported in `docs/REPORT.md`. It
  takes about 8 minutes on one core.
- `--smt2 results/smt2` also writes every obligation as an SMT-LIB2 file. Each
  file is expected to return `unsat`, so the results can be cross-checked with
  another solver such as cvc5.

The runner exits with status 0 only if all three of the following hold:

- every obligation holds and every witness exists;
- every mutant (a deliberately wrong design) is rejected by at least one
  obligation;
- every challenge-case check gives its expected result.

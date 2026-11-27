#!/usr/bin/env python3
"""
Run every verification activity and write a results report.

    python3 spec/run_all.py                 # default scopes (~8 min)
    python3 spec/run_all.py --quick         # small scopes (~5 min, mutants dominate)
    python3 spec/run_all.py --smt2 out/     # also dump each obligation as SMT-LIB2

Exit status is 0 iff
  * every obligation HOLDS on the reference model and every witness is found,
  * every mutant (wrong design) violates at least one obligation,
  * every challenge-case check gives its expected result.
"""
import argparse
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from z3 import Solver, Not, get_version_string            # noqa: E402
from obligations import (OBLIGATIONS, run_obligations, witnesses,   # noqa: E402
                         check, DEFAULT_SCOPE)
from kmodel import MUTANTS                                  # noqa: E402
from cases import ALL_CASES, K_ADV                          # noqa: E402

SCOPES = {
    "quick":   dict(comps=3, attrs=2, vals=2, locs=2, hashes=2, records=4),
    "mutants": dict(comps=3, attrs=2, vals=2, locs=2, hashes=2, records=4),
    "default": DEFAULT_SCOPE,
}


def fmt_scope(sc):
    return (f"|Comp|={sc['comps']} |Attr|={sc['attrs']} |Val|={sc['vals']} "
            f"|Loc|={sc['locs']} |Hash|={sc['hashes']} records={sc['records']}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--smt2", metavar="DIR")
    ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                  "..", "results", "verification_results.md"))
    args = ap.parse_args()
    ref_scope = SCOPES["quick"] if args.quick else SCOPES["default"]
    mut_scope = SCOPES["quick"] if args.quick else SCOPES["mutants"]
    out = []
    ok_all = True
    say = lambda s="": (print(s, flush=True), out.append(s))
    T0 = time.time()

    say("# Verification results")
    say()
    say(f"z3 {get_version_string()}, python {sys.version.split()[0]}"
        f"{' (QUICK MODE)' if args.quick else ''}")
    say()

    # 1. obligations on the reference model --------------------------------
    say(f"## 1. Obligations on the reference model ({fmt_scope(ref_scope)})")
    say()
    say("| obligation | result | time |")
    say("|---|---|---|")
    res = run_obligations(frozenset(), ref_scope)
    for r in res:
        note = "" if r["scope"] == ref_scope else f" (records={r['scope']['records']})"
        say(f"| {r['name']}{note} | {r['result']} | {r['time']:.1f}s |")
        ok_all &= r["result"] == "HOLDS"
    for r in res:
        if r["cex"]:
            say(f"\nCounterexample for {r['name']}:\n```\n{r['cex']}\n```")
    say()

    # 2. witnesses ----------------------------------------------------------
    say(f"## 2. Witnesses: legitimate states and operations exist ({fmt_scope(ref_scope)})")
    say()
    say("| witness | result | time |")
    say("|---|---|---|")
    wres = witnesses(ref_scope)
    for r in wres:
        say(f"| {r['name']} | {r['result']} | {r['time']:.1f}s |")
        ok_all &= r["result"] == "WITNESSED"
    say()
    say("<details><summary>witness states</summary>\n")
    for r in wres:
        if r["cex"]:
            say(f"{r['name']}:\n```\n{r['cex']}\n```")
    say("</details>\n")

    # 3. mutants (negative controls for the obligations) ---------------------
    say(f"## 3. Mutants: wrong designs must be rejected ({fmt_scope(mut_scope)})")
    say()
    say("| mutant | design error | violated obligations | detected |")
    say("|---|---|---|---|")
    cex_sample = []
    for m, desc in MUTANTS.items():
        mres = run_obligations(frozenset([m]), mut_scope)
        bad = [r for r in mres if r["result"] != "HOLDS"]
        det = bool(bad)
        ok_all &= det
        say(f"| `{m}` | {desc} | {', '.join(r['name'].split()[0] + ' ' + r['result'] for r in bad) or '-'}"
            f" | {'yes' if det else '**NO**'} |")
        if bad and bad[0]["cex"]:
            cex_sample.append((m, bad[0]["name"], bad[0]["cex"]))
    say()
    say("<details><summary>first counterexample per mutant</summary>\n")
    for m, n, c in cex_sample:
        say(f"`{m}` violates {n}:\n```\n{c}\n```")
    say("</details>\n")

    # 4. challenge cases -----------------------------------------------------
    say(f"## 4. Challenge cases (adversary = up to {K_ADV} arbitrary AI records)")
    for case in ALL_CASES:
        rs = case()
        say()
        say(f"### {rs[0]['case']}")
        say()
        for r in rs:
            if r["kind"] == "state":
                say(f"- state: {r['desc']}\n```{r['detail']}\n```")
            else:
                mark = "PASS" if r["ok"] else "**FAIL**"
                say(f"- {mark} [{r['kind']}] {r['desc']}" + (f" — {r['detail']}" if r["detail"] else ""))
                ok_all &= r["ok"]
    say()
    say(f"## Summary: {'ALL CHECKS PASSED' if ok_all else 'SOME CHECKS FAILED'} "
        f"(total {time.time() - T0:.0f}s)")

    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    with open(args.out, "w") as f:
        f.write("\n".join(out) + "\n")

    if args.smt2:
        os.makedirs(args.smt2, exist_ok=True)
        for ob in OBLIGATIONS:
            spec = ob(frozenset(), ref_scope)
            name, x, hyp, goal = spec[:4]
            s = Solver()
            s.add(hyp, Not(goal))
            fn = os.path.join(args.smt2, ob.__name__ + ".smt2")
            with open(fn, "w") as f:
                f.write(f"; {name}\n; expected: unsat\n" + s.to_smt2())
    sys.exit(0 if ok_all else 1)


if __name__ == "__main__":
    main()

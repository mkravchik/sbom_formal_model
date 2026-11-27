"""
Challenge cases A-E with positive checks and negative controls.

Each case is a concrete repository snapshot (locations and their content
hashes), the output of the deterministic extractor on that snapshot, and a
sequence of contributions.  Checks are of three kinds:

  expect   concrete status of a slot in a concrete state (evaluated by z3)
  never    a bad outcome is UNSAT for EVERY extension of the state by up to
           K arbitrary AI records (symbolic adversarial AI)            -> must be UNSAT
  mutant   the same bad outcome becomes reachable under a wrong design -> must be SAT
"""
import time
from z3 import (Solver, BoolVal, Bool, And, Or, Not, simplify, is_true, sat,
                unsat)
from kmodel import Universe, Model, Rec, free_rec, retraction_of

K_ADV = 3      # number of arbitrary adversarial AI records in "never" checks
_uid = [0]


class Case:
    def __init__(self, name, comps, attrs, vals, files, mech_sup=(), mech_rel=()):
        """files: {loc: hash}.  An extra hash 'forged' never occurs in the snapshot."""
        _uid[0] += 1
        self.name = name
        hashes = sorted(set(files.values())) + ["forged"]
        self.U = Universe(f"K{_uid[0]}", comps, attrs, vals, list(files), hashes,
                          snap=files, mech_sup=list(mech_sup), mech_rel=list(mech_rel))
        self.files = files
        self.results = []

    # ---- record constructors (by name) ----------------------------------
    def _cite(self, loc, forged):
        U = self.U
        return U.l[loc], (U.h["forged"] if forged else U.h[self.files[loc]])

    def sup(self, src, loc, comp, attr, val, forged=False, label=""):
        U = self.U
        l, h = self._cite(loc, forged)
        return Rec(kind=U.SUP, src=U.s[src], loc=l, hash=h, comp=U.c[comp],
                   attr=U.a[attr], val=U.v[val], comp2=U.c[comp],
                   tkind=U.SUP, tsrc=U.s[src], label=label or f"{src}:{comp}.{attr}={val}")

    def rel(self, kind, src, loc, comp, comp2, forged=False, label=""):
        U = self.U
        l, h = self._cite(loc, forged)
        sym = "~" if kind == "Same" else "->"
        return Rec(kind=U.k[kind], src=U.s[src], loc=l, hash=h, comp=U.c[comp],
                   attr=U.A[0], val=U.V[0], comp2=U.c[comp2], tkind=U.SUP,
                   tsrc=U.s[src], label=label or f"{src}:{kind} {comp}{sym}{comp2}")

    def retract(self, src, r, label=""):
        return retraction_of(self.U, r, self.U.s[src],
                             label=label or f"{src}:retract({r.label})")

    # ---- evaluation -------------------------------------------------------
    def concl(self, recs, mutants=frozenset()):
        M = Model(self.U, recs, mutants)
        return M.concl([BoolVal(True)] * len(recs))

    def status(self, K, comp, attr):
        U = self.U
        c, a = U.names["Comp"].index(comp), U.names["Attr"].index(attr)
        t = lambda e: is_true(simplify(e))
        vals = U.names["Val"]
        for v, e in enumerate(K.est[c][a]):
            if t(e):
                tag = " (contested)" if t(K.contested[c][a]) else ""
                return f"Established({vals[v]}){tag}"
        for v, e in enumerate(K.prov[c][a]):
            if t(e):
                return f"Provisional({vals[v]})"
        if t(K.conf[c][a]):
            cand = [vals[v] for v in range(len(vals)) if t(K.P[c][a][v])]
            return "Conflicting{" + ",".join(cand) + "}"
        assert t(K.unk[c][a])
        return "Unknown"

    def merged(self, K, c1, c2, firm=True):
        U = self.U
        i, j = U.names["Comp"].index(c1), U.names["Comp"].index(c2)
        return is_true(simplify((K.Ef if firm else K.Ep)[i][j]))

    def table(self, K, comps=None, attrs=None):
        U = self.U
        rows = []
        for c in comps or U.names["Comp"]:
            cells = [f"{a}={self.status(K, c, a)}" for a in (attrs or U.names["Attr"])]
            rows.append(f"      {c:10} " + "; ".join(cells))
        return "\n".join(rows)

    def export(self, K, strict=True):
        """SBOM draft view.  strict: only Established values are asserted.
        Completeness is never asserted."""
        U = self.U
        lines = ["      completeness: NOT ASSERTED"]
        for c in U.names["Comp"]:
            fields = []
            for a in U.names["Attr"]:
                st = self.status(K, c, a)
                if st.startswith("Established"):
                    fields.append(f"{a}: {st[12:].split(')')[0]}")
                elif st.startswith("Provisional") and not strict:
                    fields.append(f"{a}: {st[12:-1]} [UNREVIEWED AI INTERPRETATION]")
                else:
                    fields.append(f"{a}: NOASSERTION ({st})")
            lines.append(f"      {c}: " + ", ".join(fields))
        return "\n".join(lines)

    # ---- checks -----------------------------------------------------------
    def expect(self, desc, recs, comp, attr, expected, mutants=frozenset()):
        st = self.status(self.concl(recs, mutants), comp, attr)
        ok = st == expected
        self.results.append(dict(case=self.name, kind="expect", desc=desc,
                                 ok=ok, detail=f"{comp}.{attr} = {st} (expected {expected})"))
        return ok

    def expect_bool(self, desc, value, detail=""):
        self.results.append(dict(case=self.name, kind="expect", desc=desc, ok=bool(value),
                                 detail=detail))

    def _adversary(self, recs, mutants, bad, k=K_ADV, only_ai=True, extra=None):
        U = self.U
        adv = [free_rec(U, f"{U.name}.adv{_uid[0]}.{i}") for i in range(k)]
        _uid[0] += 1
        allr = list(recs) + adv
        inS = [BoolVal(True)] * len(recs) + [Bool(f"{U.name}.in{_uid[0]}.{i}") for i in range(k)]
        M = Model(U, allr, mutants)
        K = M.concl(inS)
        s = Solver()
        if only_ai:
            s.add([r.src == U.AI for r in adv])
        if extra is not None:
            s.add([extra(r) for r in adv])
        s.add(bad(K))
        t0 = time.time()
        r = s.check()
        return r, time.time() - t0, s, adv

    def never(self, desc, recs, bad, mutants=frozenset(), expect_unsat=True, extra=None):
        """Bad outcome must be impossible even with up to K_ADV arbitrary AI records
        (optionally restricted by `extra`)."""
        r, dt, s, adv = self._adversary(recs, mutants, bad, extra=extra)
        ok = (r == unsat) if expect_unsat else (r == sat)
        kind = "never" if expect_unsat else ("mutant" if mutants else "reachable")
        det = f"{'UNSAT' if r == unsat else 'SAT'} in {dt:.1f}s with {K_ADV} free AI records"
        if mutants:
            det += f" under mutant {sorted(mutants)}"
        self.results.append(dict(case=self.name, kind=kind, desc=desc, ok=ok, detail=det))
        return ok

    def slot(self, comp, attr):
        U = self.U
        return U.names["Comp"].index(comp), U.names["Attr"].index(attr)

    def val(self, v):
        return self.U.names["Val"].index(v)


def log_table(case, title, K):
    case.results.append(dict(case=case.name, kind="state", desc=title, ok=True,
                             detail="\n" + case.table(K)))


# ===========================================================================
# A. Conditional version
# ===========================================================================
def case_A():
    C = Case("A conditional version",
             comps=["gtestDecl", "gtestCheckout"],
             attrs=["declared_rev", "overridable", "available_version", "selected_version"],
             vals=["abc123", "1.0.0", "yes"],
             files={"CMakeLists.txt": "h_root", "third_party/gtest/CMakeLists.txt": "h_chk"},
             # deterministic extractor output on this snapshot:
             mech_sup=[("CMakeLists.txt", "gtestDecl", "declared_rev", "abc123"),
                       ("CMakeLists.txt", "gtestDecl", "overridable", "yes"),
                       ("third_party/gtest/CMakeLists.txt", "gtestCheckout",
                        "available_version", "1.0.0")])
    t1 = C.sup("Tool", "CMakeLists.txt", "gtestDecl", "declared_rev", "abc123")
    t2 = C.sup("Tool", "CMakeLists.txt", "gtestDecl", "overridable", "yes")
    t3 = C.sup("Tool", "third_party/gtest/CMakeLists.txt", "gtestCheckout",
               "available_version", "1.0.0")
    base = [t1, t2, t3]
    log_table(C, "mechanical facts only", C.concl(base))
    C.expect("declared default revision is a mechanical fact", base, "gtestDecl",
             "declared_rev", "Established(abc123)")
    C.expect("existence of an optional override is a mechanical fact", base, "gtestDecl",
             "overridable", "Established(yes)")
    C.expect("checkout version is a fact about the checkout", base, "gtestCheckout",
             "available_version", "Established(1.0.0)")
    C.expect("selected version is unknown (override value unobservable)", base,
             "gtestDecl", "selected_version", "Unknown")
    C.expect("checkout version is NOT attributed to the declaration before consolidation",
             base, "gtestDecl", "available_version", "Unknown")
    # naive AI inference "default = selected"
    a1 = C.sup("AI", "CMakeLists.txt", "gtestDecl", "selected_version", "abc123")
    s2 = base + [a1]
    C.expect("AI 'selected = default' stays an unreviewed interpretation", s2,
             "gtestDecl", "selected_version", "Provisional(abc123)")
    a2 = C.sup("AI", "third_party/gtest/CMakeLists.txt", "gtestDecl", "selected_version", "1.0.0")
    C.expect("two incompatible AI selections are a visible conflict", s2 + [a2],
             "gtestDecl", "selected_version", "Conflicting{abc123,1.0.0}")
    # human confirms that checkout and declaration are the same dependency
    h = C.rel("Same", "Human", "CMakeLists.txt", "gtestDecl", "gtestCheckout")
    s3 = base + [h]
    log_table(C, "after human-justified consolidation", C.concl(s3))
    C.expect("after consolidation: available 1.0.0 ...", s3, "gtestDecl",
             "available_version", "Established(1.0.0)")
    C.expect("... declared stays abc123 (no false conflict: distinct slots)", s3,
             "gtestDecl", "declared_rev", "Established(abc123)")
    C.expect("... and selected is still Unknown", s3, "gtestDecl", "selected_version", "Unknown")
    sc, sa = C.slot("gtestDecl", "selected_version")
    C.never("selected version can never be Established by AI reasoning", s3,
            lambda K: Or(K.est[sc][sa]))
    C.never("selected version cannot be Established by AI even under the naive AI claim",
            s2, lambda K: Or(K.est[sc][sa]))
    dc, da = C.slot("gtestDecl", "declared_rev")
    C.never("no AI contribution can change the declared revision", s3,
            lambda K: Not(K.est[dc][da][C.val("abc123")]))
    C.never("[mutant ai_trusted] selected version becomes Established", s2,
            lambda K: Or(K.est[sc][sa]), mutants={"ai_trusted"}, expect_unsat=False)

    # Negative control: conflating the three version notions into one slot.
    D = Case("A' (conflated single 'version' slot)",
             comps=["gtestDecl", "gtestCheckout"], attrs=["version"],
             vals=["abc123", "1.0.0"],
             files={"CMakeLists.txt": "h_root", "third_party/gtest/CMakeLists.txt": "h_chk"},
             mech_sup=[("CMakeLists.txt", "gtestDecl", "version", "abc123"),
                       ("third_party/gtest/CMakeLists.txt", "gtestCheckout", "version", "1.0.0")])
    d = [D.sup("Tool", "CMakeLists.txt", "gtestDecl", "version", "abc123"),
         D.sup("Tool", "third_party/gtest/CMakeLists.txt", "gtestCheckout", "version", "1.0.0"),
         D.rel("Same", "Human", "CMakeLists.txt", "gtestDecl", "gtestCheckout")]
    D.expect("[negative control] one 'version' slot turns two true facts into a spurious "
             "conflict", d, "gtestDecl", "version", "Conflicting{abc123,1.0.0}")
    return C.results + D.results


# ===========================================================================
# B. Nested components
# ===========================================================================
def case_B():
    files = {"infra/CMakeLists.txt": "h_infra",
             "infra/third_party/googletest/CMakeLists.txt": "h_gt",
             "infra/third_party/googletest/LICENSE": "h_bsd"}
    C = Case("B nested components", comps=["Infra", "GoogleTest"],
             attrs=["name", "license"], vals=["infra", "googletest", "BSD-3-Clause"],
             files=files,
             mech_sup=[("infra/CMakeLists.txt", "Infra", "name", "infra"),
                       ("infra/third_party/googletest/CMakeLists.txt", "GoogleTest", "name", "googletest"),
                       ("infra/third_party/googletest/LICENSE", "GoogleTest", "license", "BSD-3-Clause")],
             mech_rel=[("infra/CMakeLists.txt", "Dep", "Infra", "GoogleTest")])
    ti = C.sup("Tool", "infra/CMakeLists.txt", "Infra", "name", "infra")
    tg = C.sup("Tool", "infra/third_party/googletest/CMakeLists.txt", "GoogleTest", "name", "googletest")
    tl = C.sup("Tool", "infra/third_party/googletest/LICENSE", "GoogleTest", "license", "BSD-3-Clause")
    td = C.rel("Dep", "Tool", "infra/CMakeLists.txt", "Infra", "GoogleTest")
    # Infra first: the AI walks Infra's tree and finds the only LICENSE file.
    mis = C.sup("AI", "infra/third_party/googletest/LICENSE", "Infra", "license", "BSD-3-Clause",
                label="AI:Infra.license=BSD (misattributed nested LICENSE)")
    order1 = [ti, mis, td, tg, tl]           # Infra investigated first
    order2 = [tg, tl, td, ti, mis]           # GoogleTest investigated first
    K1, K2 = C.concl(order1), C.concl(order2)
    log_table(C, "Infra-first investigation (with an AI misattribution)", K1)
    C.expect_bool("discovery order does not matter (Infra-first == GoogleTest-first)",
                  C.table(K1) == C.table(K2))
    C.expect("GoogleTest license is GoogleTest's", order1, "GoogleTest", "license",
             "Established(BSD-3-Clause)")
    C.expect("Infra identity is not GoogleTest's", order1, "Infra", "name", "Established(infra)")
    C.expect("nested LICENSE attributed to Infra is only an unreviewed AI claim", order1,
             "Infra", "license", "Provisional(BSD-3-Clause)")
    clean = [ti, td, tg, tl]
    C.expect("without the AI claim, Infra's license is honestly Unknown", clean,
             "Infra", "license", "Unknown")
    fix = order1 + [C.retract("Human", mis)]
    C.expect("reviewer retracts the misattribution -> Unknown", fix, "Infra", "license", "Unknown")
    C.expect("... GoogleTest's license is unaffected by that retraction", fix,
             "GoogleTest", "license", "Established(BSD-3-Clause)")
    C.expect_bool("dependency Infra -> GoogleTest is established",
                  is_true(simplify(C.concl(order1).Fd[0][1])))
    C.expect_bool("Infra and GoogleTest are NOT consolidated", not C.merged(K1, "Infra", "GoogleTest", firm=False))
    ic, il = C.slot("Infra", "license")
    _, iname = C.slot("Infra", "name")
    C.never("GoogleTest's license can never become Established for Infra by AI contributions",
            order1, lambda K: K.est[ic][il][C.val("BSD-3-Clause")])
    C.never("GoogleTest's identity can never become Established for Infra by AI contributions",
            order1, lambda K: K.est[ic][iname][C.val("googletest")])
    # mutant: naive "files under a component's tree are about that component"
    U = C.U
    nest = And(U.inside(U.c["GoogleTest"], U.c["Infra"]),
               *[Not(U.inside(x, y)) for x in U.C for y in U.C
                 if not (x is U.c["GoogleTest"] and y is U.c["Infra"])])
    C.never("[mutant containment] GoogleTest license becomes Established for Infra from Tool facts",
            clean, lambda K: And(nest, K.est[ic][il][C.val("BSD-3-Clause")]),
            mutants={"containment"}, expect_unsat=False)
    return C.results


# ===========================================================================
# C. Incorrect interpretation
# ===========================================================================
def case_C():
    files = {"foo/README.md": "h_readme", "foo/CMakeLists.txt": "h_cm"}
    C = Case("C incorrect interpretation", comps=["Foo", "Zlib"], attrs=["name"],
             vals=["zlib", "foo"], files=files,
             mech_sup=[("foo/CMakeLists.txt", "Foo", "name", "foo")])
    wrong = C.sup("AI", "foo/README.md", "Foo", "name", "zlib",
                  label="AI:Foo.name=zlib (README merely mentions zlib)")
    forged = C.sup("AI", "foo/README.md", "Foo", "name", "zlib", forged=True,
                   label="AI:Foo.name=zlib citing a non-existent quote")
    dep = C.rel("Dep", "AI", "foo/README.md", "Foo", "Zlib")
    C.expect("genuine citation, unjustified identity: only Provisional", [wrong],
             "Foo", "name", "Provisional(zlib)")
    C.expect("citation failing the integrity check is inert", [forged], "Foo", "name", "Unknown")
    C.expect("reviewer retracts the identity claim -> Unknown",
             [wrong, C.retract("Human", wrong)], "Foo", "name", "Unknown")
    C.expect("AI may retract its own wrong interpretation",
             [wrong, C.retract("AI", wrong)], "Foo", "name", "Unknown")
    tool = C.sup("Tool", "foo/CMakeLists.txt", "Foo", "name", "foo")
    C.expect("mechanical identity dominates the wrong AI claim (shown as contested)",
             [tool, wrong], "Foo", "name", "Established(foo) (contested)")
    C.expect("AI cannot retract a mechanical fact",
             [tool, C.retract("AI", tool)], "Foo", "name", "Established(foo)")
    K = C.concl([wrong, C.retract("Human", wrong), dep])
    C.expect_bool("the README mention survives as a provisional dependency Foo -> Zlib",
                  is_true(simplify(K.Pd[0][1])) and not is_true(simplify(K.Fd[0][1])))
    fc, fa = C.slot("Foo", "name")
    C.never("'zlib' can never be an Established identity of Foo through AI contributions",
            [wrong], lambda K: K.est[fc][fa][C.val("zlib")])
    rejected = [wrong, C.retract("Human", wrong)]
    C.never("[limitation] after a reviewer rejects the README link, the AI can re-raise "
            "zlib as Provisional by citing other evidence", rejected,
            lambda K: K.prov[fc][fa][C.val("zlib")], expect_unsat=False)
    C.never("... but never as Established", rejected, lambda K: K.est[fc][fa][C.val("zlib")])
    C.never("[mutant ai_trusted] the README mention establishes Foo = zlib",
            [wrong], lambda K: K.est[fc][fa][C.val("zlib")],
            mutants={"ai_trusted"}, expect_unsat=False)
    C.never("[mutant no_integrity] a forged quote yields a Provisional identity",
            [forged], lambda K: K.prov[fc][fa][C.val("zlib")],
            mutants={"no_integrity"}, expect_unsat=False)
    return C.results


# ===========================================================================
# D. Revised component association
# ===========================================================================
def case_D():
    files = {"CMakeLists.txt": "h_root", "third_party/googletest/CMakeLists.txt": "h_gt",
             "third_party/googletest/LICENSE": "h_bsd", "LICENSE": "h_mit"}
    C = Case("D revised component association", comps=["H1", "H2", "Infra"],
             attrs=["name", "license"], vals=["gtest", "googletest", "BSD-3-Clause", "MIT", "infra"],
             files=files,
             mech_sup=[("third_party/googletest/CMakeLists.txt", "H2", "name", "googletest"),
                       ("third_party/googletest/LICENSE", "H2", "license", "BSD-3-Clause"),
                       ("LICENSE", "Infra", "license", "MIT"),
                       ("CMakeLists.txt", "Infra", "name", "infra")])
    # H1: hypothesis from a FetchContent declaration; H2: hypothesis from a checkout dir.
    t2n = C.sup("Tool", "third_party/googletest/CMakeLists.txt", "H2", "name", "googletest")
    t2l = C.sup("Tool", "third_party/googletest/LICENSE", "H2", "license", "BSD-3-Clause")
    tim = C.sup("Tool", "LICENSE", "Infra", "license", "MIT")
    tin = C.sup("Tool", "CMakeLists.txt", "Infra", "name", "infra")
    a1n = C.sup("AI", "CMakeLists.txt", "H1", "name", "gtest")
    base = [t2n, t2l, tim, tin, a1n]
    C.expect("before consolidation H1's license is Unknown", base, "H1", "license", "Unknown")
    ai_same = C.rel("Same", "AI", "CMakeLists.txt", "H1", "H2")
    s1 = base + [ai_same]
    C.expect("AI consolidation propagates only provisionally", s1, "H1", "license",
             "Provisional(BSD-3-Clause)")
    hu_same = C.rel("Same", "Human", "CMakeLists.txt", "H1", "H2")
    s2 = s1 + [hu_same]
    log_table(C, "after human-justified consolidation H1~H2", C.concl(s2))
    C.expect("justified consolidation establishes the shared license", s2, "H1", "license",
             "Established(BSD-3-Clause)")
    C.expect("the firm project name dominates the AI's alias 'gtest' (kept visible as contested)",
             s2, "H1", "name", "Established(googletest) (contested)")
    unsup = C.rel("Same", "Human", "CMakeLists.txt", "H2", "Infra", forged=True,
                  label="Human:Same H2~Infra citing forged evidence")
    s3 = s2 + [unsup]
    C.expect_bool("merge citing forged evidence has no effect",
                  not C.merged(C.concl(s3), "H2", "Infra", firm=False))
    wrong = C.rel("Same", "AI", "CMakeLists.txt", "H2", "Infra", label="AI:Same H2~Infra (wrong)")
    s4 = s2 + [wrong]
    C.expect("wrong AI merge cannot override Infra's established license", s4, "Infra",
             "license", "Established(MIT) (contested)")
    C.expect("... nor H1's", s4, "H1", "license", "Established(BSD-3-Clause) (contested)")
    s5 = s4 + [C.retract("AI", wrong)]
    C.expect_bool("retracting the wrong merge restores the previous conclusions exactly",
                  C.table(C.concl(s5)) == C.table(C.concl(s2)))
    C.expect_bool("retraction keeps every record (evidence preserved)", len(s5) == len(s4) + 1)
    s6 = s2 + [C.retract("Human", hu_same), C.retract("AI", ai_same)]
    C.expect("undoing the justified merge splits the hypotheses again", s6, "H1",
             "license", "Unknown")
    C.expect("consolidation is symmetric: retracting Same(H2,H1) undoes Same(H1,H2)",
             s2 + [C.retract("Human", C.rel("Same", "Human", "CMakeLists.txt", "H2", "H1")),
                   C.retract("AI", ai_same)], "H1", "license", "Unknown")
    h1c, h1l = C.slot("H1", "license")
    ic, il = C.slot("Infra", "license")
    C.never("AI contributions can never establish a merge-derived value for H1 without a firm merge",
            base, lambda K: Or(K.est[h1c][h1l]))
    C.never("AI contributions can never move Infra off its MIT license",
            s2, lambda K: Not(K.est[ic][il][C.val("MIT")]))
    hn = C.sup("AI", "CMakeLists.txt", "H1", "name", "googletest")
    C.never("[mutant name_merge] an AI name guess consolidates H1 and H2 firmly",
            base + [hn], lambda K: K.est[h1c][h1l][C.val("BSD-3-Clause")],
            mutants={"name_merge"}, expect_unsat=False)
    return C.results


# ===========================================================================
# E. Interrupted investigation
# ===========================================================================
def case_E():
    files = {"libfoo/CMakeLists.txt": "h_cm", "libfoo/include/foo/version.h": "h_ver",
             "libfoo/COPYING": "h_copying"}
    C = Case("E interrupted investigation", comps=["LibFoo"],
             attrs=["name", "version", "license"], vals=["libfoo", "2.3", "LGPL-2.1"],
             files=files,
             mech_sup=[("libfoo/include/foo/version.h", "LibFoo", "version", "2.3")])
    an = C.sup("AI", "libfoo/CMakeLists.txt", "LibFoo", "name", "libfoo")
    av = C.sup("AI", "libfoo/include/foo/version.h", "LibFoo", "version", "2.3")
    garbled = C.sup("AI", "libfoo/COPYING", "LibFoo", "license", "LGPL-2.1", forged=True,
                    label="AI:partial/garbled license answer before crash")
    tv = C.sup("Tool", "libfoo/include/foo/version.h", "LibFoo", "version", "2.3")
    al = C.sup("AI", "libfoo/COPYING", "LibFoo", "license", "LGPL-2.1")
    hn = C.sup("Human", "libfoo/CMakeLists.txt", "LibFoo", "name", "libfoo")
    full = [an, av, garbled, tv, al, hn]       # what a completed run would contain
    crash = full[:3]                            # interrupted after the garbled answer
    K = C.concl(crash)
    log_table(C, "interrupted state", K)
    C.results.append(dict(case=C.name, kind="state", desc="strict export of the interrupted state",
                          ok=True, detail="\n" + C.export(K, strict=True)))
    C.results.append(dict(case=C.name, kind="state", desc="review draft of the interrupted state",
                          ok=True, detail="\n" + C.export(K, strict=False)))
    C.expect("identity preserved (qualified)", crash, "LibFoo", "name", "Provisional(libfoo)")
    C.expect("version preserved (qualified)", crash, "LibFoo", "version", "Provisional(2.3)")
    C.expect("license explicitly unresolved", crash, "LibFoo", "license", "Unknown")
    # every interruption point gives a meaningful state; established facts persist
    ok = True
    for n in range(len(full)):
        before, after = C.table(C.concl(full[:n])), C.table(C.concl(full[:n + 1]))
        cells = [c.strip() for line in before.splitlines() for c in line.split(";")]
        ok &= all(c.split()[-1] in after for c in cells if "Established" in c)
    C.expect_bool("at every interruption point Established facts persist in later prefixes", ok)
    C.expect("completed run: version mechanically established", full, "LibFoo", "version",
             "Established(2.3)")
    C.expect("completed run: name human-confirmed", full, "LibFoo", "name", "Established(libfoo)")
    C.expect("completed run: license remains an AI interpretation", full, "LibFoo", "license",
             "Provisional(LGPL-2.1)")
    lc, la = C.slot("LibFoo", "license")
    nc, na = C.slot("LibFoo", "name")
    C.never("no AI continuation can Establish the license", crash, lambda K: Or(K.est[lc][la]))
    C.never("no non-retracting AI continuation (e.g. failing license attempts) can erase "
            "the identity candidate", crash, lambda K: Not(K.P[nc][na][C.val("libfoo")]),
            extra=lambda r: r.kind != C.U.RET)
    C.never("an explicit AI self-retraction CAN remove the AI identity candidate",
            crash, lambda K: Not(K.P[nc][na][C.val("libfoo")]), expect_unsat=False)
    return C.results


ALL_CASES = [case_A, case_B, case_C, case_D, case_E]

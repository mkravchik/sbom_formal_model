"""
General verification obligations of the knowledge model.

Every obligation quantifies over *all* states built from N arbitrary records
over a generic universe whose snapshot and deterministic extractor are left
uninterpreted (i.e. hold for every repository and every toolset).
The bound is the size of the carrier sets and the number of records.

An obligation  hyp ⊢ goal  is checked in two steps:
  1. hyp is satisfiable          (otherwise: VACUOUS - the check proves nothing)
  2. hyp ∧ ¬goal is unsatisfiable (otherwise: COUNTEREXAMPLE, which is printed)

Witness obligations (W*) are satisfiability checks showing that legitimate
states and operations exist.
"""
import time
from z3 import (Solver, Bool, BoolVal, And, Or, Not, Implies, sat, unsat,
                is_true)
from kmodel import (Universe, Model, free_rec, retraction_of, concl_eq,
                    concl_le, slot_eq, PARTS_ALL, PARTS_FIRM)

DEFAULT_SCOPE = dict(comps=3, attrs=2, vals=3, locs=2, hashes=2, records=6)
# O7 compares two arbitrary states record-by-record and is the most expensive
# obligation; its general form is checked at a smaller record bound, while its
# inductive core O7a is checked at the full bound.
SCOPE_OVERRIDES = {"O7": dict(records=4)}

_uid = [0]


class Ctx:
    """Generic universe + N free records + two free states S, T."""

    def __init__(self, mutants=frozenset(), scope=DEFAULT_SCOPE):
        _uid[0] += 1
        sc = scope
        self.U = U = Universe(f"G{_uid[0]}",
                              [f"c{i}" for i in range(sc["comps"])],
                              [f"a{i}" for i in range(sc["attrs"])],
                              [f"v{i}" for i in range(sc["vals"])],
                              [f"l{i}" for i in range(sc["locs"])],
                              [f"h{i}" for i in range(sc["hashes"])])
        self.N = sc["records"]
        self.recs = [free_rec(U, f"r{i}") for i in range(self.N)]
        self.M = Model(U, self.recs, mutants)
        self.R = Model(U, self.recs)          # reference semantics (no mutant)
        self.S = [Bool(f"S{i}") for i in range(self.N)]
        self.T = [Bool(f"T{i}") for i in range(self.N)]
        self.KS = self.M.concl(self.S)
        self.KT = self.M.concl(self.T)
        self.mutants = mutants

    # helpers
    def subset(self, X, Y):
        return And([Implies(x, y) for x, y in zip(X, Y)])

    def added(self, pred):
        """Every record in T \\ S satisfies pred(r)."""
        return And([Implies(And(self.T[i], Not(self.S[i])), pred(r))
                    for i, r in enumerate(self.recs)])

    def sel(self, M, comp_term, c):
        return Or([And(comp_term == self.U.C[x], M[x][c])
                   for x in range(len(self.U.C))])


def describe(ctx, m, states=("S", "T")):
    U = ctx.U
    lines = []
    ev = lambda t: m.eval(t, model_completion=True)
    short = lambda t: str(ev(t)).split(".")[-1]
    for i, r in enumerate(ctx.recs):
        mem = {n: is_true(ev(getattr(ctx, n)[i])) for n in states}
        if not any(mem.values()):
            continue
        k = short(r.kind)
        if k == "Sup":
            body = f"{short(r.comp)}.{short(r.attr)}={short(r.val)}"
        elif k in ("Same", "Dep"):
            body = f"{short(r.comp)}~{short(r.comp2)}" if k == "Same" else f"{short(r.comp)}->{short(r.comp2)}"
        else:
            body = (f"retract[{short(r.tsrc)} {short(r.tkind)} "
                    f"{short(r.comp)}/{short(r.attr)}/{short(r.val)}/{short(r.comp2)}]")
        gen = is_true(ev(U.genuine(r.loc, r.hash)))
        extra = ""
        if "latest_wins" in ctx.mutants:
            extra += f" seq={ev(r.seq)}"
        if "atom_retract" in ctx.mutants:
            extra += f" tid={ev(r.tid)}"
        lines.append(f"      r{i}: {k:4} src={short(r.src):5} {body:28} cite={short(r.loc)}/"
                     f"{short(r.hash)} genuine={gen}{extra}  in "
                     + ",".join(n for n in states if mem[n]))
    return "\n".join(lines)


def check(name, ctx, hyp, goal, states=("S", "T")):
    t0 = time.time()
    s = Solver()
    s.add(hyp)
    if s.check() != sat:
        return dict(name=name, result="VACUOUS", time=time.time() - t0, cex=None)
    s.add(Not(goal))
    r = s.check()
    res = "HOLDS" if r == unsat else ("COUNTEREXAMPLE" if r == sat else "UNKNOWN")
    cex = describe(ctx, s.model(), states) if r == sat else None
    return dict(name=name, result=res, time=time.time() - t0, cex=cex)


def witness(name, ctx, cond, states=("S",)):
    t0 = time.time()
    s = Solver()
    s.add(cond)
    r = s.check()
    res = "WITNESSED" if r == sat else "NO WITNESS"
    ex = describe(ctx, s.model(), states) if r == sat else None
    return dict(name=name, result=res, time=time.time() - t0, cex=ex)


# --------------------------------------------------------------------------
# Obligations.  Each returns (name, ctx, hyp, goal[, states]).
# --------------------------------------------------------------------------

def O1_evidence_soundness(mut, scope):
    """Established/Provisional values and dependencies have a traceable
    witness record: present in S, integrity-valid w.r.t. the REAL snapshot
    and extractor, not defeated, of firm origin for Established, and about
    the component or a component consolidated with it by the corresponding
    (firm / provisional) merge relation of the reference semantics."""
    x = Ctx(mut, scope)
    U, R, K = x.U, x.R, x.KS
    RK = R.concl(x.S)                       # reference merge relations
    live = RK.live                           # reference liveness
    goals = []
    for c in range(len(U.C)):
        for a in range(len(U.A)):
            for v in range(len(U.V)):
                wf = Or([And(live[i], r.src != U.AI, r.kind == U.SUP,
                             r.attr == U.A[a], r.val == U.V[v],
                             x.sel(RK.Ef, r.comp, c))
                         for i, r in enumerate(x.recs)])
                wp = Or([And(live[i], r.kind == U.SUP, r.attr == U.A[a],
                             r.val == U.V[v], x.sel(RK.Ep, r.comp, c))
                         for i, r in enumerate(x.recs)])
                goals += [Implies(K.est[c][a][v], wf), Implies(K.prov[c][a][v], wp)]
        for d in range(len(U.C)):
            goals.append(Implies(K.Ef[c][d], RK.Ef[c][d]))
            goals.append(Implies(K.Ep[c][d], RK.Ep[c][d]))
            goals.append(Implies(K.Fd[c][d], RK.Fd[c][d]))
    return "O1 evidence soundness (traceable genuine support)", x, BoolVal(True), And(goals), ("S",)


def O2_integrity_isolation(mut, scope):
    """Records whose citation fails the snapshot check have no effect at all."""
    x = Ctx(mut, scope)
    U = x.U
    hyp = And(x.subset(x.S, x.T),
              x.added(lambda r: And(r.kind != U.RET, Not(U.genuine(r.loc, r.hash)))))
    return "O2 fabricated evidence is inert", x, hyp, concl_eq(x.KS, x.KT)


def O3_ai_isolation(mut, scope):
    """Adding ANY set of AI records (claims, merges, dependencies, retractions)
    never changes the firm conclusions: an interpretation does not become
    established because it cites genuine evidence."""
    x = Ctx(mut, scope)
    hyp = And(x.subset(x.S, x.T), x.added(lambda r: r.src == x.U.AI))
    return "O3 AI interpretations never establish or defeat firm conclusions", x, hyp, \
        concl_eq(x.KS, x.KT, PARTS_FIRM)


def O4_subject_locality(mut, scope):
    """Claims about a component d leave every component c that is not
    (provisionally) consolidated with d untouched; claims never change the
    consolidation relations or the dependency graph."""
    x = Ctx(mut, scope)
    U = x.U
    base = And(x.subset(x.S, x.T), x.added(lambda r: r.kind == U.SUP))
    goals = [concl_eq(x.KS, x.KT, ["Ef", "Ep", "Fd", "Pd"])]
    for c in range(len(U.C)):
        hyp_c = x.added(lambda r, c=c: Not(x.sel(x.KS.Ep, r.comp, c)))
        goals.append(Implies(hyp_c, And([slot_eq(x.KS, x.KT, c, a)
                                         for a in range(len(U.A))])))
    return "O4 evidence about one component does not establish another", x, base, And(goals)


def O5_slot_independence(mut, scope):
    """Adding/retracting claims on attribute a' never changes any slot (c, a)
    with a != a' - failing to establish one claim cannot erase another."""
    x = Ctx(mut, scope)
    U = x.U
    goals = []
    for a in range(len(U.A)):
        other = x.added(lambda r, a=a: Or(And(r.kind == U.SUP, r.attr != U.A[a]),
                                          And(r.kind == U.RET, r.tkind == U.SUP,
                                              r.attr != U.A[a])))
        goals.append(Implies(other, And([slot_eq(x.KS, x.KT, c, a)
                                         for c in range(len(U.C))])))
    return "O5 slots are independent", x, x.subset(x.S, x.T), And(goals)


def O6_preservation(mut, scope):
    """Without retractions, accumulation only adds support: every support
    set, merge and dependency grows, and an Established value either stays
    Established or becomes an explicit Conflict that still lists it."""
    x = Ctx(mut, scope)
    U, KS, KT = x.U, x.KS, x.KT
    hyp = And(x.subset(x.S, x.T), x.added(lambda r: r.kind != U.RET))
    goals = [concl_le(KS, KT, ["Ef", "Ep", "F", "P", "Fd", "Pd"])]
    for c in range(len(U.C)):
        for a in range(len(U.A)):
            for v in range(len(U.V)):
                goals.append(Implies(KS.est[c][a][v],
                                     Or(KT.est[c][a][v], And(KT.conf[c][a], KT.F[c][a][v]))))
    return "O6 accumulation never silently destroys knowledge", x, hyp, And(goals)


def O7_equivalence_invariance(mut, scope):
    """States with the same contribution contents (up to duplicates, order of
    arrival and orientation of Same) have identical conclusions.  Covers
    idempotence, commutativity and discovery-order independence."""
    x = Ctx(mut, scope)
    M, S, T, recs = x.M, x.S, x.T, x.recs
    n = len(recs)
    cov = lambda X, Y: And([Implies(X[i], Or([And(Y[j], M.eq(recs[i], recs[j]))
                                               for j in range(n)])) for i in range(n)])
    hyp = And(cov(S, T), cov(T, S))
    return "O7 equivalent knowledge yields equal conclusions", x, hyp, concl_eq(x.KS, x.KT)


def O7a_duplicate_insensitivity(mut, scope):
    """Adding a record content-equivalent to one already present changes
    nothing.  O7 follows from O7a by induction: if S ≈ T then S ∪ T is
    reached from S (and from T) by adding one duplicate at a time."""
    x = Ctx(mut, scope)
    M, S, recs = x.M, x.S, x.recs
    k = x.N - 1
    Sp = [S[i] if i != k else BoolVal(False) for i in range(x.N)]
    T = [Sp[i] if i != k else BoolVal(True) for i in range(x.N)]
    hyp = Or([And(Sp[j], M.eq(recs[k], recs[j])) for j in range(k)])
    x.S, x.T = Sp, T
    return "O7a adding a duplicate contribution changes nothing", x, hyp, \
        concl_eq(M.concl(Sp), M.concl(T))


def O8_retraction_precision(mut, scope):
    """Adding a retraction x equals deleting exactly the records x defeats:
    revision is as-if-absent, everything else is unaffected, and the
    retracted records themselves stay in the state (audit trail)."""
    x = Ctx(mut, scope)
    U, M, S, recs = x.U, x.M, x.S, x.recs
    k = x.N - 1
    xr = recs[k]
    Sp = [S[i] if i != k else BoolVal(False) for i in range(x.N)]   # S without x
    T = [Sp[i] if i != k else BoolVal(True) for i in range(x.N)]    # S ∪ {x}
    hit = [And(Sp[i], recs[i].kind != U.RET, M.matches(xr, recs[i], i),
               M.authority(xr, recs[i])) for i in range(x.N)]
    R = [And(Sp[i], Not(hit[i])) for i in range(x.N)]               # S minus defeated
    hyp = And(xr.kind == U.RET, xr.src != U.TOOL)
    KT, KR = M.concl(T), M.concl(R)
    x.S, x.T = T, R          # for counterexample printing: S = with x, T = without hit
    return "O8 retraction is precise (as-if-absent)", x, hyp, concl_eq(KT, KR)


def O9_revisability(mut, scope):
    """Every record content can be revised: the human retraction built from
    record r defeats exactly the records content-equivalent to r (no
    duplicate survives, nothing else is hit); an AI retraction built from an
    AI record defeats it (AI self-correction)."""
    x = Ctx(mut, scope)
    U, M, recs = x.U, x.M, x.recs
    r0 = recs[0]
    xh = retraction_of(U, r0, U.HUMAN, tid=0)
    xa = retraction_of(U, r0, U.AI, tid=0)
    goals = []
    for i, t in enumerate(recs):
        goals.append(Implies(t.kind != U.RET,
                             And(M.matches(xh, t, i), M.authority(xh, t)) == M.eq(r0, t)))
    goals.append(Implies(r0.src == U.AI, And(M.matches(xa, r0, 0), M.authority(xa, r0))))
    return "O9 every contribution is revisable", x, r0.kind != U.RET, And(goals), ()


def O10_honest_status(mut, scope):
    """For every state (any interruption point) and every slot exactly one of
    Established(v) / Provisional(v) / Conflicting / Unknown holds, with a
    unique value; firm support implies provisional-level support."""
    x = Ctx(mut, scope)
    U, K = x.U, x.KS
    nv = len(U.V)
    goals = []
    for c in range(len(U.C)):
        for a in range(len(U.A)):
            opts = K.est[c][a] + K.prov[c][a] + [K.conf[c][a], K.unk[c][a]]
            exactly_one = And(Or(opts),
                              And([Not(And(opts[i], opts[j]))
                                   for i in range(len(opts)) for j in range(i + 1, len(opts))]))
            goals.append(exactly_one)
            goals += [Implies(K.F[c][a][v], K.P[c][a][v]) for v in range(nv)]
            goals += [Implies(K.est[c][a][v], K.F[c][a][v]) for v in range(nv)]
    for c in range(len(U.C)):
        for d in range(len(U.C)):
            goals.append(Implies(K.Ef[c][d], K.Ep[c][d]))
    return "O10 every slot has exactly one honest status", x, BoolVal(True), And(goals), ("S",)


OBLIGATIONS = [O1_evidence_soundness, O2_integrity_isolation, O3_ai_isolation,
               O4_subject_locality, O5_slot_independence, O6_preservation,
               O7_equivalence_invariance, O7a_duplicate_insensitivity, O8_retraction_precision, O9_revisability,
               O10_honest_status]


def run_obligations(mut=frozenset(), scope=DEFAULT_SCOPE, only=None):
    out = []
    for ob in OBLIGATIONS:
        if only and ob.__name__.split("_")[0] not in only:
            continue
        key = ob.__name__.split("_")[0]
        sc = dict(scope, **{k: min(v, scope[k]) for k, v in SCOPE_OVERRIDES.get(key, {}).items()})
        spec = ob(mut, sc)
        name, x, hyp, goal = spec[:4]
        states = spec[4] if len(spec) > 4 else ("S", "T")
        r = check(name, x, hyp, goal, states)
        r["scope"] = sc
        out.append(r)
    return out


# --------------------------------------------------------------------------
# Witnesses: legitimate states and operations exist (non-vacuity).
# --------------------------------------------------------------------------

def witnesses(scope=DEFAULT_SCOPE):
    out = []
    x = Ctx(frozenset(), scope)
    U, K, KT = x.U, x.KS, x.KT
    c0, c1, c2 = 0, 1, 2
    out.append(witness("W1 one state shows all four statuses", x, And(
        Or(K.est[c0][0]), Or(K.prov[c0][1]), K.conf[c1][0], K.unk[c2][1])))
    x = Ctx(frozenset(), scope); K = x.KS
    out.append(witness("W2 firm consolidation via a chain (transitivity)", x, And(
        K.Ef[0][2], *[Not(And(x.S[i], r.kind == x.U.SAME,
                                Or(And(r.comp == x.U.C[0], r.comp2 == x.U.C[2]),
                                   And(r.comp == x.U.C[2], r.comp2 == x.U.C[0]))))
                      for i, r in enumerate(x.recs)])))
    x = Ctx(frozenset(), scope); K = x.KS
    out.append(witness("W3 provisional (AI) merge propagates a value provisionally", x, And(
        K.Ep[0][1], Not(K.Ef[0][1]), Or(K.prov[0][0]),
        *[Implies(And(x.S[i], r.kind == x.U.SUP), r.comp == x.U.C[1]) for i, r in enumerate(x.recs)])))
    x = Ctx(frozenset(), scope); K, KT = x.KS, x.KT
    out.append(witness("W4 AI self-correction: Provisional -> Unknown by an AI retraction", x, And(
        x.subset(x.S, x.T), x.added(lambda r: And(r.kind == x.U.RET, r.src == x.U.AI)),
        Or(K.prov[0][0]), KT.unk[0][0]), ("S", "T")))
    x = Ctx(frozenset(), scope); K = x.KS
    out.append(witness("W5 Established value contested by an AI claim (firm dominance)", x,
                       And(Or(K.est[0][0]), K.contested[0][0])))
    x = Ctx(frozenset(), scope); K, KT = x.KS, x.KT
    out.append(witness("W6 firm merge exposes a conflict", x, And(
        x.subset(x.S, x.T), x.added(lambda r: r.kind == x.U.SAME),
        Or(K.est[0][0]), Or(K.est[1][0]), KT.conf[0][0]), ("S", "T")))
    x = Ctx(frozenset(), scope); K, KT = x.KS, x.KT
    out.append(witness("W7 human retraction of a Tool fact revises an Established value", x, And(
        x.subset(x.S, x.T), x.added(lambda r: And(r.kind == x.U.RET, r.src == x.U.HUMAN)),
        Or(K.est[0][0]), Not(Or(KT.est[0][0]))), ("S", "T")))
    x = Ctx(frozenset(), scope); K = x.KS
    out.append(witness("W8 dependency lifted through a firm merge", x, And(
        K.Fd[0][2], *[Not(And(x.S[i], r.kind == x.U.DEP, r.comp2 == x.U.C[2]))
                      for i, r in enumerate(x.recs)])))
    return out

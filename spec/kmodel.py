"""
Executable formal specification of the SBOM knowledge model (KM).

The model is written as a set of z3 (SMT) definitions.  Every quantifier
over the finite carrier sets is expanded explicitly, so each definition is a
quantifier-free formula and every verification query is decidable.

Mathematical summary (see spec/DOMAIN.md for the full text):

  Snapshot   snap : Loc -> Hash                  (fixed, read-only repository)
  Extractor  mechSup ⊆ Loc×Comp×Attr×Val,        (output of the deterministic
             mechRel ⊆ Loc×Kind×Comp×Comp         read-only tools on snap)
  Record     r = (kind, src, loc, hash, comp, attr, val, comp2, tkind, tsrc)
  State      S  = finite set of records          (grow-only; join = union)
  Conclusions concl(S) = (Ef, Ep, F, P, Fd, Pd)  and the derived statuses
             Established / Provisional / Conflicting / Unknown per slot.

Nothing in this file encodes an order of events, a lifecycle or a
"completed" flag: conclusions are a total function of the record set.

The `mutants` argument switches on deliberately wrong design variants that
are used as negative controls (they must be rejected by the obligations).
"""
from math import ceil, log2
from z3 import (EnumSort, Const, Function, BoolSort, IntSort, Int, Bool,
                BoolVal, And, Or, Not, If, Implies, Sum)

SRC_NAMES = ["Tool", "AI", "Human"]
KIND_NAMES = ["Sup", "Same", "Dep", "Ret"]

# Deliberately wrong design variants (negative controls).
MUTANTS = {
    "ai_trusted":      "AI interpretations count as firm (established) support",
    "no_integrity":    "citations are not checked against the snapshot",
    "ai_retracts_all": "an AI retraction can defeat Tool and Human records",
    "atom_retract":    "a retraction removes one record occurrence, not a content",
    "same_asym":       "retracting Same(c,d) does not match the equivalent Same(d,c)",
    "mech_asym":       "Tool Same validity depends on the orientation of the pair",
    "latest_wins":     "a slot takes the value of the most recently added support",
    "majority":        "a slot takes the value with the most supporting records",
    "containment":     "claims about a nested component are inherited by its container",
    "name_merge":      "hypotheses with an equal (possibly AI) name are merged automatically",
}


class Universe:
    """Finite carrier sets, the snapshot and the deterministic extractor.

    If `snap`/`mech_sup`/`mech_rel` are None they are left *uninterpreted*
    (arbitrary), which is how the general obligations quantify over every
    possible repository and every possible deterministic toolset.
    Otherwise they are given as concrete tables (challenge cases).
    """

    def __init__(self, name, comps, attrs, vals, locs, hashes,
                 snap=None, mech_sup=None, mech_rel=None):
        self.name = name

        def enum(sort, names):
            S, cs = EnumSort(f"{name}_{sort}", [f"{name}.{sort}.{n}" for n in names])
            return S, list(cs), dict(zip(names, cs))

        self.Comp, self.C, self.c = enum("Comp", comps)
        self.Attr, self.A, self.a = enum("Attr", attrs)
        self.Val, self.V, self.v = enum("Val", vals)
        self.Loc, self.L, self.l = enum("Loc", locs)
        self.Hash, self.H, self.h = enum("Hash", hashes)
        self.Src, self.SRC, self.s = enum("Src", SRC_NAMES)
        self.Kind, self.KIND, self.k = enum("Kind", KIND_NAMES)
        self.TOOL, self.AI, self.HUMAN = self.SRC
        self.SUP, self.SAME, self.DEP, self.RET = self.KIND
        self.names = {"Comp": comps, "Attr": attrs, "Val": vals,
                      "Loc": locs, "Hash": hashes}

        if snap is None:
            self._snap = Function(f"{name}_snap", self.Loc, self.Hash)
        else:
            self._snap_table = {self.l[x]: self.h[y] for x, y in snap.items()}
            self._snap = None
        if mech_sup is None:
            self._mech_sup = Function(f"{name}_mechSup", self.Loc, self.Comp,
                                      self.Attr, self.Val, BoolSort())
        else:
            self._mech_sup_table = [(self.l[a], self.c[b], self.a[c], self.v[d])
                                    for a, b, c, d in mech_sup]
            self._mech_sup = None
        if mech_rel is None:
            self._mech_rel = Function(f"{name}_mechRel", self.Loc, self.Kind,
                                      self.Comp, self.Comp, BoolSort())
        else:
            self._mech_rel_table = [(self.l[a], self.k[b], self.c[c], self.c[d])
                                    for a, b, c, d in mech_rel]
            self._mech_rel = None
        # Only used by the "containment" mutant: an arbitrary nesting relation.
        self.inside = Function(f"{name}_inside", self.Comp, self.Comp, BoolSort())

    # snap(l) = h  -- the integrity check of a citation (mechanically decidable)
    def genuine(self, loc, hsh):
        if self._snap is not None:
            return self._snap(loc) == hsh
        return Or([And(loc == l, hsh == h) for l, h in self._snap_table.items()])

    def mech_sup(self, l, c, a, v):
        if self._mech_sup is not None:
            return self._mech_sup(l, c, a, v)
        return Or([And(l == x, c == y, a == z, v == w)
                   for x, y, z, w in self._mech_sup_table] or [BoolVal(False)])

    def mech_rel(self, l, k, c, d):
        if self._mech_rel is not None:
            return self._mech_rel(l, k, c, d)
        return Or([And(l == x, k == y, c == z, d == w)
                   for x, y, z, w in self._mech_rel_table] or [BoolVal(False)])


class Rec:
    """A record (an immutable contribution).  All fields are z3 terms."""
    FIELDS = ["kind", "src", "loc", "hash", "comp", "attr", "val", "comp2",
              "tkind", "tsrc"]

    def __init__(self, **kw):
        for f in self.FIELDS:
            setattr(self, f, kw[f])
        # Not part of the model: only read by the latest_wins / atom_retract mutants.
        self.seq = kw.get("seq")
        self.tid = kw.get("tid")
        self.label = kw.get("label", "")


def free_rec(U, p):
    """A record with arbitrary (symbolic) fields."""
    return Rec(kind=Const(p + ".kind", U.Kind), src=Const(p + ".src", U.Src),
               loc=Const(p + ".loc", U.Loc), hash=Const(p + ".hash", U.Hash),
               comp=Const(p + ".comp", U.Comp), attr=Const(p + ".attr", U.Attr),
               val=Const(p + ".val", U.Val), comp2=Const(p + ".comp2", U.Comp),
               tkind=Const(p + ".tkind", U.Kind), tsrc=Const(p + ".tsrc", U.Src),
               seq=Int(p + ".seq"), tid=Int(p + ".tid"), label=p)


def retraction_of(U, r, src, label="", tid=None):
    """The retraction, issued by `src`, of the content of record r."""
    return Rec(kind=U.RET, src=src, tkind=r.kind, tsrc=r.src, loc=r.loc,
               hash=r.hash, comp=r.comp, attr=r.attr, val=r.val, comp2=r.comp2,
               seq=None, tid=tid, label=label)


class Concl:
    """Conclusions derived from one state.  Matrices are indexed by the
    positions of the carrier constants in U.C / U.A / U.V."""


class Model:
    def __init__(self, U, recs, mutants=frozenset()):
        unknown = set(mutants) - set(MUTANTS)
        assert not unknown, unknown
        self.U, self.recs, self.mut = U, recs, frozenset(mutants)

    # ---------- record-level predicates ---------------------------------
    def genuine(self, r):
        if "no_integrity" in self.mut:
            return BoolVal(True)
        return self.U.genuine(r.loc, r.hash)

    def mech_ok(self, r):
        U = self.U
        rel = U.mech_rel(r.loc, r.kind, r.comp, r.comp2)
        if "mech_asym" not in self.mut:
            # Same is an unordered relation: an extractor output Same(d,c)
            # also certifies Same(c,d).
            rel = Or(rel, And(r.kind == U.SAME,
                              U.mech_rel(r.loc, r.kind, r.comp2, r.comp)))
        return If(r.kind == U.SUP, U.mech_sup(r.loc, r.comp, r.attr, r.val), rel)

    def valid(self, r):
        """Mechanically checkable integrity of a record."""
        U = self.U
        return If(r.kind == U.RET, r.src != U.TOOL,
                  And(self.genuine(r), Implies(r.src == U.TOOL, self.mech_ok(r))))

    def firm(self, r):
        if "ai_trusted" in self.mut:
            return BoolVal(True)
        return r.src != self.U.AI

    def same_pair(self, x, y):
        """x and y designate the same claim content (ignoring src)."""
        U = self.U
        sup = And(x.comp == y.comp, x.attr == y.attr, x.val == y.val)
        ordered = And(x.comp == y.comp, x.comp2 == y.comp2)
        swapped = And(x.comp == y.comp2, x.comp2 == y.comp)
        rel = If(y.kind == U.SAME, Or(ordered, swapped), ordered)
        return If(y.kind == U.SUP, sup, rel)

    def matches(self, x, r, i):
        """Retraction x designates the content of record r (index i)."""
        U = self.U
        if "atom_retract" in self.mut:
            return And(r.kind != U.RET, x.tid == i)
        if "same_asym" in self.mut:
            pair = If(r.kind == U.SUP,
                      And(x.comp == r.comp, x.attr == r.attr, x.val == r.val),
                      And(x.comp == r.comp, x.comp2 == r.comp2))
        else:
            pair = self.same_pair(x, r)
        return And(r.kind != U.RET, x.tkind == r.kind, x.tsrc == r.src,
                   x.loc == r.loc, x.hash == r.hash, pair)

    def authority(self, x, r):
        U = self.U
        if "ai_retracts_all" in self.mut:
            return BoolVal(True)
        return Or(x.src == U.HUMAN, And(x.src == U.AI, r.src == U.AI))

    def eq(self, r, t):
        """Content equivalence of two records (the meaning of a contribution)."""
        U = self.U
        common = And(r.kind == t.kind, r.src == t.src, r.loc == t.loc,
                     r.hash == t.hash)
        target = And(r.tkind == t.tkind, r.tsrc == t.tsrc)
        # For a retraction the designated content is compared as for its tkind.
        tgt_pair = If(r.tkind == U.SUP,
                      And(r.comp == t.comp, r.attr == t.attr, r.val == t.val),
                      If(r.tkind == U.SAME,
                         Or(And(r.comp == t.comp, r.comp2 == t.comp2),
                            And(r.comp == t.comp2, r.comp2 == t.comp)),
                         If(r.tkind == U.DEP,
                            And(r.comp == t.comp, r.comp2 == t.comp2),
                            BoolVal(True))))
        return And(common, If(r.kind == U.RET, And(target, tgt_pair),
                              self.same_pair(r, t)))

    # ---------- state-level conclusions ---------------------------------
    def live(self, inS):
        recs = self.recs
        U = self.U
        out = []
        for i, r in enumerate(recs):
            defeated = Or([And(inS[j], x.kind == U.RET, self.valid(x),
                               self.matches(x, r, i), self.authority(x, r))
                           for j, x in enumerate(recs)])
            out.append(And(inS[i], r.kind != U.RET, self.valid(r), Not(defeated)))
        return out

    def _closure(self, base):
        n = len(base)
        E = [[BoolVal(True) if i == j else Or(base[i][j], base[j][i])
              for j in range(n)] for i in range(n)]
        for _ in range(max(1, ceil(log2(max(n, 2))))):
            E = [[Or(E[i][j], *[And(E[i][k], E[k][j]) for k in range(n)])
                  for j in range(n)] for i in range(n)]
        return E

    def _base(self, live, firm_only):
        U, C = self.U, self.U.C
        n = len(C)
        B = [[None] * n for _ in range(n)]
        for x in range(n):
            for y in range(n):
                terms = []
                for i, r in enumerate(self.recs):
                    lvl = self.firm(r) if firm_only else BoolVal(True)
                    terms.append(And(live[i], lvl, r.kind == U.SAME,
                                     Or(And(r.comp == C[x], r.comp2 == C[y]),
                                        And(r.comp == C[y], r.comp2 == C[x]))))
                if "name_merge" in self.mut:
                    # automatic consolidation on equal values of attribute 0 ("name")
                    for i, r in enumerate(self.recs):
                        for j, t in enumerate(self.recs):
                            terms.append(And(live[i], live[j], r.kind == U.SUP,
                                             t.kind == U.SUP, r.attr == U.A[0],
                                             t.attr == U.A[0], r.val == t.val,
                                             r.comp == C[x], t.comp == C[y]))
                B[x][y] = Or(terms)
        return B

    def concl(self, inS):
        U, recs = self.U, self.recs
        C, A, V = U.C, U.A, U.V
        nc, na, nv = len(C), len(A), len(V)
        K = Concl()
        K.live = live = self.live(inS)
        K.Ef = self._closure(self._base(live, True))
        K.Ep = self._closure(self._base(live, False))

        def scope(E, x, c):
            if "containment" in self.mut:
                return Or(E[x][c], U.inside(C[x], C[c]))
            return E[x][c]

        def about(r, E, c):
            return Or([And(r.comp == C[x], scope(E, x, c)) for x in range(nc)])

        def supp(i, firm_only, c, a, v):
            r = recs[i]
            lvl = self.firm(r) if firm_only else BoolVal(True)
            E = K.Ef if firm_only else K.Ep
            return And(live[i], lvl, r.kind == U.SUP, r.attr == A[a],
                       r.val == V[v], about(r, E, c))

        def support_set(firm_only):
            M = [[[None] * nv for _ in range(na)] for _ in range(nc)]
            for c in range(nc):
                for a in range(na):
                    for v in range(nv):
                        if "latest_wins" in self.mut:
                            M[c][a][v] = Or([And(supp(i, firm_only, c, a, v),
                                                 Not(Or([And(supp(j, firm_only, c, a, w),
                                                             recs[j].seq > recs[i].seq)
                                                         for j in range(len(recs))
                                                         for w in range(nv) if w != v])))
                                             for i in range(len(recs))])
                        else:
                            M[c][a][v] = Or([supp(i, firm_only, c, a, v)
                                             for i in range(len(recs))])
            return M

        K.F = support_set(True)
        K.P = support_set(False)

        def deps(firm_only):
            E = K.Ef if firm_only else K.Ep
            D = [[None] * nc for _ in range(nc)]
            for c in range(nc):
                for d in range(nc):
                    D[c][d] = Or([And(live[i],
                                      self.firm(r) if firm_only else BoolVal(True),
                                      r.kind == U.DEP,
                                      Or([And(r.comp == C[x], E[x][c]) for x in range(nc)]),
                                      Or([And(r.comp2 == C[y], E[y][d]) for y in range(nc)]))
                                  for i, r in enumerate(recs)])
            return D

        K.Fd, K.Pd = deps(True), deps(False)

        # ---- statuses -----------------------------------------------------
        K.est = [[[None] * nv for _ in range(na)] for _ in range(nc)]
        K.prov = [[[None] * nv for _ in range(na)] for _ in range(nc)]
        K.conf = [[None] * na for _ in range(nc)]
        K.unk = [[None] * na for _ in range(nc)]
        K.contested = [[None] * na for _ in range(nc)]
        for c in range(nc):
            for a in range(na):
                F, P = K.F[c][a], K.P[c][a]
                anyF, anyP = Or(F), Or(P)
                if "majority" in self.mut:
                    cnt = [Sum([If(supp(i, True, c, a, v), 1, 0)
                                for i in range(len(recs))]) for v in range(nv)]
                    for v in range(nv):
                        K.est[c][a][v] = And(cnt[v] > 0, *[cnt[v] > cnt[w]
                                                          for w in range(nv) if w != v])
                    no_winner = Not(Or(K.est[c][a]))
                    many_F = And(anyF, no_winner)
                else:
                    for v in range(nv):
                        K.est[c][a][v] = And(F[v], *[Not(F[w]) for w in range(nv) if w != v])
                    many_F = Or([And(F[v], F[w]) for v in range(nv) for w in range(nv) if v < w])
                many_P = Or([And(P[v], P[w]) for v in range(nv) for w in range(nv) if v < w])
                for v in range(nv):
                    K.prov[c][a][v] = And(Not(anyF), P[v],
                                          *[Not(P[w]) for w in range(nv) if w != v])
                K.conf[c][a] = Or(many_F, And(Not(anyF), many_P))
                K.unk[c][a] = Not(anyP)
                K.contested[c][a] = Or([And(K.est[c][a][v], P[w])
                                        for v in range(nv) for w in range(nv) if v != w])
        return K


# ---------- helpers on conclusions -----------------------------------------
def _flat(x):
    if isinstance(x, list):
        for y in x:
            yield from _flat(y)
    else:
        yield x


PARTS_ALL = ["Ef", "Ep", "F", "P", "Fd", "Pd", "est", "prov", "conf", "unk"]
PARTS_FIRM = ["Ef", "F", "Fd", "est"]


def concl_eq(K1, K2, parts=PARTS_ALL):
    return And([a == b for p in parts
                for a, b in zip(_flat(getattr(K1, p)), _flat(getattr(K2, p)))])


def concl_le(K1, K2, parts):
    """K1 ⊆ K2 component-wise (for monotone parts)."""
    return And([Implies(a, b) for p in parts
                for a, b in zip(_flat(getattr(K1, p)), _flat(getattr(K2, p)))])


def slot_eq(K1, K2, c, a):
    return And(And([x == y for x, y in zip(K1.est[c][a], K2.est[c][a])]),
               And([x == y for x, y in zip(K1.prov[c][a], K2.prov[c][a])]),
               K1.conf[c][a] == K2.conf[c][a], K1.unk[c][a] == K2.unk[c][a],
               And([x == y for x, y in zip(K1.F[c][a], K2.F[c][a])]),
               And([x == y for x, y in zip(K1.P[c][a], K2.P[c][a])]))

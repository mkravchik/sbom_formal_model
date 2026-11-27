# A Minimal Knowledge Model for AI-Assisted SBOM Generation

## Domain specification

This document defines the model mathematically. The executable version is
`spec/kmodel.py`, and each definition here corresponds to a function in that
file (named in brackets). Results are in `docs/REPORT.md`.

---

## 1. The idea in one paragraph

An investigation produces **contributions**, and nothing else. A contribution
is an immutable record saying "artifact *x* of the repository snapshot,
quoted with content hash *h*, supports claim *q*". Each record also says
whether it came from a deterministic tool, the AI, or a human. Retracting a
contribution is done by adding another record. The **knowledge state** is the
set of records received so far, and two states are combined by set union.
**Conclusions** are a total function of that set. There are no events, no
timestamps, no lifecycle and no "investigation complete" flag. Trust is
handled by two evaluation levels:

- The **firm** level reads only records whose correctness can be rechecked
  mechanically (Tool) or that were made by an authorised reviewer (Human).
- The **provisional** level also reads AI interpretations.

Each attribute slot of each component then gets exactly one of four statuses:
**Established**, **Provisional**, **Conflicting** or **Unknown**.

---

## 2. Carrier sets and fixed context

| Symbol | Meaning |
|---|---|
| `Loc` | locations in the repository snapshot (file, or file region) |
| `Hash` | content digests |
| `Comp` | component *hypotheses*: handles for "a logical component". Creating one costs nothing and means nothing on its own |
| `Attr` | attribute names, e.g. `name`, `license`, `declared_rev`, `available_version`, `selected_version`, `purl`, `origin` |
| `Val` | attribute values (opaque) |
| `Src = {Tool, AI, Human}` | who made a contribution |
| `Kind = {Sup, Same, Dep, Ret}` | what a contribution says |

The **fixed context** of one investigation:

- `snap : Loc → Hash` is the read-only snapshot. `genuine(l,h) :⇔ snap(l) = h`
  is decidable by re-reading the file. [`Universe.genuine`]
- `mechSup ⊆ Loc×Comp×Attr×Val` and `mechRel ⊆ Loc×Kind×Comp×Comp` are the
  output of the deterministic read-only extractors run on `snap`. They are
  recomputable. [`Universe.mech_sup`, `Universe.mech_rel`]

All general obligations treat `snap`, `mechSup` and `mechRel` as
**uninterpreted**. The results therefore hold for every repository and every
deterministic toolset within the bounds.

## 3. Records (contributions)

A record is a tuple
`r = (kind, src, loc, hash, comp, attr, val, comp2, tkind, tsrc)`.
Each kind uses only some of the fields:

| kind | reading | content fields |
|---|---|---|
| `Sup` | the cited artifact supports `comp.attr = val` | src, loc, hash, comp, attr, val |
| `Same` | the cited artifact supports "`comp` and `comp2` are the same component" | src, loc, hash, {comp, comp2} (unordered) |
| `Dep` | the cited artifact supports "`comp` depends on `comp2`" | src, loc, hash, comp, comp2 |
| `Ret` | `src` withdraws the contribution whose content is (tkind, tsrc, loc, hash, comp, attr, val, comp2) | src, tkind, tsrc + the target's content fields |

A `Ret` names the **content** it withdraws, not a record occurrence. The
mutant `atom_retract` shows why this matters: if a retraction names one
occurrence, a duplicate of the withdrawn record brings the claim back.

**Content equivalence** `r ≈ t` means equal kind and equal content fields,
with `Same` compared as an unordered pair. [`Model.eq`] Two contributions that
are content-equivalent are *the same knowledge*.

Every attribute slot `(c, a)` holds **at most one** true value. Things that
naturally have several values are encoded so that each slot has one value:

- a dependency is a separate `Dep` relation;
- several licences form one SPDX expression;
- "the version" is split into distinct attributes: *declared*, *available*
  and *selected*.

## 4. Integrity, authority, liveness

```
valid(r)  :⇔  kind r = Ret  ⇒  src r ≠ Tool                                  (tools never retract)
              kind r ≠ Ret  ⇒  genuine(loc r, hash r)
                               ∧ (src r = Tool ⇒ claim(r) ∈ mech)            (Tool claims are recomputable)
firm(r)   :⇔  src r ∈ {Tool, Human}
x ▷ r     :⇔  kind x = Ret ∧ kind r ≠ Ret ∧ tkind x = kind r ∧ tsrc x = src r
              ∧ x and r designate the same content
auth(x,r) :⇔  src x = Human  ∨  (src x = AI ∧ src r = AI)
live(S)   =   { r ∈ S | kind r ≠ Ret ∧ valid r ∧ ¬∃x∈S. valid x ∧ x ▷ r ∧ auth(x,r) }
```

`valid` is a **purely mechanical integrity check**. It says the quotation
exists in the snapshot and that a "Tool" label cannot be forged. It says
nothing about whether the claim *means* what it says. That **semantic
correctness** is carried only by the source:

- For a Tool record it is assumption A2 (the extractor is correct).
- For a Human record it is assumption A3 (the reviewer is authorised).
- For an AI record it is **never assumed**.

Retractions cannot themselves be retracted. A mistaken retraction is corrected
by adding a *new* supporting record, and that record is not covered by the old
retraction unless its content is identical.

## 5. Conclusions

The two merge relations are the equivalence closures of the live `Same`
records:

```
≡f = equivalence closure of { (comp r, comp2 r) | r ∈ live S, kind r = Same, firm r }
≡p = equivalence closure of { (comp r, comp2 r) | r ∈ live S, kind r = Same }
```

The support sets and dependency relations are:

```
F(c,a) = { val r | r ∈ live S, kind r = Sup, firm r, attr r = a, comp r ≡f c }
P(c,a) = { val r | r ∈ live S, kind r = Sup,         attr r = a, comp r ≡p c }
Fd     = { (c,d) | ∃ r ∈ live S, kind r = Dep, firm r, comp r ≡f c, comp2 r ≡f d }
Pd     = the same with ≡p and any source
```

`concl(S) = (≡f, ≡p, F, P, Fd, Pd)`. [`Model.concl`]

**Status of a slot (c, a).** These cases are exclusive and cover every slot,
as obligation O10 checks.

| status | condition | meaning |
|---|---|---|
| **Established(v)** | `F = {v}` | firmly supported, not firmly contradicted |
| **Conflicting** | `|F| ≥ 2`, or `F = ∅ ∧ |P| ≥ 2` | incompatible supported values; all are kept as candidates |
| **Provisional(v)** | `F = ∅ ∧ P = {v}` | only AI-interpreted, uncontradicted |
| **Unknown** | `P = ∅` | nothing valid supports any value |

*Contested* annotates Established(v) when `P ⊋ {v}`, meaning an AI
interpretation disagrees. It is displayed, but it does not override the firm
level. The firm level is defined without reference to AI records at all, as
obligation O3 checks.

**Export rule.** This is when a conclusion is "sufficiently supported".

- **Strict SBOM:** a value is asserted **iff** its slot is Established.
  Otherwise the slot is `NOASSERTION`, together with the reason (Provisional,
  Conflicting with its candidates, or Unknown). Components are grouped by
  `≡f`, and dependencies are taken from `Fd`.
- **Review draft:** as strict, but Provisional values and `≡p` / `Pd` links
  are shown, labelled "unreviewed AI interpretation".
- **Completeness is never asserted.** The model has no notion of "all
  components" or "finished", so no export can claim it.

## 6. Operations

```
add(S, r)  = S ∪ {r}        (any kind - including Ret - from any source)
join(S, T) = S ∪ T          (merging parallel or resumed investigations)
```

There is no delete, overwrite or "merge components" operation. Consolidation
is adding a `Same` record, and revision is adding a `Ret` record. An
interrupted investigation is just the state it had reached. Any subset of the
records of any run is a legal state.

**Consequences of the algebra.** These need no solver. `(𝒫(Rec), ∪, ∅)` is a
join-semilattice: union is idempotent, commutative and associative. So every
interleaving of the same contributions reaches the same `S`, and because
`concl` depends only on `S`, every interleaving reaches the same conclusions.
The solver checks the stronger statement O7: states that are equal *up to
content equivalence* have equal conclusions. Content equivalence covers
duplicates, re-submissions and `Same` orientation.

## 7. Invariants and obligations

For every state `S, T` (finite sets of arbitrary records), every snapshot and
every extractor:

| # | property (requirement) | formal statement |
|---|---|---|
| O1 | evidence soundness (1) | `Est(c,a,v)` ⇒ ∃ r ∈ live S, firm, `Sup`, a, v, with `comp r ≡f c`; `Prov(v)` ⇒ the same with ≡p; every merge and firm dependency is generated by live genuine records (checked against the *reference* semantics) |
| O2 | integrity (1) | adding records whose citation fails `genuine` leaves `concl` unchanged |
| O3 | interpretation ≠ establishment (1) | if `T \ S` consists only of AI records, then `≡f, F, Fd, Est` are equal in S and T |
| O4 | subject locality (1, B) | adding `Sup` records about components not `≡p`-related to c leaves every slot of c unchanged; `Sup` records never change merges or dependencies |
| O5 | slot independence (3) | adding or retracting claims on attribute a′ leaves every slot (c, a) with a ≠ a′ unchanged |
| O6 | preservation (2) | if `T \ S` contains no `Ret`, then ≡f, ≡p, F, P, Fd, Pd are ⊆-monotone, and `Est_S(v)` ⇒ `Est_T(v) ∨ (Conf_T ∧ v ∈ F_T)` |
| O7 | equivalence invariance (2) | `S ≈ T` (each record of one has a content-equivalent in the other) ⇒ `concl(S) = concl(T)` and all statuses are equal |
| O7a | duplicate insensitivity (2) | adding a record `≈` to one already in S leaves `concl` unchanged. O7 follows from O7a by induction, since S ∪ T is reached from S, and from T, one duplicate at a time. O7a is checked at a larger bound than O7 |
| O8 | precise revision (2) | for a retraction x: `concl(S ∪ {x}) = concl(S \ {r ∈ S | x ▷ r ∧ auth(x,r)})`. Retracted records remain in S (audit trail) |
| O9 | revisability (2) | the Human retraction built from r defeats exactly the records `≈ r`; an AI retraction defeats AI records |
| O10 | honest partial conclusions (3) | in every S, every slot has exactly one status; `F ⊆ P`; `≡f ⊆ ≡p` |

W1–W8 are **witness** (satisfiability) obligations. They show that the
interesting legitimate behaviours exist:

- all four statuses can occur in one state;
- transitive firm consolidation works;
- an AI merge propagates values only provisionally;
- the AI can correct itself;
- an Established value can be contested;
- a firm merge can expose a conflict;
- a human can retract a Tool fact;
- dependencies are lifted through merges.

These witnesses also rule out vacuity. In addition, every implication
obligation first checks that its hypothesis is satisfiable.

## 8. Assumptions

These are stated, not hidden.

- **A1 Snapshot.** The snapshot does not change during the investigation, and
  the hash is collision-free. Only under this assumption does `genuine` mean
  "this quotation really is in the repository".
- **A2 Extractor correctness.** A deterministic extractor emits only
  *literal* facts that its parsing semantics justifies. Examples: "this
  `FetchContent_Declare` declares `GIT_TAG abc123`", or "the LICENSE file at
  the root of hypothesis `c` has SPDX text X". The model can **check** that a
  Tool record is a recomputable extractor output. It cannot check that the
  extractor's semantics is right. This is the boundary of "mechanically
  established".
- **A3 Reviewer authority.** Human records are authoritative until a Human
  retracts them. Human errors are revisable but not detected.
- **A4 Source authentication.** The `src` label of AI and Human records is
  authentic. A Tool label is protected by A2 and `valid`; Human labels need
  authentication outside the model.
- **A5 Attribute vocabulary.** Each attribute is single-valued per
  (consolidated) component. Attributes whose meanings differ, such as
  declared, available and selected version, must be distinct attribute
  names. Case A′ shows what goes wrong otherwise.
- **A6 Hypotheses are free.** A component exists in the knowledge only
  through records that mention it.

## 9. What the model deliberately does not contain

- **No containment relation between components or locations.** Nesting is
  never a reason to attribute evidence, and the `containment` mutant shows the
  failure it would cause. Attribution to a subject happens only through an
  explicit record.
- **No inference rules** (for example "if not overridden then selected =
  declared"). A derived conclusion enters the knowledge in one of two ways:
  - as a Tool record, if a deterministic rule computes it; or
  - as an AI or Human record citing the evidence.
- **No negative evidence.** "Evidence against v" is support for an
  incompatible value of the same single-valued slot. "This evidence does not
  support the claim" is a retraction.
- **No confidence scores, votes, timestamps or lifecycle.** The `majority` and
  `latest_wins` mutants show that each of these breaks equivalence invariance.
- **No completeness.** The model never claims completeness, and nothing can
  establish it.

# Verification and Critical-Review Report

## 0. Summary

**Can a small, mathematically sound knowledge model serve as the foundation
for an AI-assisted SBOM generator?** Yes, with two qualifications. The model
in `docs/DOMAIN.md` has the following parts:

- **records:** 7 carrier sets and 4 record kinds;
- **state:** a set of records;
- **operation:** one operation, set union;
- **conclusions:** one total function from a state to its conclusions;
- **statuses:** 4 per attribute slot.

All ten essential-property obligations, together with the O7a lemma, hold
within the stated bounds, for every repository snapshot and every
deterministic toolset. Every witness of legitimate behaviour exists. All
10 deliberately wrong designs are rejected by at least one obligation. All
challenge cases A–E behave as intended, including their negative controls.

The two qualifications are:

1. **The model only bounds the damage AI interpretations can do.** It cannot
   make them correct. An AI interpretation never becomes Established without
   one of two things:
   - a deterministic extractor output, or
   - a reviewer.

   How useful the strict SBOM is therefore depends on extractor coverage and
   review effort. The model cannot settle that.
2. **The meaning of "mechanically established" is only as good as the
   extractor contracts** (assumption A2) **and the attribute vocabulary** (A5).
   These are the highest-risk design items for the generator. They are not
   formal-model problems.

Section 5 lists the remaining unresolved problems.

---

## 1. Choice of formalism and tool

| considered | outcome |
|---|---|
| Alloy 6, whose relational, small-scope, counterexample-driven style is the best fit | could not be used: downloading the Alloy distribution was not permitted in the execution environment |
| TLA+/TLC | the model has no essential temporal behaviour (see §2.3), so a state-machine checker adds nothing |
| **SMT (z3, via `z3-solver` from PyPI)** | **used** |

The specification is written with the z3 Python API. Every carrier set is a
finite enumerated sort. Every quantifier over records, components, attributes
or values is expanded explicitly, so every query is a quantifier-free SMT
problem. Each check is therefore decidable and complete within its bound:
`unsat` means "no counterexample exists in the bound", and `sat` comes with a
concrete state.

The snapshot `snap` and the extractor outputs `mechSup` and `mechRel` are
uninterpreted functions. The solver therefore quantifies over all of them, and
they hide no semantics. `run_all.py --smt2 DIR` exports each obligation as
SMT-LIB2, so another solver can check it independently.

## 2. Model recap and the key design decisions

The full definitions are in `docs/DOMAIN.md`. This section covers the
decisions that matter most for the requirements.

### 2.1 Integrity versus semantic correctness

**Integrity** is decidable, and the model checks it:

- the quotation exists: `snap(loc) = hash`;
- a record labelled Tool is a recomputable extractor output.

**Semantic correctness** depends on the source:

| source | basis for semantic correctness |
|---|---|
| Tool | assumption A2 |
| Human | assumption A3 |
| AI | never assumed |

The firm level, which produces **Established**, does not read AI records at
all (O3). A genuine citation therefore only makes an interpretation
*Provisional* (case C). The distinction is structural, not a matter of
confidence scores.

### 2.2 Order and duplicates are not modelled at all

A state is a set of content-addressed records, and conclusions are a function
of that set. Order independence and idempotence are consequences of the
set-union algebra. O7 and O7a then verify the non-trivial part: conclusions
respect *content* equivalence. Content equivalence covers duplicates,
re-submissions and the unordered `Same` pair.

### 2.3 Revision without destruction

Retraction is a record that names a *content*, so nothing is ever deleted.
O8 proves that adding a retraction is the same as deleting exactly the
records it defeats. The retracted evidence stays in the state as an audit
trail.

Retractions cannot be retracted. **This is forced, not chosen.** Suppose a
later re-assertion of the same content could revive it. Then the result of
{assert, retract, assert} would depend on the order of arrival, and O7 would
fail; the `latest_wins` mutant shows this. A wrong retraction is corrected by
new content, meaning a different citation or a different source.

### 2.4 Subjects are explicit

Evidence attaches to a component only through a record naming that
component. Nesting of directories plays no role, and there are no inference
rules. Information crosses between component hypotheses only through
explicit `Same` records:

- a firm `Same` propagates firmly;
- an AI `Same` propagates only provisionally.

## 3. Verification results

These are the actual results of `python3 spec/run_all.py`. The full output,
with witness states and mutant counterexamples, is in
`results/verification_results.md`.

RESULTS_PLACEHOLDER

### 3.1 Verification bounds

| check | bound |
|---|---|
| reference obligations O1–O6, O7a, O8–O10, witnesses | 3 components, 2 attributes, 3 values, 2 locations, 2 hashes, **6 arbitrary records**, and for two-state obligations two arbitrary states over them, whose records are otherwise unconstrained |
| O7 (two arbitrary states compared through content equivalence) | the same, with 4 records. O7 also follows from O7a (6 records) by induction, as argued in DOMAIN §7 |
| mutants | 3 / 2 / 2 / 2 / 2, with 4 records |
| challenge cases | concrete snapshots, plus **3 additional arbitrary AI records** (every field free) for each "never" check |

What these bounds cover:

- **Merges:** 3 components and up to 6 records are enough for transitive
  merge chains (W2), merge-exposed conflicts (W6) and lifted dependencies
  (W8).
- **Values:** 3 values allow a conflict next to a third, unrelated value.
- **Retractions:** 6 records allow, for example, a duplicate, its
  retraction, and an interaction with a merge, all in one counterexample.

All design defects seeded as mutants are found with at most 4 records.
Section 5 explains why larger bounds are unlikely to reveal new behaviour,
but that argument is not mechanically checked.

### 3.2 What the challenge cases show

- **A — Conditional version.** The three version notions are different
  slots: `declared_rev`, `available_version` and `selected_version`.
  - The declared default `abc123` and the existence of an override are Tool
    facts.
  - `1.0.0` is a fact about the *checkout* hypothesis. It reaches the
    declaration only after a justified consolidation.
  - `selected_version` stays Unknown. The naive AI inference "default =
    selected" is only Provisional.
  - *Negative controls:*
    - Even with arbitrary additional AI records, no state establishes
      `selected_version`.
    - Under `ai_trusted` it can be established.
    - A′: conflating the notions into a single `version` slot turns two true
      facts into a spurious conflict.
- **B — Nested components.** Two investigation orders, Infra first and
  GoogleTest first, give identical tables.
  - GoogleTest's identity and licence never become Established for Infra,
    whatever arbitrary AI records are added.
  - An AI misattribution of the nested LICENSE is at most Provisional, is
    revisable, and its retraction leaves GoogleTest's licence untouched.
  - *Negative control:* under the `containment` mutant ("files under a
    component are about it"), GoogleTest's licence becomes Established for
    Infra from Tool facts alone.
- **C — Incorrect interpretation.** A README that mentions zlib is a genuine
  citation, but "Foo = zlib" is only Provisional.
  - A forged quotation is inert.
  - A reviewer or the AI itself can retract the claim. The AI cannot retract
    a Tool fact.
  - The mention can still be recorded as the *dependency* it actually
    supports.
  - *Negative controls:* `ai_trusted` establishes zlib, and `no_integrity`
    accepts the forged quote.
  - *Limitation, shown as reachable:* §5.3.
- **D — Revised association.**
  - An AI `Same` propagates the licence only provisionally. A reviewer's
    `Same` establishes it.
  - A merge citing forged evidence has no effect.
  - A wrong AI merge cannot disturb any Established value.
  - Retracting the wrong merge restores the previous table exactly, and
    every record remains.
  - Retracting the justified merges splits the hypotheses again,
    independently of the orientation of `Same`.
  - *Negative control:* `name_merge` (automatic consolidation on equal names)
    lets an AI name guess establish a merged licence.
- **E — Interrupted investigation.** The state after the crash gives
  `name = Provisional(libfoo)`, `version = Provisional(2.3)` and
  `license = Unknown`.
  - A garbled partial answer is inert.
  - The strict export asserts nothing and gives reasons. The review draft
    shows the qualified values. Neither asserts completeness.
  - At every interruption point of the full run, every Established fact
    persists in all later prefixes.
  - No AI continuation establishes the licence.
  - Non-retracting continuations cannot erase the identity candidate. An
    explicit AI self-retraction can, and that is the intended revisability.

### 3.3 Counterexamples found during development, and refinements

Development counterexamples are listed here exactly as they happened.

1. **Case D, merge-exposed conflict (my expectation was wrong).** I expected
   the consolidation H1~H2 to make the name Conflicting{gtest, googletest}.
   The model reported `Established(googletest) (contested)`, because "gtest"
   came from the AI and the firm level dominates.
   - Investigation showed this is the intended semantics: an AI alias must
     not demote a mechanical fact.
   - The expectation was corrected. A *firm* conflict exposed by a merge is
     covered by witness W6.
2. **Case E, an over-strong negative control (my claim was false).** "No AI
   continuation can erase the identity candidate" is satisfiable: the AI may
   retract its own provisional interpretation.
   - Refined into two checks: non-retracting continuations cannot erase it
     (UNSAT), and self-retraction can (SAT).
   - This makes the precise preservation guarantee explicit:
     *Provisional knowledge is preserved against everything except an
     explicit, authorised retraction of that content.*
3. **O7 cost.** At 5 records, O7 (comparing two arbitrary states) did not
   finish within about 20 minutes.
   - It was refined into the inductive core O7a (adding one duplicate), which
     takes seconds at 6 records.
   - O7 is kept at 4 records as a direct cross-check.
   - Every order and duplicate mutant is caught by O7a as well.
4. **Defects anticipated during design, kept as regression controls.** Three
   risks were identified before running the verifier and built into the
   model from the start:
   - retracting an *occurrence* instead of a content;
   - a retraction of `Same(c,d)` not matching `Same(d,c)`;
   - Tool validity of `Same` depending on orientation.

   They are therefore **not** claimed as verifier discoveries. They are
   encoded as mutants, and the verifier confirms each would break O7/O7a or
   O9 (table above).

No counterexample to any obligation was found on the final reference model.

## 4. Critical review for unnecessary complexity

### 4.1 Removed during design, because no essential property needed it

| concept | why it is not needed |
|---|---|
| separate *observation* records | the citation `(loc, hash)` is itself verifiable evidence |
| support/contradiction polarity, and "functional attribute" flags | every slot is single-valued, so contradiction is support for another value, and "does not support" is a retraction |
| a containment relation | it is not needed, and using it for attribution is exactly the B failure (`containment` mutant) |
| confidence, votes, timestamps | they break equivalence invariance (`majority` and `latest_wins` mutants) |
| a lifecycle or "investigation complete" flag | conclusions are total for every state (O10), and completeness is never asserted |
| inference rules (e.g. default ⇒ selected) | a deterministic rule is an extractor (Tool record), and anything else is an interpretation (AI or Human record) |
| required-field lists per component | Unknown already makes every unresolved slot explicit |
| retractable retractions | forced out by order independence (§2.3) |

### 4.2 What remains, and whether each part is necessary

| element | needed for | could it go? |
|---|---|---|
| Tool / AI / Human sources | distinguishing mechanical, interpreted and reviewed knowledge (1); revising Tool facts (2) | no: with two sources either nothing AI-found could ever be established, or Tool facts could not be revised |
| firm and provisional levels | "an interpretation is not correct because it cites genuine evidence" (1, C) | no |
| `Same` and two equivalence closures | revisable consolidation (D) | no |
| `Dep` | component relationships, from the product context | yes, for the essential properties alone, but the SBOM needs it; its semantics is minimal: lifted modulo merges, with no conflicts |
| AI authority to retract AI records | AI self-correction without a human (unattended runs) | **optional**: removing it costs one disjunct and loses W4; humans would remain the only revisers |
| `contested` | display only | **optional**: it is derived and carries no state |
| `Loc` × `Hash` | an executable, non-axiomatic integrity check | it could be merged into an abstract `genuine` predicate, but that would hide a decidable check inside an undefined predicate |

The critique found nothing else to remove.

## 5. Limitations and unresolved problems

### 5.1 Not mechanically established

- **Unbounded validity.** Every result holds within the bounds of §3.1.

  An informal argument that the bounds are adequate: every obligation is
  *local*. Its violation needs a few witness records. These are:
  - the added or duplicated record;
  - the records it defeats, duplicates or connects;
  - a merge path, whose length is bounded by the number of components.

  On that basis I expect no new behaviour at larger bounds. This argument is
  a hand argument, not a proof. A Lean or Isabelle formalisation of
  O3/O7a/O8 over arbitrary finite sets would close the gap; the definitions
  are directly transferable.
- **Semantic correctness of AI interpretations.** It is never decided, and
  only isolated (O3).
- **Extractor correctness (A2), reviewer correctness (A3) and source
  authentication (A4).** These are assumptions. The model checks only that a
  Tool record is a recomputable extractor output.
- **Completeness.** It is unknowable. The model never claims it.

### 5.2 Remaining semantic problems for the generator

These are in the extractor contracts and the vocabulary, not in the model.

- **Extractor contracts (A2).** Example: "the LICENSE at the root of
  hypothesis c". Contracts like this need the *roots* of component
  hypotheses to be mechanically defined, for instance a directory with its
  own `project()`. If an extractor is wrong, the result is a wrong
  *Established* value. This is the main remaining trust risk.
- **Attribute vocabulary (A5).** Distinct meanings need distinct slots, as
  case A′ shows. Choosing a vocabulary that is both complete and
  non-conflating is design work.
- **Value normalisation.** Values are compared syntactically. For example,
  `BSD-3-Clause` against `BSD 3-Clause`, or `v1.0.0` against `1.0.0`, gives a
  spurious conflict unless an extractor normalises the value
  deterministically.
- **Wrong merges.** A merge of hypotheses with different firm values becomes
  an honest Conflict. The model cannot say whether the merge or a value is
  wrong.
- **Odd or incomplete dependency results.** Merging a dependency's endpoints
  produces a self-loop. The model also cannot express that a dependency is
  *absent*.

### 5.3 Known gap: reviewer rejection is per evidence link, not per claim

Case C has a reachable check for this. After a reviewer retracts "README ⇒
Foo = zlib", the AI can raise "Foo = zlib" again as Provisional by citing
different evidence. It can never make it Established.

The review draft can therefore be flooded with re-raised misinterpretations,
although the strict SBOM cannot. The reviewer's workaround is a firm record
for the correct value, after which the claim is only "contested". But if the
truth is unknown, "Foo is *not* zlib" cannot be expressed.

A possible extension is a Human claim-level veto: a `Ret` whose evidence
fields are wildcards. Because the veto is a monotone Human-only record, I
expect it to keep O3–O8. It has not been added or verified.

### 5.4 Out of scope

- **Knowledge across repository revisions.** The snapshot is fixed (A1).
  Moving to a new revision would make every record whose cited file changed
  automatically invalid, and so inert. That behaviour is a plausible basis
  for incremental re-investigation, but it is not verified.

## 6. Feasibility recommendation

**Recommended as the core of the generator.** The verified part is small and
robust:

- an append-only, content-addressed record set;
- union as the only operation;
- a pure, total conclusion function with two trust levels and four statuses.

It supports interruption, parallel and resumed investigations (union),
idempotent retries, AI self-correction and human review without any
lifecycle. AI errors stay confined to the review draft: they never establish,
defeat or erase firm conclusions.

Suggested next steps, in order of risk:

1. Specify the extractor contracts and the attribute vocabulary (A2, A5),
   including value normalisation and how component roots are defined. Every
   extractor output must be literal and recomputable.
2. Decide whether a claim-level reviewer veto (§5.3) is needed, and verify
   it as an extension with the existing obligations.
3. Implement `concl` as a pure function. Use this specification as a
   test oracle, for example by property-based tests comparing the
   implementation with the z3 model on random small states.
4. Measure, on real repositories, what fraction of SBOM slots extractors can
   establish and how much review effort is left. This is the decisive
   *practical* feasibility question, and the formal model cannot answer it.

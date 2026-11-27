# Verification results

z3 5.4.1, python 3.13.18

## 1. Obligations on the reference model (|Comp|=3 |Attr|=2 |Val|=3 |Loc|=2 |Hash|=2 records=6)

| obligation | result | time |
|---|---|---|
| O1 evidence soundness (traceable genuine support) | HOLDS | 0.0s |
| O2 fabricated evidence is inert | HOLDS | 3.5s |
| O3 AI interpretations never establish or defeat firm conclusions | HOLDS | 0.8s |
| O4 evidence about one component does not establish another | HOLDS | 58.3s |
| O5 slots are independent | HOLDS | 70.8s |
| O6 accumulation never silently destroys knowledge | HOLDS | 5.4s |
| O7 equivalent knowledge yields equal conclusions | HOLDS | 20.5s |
| O7a adding a duplicate contribution changes nothing | HOLDS | 10.3s |
| O8 retraction is precise (as-if-absent) | HOLDS | 3.7s |
| O9 every contribution is revisable | HOLDS | 0.0s |
| O10 every slot has exactly one honest status | HOLDS | 0.3s |

## 2. Witnesses: legitimate states and operations exist (|Comp|=3 |Attr|=2 |Val|=3 |Loc|=2 |Hash|=2 records=6)

| witness | result | time |
|---|---|---|
| W1 one state shows all four statuses | WITNESSED | 0.2s |
| W2 firm consolidation via a chain (transitivity) | WITNESSED | 0.2s |
| W3 provisional (AI) merge propagates a value provisionally | WITNESSED | 0.2s |
| W4 AI self-correction: Provisional -> Unknown by an AI retraction | WITNESSED | 0.3s |
| W5 Established value contested by an AI claim (firm dominance) | WITNESSED | 0.2s |
| W6 firm merge exposes a conflict | WITNESSED | 0.2s |
| W7 human retraction of a Tool fact revises an Established value | WITNESSED | 0.2s |
| W8 dependency lifted through a firm merge | WITNESSED | 0.3s |

<details><summary>witness states</summary>

W1 one state shows all four statuses:
```
      r0: Sup  src=Human c1.a1=v0                     cite=l1/h1 genuine=True  in S
      r2: Same src=AI    c0~c1                        cite=l0/h0 genuine=True  in S
      r3: Sup  src=AI    c0.a0=v2                     cite=l0/h0 genuine=True  in S
      r4: Sup  src=Human c0.a0=v0                     cite=l0/h0 genuine=True  in S
```
W2 firm consolidation via a chain (transitivity):
```
      r1: Same src=Tool  c1~c0                        cite=l1/h1 genuine=True  in S
      r3: Same src=Tool  c1~c2                        cite=l0/h0 genuine=True  in S
```
W3 provisional (AI) merge propagates a value provisionally:
```
      r0: Same src=AI    c1~c2                        cite=l1/h0 genuine=True  in S
      r2: Sup  src=Tool  c1.a0=v2                     cite=l1/h0 genuine=True  in S
      r4: Same src=AI    c2~c0                        cite=l1/h0 genuine=True  in S
```
W4 AI self-correction: Provisional -> Unknown by an AI retraction:
```
      r1: Same src=AI    c2~c0                        cite=l1/h1 genuine=True  in S,T
      r3: Sup  src=Human c2.a0=v0                     cite=l1/h1 genuine=True  in S,T
      r5: Ret  src=AI    retract[AI Same c2/a0/v1/c0] cite=l1/h1 genuine=True  in T
```
W5 Established value contested by an AI claim (firm dominance):
```
      r1: Sup  src=Tool  c1.a0=v0                     cite=l1/h1 genuine=True  in S
      r3: Same src=AI    c0~c1                        cite=l1/h1 genuine=True  in S
      r4: Sup  src=Tool  c0.a0=v2                     cite=l0/h0 genuine=True  in S
```
W6 firm merge exposes a conflict:
```
      r1: Sup  src=Human c0.a0=v2                     cite=l1/h0 genuine=True  in S,T
      r3: Sup  src=Human c1.a0=v0                     cite=l0/h0 genuine=True  in S,T
      r4: Same src=Human c1~c0                        cite=l1/h0 genuine=True  in T
      r5: Sup  src=Human c1.a0=v0                     cite=l1/h0 genuine=True  in S,T
```
W7 human retraction of a Tool fact revises an Established value:
```
      r0: Dep  src=Human c0->c1                       cite=l1/h0 genuine=False  in S,T
      r3: Sup  src=Human c0.a0=v1                     cite=l1/h1 genuine=True  in S,T
      r5: Ret  src=Human retract[Human Sup c0/a0/v1/c0] cite=l1/h1 genuine=True  in T
```
W8 dependency lifted through a firm merge:
```
      r2: Same src=Tool  c2~c0                        cite=l1/h0 genuine=True  in S
      r4: Dep  src=Human c2->c0                       cite=l1/h0 genuine=True  in S
```
</details>

## 3. Mutants: wrong designs must be rejected (|Comp|=3 |Attr|=2 |Val|=2 |Loc|=2 |Hash|=2 records=4)

| mutant | design error | violated obligations | detected |
|---|---|---|---|
| `ai_trusted` | AI interpretations count as firm (established) support | O1 COUNTEREXAMPLE, O3 COUNTEREXAMPLE | yes |
| `no_integrity` | citations are not checked against the snapshot | O1 COUNTEREXAMPLE, O2 COUNTEREXAMPLE | yes |
| `ai_retracts_all` | an AI retraction can defeat Tool and Human records | O3 COUNTEREXAMPLE | yes |
| `atom_retract` | a retraction removes one record occurrence, not a content | O1 COUNTEREXAMPLE, O5 COUNTEREXAMPLE, O7 COUNTEREXAMPLE, O7a COUNTEREXAMPLE, O9 COUNTEREXAMPLE | yes |
| `same_asym` | retracting Same(c,d) does not match the equivalent Same(d,c) | O1 COUNTEREXAMPLE, O7 COUNTEREXAMPLE, O7a COUNTEREXAMPLE, O9 COUNTEREXAMPLE | yes |
| `mech_asym` | Tool Same validity depends on the orientation of the pair | O7 COUNTEREXAMPLE, O7a COUNTEREXAMPLE | yes |
| `latest_wins` | a slot takes the value of the most recently added support | O6 COUNTEREXAMPLE, O7 COUNTEREXAMPLE, O7a COUNTEREXAMPLE, O10 COUNTEREXAMPLE | yes |
| `majority` | a slot takes the value with the most supporting records | O6 COUNTEREXAMPLE, O7 COUNTEREXAMPLE, O7a COUNTEREXAMPLE | yes |
| `containment` | claims about a nested component are inherited by its container | O1 COUNTEREXAMPLE, O4 COUNTEREXAMPLE | yes |
| `name_merge` | hypotheses with an equal (possibly AI) name are merged automatically | O1 COUNTEREXAMPLE, O3 COUNTEREXAMPLE, O4 COUNTEREXAMPLE, O5 COUNTEREXAMPLE | yes |

<details><summary>first counterexample per mutant</summary>

`ai_trusted` violates O1 evidence soundness (traceable genuine support):
```
      r2: Same src=AI    c2~c1                        cite=l1/h1 genuine=True  in S
```
`no_integrity` violates O1 evidence soundness (traceable genuine support):
```
      r2: Sup  src=Human c1.a0=v1                     cite=l0/h1 genuine=False  in S
```
`ai_retracts_all` violates O3 AI interpretations never establish or defeat firm conclusions:
```
      r0: Sup  src=Human c0.a1=v1                     cite=l1/h0 genuine=True  in S,T
      r1: Ret  src=AI    retract[Human Sup c0/a1/v1/c2] cite=l1/h0 genuine=True  in T
      r2: Same src=Human c0~c2                        cite=l1/h0 genuine=True  in S,T
      r3: Same src=Human c0~c2                        cite=l1/h0 genuine=True  in S,T
```
`atom_retract` violates O1 evidence soundness (traceable genuine support):
```
      r1: Same src=Tool  c2~c0                        cite=l1/h1 genuine=True tid=0  in S
      r2: Ret  src=Human retract[Tool Same c0/a0/v0/c2] cite=l1/h1 genuine=True tid=4  in S
```
`same_asym` violates O1 evidence soundness (traceable genuine support):
```
      r0: Sup  src=Tool  c0.a1=v1                     cite=l1/h1 genuine=True  in S
      r1: Ret  src=Human retract[Human Same c2/a0/v0/c0] cite=l1/h1 genuine=True  in S
      r2: Same src=Human c0~c2                        cite=l1/h1 genuine=True  in S
      r3: Same src=Tool  c1~c2                        cite=l1/h1 genuine=True  in S
```
`mech_asym` violates O7 equivalent knowledge yields equal conclusions:
```
      r0: Same src=Tool  c0~c2                        cite=l1/h1 genuine=True  in S
      r1: Same src=Human c1~c2                        cite=l1/h1 genuine=True  in S,T
      r2: Same src=Tool  c2~c0                        cite=l1/h1 genuine=True  in T
```
`latest_wins` violates O6 accumulation never silently destroys knowledge:
```
      r0: Sup  src=Tool  c1.a1=v1                     cite=l0/h1 genuine=True seq=0  in S,T
      r1: Same src=Tool  c1~c0                        cite=l1/h0 genuine=True seq=0  in S,T
      r2: Dep  src=Tool  c1->c1                       cite=l1/h0 genuine=True seq=0  in T
      r3: Sup  src=Tool  c1.a1=v0                     cite=l1/h0 genuine=True seq=2  in T
```
`majority` violates O6 accumulation never silently destroys knowledge:
```
      r0: Dep  src=Tool  c2->c2                       cite=l1/h1 genuine=False  in T
      r1: Sup  src=Human c2.a1=v1                     cite=l1/h0 genuine=True  in T
      r2: Sup  src=Human c2.a1=v0                     cite=l0/h0 genuine=True  in S,T
      r3: Sup  src=Human c2.a1=v1                     cite=l0/h0 genuine=True  in T
```
`containment` violates O1 evidence soundness (traceable genuine support):
```
      r3: Sup  src=Tool  c2.a0=v1                     cite=l1/h0 genuine=True  in S
```
`name_merge` violates O1 evidence soundness (traceable genuine support):
```
      r0: Sup  src=Human c1.a0=v1                     cite=l0/h0 genuine=True  in S
      r3: Sup  src=Human c2.a0=v1                     cite=l0/h0 genuine=True  in S
```
</details>

## 4. Challenge cases (adversary = up to 3 arbitrary AI records)

### A conditional version

- state: mechanical facts only
```
      gtestDecl  declared_rev=Established(abc123); overridable=Established(yes); available_version=Unknown; selected_version=Unknown
      gtestCheckout declared_rev=Unknown; overridable=Unknown; available_version=Established(1.0.0); selected_version=Unknown
```
- PASS [expect] declared default revision is a mechanical fact — gtestDecl.declared_rev = Established(abc123) (expected Established(abc123))
- PASS [expect] existence of an optional override is a mechanical fact — gtestDecl.overridable = Established(yes) (expected Established(yes))
- PASS [expect] checkout version is a fact about the checkout — gtestCheckout.available_version = Established(1.0.0) (expected Established(1.0.0))
- PASS [expect] selected version is unknown (override value unobservable) — gtestDecl.selected_version = Unknown (expected Unknown)
- PASS [expect] checkout version is NOT attributed to the declaration before consolidation — gtestDecl.available_version = Unknown (expected Unknown)
- PASS [expect] AI 'selected = default' stays an unreviewed interpretation — gtestDecl.selected_version = Provisional(abc123) (expected Provisional(abc123))
- PASS [expect] two incompatible AI selections are a visible conflict — gtestDecl.selected_version = Conflicting{abc123,1.0.0} (expected Conflicting{abc123,1.0.0})
- state: after human-justified consolidation
```
      gtestDecl  declared_rev=Established(abc123); overridable=Established(yes); available_version=Established(1.0.0); selected_version=Unknown
      gtestCheckout declared_rev=Established(abc123); overridable=Established(yes); available_version=Established(1.0.0); selected_version=Unknown
```
- PASS [expect] after consolidation: available 1.0.0 ... — gtestDecl.available_version = Established(1.0.0) (expected Established(1.0.0))
- PASS [expect] ... declared stays abc123 (no false conflict: distinct slots) — gtestDecl.declared_rev = Established(abc123) (expected Established(abc123))
- PASS [expect] ... and selected is still Unknown — gtestDecl.selected_version = Unknown (expected Unknown)
- PASS [never] selected version can never be Established by AI reasoning — UNSAT in 0.0s with 3 free AI records
- PASS [never] selected version cannot be Established by AI even under the naive AI claim — UNSAT in 0.0s with 3 free AI records
- PASS [never] no AI contribution can change the declared revision — UNSAT in 0.0s with 3 free AI records
- PASS [mutant] [mutant ai_trusted] selected version becomes Established — SAT in 0.0s with 3 free AI records under mutant ['ai_trusted']
- PASS [expect] [negative control] one 'version' slot turns two true facts into a spurious conflict — gtestDecl.version = Conflicting{abc123,1.0.0} (expected Conflicting{abc123,1.0.0})

### B nested components

- state: Infra-first investigation (with an AI misattribution)
```
      Infra      name=Established(infra); license=Provisional(BSD-3-Clause)
      GoogleTest name=Established(googletest); license=Established(BSD-3-Clause)
```
- PASS [expect] discovery order does not matter (Infra-first == GoogleTest-first)
- PASS [expect] GoogleTest license is GoogleTest's — GoogleTest.license = Established(BSD-3-Clause) (expected Established(BSD-3-Clause))
- PASS [expect] Infra identity is not GoogleTest's — Infra.name = Established(infra) (expected Established(infra))
- PASS [expect] nested LICENSE attributed to Infra is only an unreviewed AI claim — Infra.license = Provisional(BSD-3-Clause) (expected Provisional(BSD-3-Clause))
- PASS [expect] without the AI claim, Infra's license is honestly Unknown — Infra.license = Unknown (expected Unknown)
- PASS [expect] reviewer retracts the misattribution -> Unknown — Infra.license = Unknown (expected Unknown)
- PASS [expect] ... GoogleTest's license is unaffected by that retraction — GoogleTest.license = Established(BSD-3-Clause) (expected Established(BSD-3-Clause))
- PASS [expect] dependency Infra -> GoogleTest is established
- PASS [expect] Infra and GoogleTest are NOT consolidated
- PASS [never] GoogleTest's license can never become Established for Infra by AI contributions — UNSAT in 0.0s with 3 free AI records
- PASS [never] GoogleTest's identity can never become Established for Infra by AI contributions — UNSAT in 0.0s with 3 free AI records
- PASS [mutant] [mutant containment] GoogleTest license becomes Established for Infra from Tool facts — SAT in 0.0s with 3 free AI records under mutant ['containment']

### C incorrect interpretation

- PASS [expect] genuine citation, unjustified identity: only Provisional — Foo.name = Provisional(zlib) (expected Provisional(zlib))
- PASS [expect] citation failing the integrity check is inert — Foo.name = Unknown (expected Unknown)
- PASS [expect] reviewer retracts the identity claim -> Unknown — Foo.name = Unknown (expected Unknown)
- PASS [expect] AI may retract its own wrong interpretation — Foo.name = Unknown (expected Unknown)
- PASS [expect] mechanical identity dominates the wrong AI claim (shown as contested) — Foo.name = Established(foo) (contested) (expected Established(foo) (contested))
- PASS [expect] AI cannot retract a mechanical fact — Foo.name = Established(foo) (expected Established(foo))
- PASS [expect] the README mention survives as a provisional dependency Foo -> Zlib
- PASS [never] 'zlib' can never be an Established identity of Foo through AI contributions — UNSAT in 0.0s with 3 free AI records
- PASS [reachable] [limitation] after a reviewer rejects the README link, the AI can re-raise zlib as Provisional by citing other evidence — SAT in 0.0s with 3 free AI records
- PASS [never] ... but never as Established — UNSAT in 0.0s with 3 free AI records
- PASS [mutant] [mutant ai_trusted] the README mention establishes Foo = zlib — SAT in 0.0s with 3 free AI records under mutant ['ai_trusted']
- PASS [mutant] [mutant no_integrity] a forged quote yields a Provisional identity — SAT in 0.0s with 3 free AI records under mutant ['no_integrity']

### D revised component association

- PASS [expect] before consolidation H1's license is Unknown — H1.license = Unknown (expected Unknown)
- PASS [expect] AI consolidation propagates only provisionally — H1.license = Provisional(BSD-3-Clause) (expected Provisional(BSD-3-Clause))
- state: after human-justified consolidation H1~H2
```
      H1         name=Established(googletest) (contested); license=Established(BSD-3-Clause)
      H2         name=Established(googletest) (contested); license=Established(BSD-3-Clause)
      Infra      name=Established(infra); license=Established(MIT)
```
- PASS [expect] justified consolidation establishes the shared license — H1.license = Established(BSD-3-Clause) (expected Established(BSD-3-Clause))
- PASS [expect] the firm project name dominates the AI's alias 'gtest' (kept visible as contested) — H1.name = Established(googletest) (contested) (expected Established(googletest) (contested))
- PASS [expect] merge citing forged evidence has no effect
- PASS [expect] wrong AI merge cannot override Infra's established license — Infra.license = Established(MIT) (contested) (expected Established(MIT) (contested))
- PASS [expect] ... nor H1's — H1.license = Established(BSD-3-Clause) (contested) (expected Established(BSD-3-Clause) (contested))
- PASS [expect] retracting the wrong merge restores the previous conclusions exactly
- PASS [expect] retraction keeps every record (evidence preserved)
- PASS [expect] undoing the justified merge splits the hypotheses again — H1.license = Unknown (expected Unknown)
- PASS [expect] consolidation is symmetric: retracting Same(H2,H1) undoes Same(H1,H2) — H1.license = Unknown (expected Unknown)
- PASS [never] AI contributions can never establish a merge-derived value for H1 without a firm merge — UNSAT in 0.0s with 3 free AI records
- PASS [never] AI contributions can never move Infra off its MIT license — UNSAT in 0.0s with 3 free AI records
- PASS [mutant] [mutant name_merge] an AI name guess consolidates H1 and H2 firmly — SAT in 0.0s with 3 free AI records under mutant ['name_merge']

### E interrupted investigation

- state: interrupted state
```
      LibFoo     name=Provisional(libfoo); version=Provisional(2.3); license=Unknown
```
- state: strict export of the interrupted state
```
      completeness: NOT ASSERTED
      LibFoo: name: NOASSERTION (Provisional(libfoo)), version: NOASSERTION (Provisional(2.3)), license: NOASSERTION (Unknown)
```
- state: review draft of the interrupted state
```
      completeness: NOT ASSERTED
      LibFoo: name: libfoo [UNREVIEWED AI INTERPRETATION], version: 2.3 [UNREVIEWED AI INTERPRETATION], license: NOASSERTION (Unknown)
```
- PASS [expect] identity preserved (qualified) — LibFoo.name = Provisional(libfoo) (expected Provisional(libfoo))
- PASS [expect] version preserved (qualified) — LibFoo.version = Provisional(2.3) (expected Provisional(2.3))
- PASS [expect] license explicitly unresolved — LibFoo.license = Unknown (expected Unknown)
- PASS [expect] at every interruption point Established facts persist in later prefixes
- PASS [expect] completed run: version mechanically established — LibFoo.version = Established(2.3) (expected Established(2.3))
- PASS [expect] completed run: name human-confirmed — LibFoo.name = Established(libfoo) (expected Established(libfoo))
- PASS [expect] completed run: license remains an AI interpretation — LibFoo.license = Provisional(LGPL-2.1) (expected Provisional(LGPL-2.1))
- PASS [never] no AI continuation can Establish the license — UNSAT in 0.0s with 3 free AI records
- PASS [never] no non-retracting AI continuation (e.g. failing license attempts) can erase the identity candidate — UNSAT in 0.0s with 3 free AI records
- PASS [reachable] an explicit AI self-retraction CAN remove the AI identity candidate — SAT in 0.0s with 3 free AI records

## Summary: ALL CHECKS PASSED (total 443s)

# Reviewer Audit Questions

## Purpose and scope

This worksheet turns the repository's major mathematical, checker, complexity, and publication claims into explicit audit tasks.

For each claim it records:

- the claim being made;
- where the claim appears;
- the theorem, file, function, or artefact intended to support it;
- a concrete inspection or test path;
- what would count as a refutation or material defect.

The worksheet is not evidence that any claim is correct. It is a map for producing independent evidence or a precise counterexample.

## Pinned release coordinates

Use these immutable coordinates when auditing the recorded 7072f8d release:

```text
source tag:    final-pnp-proof-report-hardened-7072f8d
source commit: 7072f8d0bda6d44d240f9bb3fad624fd357e1278
artefact tag:  final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
artefact commit: 9d1de19f827e5cb6880741352eb2349cbbb45994
artefact path: proof-artifacts/final-pnp-proof-report-hardened-7072f8d/
```

Reviewer documentation on `main`, including this worksheet, may postdate the frozen source/checker tag. Do not treat later documentation or tests as part of the original sealed theorem release.

## Status vocabulary

Use one status for each audit question:

```text
NOT REVIEWED
IMPLEMENTATION CHECKED ONLY
MATHEMATICALLY REVIEWED
REPRODUCED
NEEDS CLARIFICATION
MATERIAL DEFECT FOUND
REFUTED
```

`IMPLEMENTATION CHECKED ONLY` means that the relevant code or tests behaved as documented. It does not mean that the mathematical implication encoded by the checker is sound.

## Reviewer record template

Copy this block under any question being audited:

```text
reviewer:
date in UTC:
pinned ref:
status:
files and lines inspected:
commands run:
positive evidence:
negative or mutation evidence:
independent derivation or implementation:
remaining assumptions:
finding or counterexample:
impact classification:
```

Impact classifications should use the narrowest applicable category:

```text
mathematical defect
specification mismatch
checker defect
parser or canonical-encoding defect
complexity-bound defect
provenance defect
reproducibility defect
documentation defect
```

---

## AQ-01 — Exact public claim boundary

**Claim**

The public conclusion is conditional and is emitted only at the boundary:

```text
CheckPCCPackexp(GeneratePCCPack())=accept => P = NP
```

**Where it appears**

- `canonical_proof_report.tex`, §§1.1–1.2, 18.3–18.4, 20.21, and 23.4.
- `docs/reviewer_guide.md`, executive summary.

**Supporting theorem, file, or function**

- Theorem 1.1, Theorems 18.2–18.3, and the final theorem-extraction section.
- `pcc-final-proof-report0.mjs::CheckFinalPNPProofReport0`.
- `pcc-final-pnp-release-gate0.mjs::CheckFinalPNPReleaseGate0`.
- `pcc-final-pnp-certificate0.mjs::CheckFinalPNPCertificate0`.

**How to test or inspect it**

1. Read every public theorem string in the report and generated records.
2. Trace the fields `theorem`, `publicConclusionAntecedent`, `publicConclusionConsequent`, `publicConclusionConditional`, and `publicConclusionStatement` through the final certificate, release gate, and proof-report checker.
3. Run:

```bash
node --test \
  test/pcc-final-pnp-certificate0.test.mjs \
  test/pcc-final-pnp-release-gate0.test.mjs \
  test/pcc-final-proof-report0.test.mjs
```

4. Mutate the antecedent, consequent, conditional flag, or gate status and require a named rejection.

**What would count as a refutation or material defect**

- Any public `P = NP` conclusion emitted when the package, replay, certificate, or release gate rejects.
- Acceptance of a different antecedent, a nonconditional theorem field, or a stronger public statement than the checked record supports.
- A report or website statement that presents checker acceptance as independent mathematical acceptance.

---

## AQ-02 — Direct-wire circuit model and size convention

**Claim**

The repository uses one fixed multi-output NAND direct-wire model, with an ordered output tuple and a size measure determined by charged NAND gates and declared materializers.

**Where it appears**

- Report §§2.1, 4.1–4.2, and 17.4.
- `docs/terminology_crosswalk.md`, entries for direct-wire word and carrier.

**Supporting theorem, file, or function**

- The direct-wire definitions in §2.1.
- Theorem 4.1, charge soundness.
- `pcc-final-framework0.mjs::CheckFinalFrameworkMatch0`.
- Core type, canonical-record, and row-key logic in `pcc-core.mjs`.

**How to test or inspect it**

1. Write down independently what counts as a source, output, gate, constant, repeated output, materializer, and charged object.
2. Compare the definitions used by Package O, Package G, the SAT decision, and the final framework match.
3. Test edge cases: constant outputs, projection outputs, repeated outputs, unused gates, and profile records that are computational versus proof-only.
4. Run:

```bash
node --test \
  test/pcc-core.test.mjs \
  test/pcc-final-framework0.test.mjs
```

**What would count as a refutation or material defect**

- Two claim-critical modules use different size, constant, output, or equivalence conventions.
- A proof-only or profile record supplies a free Boolean value that the mathematical model charges or forbids.
- A lower bound counts an output that can legally be supplied without a NAND gate under the declared model.

---

## AQ-03 — Compatible replacement and global slack law

**Claim**

A same-frontier replacement of a compatible support preserves the global function, and every local gain is bounded by global residual slack:

```text
g_C(U) <= Lambda(C)
```

**Where it appears**

- Report §2.2, Lemmas 2.1–2.2.
- Report §6.1, Theorem 6.1.

**Supporting theorem, file, or function**

- Lemma 2.1, compatible replacement.
- Lemma 2.2, global slack law.
- Package theorem `E.VerifyDWSoundness`.
- `pcc-local-packages0.mjs::CheckLocalPackageFamily0` and `CheckLocalPackages0`.

**How to test or inspect it**

1. Re-derive Lemmas 2.1–2.2 without using checker fields.
2. Verify that extraction lists every incoming and outgoing wire and that replacement preserves output order and carrier/profile obligations.
3. Construct small circuits with a proper support, replace it manually, and compare complete truth tables and exact charged sizes.
4. Inspect Package E's record fields and proof-DAG node rather than relying only on `accepted: true` contract flags.
5. Run:

```bash
node --test test/pcc-local-packages0.test.mjs
```

**What would count as a refutation or material defect**

- A compatible support and accepted replacement that changes the global Boolean function.
- A local gain larger than the actual global residual slack under the same size convention.
- An omitted boundary wire, open obligation, or charge owner that makes the replacement theorem false.

---

## AQ-04 — Saturation, support-square closure, and charge ownership

**Claim**

Saturation is extensive, idempotent, and monotone; accepted support squares are carrier-compatible; and every computational charge has one owner and is counted exactly once.

**Where it appears**

- Report §§3.1–3.2 and 4.1–4.2.
- Theorems 3.1–3.3 and 4.1.

**Supporting theorem, file, or function**

- RW, BN2, E, N, Splice, and charge contracts represented in `pcc-local-packages0.mjs`.
- Global theorem nodes in `pcc-global-proof-dag0.mjs`.
- Row and package coverage in `pcc-rows0.mjs` and `pcc-pack-sufficiency0.mjs`.

**How to test or inspect it**

1. Verify each closure generator and prove termination on the finite primitive-record universe.
2. Check whether raw union/intersection is ever used without completion and saturation.
3. For representative squares, recompute all frontiers, transports, charge owners, and obligation states.
4. Search for duplicate charge owners, uncharged materializers, and proof-only records entering computational semantics.
5. Run:

```bash
node --test \
  test/pcc-local-packages0.test.mjs \
  test/pcc-rows0.test.mjs \
  test/pcc-global-proof-dag0.test.mjs
```

**What would count as a refutation or material defect**

- A closure step that is nonmonotone, nonidempotent, or fails to terminate.
- A support square whose four corners do not share a valid transported carrier/frontier.
- A computational object counted zero times or more than once.
- A strict saving that disappears after complete charge accounting.

---

## AQ-05 — Full/quotient mode firewall

**Claim**

Quotient equality is comparison-only unless a checked full lift exists and all lost information or obligations are discharged.

**Where it appears**

- Report §§5.1–5.2 and 10.1.1.
- `docs/terminology_crosswalk.md`, mode firewall.

**Supporting theorem, file, or function**

- Theorem 5.1 and the transfer identity.
- `pcc-core.mjs::checkModeUse0`.
- `pcc-global-firewalls0.mjs::CheckGlobalFirewalls0`.
- Mode and obligation contracts in `pcc-local-packages0.mjs`.

**How to test or inspect it**

1. Enumerate every consumer of quotient-mode equality or projected words.
2. Confirm that constructive consumers require full-mode evidence and discharged obligations.
3. Run:

```bash
node examples/minimal/03-mode-firewall.mjs
npm run test:negative
node --test \
  test/pcc-core.negative.test.mjs \
  test/pcc-global-firewalls0.test.mjs
```

4. Mutation-test each full-lift and obligation field independently.

**What would count as a refutation or material defect**

- Any accepted constructive replacement based only on quotient equality.
- A full lift whose lost-bit or finite-kernel obligation remains open.
- A mode annotation controlled by unverified input rather than recomputed semantics.

---

## AQ-06 — Verified gains, normalization, and splice transport

**Claim**

Every constructive saving compiles to an explicit same-frontier replacement accepted by the direct-wire verifier, and strict savings survive normalization and splice composition.

**Where it appears**

- Report §§6.1–6.3.
- Theorems 6.1–6.4.

**Supporting theorem, file, or function**

- Package theorems `E.VerifyDWSoundness`, `N.TraceableNormalization`, and `Splice.BoundedAndComposed`.
- `pcc-local-packages0.mjs::CheckLocalPackages0`.
- Corresponding nodes in `pcc-global-proof-dag0.mjs`.

**How to test or inspect it**

1. Trace one accepted gain from its originating package into the E verifier.
2. Recompute truth tables, frontier equality, obligation closure, and integer size ledgers.
3. Check pullback/expansion equalities for every normalization operation N1–N10.
4. Check seam compatibility and charge ownership for a composed splice with one strict component.
5. Remove one transport, seam, obligation, or strictness field at a time and require rejection.

**What would count as a refutation or material defect**

- A package emits a gain without an accepted E proof.
- A normalized saving does not pull back to the original circuit.
- A splice changes semantics, output order, obligations, or exact size.
- Strictness is inferred from a local component but lost in the global charge total.

---

## AQ-07 — Finite-table and router coverage

**Claim**

Every governed bounded configuration is represented, normalized, and routed by FT/FT-X/X, and every governed branch-cycle or unary case reaches a named sound outcome.

**Where it appears**

- Report §§7.1–7.4.
- Theorems 7.1–7.3.

**Supporting theorem, file, or function**

- `FT.FiniteTableCoverage`, `FTX.CriticalWindowTables`, `X.CriticalWindowRouting`, `BC.BranchCycleRouting`, and `UN.UnaryDecoderRouting`.
- `pcc-local-packages0.mjs`.
- `pcc-rows0.mjs::CheckRows0`, `CheckRowFamilies0`, and `CheckBatchDeps0`.

**How to test or inspect it**

1. Define the governed physical universe independently of the generated rows.
2. Prove that normalization is total and semantics-preserving on that universe.
3. Compare the candidate tower, route priority, and first-failure rules against every row kind.
4. Verify that BC and UN do not import one another and that emitted tokens are not consumed as proofs.
5. Generate boundary cases at maximum schedule parameters and inspect row counts and runtime.

**What would count as a refutation or material defect**

- A governed physical configuration with no row.
- Two rows for one canonical case selecting incompatible routes.
- An active higher-priority gain hidden by a lower-priority obstruction.
- An unhandled BC/UN case or an illicit BC↔UN proof dependency.
- A table whose actual size is super-polynomial in the declared input measure.

---

## AQ-08 — Hereditary and budget exact routes

**Claim**

The HN grammar and BUD dynamic programs return exact minima on their governed classes, and the `NoHereditary` and `NoBudget` sidecars completely classify unsolved candidates.

**Where it appears**

- Report §§8.1–8.3.
- Theorems 8.1–8.4.

**Supporting theorem, file, or function**

- `HN.LeafTightness`.
- `HResolve.GlobalHereditaryResolver`.
- `BUD.BudgetResolver`.
- Local-package and global-proof-DAG records.

**How to test or inspect it**

1. Prove BWL exactness for the accepted grammar independently.
2. Verify ParseOrExit completeness: every same-frontier equivalent word must parse or trigger a higher-priority exit.
3. Check critical-pair coverage, termination, and confluence of local normal rules.
4. Check that sidecars enumerate every governed candidate exactly once and carry a valid blocker or solved status.
5. Compare small governed instances against independent brute-force minima.

**What would count as a refutation or material defect**

- A governed word outside both the grammar and the exit set.
- A BWL or budget output larger than an independently found equivalent realization.
- An omitted or multiply classified sidecar candidate.
- Circular HN/BUD blocking with no lower-rank base reason.

---

## AQ-09 — Terminal MuBridge and positive-witness saturation

**Claim**

Whole-circuit minimum equals the terminal full-word minimum, and deterministic saturation preserves positive residual evidence or emits the first named route.

**Where it appears**

- Report §§10.1–10.3.
- Theorems 10.1–10.3.

**Supporting theorem, file, or function**

- RW contracts `terminal-mu-bridge` and `saturate-positive`.
- Package theorem `RW.BCELReady` and its prerequisite proof nodes.
- `pcc-local-packages0.mjs` and `pcc-global-proof-dag0.mjs`.

**How to test or inspect it**

1. Construct both directions of the whole-circuit/closed-full-word translation and verify exact size preservation.
2. Confirm that terminal carrier fields do not become free computational semantics.
3. Step through every saturation rule, recomputing full positivity and projection defect.
4. Check that every nontransparent step is routed rather than silently absorbed.
5. Search for a whole-span cheaper word that the route treats as a local gain rather than strict descent.

**What would count as a refutation or material defect**

- A closed full word that cannot be interpreted as an equivalent whole circuit with the same size.
- Terminalization adds or removes a charged gate/materializer.
- Saturation destroys positivity without a named route.
- Quotient equality is used in the reverse MuBridge direction without a checked full lift.

---

## AQ-10 — BCEL-ready positive nucleus

**Claim**

Positive residual slack, after earlier routes are excluded, yields a finite saturated projection-positive hull with Boolean anchor algebra, an inclusion-minimal positive nucleus of at least two anchors, and a constant proper-cut equation.

**Where it appears**

- Report §10.4, Theorem 10.4.
- ZeroSlack obligations listed in §§16.1.1–16.1.2.

**Supporting theorem, file, or function**

- Package theorem `RW.BCELReady`.
- Residual-band theorem fields in `pcc-pack-sufficiency0.mjs`.
- Global proof nodes in `pcc-global-proof-dag0.mjs`.

**How to test or inspect it**

1. Start from an explicit positive residual witness and reconstruct the anchor partition.
2. Verify Boolean intersection/union identities for every anchor subset used by the proof.
3. Check how an inclusion-minimal positive subset is found and whether the search is polynomial.
4. Re-derive the constant-cut equation from the transfer identity and minimality.
5. Test singleton nuclei and non-Boolean anchor failures to ensure they route rather than disappear.

**What would count as a refutation or material defect**

- Positive slack with no BCEL-ready hull and no earlier named route.
- A non-Boolean anchor family accepted as Boolean.
- A positive proper subnucleus contradicting minimality.
- A failed proper-cut equation accepted without routing.
- Exponential subset search hidden inside the nucleus construction.

---

## AQ-11 — BN2 through BN6 residual arithmetic

**Claim**

The BN2–BN6 chain converts a BCEL-ready positive nucleus into a positive pair, balanced-triple, or full-span packet using side-tight optima, exact request antichains, activation-exact cancellation, full-shadow localization, separating consumers, and nonnegative constant-cut hypergraph rigidity.

**Where it appears**

- Report §§11.1–11.6 and §12.
- Theorems 11.1–11.6 and 12.1–12.2.

**Supporting theorem, file, or function**

- `BN2.SideTightCoherentOptimum`.
- `BN3.SimultaneousEnvelope`.
- `BN4.ActivationExact`.
- `BN5.FullShadowLocalization`.
- `PkgC.SeparatingConsumers`.
- `BN6.HypergraphPacket`.
- Local-package records and global proof DAG.

**How to test or inspect it**

1. Verify the four-corner identity and ensure only side-tight tuples represent merge defect.
2. Check that minimal-consumer antichains exactly encode request predicates and are jointly realizable in one basis.
3. Prove active-antichain equality is equivalent to activation equality without enumerating all cuts.
4. Recompute signed mass cancellation by full activation-exact keys.
5. Inspect every negative residual key's shadow graph and Hall witness.
6. Re-prove V53/V54 and test the mixed three-anchor case.
7. Measure antichain, graph, cell, and certificate sizes on worst-case accepted schedules.

**What would count as a refutation or material defect**

- A non-side-tight basis used as an exact merge-defect value.
- Two different activation functions sharing an accepted key.
- Cancellation across different semantic or transport keys.
- A cut-active negative full residual that remains silent.
- A nonsingleton separating consumer surviving PkgC without a route.
- A nonnegative constant-cut hypergraph outside the claimed packet classification.
- Exponential antichain or cut work hidden in an asserted polynomial step.

---

## AQ-12 — Selector completeness, realizer, and HB closure

**Claim**

Every positive packet has a representative in the polynomial selector universe; a faithful selector yields a verified gain or a typed lower-rank/HN/BUD blocker; and the combined blocker graph is well-founded and noncircular.

**Where it appears**

- Report §§13.1–15.1.
- Theorems 13.1–13.4, 14.1–14.2, and 15.1–15.2.

**Supporting theorem, file, or function**

- `Packet.SelectorSeeds`.
- `R.SelectorRealization`.
- `HB.NegativeClosure`.
- Package O's rank-ordered oracle records.

**How to test or inspect it**

1. For each packet type, reconstruct the selector handles and payload from the packet witness.
2. Check the claimed bound on selector count and payload bit length.
3. Decode representative selectors and verify the same-frontier replacement and strict charge-surplus injection.
4. Inspect every typed bottom reason and verify rank nonincrease or strict tie-break descent.
5. Build the complete HN/BUD blocker graph and run an independent cycle check.

**What would count as a refutation or material defect**

- A positive packet with no selector and no earlier route.
- A faithful selector whose realizer returns an untyped or rank-increasing failure.
- A claimed strict charge surplus with no unmatched positive-weight charge.
- A cycle in the HN/BUD blocker graph.
- A selector universe or payload family that grows super-polynomially.

---

## AQ-13 — ZeroSlack soundness

**Claim**

If the rank-ordered oracle returns `ZeroSlack(C,Z)`, then `Lambda(C)=0`.

**Where it appears**

- Report §§16.1–16.1.2.
- Theorem 16.1.

**Supporting theorem, file, or function**

- Package theorem `O.ZeroSlackOracle`.
- Residual-band theorem object in `pcc-pack-sufficiency0.mjs`.
- Local package and global proof-DAG records.
- Reviewer negative test for `zeroSlackSound`.

**How to test or inspect it**

1. Trace the complete contradiction:

```text
positive slack
=> positive residual witness
=> BCEL-ready nucleus
=> positive packet
=> faithful selector
=> verified gain or typed blocker
=> contradiction with selector silence and HB closure
```

2. Verify the no-lower ledger covers every earlier gain, exact, route, descent, saturation, and packet outcome.
3. Verify selector silence at every rank, not only globally.
4. Mutate each ZeroSlack obligation separately and require a named rejection.
5. Run:

```bash
node examples/minimal/06-zero-slack.mjs
npm run test:negative
node --test test/pcc-pack-sufficiency0.test.mjs
```

**What would count as a refutation or material defect**

- Any positive-slack circuit accepted with `ZeroSlack`.
- An omitted earlier route or selector rank.
- A sidecar or blocker reference that is stale, circular, or not independently verified.
- A contradiction represented only by assertion-shaped booleans with no sound proof path.
- A ZeroSlack certificate whose size is super-polynomial.

---

## AQ-14 — Residual-band exact minimization

**Claim**

If the accepted package is valid and the initial residual slack is `O(log |C0|)`, `PCCMin` returns an exact equivalent minimum in polynomial time.

**Where it appears**

- Report §16.2, Theorem 16.2.
- Report §18.1, package sufficiency.

**Supporting theorem, file, or function**

- `PackSufficiencyTheorem.residualBandMinimization` in `pcc-pack-sufficiency0.mjs`.
- Package O and all prerequisite local-package theorems.
- `pcc-global-proof-dag0.mjs`.

**How to test or inspect it**

1. Prove that every nonterminal iteration lowers the same integer residual measure by at least one.
2. Verify normalization cannot reset or change the minimum notion.
3. Verify each terminal `Minimum` route and `ZeroSlack` route is exact.
4. Derive total runtime and certificate size from actual loops, state graphs, selector counts, and bit complexity.
5. Compare small instances with an independent brute-force minimizer.

**What would count as a refutation or material defect**

- A nonterminal iteration that fails to lower residual slack.
- A terminal output that is not globally minimum under the declared framework.
- A call to exact minimization or exhaustive equivalent-circuit search inside the claimed polynomial path.
- A local table, DP, selector family, integer operation, or certificate that has super-polynomial worst-case size.

---

## AQ-15 — Locked-NAND macro semantics and separation

**Claim**

The equality, constant, NAND-trace, prefix, and final-lock gadgets compute their displayed functions and satisfy global slot/separation invariants.

**Where it appears**

- Report §§17.1–17.2 and Appendix A.
- GPack description in §20.6.

**Supporting theorem, file, or function**

- GPack fields `SlotAlloc`, `SepCert`, `CohCert`, `MacroTables`, and `PrefixCert`.
- `pcc-gpack0.mjs::CheckGPack0` and `CheckRowFamG0`.
- `test/pcc-gpack0.test.mjs`.

**How to test or inspect it**

1. Exhaustively evaluate every macro output for every local input assignment.
2. Confirm declared distinguished outputs and exposed-output order.
3. Check global renaming, fresh locks, duplicate occurrence slots, and final-lock exclusivity.
4. Brute-force small source circuits and compare the generated trace predicate with direct NAND evaluation.
5. Run:

```bash
node examples/minimal/01-locked-nand.mjs
npm run test:negative
node --test test/pcc-gpack0.test.mjs
```

**What would count as a refutation or material defect**

- A macro truth-table mismatch.
- A slot collision accepted by the checker.
- A baseline output or prefix node depending on the final lock.
- A duplicate source occurrence silently sharing a slot where separation is required.
- A checker field that asserts separation without deriving or checking it.

---

## AQ-16 — Baseline lower bound and distinctness

**Claim**

The baseline contains exactly `B_phi` pairwise distinct nonconstant nonprojection functions, so every direct-wire realization needs at least `B_phi` NAND gates.

**Where it appears**

- Report §17.3 and §17.4.
- Theorem 17.1 and Lemmas 17.3–17.4.

**Supporting theorem, file, or function**

- `pcc-gpack0.mjs::computeLockedNANDBaseline0`.
- GPack `BaselineCert` and proof node `G.BaselineDistinct`.
- `pcc-global-proof-dag0.mjs` and final G linkage.

**How to test or inspect it**

1. Recompute the formula:

```text
18m + 10w_eq + 3w_0 + 2w_1 + 2(3m-1)
```

2. Verify every exposed function is nonconstant, not a positive boundary projection, and distinct from every other exposed function on the full carrier.
3. Check cross-instance distinctness under all permitted carrier assignments, not only coherent traces.
4. Search for repeated outputs that can share one gate legally.
5. Independently minimize small baseline tuples.

**What would count as a refutation or material defect**

- Two counted baseline coordinates compute the same Boolean function.
- A counted coordinate is constant or a free projection.
- The formula overcounts or undercounts actual exposed outputs.
- Cross-instance distinctness holds only under coherent assignments rather than as full carrier functions.

---

## AQ-17 — Trace equivalence and locked threshold

**Claim**

The trace predicate is satisfiable exactly when the source NAND circuit is satisfiable, and:

```text
phi not in SAT => mu(W_phi)=B_phi
phi in SAT     => B_phi+1 <= mu(W_phi) <= B_phi+4
```

**Where it appears**

- Report Theorem 17.2 and Lemmas 17.5–17.7.
- Final SAT decision in §18.4.

**Supporting theorem, file, or function**

- GPack `TraceCert` and `ThresholdCert`.
- G proof nodes for `TraceEquivalence`, `ZeroOutputConvention`, and `FinalLockSeparation`.
- `pcc-gpack0.mjs::CheckGPack0`.

**How to test or inspect it**

1. Prove both directions of trace equivalence by topological induction.
2. Verify the unsatisfiable case makes the final output zero on the whole carrier, not only coherent traces.
3. Verify the satisfiable final output is nonconstant, nonprojection, and distinct from every baseline function.
4. Brute-force all source circuits up to a small gate bound and independently minimize the corresponding locked output tuples where feasible.
5. Attempt to find a satisfiable instance at the baseline or an unsatisfiable instance above it.

**What would count as a refutation or material defect**

- A source assignment and accepted trace extension disagree about circuit output.
- An incoherent full-carrier assignment makes the unsatisfiable final output nonzero.
- A satisfiable final output equals a baseline output or free projection.
- Any small counterexample to the displayed threshold.

---

## AQ-18 — Residual bound and framework match

**Claim**

The locked word has size `B_phi+4`, hence residual slack at most four, and Package O and Package G use identical circuit, output, charge, minimum, and slack conventions.

**Where it appears**

- Report Theorem 17.2, §§18.4 and 20.6.

**Supporting theorem, file, or function**

- GPack `ThresholdCert`.
- `pcc-final-framework0.mjs::CheckFinalFrameworkMatch0` and `CheckFinalIntegration0`.
- `test/pcc-final-framework0.test.mjs`.

**How to test or inspect it**

1. Count the final conjunction gates under the exact direct-wire model.
2. Verify the lower bound used to infer residual slack.
3. Compare O and G maps field by field: syntax, charge, carrier constants, output convention, normalization, minimum, and slack.
4. Run:

```bash
node examples/minimal/02-residual-slack.mjs
node --test test/pcc-final-framework0.test.mjs
```

**What would count as a refutation or material defect**

- A locked instance with residual slack greater than four.
- A mismatch between the minimizer's framework and the reduction's framework.
- A bridge that compares different equivalence relations, size measures, or output conventions.

---

## AQ-19 — SAT decision and polynomial-time bound

**Claim**

The final procedure converts input to NAND, builds the locked instance, computes its exact minimum, compares with the baseline, and runs in deterministic polynomial time.

**Where it appears**

- Report §§18.4 and 20.6.
- Theorem 18.2 and Theorem 20.5.

**Supporting theorem, file, or function**

- `pcc-final-framework0.mjs::CheckSATDecision0` and `CheckSATBounds0`.
- `pcc-final0.mjs::CheckFinal0` and `CheckRowFamFinal0`.
- Final proof-DAG nodes.

**How to test or inspect it**

1. Verify the Boolean-to-NAND conversion and input-size model.
2. Verify the comparator is exact `minSize > baseline`.
3. Derive every claimed exponent from source loops, table sizes, selector counts, certificate sizes, and integer bit lengths.
4. Ensure the algorithm is uniform and does not depend on precomputed input-specific proofs.
5. Run:

```bash
node --test \
  test/pcc-final-framework0.test.mjs \
  test/pcc-final0.test.mjs
```

**What would count as a refutation or material defect**

- Conversion fails to preserve satisfiability or has super-polynomial expansion.
- An approximate minimum is accepted by the decision rule.
- A claimed polynomial subroutine has exponential worst-case state or certificate size.
- Input-dependent package generation or proof search is omitted from runtime accounting.

---

## AQ-20 — PCCPack completeness and package sufficiency

**Claim**

An accepted PCCPack contains all required package families, rows, proof nodes, reflection records, bounds, and final linkages needed for the residual-band and SAT conclusions.

**Where it appears**

- Report §§18.2–18.3 and 19.1–19.5.
- Theorems 18.1, 18.3, 19.1, and 19.2.

**Supporting theorem, file, or function**

- `pcc-pack-sufficiency0.mjs::CheckPackSufficiency0`.
- `pcc-check-pcc-pack-exp0.mjs::CheckPCCPackexp0`.
- `pcc-local-packages0.mjs::CheckLocalPackages0`.
- `pcc-rows0.mjs::CheckRows0`.
- `pcc-global-proof-dag0.mjs::CheckGlobalProofDAG0`.

**How to test or inspect it**

1. Build an independent manifest of every theorem premise and compare it with the package inventory.
2. Remove one package family, theorem node, row family, bound, reflection, or final edge at a time.
3. Confirm the first missing obligation produces a named rejection.
4. Run:

```bash
node examples/minimal/07-pccpack.mjs
node --test \
  test/pcc-local-packages0.test.mjs \
  test/pcc-rows0.test.mjs \
  test/pcc-global-proof-dag0.test.mjs \
  test/pcc-pack-sufficiency0.test.mjs \
  test/pcc-check-pcc-pack-exp0.test.mjs
```

**What would count as a refutation or material defect**

- Acceptance with a missing theorem premise or package family.
- A package theorem represented only by an unproved assertion field.
- A row-coverage claim whose governed universe is not completely represented.
- A final theorem path that bypasses a required locked-NAND or residual-band proof node.

---

## AQ-21 — Parser, canonical encoding, row identity, and hash discipline

**Claim**

Accepted bytes have one typed parse and canonical encoding; row identity excludes selected route; duplicate conflicts are rejected; and hashes are indexes or seals rather than semantic equality.

**Where it appears**

- Report §§19.3–19.4 and 20.15–20.19.
- Theorem 19.2.

**Supporting theorem, file, or function**

- `pcc-core.mjs::parseTop0`, canonical encoders/normalizers, `computeRowKey0`, `checkRowKey0`, and duplicate/hash helpers.
- `pcc-rows0.mjs::CheckRows0`.
- Acceptance replay and canonical-byte comparison modules.

**How to test or inspect it**

1. Differentially implement the parser and serializer.
2. Fuzz malformed lengths, arities, names, integers, duplicate keys, type tags, and trailing bytes.
3. Verify normalization idempotence and round-trip identity.
4. Confirm every digest lookup is followed by full key or canonical-byte comparison.
5. Run:

```bash
node examples/minimal/05-canonical-parser.mjs
npm run test:negative
node --test \
  test/pcc-core.test.mjs \
  test/pcc-core.negative.test.mjs \
  test/pcc-rows0.test.mjs
```

**What would count as a refutation or material defect**

- Ambiguous parsing or accepted trailing bytes.
- Two canonical encodings for one object or one encoding for two typed objects.
- Selected route included in identity so conflicting classifications do not collide.
- Digest equality used as proof-object or semantic equality without full comparison.

---

## AQ-22 — Proof kernel, Sigma schemas, reflection, and global proof DAG

**Claim**

Every accepted theorem node is typed, acyclic, justified by a permitted primitive rule, Sigma instance, reflection instance, or earlier proof; and reflection maps each checker predicate to the exact theorem it checks.

**Where it appears**

- Report §§18.1, 20.4, 20.9, and 20.12.
- Theorems 20.3, 20.8, and 20.11.

**Supporting theorem, file, or function**

- `pcc-kimpl0.mjs::CheckKImpl0`, `CheckKBundle0`, `CheckConformance0`, `CheckSigmaRegistry0`, and `CheckReflectionRegistry0`.
- `pcc-global-proof-dag0.mjs::CheckGlobalProofDAG0`.

**How to test or inspect it**

1. Give each primitive rule an independent mathematical semantics and prove local soundness.
2. Audit substitution, induction, transport, arithmetic, Hall, and finite-exhaustion side conditions.
3. Expand critical Sigma instances into primitive derivations.
4. Compare every reflection conclusion with the exact source checker predicate and theorem statement.
5. Remove, reorder, cycle, or mistype proof nodes and require rejection.
6. Run:

```bash
node --test \
  test/pcc-kimpl0.test.mjs \
  test/pcc-global-proof-dag0.test.mjs
```

**What would count as a refutation or material defect**

- An unsound primitive rule or unchecked side condition.
- An overbroad Sigma substitution.
- A reflection from a weaker checker predicate to a stronger theorem.
- A cycle, forward reference, opaque proof blob, missing premise, or type mismatch accepted by the DAG checker.

---

## AQ-23 — No-hidden-minimization and import firewalls

**Claim**

After macro, alias, generated-template, and import expansion, no exact-minimization operation occurs in executable position, and forbidden package dependencies are rejected.

**Where it appears**

- Report §§19.2 and 20.5.
- Theorem 20.4.

**Supporting theorem, file, or function**

- `pcc-core.mjs::checkNoHiddenMin0`.
- `pcc-global-firewalls0.mjs::CheckNoHiddenMin0`, `CheckImportGraph0`, and `CheckGlobalFirewalls0`.
- No-min checks in GPack, local packages, package sufficiency, and top-level package checking.

**How to test or inspect it**

1. Build a complete executable call graph after all expansion stages.
2. Inspect aliases, computed property access, strings, callbacks, imports, generated code, and wrappers.
3. Search for semantically equivalent brute-force minimization that avoids forbidden names.
4. Verify the forbidden edges `BC↔UN`, `BCEL→R`, `BUD→R`, `O→G`, and `G→O` across all imports and proof references.
5. Run:

```bash
node examples/minimal/04-no-hidden-minimization.mjs
npm run test:negative
node --test \
  test/pcc-core.negative.test.mjs \
  test/pcc-global-firewalls0.test.mjs \
  test/pcc-gpack0.test.mjs
```

**What would count as a refutation or material defect**

- Any executable exact minimizer, `argmin`, equivalent-circuit exhaustive search, or optimization oracle on the claimed SAT path.
- A forbidden operation hidden by aliasing, dynamic dispatch, or generated code.
- A forbidden dependency or circular proof import accepted by the checker.
- A syntactic scan that misses an exponential search implemented without a forbidden identifier.

---

## AQ-24 — Generator is untrusted and the materialized package is checked

**Claim**

`GeneratePCCPack` is not trusted as a proof oracle; the actual generated package and concrete records are materialized, checked, and linked to the acceptance run.

**Where it appears**

- Report §§19.1, 20.7, and 20.14.
- Theorems 19.1, 20.6, and 20.13.

**Supporting theorem, file, or function**

- `pcc-generate-pcc-pack0.mjs`.
- `pcc-pack-concrete-materialized0.mjs`.
- `pcc-check-pcc-pack-exp0.mjs::CheckPCCPackexp0`.
- `pcc-accept-run0.mjs::CheckAcceptRun0` and `ReplayAcceptRun0`.

**How to test or inspect it**

1. Ignore generator intent and inspect only the bytes presented to concrete checkers.
2. Mutate generated package fields after generation and require rejection.
3. Confirm the acceptance transcript records the exact package canonical bytes and phase outputs.
4. Write an independent generator or materializer and compare canonical package semantics.
5. Run:

```bash
node --test \
  test/pcc-pack-concrete-materialized0.test.mjs \
  test/pcc-check-pcc-pack-exp0.test.mjs \
  test/pcc-accept-run0.test.mjs
```

**What would count as a refutation or material defect**

- Generator output trusted without complete checking.
- Acceptance record detached from the actual package bytes.
- A mutated materialized package accepted because only metadata or a stale digest is checked.
- Input-dependent hidden proof search performed by the generator and omitted from the claimed algorithm.

---

## AQ-25 — Acceptance replay and final release linkage

**Claim**

The accepted package, acceptance run, replay, final verdict, certificate, release gate, and final proof report all refer to the same canonical records and exact theorem boundary.

**Where it appears**

- Report §§20.7, 20.14, 20.21, and 23.2–23.4.

**Supporting theorem, file, or function**

- `pcc-accept-run0.mjs::CheckAcceptRun0`, `ReplayAcceptRun0`, and `EmitFinalVerdict0`.
- `pcc-final-acceptance-replay0.mjs::CheckConcreteFinalAcceptanceReplay0`.
- `pcc-final-pnp-certificate0.mjs::CheckFinalPNPCertificate0`.
- `pcc-final-pnp-release-gate0.mjs::CheckFinalPNPReleaseGate0`.
- `pcc-final-proof-report0.mjs::CheckFinalPNPProofReport0`.

**How to test or inspect it**

1. Trace canonical package bytes and every central digest through all layers.
2. Alter one record at each layer and require the first dependent layer to reject with a named mismatch.
3. Confirm replay recomputes records rather than accepting stored booleans or digests alone.
4. Run:

```bash
node --test \
  test/pcc-accept-run0.test.mjs \
  test/pcc-final-acceptance-replay0.test.mjs \
  test/pcc-final-pnp-certificate0.test.mjs \
  test/pcc-final-pnp-release-gate0.test.mjs \
  test/pcc-final-proof-report0.test.mjs
```

**What would count as a refutation or material defect**

- Replay accepts a different package, transcript, certificate, or theorem record.
- Digest-only linkage substitutes for canonical-byte or full-record comparison.
- A failed or missing phase is omitted from the final verdict.
- The final report accepts a stale certificate or mismatched release gate.

---

## AQ-26 — Sealed artefact identity and reproducibility

**Claim**

The sealed artefact tag contains the published proof-report bundle; the listed files match `SHA256SUMS`; and an independent fresh clone can reproduce the documented implementation-level acceptance fields.

**Where it appears**

- Report §§20.22 and 23.1–23.5.
- `REPRODUCE.md` and `docs/reproducibility.md`.

**Supporting theorem, file, or function**

- `proof-artifacts/final-pnp-proof-report-hardened-7072f8d/release-seal.json`.
- `SHA256SUMS` and `SHA256SUMS.sha256`.
- Final proof-report writer and release-audit tooling.

**How to test or inspect it**

1. Follow `docs/reproducibility.md` from a clean clone.
2. Resolve annotated tags to peeled commits.
3. Verify both checksum ledgers.
4. Run targeted tests and, where resources permit, the full pinned `npm run validate` suite.
5. Regenerate compact and full report records outside the repository.
6. Compare claim-critical semantic fields before demanding byte-for-byte equality.

**What would count as a refutation or material defect**

- A tag resolves to the wrong commit.
- A sealed file fails its checksum.
- Documented public commands cannot retrieve or run the release under the stated toolchain.
- Regenerated claim-critical theorem or acceptance fields differ.
- A hash match is presented as mathematical correctness rather than file identity.

---

## AQ-27 — External verification status

**Claim**

The repository records internal checker acceptance and a reproducible release, but it does not by itself establish independent mathematical verification, checker soundness, peer-review acceptance, or community consensus.

**Where it appears**

- `README.md`.
- `docs/reviewer_guide.md`.
- `docs/trust_model.md`.
- `EXTERNAL_REVIEW_STATUS.md`.

**Supporting theorem, file, or function**

No checker function can establish external acceptance. This is a publication-status and evidence-classification statement.

**How to test or inspect it**

1. Compare every public status statement across README, report, website, release notes, and external-review records.
2. Require named, public, attributable independent reviews before changing the status.
3. Distinguish outreach, silence, partial reproduction, implementation review, and mathematical validation.

**What would count as a refutation or material defect**

- Public wording implying independent validation where none is documented.
- Treating silence, email delivery, repository access, internal tests, or hash verification as expert acceptance.
- Omitting a known substantive external criticism or unresolved reproduction failure from the status record.

---

## Cross-claim completion checklist

A serious review should not mark the overall claim complete until all of the following have independent evidence:

```text
[ ] exact mathematical definitions fixed
[ ] locked-NAND macro semantics independently checked
[ ] baseline distinctness and threshold independently proved
[ ] residual slack <= 4 independently verified
[ ] Terminal MuBridge independently proved
[ ] positive-witness and BCEL-ready completeness independently proved
[ ] BN2-BN6 arithmetic and packet classification independently proved
[ ] selector completeness and polynomial bound independently proved
[ ] realizer and HB closure independently proved
[ ] ZeroSlack contradiction independently proved
[ ] PCCMin exactness and polynomial runtime independently proved
[ ] parser and canonical codec independently checked
[ ] proof-kernel rules and Sigma schemas independently checked
[ ] reflection mappings independently checked
[ ] no-hidden-minimization and complete call graph independently checked
[ ] package coverage and global proof DAG independently checked
[ ] final SAT reduction and complexity implication independently checked
[ ] sealed release reproduced from public refs
[ ] external review status reported conservatively
```

A successful checksum, test run, or checker acceptance may satisfy one implementation or provenance item. It cannot be used to mark the mathematical items complete without an independent argument.

## Finding report template

```text
question ID:
claim attacked:
pinned source or artefact ref:
report theorem or section:
source file and function:
minimal counterexample or malformed fixture:
expected mathematical or checker behaviour:
observed behaviour:
exact rejection coordinate, if any:
independent derivation or reproduction transcript:
impact classification:
proposed correction:
```

Prefer a minimal counterexample, accepted malformed certificate, missing implication, asymptotic lower bound, or reproducible command failure over a general statement of concern.

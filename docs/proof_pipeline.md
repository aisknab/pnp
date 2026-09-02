# Proof and Checker Pipeline

> **Current authority:** This document maps the author's intended argument and the historical
> JavaScript assertion-checker pipeline. It does not establish `P = NP` and is not an active release
> gate. Current status and remaining formal obligations are in
> [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json) and
> [`FORMAL_RECONSTRUCTION.md`](FORMAL_RECONSTRUCTION.md).

> **Historical report-citation boundary:** Every numbered `Report §...`, appendix, or
> `canonical_proof_report.tex` citation below refers exclusively to the historical 56-page
> manuscript at source tag `final-pnp-proof-report-hardened-7072f8d` (commit
> `7072f8d0bda6d44d240f9bb3fad624fd357e1278`). It never refers to the generated six-page report
> now at the repository root. For current authority, start with
> [`lean_theorem_inventory.md`](lean_theorem_inventory.md).

## Purpose and review boundary

This document explains the claimed proof and checker pipeline in conventional complexity-theory and software-assurance terms before introducing repository-specific package names.

It describes what the repository claims and where the corresponding assertions are represented. It does not establish that any mathematical implication, checker predicate, complexity bound, or reflection rule is sound.

The historical release-specific source coordinates are:

```text
source tag:    final-pnp-proof-report-hardened-7072f8d
source commit: 7072f8d0bda6d44d240f9bb3fad624fd357e1278
artefact tag:  final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
artefact path: proof-artifacts/final-pnp-proof-report-hardened-7072f8d/
```

Reviewer documentation on `main`, including this file, is not itself part of the pinned theorem/checker release.

## 1. Problem statement in standard terms

`P` is the class of decision problems solvable by a deterministic polynomial-time algorithm. `NP` is the class of decision problems for which a proposed positive answer can be verified in polynomial time. SAT is NP-complete.

A proof that SAT has a deterministic polynomial-time decision algorithm would imply:

```text
SAT is in P
=> every language in NP reduces to a language in P
=> NP is contained in P
=> P = NP
```

The repository claims such a SAT algorithm by reducing SAT to an exact circuit-minimisation problem on a restricted family of multi-output NAND circuits, then claiming a polynomial-time exact minimiser for those instances.

The logical route is:

1. convert a Boolean formula or circuit to NAND;
2. build a restricted NAND minimisation instance and an integer threshold;
3. compute the exact minimum size of that instance;
4. decide SAT by comparing the exact minimum with the threshold;
5. prove that every step, including the exact minimisation, runs in polynomial time.

The checker and release machinery are a second, historical evidence layer. They establish only that
a finite package satisfied the implemented predicates. They do not establish the mathematical route
or discharge the current formal obligations.

## 2. Claimed mathematical route

For a NAND circuit `phi`, the repository constructs a locked multi-output NAND direct-wire word `W_phi` and a baseline `B_phi`.

The claimed threshold theorem is:

```text
phi is unsatisfiable  => mu(W_phi) = B_phi
phi is satisfiable    => B_phi + 1 <= mu(W_phi) <= B_phi + 4
```

Therefore:

```text
phi is satisfiable iff mu(W_phi) > B_phi
```

The constructed word has size `B_phi + 4`, so the claimed residual slack is:

```text
Lambda(W_phi) = size(W_phi) - mu(W_phi) <= 4
```

The repository then claims that its residual-band algorithm, called `PCCMin`, computes an exact minimum in polynomial time whenever the starting residual slack is logarithmically bounded. Since the locked instance has residual slack at most four, the claimed SAT algorithm is:

```text
M = PCCMin(W_phi)
return SAT iff size(M) > B_phi
```

The final complexity-theory step is standard only if all preceding statements hold uniformly and in polynomial time.

## 3. Mathematical pipeline and executable evidence pipeline

```mermaid
flowchart TD
  subgraph M[Claimed mathematical and algorithmic pipeline]
    A[Boolean formula or circuit] --> B[Polynomial conversion to NAND]
    B --> C[Build locked multi-output NAND word W_phi]
    C --> D[Compute baseline B_phi]
    C --> E[Prove locked threshold and residual slack at most 4]
    D --> F[Exact residual-band minimiser PCCMin]
    E --> F
    F --> G[Obtain exact minimum mu(W_phi)]
    G --> H[Compare mu(W_phi) with B_phi]
    H --> I[SAT decision in polynomial time]
    I --> J[P = NP via SAT NP-completeness]
  end

  subgraph X[Executable certificate, checker, and release pipeline]
    K[GeneratePCCPack0: untrusted generator] --> L[Materialised PCCPack]
    L --> M1[Structural, kernel, row, package, firewall, GPack, and final checks]
    M1 --> N[CheckPCCPackexp0 acceptance record]
    N --> O[Acceptance run and canonical-byte replay]
    O --> P[Final certificate and release gate]
    P --> Q[CheckFinalPNPProofReport0]
    Q --> R[Conditional public conclusion record]
    R --> S[Release seal and SHA-256 ledgers]
  end

  E -. encoded by GPack and proof DAG .-> M1
  F -. encoded by local packages, ZeroSlack, and package sufficiency .-> M1
  J -. encoded by final framework, reflection, and final theorem records .-> P

  T[Independent review required] -. audits mathematics .-> M
  T -. audits checker soundness .-> X
```

The final seal authenticates published bytes. It does not validate any mathematical arrow.

## 4. Stage-by-stage audit map

| Stage | Conventional claim | Repository terms | Where correctness is asserted | Where polynomial time is asserted | Primary implementation and tests | A decisive refutation would be |
| --- | --- | --- | --- | --- | --- | --- |
| 1. Input and NAND conversion | Every supported Boolean input is converted to an equisatisfiable NAND circuit with polynomial blow-up. | `PreNAND`, `NandConversion` | Report §§17–18; `GPack.PreNAND`; `SATDecision.NandConversion`. | `SATBounds.Converter`; final polynomial-bound records. | `pcc-gpack0.mjs`; `pcc-final-framework0.mjs`; `test/pcc-gpack0.test.mjs`; `test/pcc-final-framework0.test.mjs`. | An input whose conversion changes satisfiability, changes the declared output, or has super-polynomial size. |
| 2. Locked instance construction | The NAND circuit is transformed into one restricted multi-output NAND instance with a computable baseline. | Locked NAND, `G-Sep+`, `G-Coh`, macro tables, `BaselineCert` | Report §17 and Appendix A; GPack certificates; locked-NAND proof-DAG nodes. | `BoundsCert`, `SATBounds.LockedBuilder`, public schedule. | `pcc-gpack0.mjs::CheckGPack0`; `computeLockedNANDBaseline0`; G row-family checker; GPack tests. | A slot collision, false macro truth table, collapsed exposed output, incorrect baseline, or input-dependent super-polynomial construction. |
| 3. Threshold theorem | Exact minimum equals the baseline in the unsatisfiable case and exceeds it in the satisfiable case. | `BaselineDistinct`, `TraceEquivalence`, `ZeroOutputConvention`, `FinalLockSeparation`, `G.ThresholdCert.proof` | Report Theorem 17.2 and Lemmas 17.3–17.7; `GlobalProofDAG` G nodes; `FinalIntegration` G linkage; typed semantic theorem `fullCandidate_satisfiable_iff_referenceMinimum_ge_succ`. | The threshold construction itself must be polynomial; the semantic theorem is otherwise a correctness statement. | `lean/PNP/LockedNANDGlobalSemanticThreshold.lean` and its audit/regression; legacy GPack/final-framework checks remain the encoded-construction surface. | A satisfiable instance with minimum at the baseline, an unsatisfiable instance above the baseline, a baseline output that is constant/projection/duplicate, or a final output not separated by the fresh lock. |
| 4. Residual-slack bridge | The locked instance is within four gates of its exact minimum. | `Lambda(C)`, residual band, `SlackMap` | Typed theorem `fullCandidate_residualSlack_le_four`; Report Theorem 17.2; GPack threshold record; final framework match. | The bound four is used to limit the number of descent steps; constructing the encoded instance must still be polynomial. | `lean/PNP/LockedNANDGlobalSemanticThreshold.lean`; legacy GPack/final-framework checks remain the encoded linkage surface. | A constructed instance with residual slack above four or a mismatch in the size/minimum convention used by G and O. |
| 5. Exact minimisation in the residual band | A deterministic algorithm returns an exact equivalent minimum when residual slack is bounded. | `PCCMin`, `PCCOracle`, `ZeroSlack`, packages E through O | Report §§2–16, especially Theorems 16.1–16.2; `PackSufficiencyTheorem.residualBandMinimization`; proof-DAG package nodes. | Each verified gain lowers residual slack; all local tables, DPs, selectors, ledgers, and certificates are claimed polynomial. | `pcc-local-packages0.mjs`; `pcc-pack-sufficiency0.mjs`; `pcc-global-proof-dag0.mjs`; local-package and package-sufficiency tests. | A positive-slack circuit that reaches `ZeroSlack`, an unhandled route, an invalid gain, an exact route without proof, a circular HN/BUD blocker, or any super-polynomial subroutine/state space. |
| 6. Framework compatibility | The minimiser and locked construction use exactly the same syntax, outputs, charges, carrier constants, minimum notion, and residual-slack definition. | Package O/G framework match, `SyntaxMap`, `ChargeMap`, `CarrierMap`, `OutputMap`, `MinMap`, `SlackMap` | Report §§18.4 and 20.6; `CheckFinalFrameworkMatch0`. | The bridge must preserve the already-claimed polynomial bounds. | `pcc-final-framework0.mjs`; `test/pcc-final-framework0.test.mjs`. | O minimises a different model from G, uses a different output convention, or treats profile data/constants differently. |
| 7. SAT decision | Exact minimum above the baseline means SAT; equality means UNSAT. | `SATDecision`, `DecisionRule`, `PCCMinBridge` | Report §18.4; `CheckSATDecision0`; `CheckFinal0`. | `CheckSATBounds0`; final polynomial-bound record. | `pcc-final-framework0.mjs`; `pcc-final0.mjs`; final-framework and final tests. | Approximate rather than exact minimisation is accepted, comparator direction is wrong, or the decision record is not bound to the accepted GPack. |
| 8. Package sufficiency | The finite package contains every required theorem, row, rule, bound, and linkage needed for the route. | `PCCPack`, `CheckPackSufficiency0`, proof DAG, reflection, firewalls | `PackSufficiencyTheorem`; global proof DAG; reflection registry; local and global checkers. | Bounds ledgers, schedule, row generation, and package theorem all claim finite polynomial checking. | `pcc-pack-sufficiency0.mjs`; `pcc-global-proof-dag0.mjs`; `pcc-global-firewalls0.mjs`; `pcc-rows0.mjs`; package tests. | A required theorem is represented only by an assertion-shaped field, a missing premise still accepts, a reflection maps a weaker checker to a stronger theorem, or coverage is incomplete. |
| 9. Materialised package acceptance | The actual generated package bytes satisfy the concrete top-level checker and public claim boundary. | `GeneratePCCPack0`, `CheckConcreteMaterializedPCCPack0`, `CheckPCCPackexp0` | Concrete package checker and record-alignment checks. | Checker runtime must be polynomial in package/input size; generation is explicitly untrusted. | `pcc-generate-pcc-pack0.mjs`; `pcc-pack-concrete-materialized0.mjs`; `pcc-check-pcc-pack-exp0.mjs`; materialised tests. | Checker acceptance can be obtained with missing concrete coverage, mismatched records, noncanonical JSON, or a changed claim boundary. |
| 10. Replay and publication | The accepted package is the package replayed and named by the final certificate, release gate, and report. | `AcceptRun`, replay, final certificate, release gate, final proof report | Acceptance-run, canonical-byte replay, final linkage, exact theorem fields. | Replay and checking are claimed polynomial over finite artefacts. | `pcc-accept-run0.mjs`; `pcc-final-acceptance-replay0.mjs`; certificate, release-gate, and proof-report modules/tests. | Digest-only substitution, skipped phase, stale package, theorem drift, reject run emitting a public conclusion, or mismatched canonical bytes. |
| 11. Release identity | Published files are the files named by the release. | artefact tag, `release-seal.json`, `SHA256SUMS` | File hashes, sizes, paths, tag/commit coordinates. | Not part of the SAT runtime claim. | Sealed artefact directory; `REPRODUCE.md`; independent `sha256sum`. | Missing/mismatched bytes or stale coordinates. A successful hash is not evidence against a mathematical counterexample. |

## 5. Where correctness is asserted

The route has several distinct correctness obligations. A reviewer should not treat a single top-level `accept` as proving all of them automatically.

### 5.1 Semantics and replacement correctness

The base framework claims that a compatible subcircuit can be replaced by a smaller same-frontier circuit without changing the global Boolean function. Package E is intended to make each constructive saving explicit and checkable.

Review targets:

- exact input and output semantics of direct-wire NAND words;
- compatibility of support boundaries;
- same-frontier equality;
- charge ownership and size accounting;
- obligation creation and discharge;
- transport of gains through normalization and splice.

Primary artefacts:

```text
canonical_proof_report.tex §§2–6
pcc-local-packages0.mjs
pcc-global-proof-dag0.mjs
pcc-global-firewalls0.mjs
```

### 5.2 Locked-NAND reduction correctness

The reduction requires all of these claims:

1. NAND conversion preserves satisfiability.
2. Macro truth tables are correct.
3. slot families are disjoint and locks are fresh;
4. every baseline output is distinct, nonconstant, and nonprojection;
5. the prefix covers every distinguished check exactly as claimed;
6. the trace predicate is equivalent to a valid NAND evaluation;
7. unsatisfiability makes the final output identically zero on the whole carrier;
8. satisfiability makes the fresh-lock output distinct from the baseline;
9. the baseline formula and four-gate overhead are exact.

The checker records these through GPack fields, G proof-DAG nodes, row coverage, and final G linkage. A reviewer must still verify that the implemented predicates prove the mathematical statements rather than merely restating them as booleans.

The current Lean reconstruction now proves items 1--9 for its typed
topological NAND circuit and fixes a strict external source/target grammar.
It serializes the complete candidate and baseline, rejects malformed bytes,
and proves the pure bitstring transformation preserves satisfiability at the
threshold. A literal 228-state, 2,052-rule source parser now decides every
bitstring exactly: valid source bytes are preserved, invalid bytes produce the
empty word, and the compiled parser cannot time out within
`6 * 4096 * (n + 1)^3` raw transitions. It is packaged as a polynomial-time
language machine, a nonexpanding polynomial-time validation function, and a
leaf raw-machine refinement.

The exact target emitter, parser/emitter composition, runtime and output-size
bounds, and final strict-v0 `PolynomialReduction` package are now formalized.
A separate fixed all-input machine computes the exact encoded CNF-to-NAND
translation in polynomial time and packages both the direct
`CNFSAT`-to-`EncodedNANDSAT` reduction and its explicit composition with the
strict locked-NAND reduction. M186 makes the report-facing SAT and locked-NAND
interfaces exact aliases of these concrete languages, reuses the compiled NP
verifier and all-bitstring reduction, and removes the duplicate locked-NAND
project axiom and caller trust field. M187 makes the report-facing residual-band
language the general concrete encoded direct-wire minimum-threshold predicate
and replaces the supplied locked-to-residual edge with the identity reduction.
M188 then makes report-facing PCCPack generation and checking transparent typed
definitions over an explicit `PCCMinLoopCertificate`, removing the final two
project-specific axiom declarations and the generator/checker trust field.
M189 adds general well-founded PCCMin control flow under an explicit
proof-bearing `PCCMinTotalOracle`: strict gain responses preserve semantics and
lower residual slack, while terminal responses carry exact-minimum or ZeroSlack
evidence. The loop returns an exact minimum and has a checked gain-iteration
bound for arbitrary finite direct-wire implementations. M190 adds the preceding
proof-bearing `PCCMinTotalNormalizer` stage: direct normalization gains remain
strict, gains found by the following oracle lift through non-increasing semantic
normalization, and exact or ZeroSlack endpoints transport back before the same
recursive loop runs. Exhaustive reference minimization remains only a regression
fixture and semantic specification, not a polynomial algorithm, and the total
normalizer, total oracle, and explicit loop certificate are still not
constructed. M191 opens that oracle into proof-bearing HResolve and
BudgetResolve outcomes followed by arbitrary finite selector rows scanned in
canonical rank order. ZeroSlack is reachable only after the scan retains one
typed blocker equation for every selector in every rank row. The resolver
algorithms, selector rows, realizer, blocker semantics, and final ZeroSlack
closure remain supplied rather than constructed. M192 removes the arbitrary
row and proof-bearing realizer inputs at the selector stage: it checks
data-only gain/HN/budget/lower-seed claims at every canonical Packet handle and
derives exact rows from the complete handle list and supplied rank map. The
family, ranks, claims, resolver algorithms, blocker semantics, and ZeroSlack
closure are still supplied. M193 removes that opaque closure callback by
reflecting complete checked rank-row silence into the executable selector
silence checker and applying checked HB no-outcome closure to eliminate every
faithful handle. The exact remaining premise says that positive residual slack
constructs a faithful canonical handle; under that supplied bridge, the final
contradiction yields conditional ZeroSlack and feeds the same loop. Terminal
data, that positive-slack bridge, resolver algorithms, normalizer, and
polynomial bounds remain supplied or open. M194 replaces the direct faithful-
selector premise with the earlier positive-slack-to-constant-activation
boundary: the general BN6 theorem constructs a Packet and executable
route-clear payload checks construct faithfulness in the canonicalized table.
Constant activation, terminal-family construction, payload and route-clear
evidence, resolver algorithms, normalizer, and polynomial bounds remain
supplied or open. M195 removes the opaque constant-activation callback from its
new endpoint by exhaustively comparing the same-candidate checked BCEL nucleus
with the Packet carrier, cut value, and every proper-cut activation weight.
Coherence derives constant activation and conditional ZeroSlack; any failure is
retained as an exact typed mismatch route. The supporting terminal data remain
supplied, the routes are not yet gains or globally decreasing, and the subset
scan may be exponential. The
M196 boundary then removes the independently supplied Packet carrier and cut
value: both, carrier uniqueness, and cut-value positivity are constructed from
the checked BCEL nucleus. The carrier and cut-value mismatch branches become
impossible, leaving the exact proper-cut activation mismatch or conditional
ZeroSlack. The grouped cells and payloads remain supplied, so this still does
not complete PkgC/BN3--BN6 integration; the remaining route has no proved gain
or global rank-decrease semantics, and the inherited subset scan may be
exponential. M197 then constructs the structural grouping from supplied raw
positive supports and payload atoms: supports are normalized inside the
checked carrier, singleton consumer systems are built, duplicate footprints
are coalesced, and every positive payload atom is retained in its canonical
group. The raw cells still are not derived from terminal BN3, BN4, BN5, or PkgC
data. M198 then proves that this coalescing preserves the exact direct raw
positive-cell crossing-mass sum on every cut and exposes the surviving BCEL
mismatch against that raw ledger. M199 replaces the resulting endpoint's
all-proper-cut powerset scan with an exact two-anchor, three-singleton, or
four-plus full-span basis and a total typed classifier. The raw cells, forced
basis acceptance or decreasing rejection routes, global descent, and complete
polynomial construction remain open. M200 then proves that singleton and pair
proper cuts alone are a complete quadratic-size test family and returns the
first exact small-cut raw activation mismatch on rejection. That mismatch
still lacks gain and global rank-decrease semantics, while the raw cells and
complete encoded-input construction remain supplied, so the
risk-weighted estimate remains 35 percent and zero of five global gates are
closed.
M201 then classifies arbitrary finite supplied active V54 consumer systems into
the first exact PkgC same-key cancellation or an all-singletonized branch whose
raw BN6 positive-cell supports are derived from the consumer footprints. It
preserves payload order and exact activation weight on every cut, but the
terminal source systems, active cuts, payloads, and typed restorer remain
supplied, cancellation has no global gain or rank-decrease theorem, and the
complete encoded-input construction remains open. The risk-weighted estimate
therefore remains 35 percent and zero of five global gates are closed.
M202 composes those source-derived cells with the checked sparse BN6/BCEL
route. It retains exact cancellation, conditional ZeroSlack, or one exact
singleton/pair source-ledger activation mismatch, without accepting a second
raw-cell list. Source construction, downstream tables, selector silence,
blocker semantics, gain, global rank decrease, and complete polynomial bounds
remain supplied or open, so the risk-weighted estimate remains 35 percent and
zero of five global gates are closed.
M203 then computes the exact ambient BN4 remainder for M202's PkgC
cancellation with order-independent, multiplicity-preserving remove-first
recursion. It returns the induced complete residual-ledger reduction or proves
that no exact remainder embedding exists, and constructs the candidate-bound
BN4 kernel against the same checked BCEL nucleus. The ambient ledger and other
source/downstream objects remain supplied, the remainder is not proved empty,
and incompatibility is not yet a global decreasing route, so the risk-weighted
estimate remains 35 percent and zero of five global gates are closed.
M204 replaces the local always-total typed restorer with the finite exact-
coordinate restoration classifier. It retains the first Hall deficit and
forced Q route, or constructs balanced BN4 unit cells from complete coverage
and computes the exact ambient remainder and residual reduction in arbitrary
order, with a proof-bearing no-embedding alternative. The restoration
universe and maps, consumer system and ambient ledger remain supplied;
coordinate coverage is not semantic full-candidate materialization and no
returned branch is yet a verified global rank decrease. The risk-weighted
estimate therefore remains 35 percent and zero of five global gates are
closed.
M205 lifts M204 over the complete arbitrary-finite active PkgC source ledger
in list order. If every source singletonizes, the complete BN6 positive-cell
ledger is constructed with exact length, payload order, and all-cut activation
conservation. Otherwise, the first source-member Hall deficit, exact ambient
reduction, or no-embedding witness is retained. The source cells and cuts,
payloads, restoration universes and maps, and ambient ledgers remain supplied;
the computed remainder is not proved empty and no obstruction has a complete
global gain or rank-decrease theorem. Formal artefact coverage is 181 of 183,
the risk-weighted estimate remains 35 percent, and zero of five global gates
are closed. See
[lean_residual_terminal_pkgc_restoration_coverage_bn6_ledger.md](lean_residual_terminal_pkgc_restoration_coverage_bn6_ledger.md).

M206 binds those source and ambient ledgers to the same computed BCEL nucleus
and composes only the all-singletonized branch with the checked sparse BN6/BCEL
Packet/HB classifier. Exact Hall, residual-reduction, and no-embedding
outcomes remain first-class; the downstream alternatives are conditional
ZeroSlack or a proper singleton/pair activation mismatch reflected to the
original enriched source ledger. Terminal, source, restoration, ambient, rank,
claim, dependency, and selector data remain supplied. No local obstruction has
yet been proved a complete global descent. Formal artefact coverage is 182 of
184, the risk-weighted estimate remains 35 percent, and zero of five global
gates are closed. See
[lean_pccmin_checked_packet_pkgc_restoration_coverage_bn6_bcel_route.md](lean_pccmin_checked_packet_pkgc_restoration_coverage_bn6_bcel_route.md).

M207 compiles M206's successful ambient extraction into a strict formal
rank transition. Exact permutation preserves multiplicity, the removed
coverage subledger has strictly positive mass-summed unsigned charge, and the
remainder decreases the ten-coordinate rank at `chargeSize` for every fixed
surrounding context while preserving the canonical residual ledger. The other
M206 branches and all supplied terminal, Packet, and HB inputs remain open.
Formal artefact coverage is 183 of 185, the risk-weighted estimate remains 35
percent, and zero of five global gates are closed. See
[lean_pccmin_checked_packet_pkgc_restoration_coverage_charge_descent.md](lean_pccmin_checked_packet_pkgc_restoration_coverage_charge_descent.md).

M208 replaces further fixed-slot Cook-Levin control extension with one
all-input full-schedule controller. The semantic cursor returns the entire
canonical token schedule, and a deterministic finite raw machine computes and
consumes the exact polynomial body-opportunity count before materializing the
terminal coordinate within an explicit polynomial bound. The raw loop does not
yet decode or emit each body entry, so the complete formula builder and
packaged reduction remain open. Formal artefact coverage is 184 of 186, the
risk-weighted estimate remains 35 percent, and zero of five global gates are
closed. See
[lean_cook_levin_builder_full_schedule_cursor_controller.md](lean_cook_levin_builder_full_schedule_cursor_controller.md).

M209 adds the first uniform raw interpretation layer for arbitrary schedule
coordinates. One fixed 54-rule comparator chooses the exact header versus
post-header branch, agrees with the top-level direct lookup, and has exact
accept/reject, in-range polynomial compiled-time, one-step-short, and malformed
input theorems. It does not decode the post-header clause/slot quotient or emit
a body token, so the complete formula builder and packaged reduction remain
open. Formal artefact coverage is 185 of 187, the risk-weighted estimate
remains 35 percent, and zero of five global gates are closed. See
[lean_cook_levin_builder_arbitrary_slot_header_router.md](lean_cook_levin_builder_arbitrary_slot_header_router.md).

M210 refines every post-header coordinate with one structurally recursive
semantic rectangle decoder. It returns the exact finite clause/within-clause
pair, the unique `Finish`, or the out-of-range suffix; reconstructs body
coordinates; agrees with direct token lookup; and reads the exact shifted
remainder from M209's checked raw result configuration. It does not implement
raw division or raw body-token emission, so the complete raw formula builder
and packaged reduction remain open. Formal artefact coverage is 186 of 188,
the risk-weighted estimate remains 35 percent, and zero of five global gates
are closed. See
[lean_cook_levin_builder_arbitrary_slot_post_header_decoder.md](lean_cook_levin_builder_arbitrary_slot_post_header_decoder.md).

M211 implements one fixed 99-rule unary quotient/remainder machine. Every
natural dividend and positive width has an exact accepting trace with the
natural quotient and strict remainder, exact reconstruction, exact six-step
raw compilation, a one-step-short timeout boundary, and a quadratic bound in
the complete unary input length. M210 body coordinates instantiate that same
decoded pair. The divider is not yet spliced onto M209's checked raw result and
emits no body token, so the complete raw formula builder and packaged reduction
remain open. Formal artefact coverage is 187 of 189, the risk-weighted estimate
remains 35 percent, and zero of five global gates are closed. See
[lean_cook_levin_builder_post_header_raw_divider.md](lean_cook_levin_builder_post_header_raw_divider.md).

M212 joins M209's exact checked remainder, M210's all-coordinate semantic route
classifier, and M211's exact divider through executable Lean orchestration.
For every natural coordinate it derives the header or post-header launch
without supplied route data, retains both exact traces, recovers body,
`Finish`, and out-of-range results, excludes out-of-range post-header results
inside the complete schedule, and bounds the combined compiled work by one
verifier-derived source-size polynomial. It is not a literal raw tape rewrite,
does not preserve the complete builder workspace through such a bridge, and
emits no body or `Finish` token, so the complete raw formula builder and
packaged reduction remain open. Formal artefact coverage is 188 of 190, the
risk-weighted estimate remains 35 percent, and zero of five global gates are
closed. See
[lean_cook_levin_builder_post_header_raw_launch.md](lean_cook_levin_builder_post_header_raw_launch.md).

M213 replaces that value-level launch with one fixed 351-rule literal tape
bridge from both exact M209 post-header terminal layouts into a shielded M211
divider input. It copies zero or the exact positive shifted remainder plus the
positive problem width, preserves arbitrary exterior workspace, retains exact
bridge and divider traces, decodes the final quotient and remainder, compiles
at six raw steps per work step, times out one step short, and fits one
verifier-derived source-size polynomial for every in-range coordinate. It
emits no selected body or `Finish` token and does not iterate the full schedule,
so the complete raw builder and packaged reduction remain open. Formal
artefact coverage is 189 of 191, the risk-weighted estimate remains 35 percent,
and zero of five global gates are closed. See
[lean_cook_levin_builder_post_header_raw_tape_bridge.md](lean_cook_levin_builder_post_header_raw_tape_bridge.md).

M214 continues from that exact divider tape with one fixed 180-rule literal
post-divider classifier. It copies the problem-derived clause count from a
restored workspace sidecar, preserves the full exterior and remainder ledger,
and exposes the quotient to a shielded M209 comparator. Exact bridge and
comparator traces compile at six raw steps per work step, time out one step
short, agree with every in-range M210 body or unique `Finish` route, and fit
one verifier-derived source-size polynomial. It still does not inspect, select,
emit, or append the corresponding token or iterate the complete schedule, so
the complete raw builder, `RawRefinement`, and packaged reduction remain
open. Formal artefact coverage is 190 of 192, the risk-weighted estimate
remains 35 percent, and zero of five global gates are closed. See
[lean_cook_levin_builder_post_divider_raw_route_classifier.md](lean_cook_levin_builder_post_divider_raw_route_classifier.md).

M215 derives every post-header padding, body-token, or unique `Finish` entry
from the canonical schedule without a supplied route or token. It retains
M214's physical classifier contract for arbitrary workspace, leaves the
canonical emitted prefix unchanged at padding, and runs the existing fixed
59-rule appender for every populated coordinate to reach exactly the next
emitted prefix. Exact work and six-for-one compiled traces, one-step-short
nonhalting, and the combined staged source-size polynomial are all checked.
The selection handoff is still executable Lean orchestration rather than one
literal raw selector, and the schedule is not iterated, so the complete raw
builder, `RawRefinement`, and packaged reduction remain open. Formal artefact
coverage is 191 of 193, the risk-weighted estimate remains 35 percent, and
zero of five global gates are closed. See
[lean_cook_levin_builder_post_divider_selected_token_launch.md](lean_cook_levin_builder_post_divider_selected_token_launch.md).

M216 recursively consumes every verifier-derived post-header schedule
opportunity without a supplied coordinate, token, route, trace, schedule, or
precomputed formula. Every bounded run equals the canonical emitted prefix and
the complete run equals the exact `encodeCNFTokens problem.formula` stream.
Every coordinate retains M215's physical classifier/appender evidence for
arbitrary workspace, while a recursive accumulator bounds the aggregate staged
compiled work by one source-size polynomial. The recursion is executable Lean
orchestration over separately checked stages, not one literal raw-machine loop
or a physical tape-to-tape inter-stage handoff, so complete builder
`RawRefinement` and the packaged reduction remain open. Formal artefact
coverage is 192 of 194, the risk-weighted estimate remains 35 percent, and zero
of five global gates are closed. See
[lean_cook_levin_builder_complete_schedule_iteration.md](lean_cook_levin_builder_complete_schedule_iteration.md).

M217 replaces M215's value-level selector-to-appender handoff with one
fixed 64-rule physical work machine for the complete five-symbol request
alphabet. A tape-resident padding or CNF-token request restores the canonical
builder left boundary and either preserves the emitted prefix or enters the
existing renamed 59-rule appender. Exact work and six-for-one compiled traces
cover arbitrary input, exterior workspace and output prefix; malformed blank
requests and one-step-short fuel remain nonhalting. Every canonical
post-header coordinate derives its request from `scheduleEntry`, and the
stage fits one verifier-derived source-size polynomial. The request cell is
still an input to this stage: it is not produced from M214's raw classifier,
connected through a literal classifier-to-dispatcher tape handoff, or iterated
as one physical schedule loop, so complete builder `RawRefinement` and the
packaged reduction remain open. Formal artefact coverage is 193 of 195, the
risk-weighted estimate remains 35 percent, and zero of five global gates are
closed. See
[lean_cook_levin_builder_physical_optional_token_dispatch.md](lean_cook_levin_builder_physical_optional_token_dispatch.md).

M218 composes M217's fixed physical optional-token dispatcher across every
canonical post-header coordinate. The recursive output agrees with the canonical
emitted prefix at every bounded coordinate and reaches the exact
`encodeCNFTokens problem.formula` stream at the complete schedule. Every step
retains exact work, compiled, and one-step-short physical traces for arbitrary
input and exterior workspace, carries the M214 physical classifier evidence, and
the aggregate compiled work fits one verifier-derived source-size polynomial.
Each request is still constructed in Lean from the canonical schedule rather
than produced by the raw classifier on tape, and successive configurations are
not connected by one literal raw-machine loop. Complete builder
`RawRefinement` and the packaged reduction therefore remain open. Formal
artefact coverage is 194 of 196 current scoped publication rows earned; the
risk-weighted estimate remains 35 percent, and zero of five global gates are
closed. See
[lean_cook_levin_builder_physical_dispatch_schedule.md](lean_cook_levin_builder_physical_dispatch_schedule.md).

M219 closes the first literal classifier-to-request branch for the unique
canonical `Finish` coordinate. The problem derives that coordinate internally,
M214 proves its equal-classifier result, and the canonical builder workspace is
preserved as a protected suffix beyond the comparator's end marker. One fixed
writer produces M217's tape-resident `Finish` request, and one collision-free
137-rule composition runs the classifier, writer, and dispatcher. Exact work,
six-for-one compiled, and one-step-short traces hold for arbitrary classifier
exterior, and one verifier-derived polynomial bounds the compiled work. Body-token
and padding request derivation, the preceding suffix-preserving classifier handoff,
one literal repeated loop, complete builder `RawRefinement`, and the packaged
reduction remain open. Formal artefact coverage is 195 of 197 current scoped
publication rows earned; the risk-weighted estimate remains 35 percent, and zero
of five global gates are closed.
See
[lean_cook_levin_builder_physical_finish_request.md](lean_cook_levin_builder_physical_finish_request.md).

M220 completes the suffix-preserving physical classifier pipeline for every
canonical post-header coordinate. One fixed collision-free 711-rule machine
composes M213's router-to-divider bridge, M211's exact divider, M214's
divider-to-comparator bridge and comparator through three exact tape handoffs
over arbitrary protected builder workspace. The final raw state agrees with
M214's typed body-or-`Finish` semantics, while exact work, six-for-one compiled
execution, one-step-short nonhalting, component decomposition, and one
source-size polynomial bound are checked. Body-token and padding request symbols
are not yet written and the classifier result is not connected to M217's
dispatcher; one literal repeated schedule loop, complete builder `RawRefinement`,
and the packaged reduction remain open. Formal artefact coverage is 196 of 198
current scoped publication rows earned; the risk-weighted estimate remains 35
percent, and zero of five global gates are closed. See
[lean_cook_levin_builder_physical_classifier_pipeline.md](lean_cook_levin_builder_physical_classifier_pipeline.md).

M221 closes the full-classifier-to-`Finish`-request-cell edge. It derives the
unique canonical `Finish` coordinate, reinterprets M220's terminal verdict names
without changing classifier transition semantics, and chains the complete
classifier to M219's one-cell writer as one collision-free 721-rule machine.
For arbitrary protected workspace, the final tape is exactly M220's terminal
tape with the focused end marker replaced by M217's `Finish` request; exact work,
six-for-one compiled execution, one-step-short nonhalting, and a source-size
polynomial bound remain checked. Body-token and padding request generation,
dispatcher-ready workspace orientation and connection, one literal repeated
loop, builder `RawRefinement`, and the packaged reduction remain open. Formal
artefact coverage is 197 of 199 current scoped publication rows earned; the
risk-weighted estimate remains 35 percent, and zero of five global gates are
closed. See
[lean_cook_levin_builder_physical_classifier_finish_request.md](lean_cook_levin_builder_physical_classifier_finish_request.md).

M222 closes the unique full-classifier `Finish` workspace-orientation edge.
It inserts one blank sentinel before the canonical builder workspace, derives
the complete M220/M221 classifier prefix, proves that prefix is blank-free, and
chains M221 to a fixed ten-rule left scanner. The resulting collision-free
740-rule machine crosses exactly the derived prefix and halts with a tape equal
to the spatial mirror of M217's canonical `Finish` request entry, while
retaining the classifier evidence as exterior data. Exact work, six-for-one
compiled execution, one-step-short nonhalting, a prefix-size bound, and one
source-size polynomial bound are checked. M217 is not yet executed on the
mirrored representation; body-token and padding request generation, all-route
dispatcher connection, one literal repeated loop, builder `RawRefinement`, and
the packaged reduction remain open. Formal artefact coverage is 198 of 200
current scoped publication rows earned; the risk-weighted estimate remains 35
percent, and zero of five global gates are closed. See
[lean_cook_levin_builder_physical_classifier_finish_workspace_orientation.md](lean_cook_levin_builder_physical_classifier_finish_workspace_orientation.md).

M223 closes reflected dispatcher execution for the unique full-classifier
`Finish` path. It defines spatial reflection for arbitrary literal work
machines, proves that rule lookup, steps, and exact runs commute with reflection,
and specializes that result to M217's fixed 64-rule dispatcher. Chained after
M222, the resulting collision-free 813-rule machine runs from the complete
classifier entry to a reflected appender endpoint containing the complete
canonical CNF token stream. Exact work, six-for-one compiled execution,
one-step-short nonhalting, and one source-size polynomial bound are checked.
Body-token and padding request generation, all-route dispatcher connection, one
literal repeated loop, builder `RawRefinement`, and the packaged reduction
remain open. Formal artefact coverage is 199 of 201 current scoped publication
rows earned; the risk-weighted estimate remains 35 percent, and zero of five
global gates are closed. See
[lean_cook_levin_builder_physical_classifier_finish_mirrored_dispatch.md](lean_cook_levin_builder_physical_classifier_finish_mirrored_dispatch.md).

A deterministic target decider, the
CNFSAT-in-P result, remaining NP-hardness transport, and `P = NP` remain
unproved. See
[`lean_concrete_legacy_locked_nand_compatibility.md`](lean_concrete_legacy_locked_nand_compatibility.md).
See also
[`lean_concrete_residual_band_compatibility.md`](lean_concrete_residual_band_compatibility.md).
See also
[`lean_typed_pccpack_reflection.md`](lean_typed_pccpack_reflection.md).
See also
[`lean_pccmin_total_oracle_loop.md`](lean_pccmin_total_oracle_loop.md).
See also
[`lean_pccmin_normalize_oracle_composition.md`](lean_pccmin_normalize_oracle_composition.md).
See also
[`lean_pccmin_rank_ordered_oracle.md`](lean_pccmin_rank_ordered_oracle.md).
See also
[`lean_pccmin_checked_packet_bn6_hb_zeroslack_bridge.md`](lean_pccmin_checked_packet_bn6_hb_zeroslack_bridge.md).
See also
[`lean_pccmin_checked_packet_ranked_selector.md`](lean_pccmin_checked_packet_ranked_selector.md).
See also
[`lean_pccmin_checked_packet_hb_zeroslack_bridge.md`](lean_pccmin_checked_packet_hb_zeroslack_bridge.md).
See also
[`lean_pccmin_checked_packet_bn6_bcel_activation_route.md`](lean_pccmin_checked_packet_bn6_bcel_activation_route.md).
See also
[`lean_pccmin_checked_packet_bn6_bcel_derived_family.md`](lean_pccmin_checked_packet_bn6_bcel_derived_family.md).
See also
[`lean_pccmin_checked_packet_bn6_bcel_canonical_grouping.md`](lean_pccmin_checked_packet_bn6_bcel_canonical_grouping.md).
See also
[`lean_pccmin_checked_packet_bn6_bcel_canonical_cut_ledger.md`](lean_pccmin_checked_packet_bn6_bcel_canonical_cut_ledger.md).
See also
[`lean_pccmin_checked_packet_bn6_bcel_canonical_constant_cut_basis.md`](lean_pccmin_checked_packet_bn6_bcel_canonical_constant_cut_basis.md).

The reconstruction now also verifies the iteration-count subclaim used by
`PCCMin`: for any finite supplied chain whose every adjacent replacement is a
strict equivalent gain, the final residual slack plus the number of steps is
at most the initial residual slack. Since the complete locked candidate has
residual slack at most four, no such verified chain can contain more than four
gains. This does not construct the chain, prove its completeness, justify a
stopping decision, or prove the remaining exactness and runtime claims.

The semantic stopping condition is now also kernel checked over the whole
finite direct-wire implementation space. Positive residual slack holds if and
only if some strict equivalent gain exists; zero residual slack and semantic
minimality hold if and only if no such implementation exists. Thus a verified
chain endpoint can be packaged as an exact minimum once global no-gain is
separately proved. The proof uses exhaustive reference minimization as its
existence witness. It does not derive global absence from a finite candidate
scan, construct the report's `ZeroSlack` certificate, generate the route, or
provide a polynomial stopping algorithm.

The latest conditional bridge now derives global absence from the exhaustive
Packet scan only when the caller supplies an explicit gain-coverage certificate
mapping every strict equivalent implementation to an original payload in a
canonical source cell. Under that premise, the unresolved branch carries a
proof-bearing semantic minimum and zero residual slack. An empty-family
positive-slack regression proves that finite silence cannot infer the premise.
This is not unconditional ZeroSlack: certificate construction, manuscript
faithfulness and compatibility, typed blockers, encoded-size bounds, and
polynomial generation/runtime remain open.

The finite `R-ChargeSurplus` arithmetic edge is now kernel checked separately.
For arbitrary finite ledgers, exact multiplicity-preserving occurrence pairing,
pairwise weight preservation, and an unmatched positive support charge force
strictly smaller replacement weight. Exact gate-count accounting and
independently proved semantics then yield a `StrictEquivalentGain` and residual
descent. The replacement circuit, its ledger, and the pairing are not yet
constructed from a Packet selector, so this result is not unconditional
ZeroSlack and does not complete the realizer or its typed failure routes.

The next checked edge accepts data-only unit-charge blueprints for replacements.
It derives both charge ledgers canonically from the two NAND gate counts,
validates exact occurrence pairing with a constructive remove-first checker,
requires a nonempty unmatched remainder, and checks semantic equivalence. An
accepted blueprint therefore constructs the charge-surplus realization and a
strict equivalent gain without assuming gate decrease. Every blueprint atom
behind every canonical handle in one supplied explicit family is scanned, but
the unresolved result is only family-local validator silence. Blueprint and
family construction, selector faithfulness/compatibility, typed blockers,
complete routing, and polynomial bounds remain open.

The checked Packet typed-realizer contract replaces untyped faithful-row
silence with a data-only typed contract over arbitrary finite selector lists. Each accepted
faithful row is exactly a checked unit-charge gain, an active HN bot at no
greater supplied rank, an active budget bot at no greater supplied rank, or a
faithful strictly lower-rank seed bot. The specialization checks every
canonical handle of one supplied grouped BN6 family. Rank assignment,
faithfulness, claims, and blocker activity remain explicit tables; their
manuscript semantics, construction, HB acyclicity, global silence, and
polynomial bounds remain open.

The checked HB blocker-graph acyclicity boundary takes the next local step.
For an arbitrary supplied finite HN/BUD edge list, it exhaustively checks that
the finite rank indices embed strictly into the existing exact ten-coordinate
residual rank and that every dependency edge strictly descends that rank.
Acceptance derives accessibility and a well-founded dependency relation, and
excludes every nonempty directed cycle rather than only self-loops. A valid
lower-seed bot also inherits exact-rank descent, and the result composes with
every faithful canonical typed-realizer handle. The graph, edges, rank map,
dependency completeness, and blocker semantics remain supplied or open; this
is not rank-complete selector silence, the full HB negative closure,
unconditional ZeroSlack, or a polynomial bound.

The checked total-table HB dependency boundary removes the graph's separate
edge-list input. Every HN and budget node at every finite rank has one total
data-only dependency row, and the graph is materialized mechanically from all
rows. Exact theorems identify graph edges with row membership in both
directions. The checker verifies every listed dependency against the existing
ten-coordinate rank, yielding accessibility, well-founded induction for any
predicate with an explicit local step, and exclusion of every nonempty cycle.
HN and budget typed bots now name covered rows, while lower seeds inherit
exact-rank descent. The table and local step remain inputs. This closes finite
representation omissions only, not blocker semantics or semantic dependency
completeness from terminal data, so it is not rank-complete selector silence,
the full HB negative closure, unconditional ZeroSlack, or a polynomial bound.

The checked HB active-dependency closure supplies that structural local step
for the explicit tables. It projects HN/BUD activity from the typed-realizer
environment and exhaustively requires every active node to have an active
dependency in its own total row. Combined with exact-rank descent,
well-founded induction forces all supplied activity bits false. Typed-realizer
composition therefore removes HN and budget bots and retains only a verified
gain or faithful strictly lower-rank seed. The activity and dependency tables
are still inputs: blocker semantics and semantic dependency completeness are
not derived from terminal data. Gain exclusion, lower-seed closure,
rank-complete selector silence, the full HB negative closure, unconditional
ZeroSlack, and polynomial bounds remain open.

The conditional selector-silence rank closure now consumes explicit global
semantic gain exclusion after checked HB inactivity. An accepted faithful row
can then name only a faithful strictly lower-rank selector, and strong induction
on the supplied finite rank proves every canonical handle nonfaithful. The
gain-coverage specialization derives global exclusion only from an explicit
coverage certificate plus exact source-cell no-gain. This does not establish
selector faithfulness or compatibility, construct the tables or certificate
from terminal data, prove unconditional HB negative closure or ZeroSlack, or
provide encoded-size and polynomial-runtime bounds.

The executable selector-silence induction now removes that global semantic
no-gain premise from the theorem interface. A data-only checker exhaustively
requires every canonical realizer claim to be a typed bottom. Checked HB
closure eliminates HN/BUD bottoms, and strong finite-rank induction eliminates
faithful lower seeds. The grouped family, ranks, faithfulness, claims, activity,
dependency rows, and rank map remain explicit inputs and are not constructed
from terminal data. This is not the full unconditional HB negative closure,
ZeroSlack, or a polynomial completeness theorem.

The Packet selector-faithfulness routing bridge now checks ten data-only fields
on the canonical positive source payload behind every handle, exposes the first
failed route, and binds the computed result exactly to the supplied HB table.
Every positive BN6 Packet branch supplies a handle. Complete route-clear
acceptance therefore produces a faithful handle, contradicting accepted
executable selector silence. The grouped family, payload checks, rank tags,
binding, claims, blocker activity, and dependencies remain explicit inputs;
positive slack, SaturatePositive, BCELReady, terminal-data construction,
complete route silence, unconditional ZeroSlack, and polynomial PCCMin remain
open.

The canonical Packet faithfulness-table constructor now removes that
independent faithfulness-table choice. For every arbitrary finite grouped BN6
family, it rebuilds the typed-realizer environment with faithfulness equal to
the canonical payload computation while preserving the rank map, HN/BUD
activity, and realizer claims exactly. The binding checker accepts the rebuilt
table by construction, so the positive-Packet versus selector-silence
contradiction no longer takes a binding premise. The payload checks, rank map,
family, claims, activity and dependency rows remain explicit inputs rather than
terminal-candidate constructions. This is not the manuscript's full external
selector compatibility claim, complete route silence, unconditional HB
negative closure, ZeroSlack, or a polynomial bound.

The total Packet selector first-route outcome now proves the converse side of
that payload classifier. No route is returned exactly on checker acceptance,
and every rejection returns the earliest of the ten typed routes. Thus every
positive Packet yields a faithful canonical handle or a concrete first route.
For the canonicalized table, accepted executable selector silence and HB
active-dependency closure eliminate the faithful alternative without assuming
route-clear acceptance or a separate binding. This names every checked payload
failure, but it does not prove a route's external terminal semantics or map the
route into a decreasing complete global outcome system. The terminal data and
all remaining tables are still explicit inputs.

Exact Packet first-route semantics now strengthens that route witness at the
same supplied-data boundary. Each of the ten route constructors is equivalent
to the corresponding earliest failed payload field, so the classifier also
proves all preceding checks accepted. The exact failure is unique, and the
canonical positive-Packet/HB endpoint retains this proof alongside the route.
This does not derive payload fields from terminal data, validate their external
manuscript semantics, or yet provide a decreasing complete global outcome.

Rank-reflected Packet descent now replaces the final caller-supplied Boolean
with `terminalResidualRankLTBool after before`. The first nine fields are
preserved exactly. A computed `.descent` failure therefore proves that the
supplied transition is nondecreasing in the exact ten-coordinate `RankWF`
relation, and the canonical Packet/HB endpoint returns that proof or an
earlier exact route. The before/after ranks and remaining nine fields are still
explicit inputs; this is one mapped route, not complete global routing.

Canonical Packet rank-tag reflection now removes the payload's separate copy
of its finite handle rank. The table-owned `rankOf handle` is copied into
`rankTag`, while the exact residual-descent computation is retained. The
canonical classifier therefore cannot return `.rank`; its final `.descent`
route still carries actual nondecrease. The rank map, residual ranks, seven
earlier Boolean fields, and `exactRouteClear` remain explicit inputs. The eight
remaining routes still lack complete external semantics and global routing,
so this does not establish route silence, ZeroSlack, or polynomial PCCMin.

Canonical Packet exact-route reflection now removes the payload's separate
internal source-route bit. Every canonical handle already selects an original
positive payload atom from its exact grouped cell and footprint, so the active
payload sets `exactRouteClear` by construction while retaining the table-owned
rank and computed residual descent. The canonical classifier can return
neither `.exactRoute` nor `.rank`; a final `.descent` route still carries actual
nondecrease. This internal route is not an external exact minimum. The seven
semantic Boolean fields, grouped family, rank map, residual ranks, and HB data
remain explicit. The seven remaining routes still lack complete external
semantics and global routing, so this does not establish route silence,
unconditional ZeroSlack, or polynomial PCCMin.

Canonical Packet charge-route reflection now removes the payload's separate
internal charge bit. The selected original source atom already carries a proof
of strictly positive mass, so the active payload sets `chargeChecked` by
construction while retaining exact-route, rank-tag, and residual-descent
reflection. The canonical classifier can return none of `.charge`,
`.exactRoute`, or `.rank`; a final `.descent` route still carries actual
nondecrease. Positive source mass is not the complete external charge-surplus,
replacement, budget, or selector-compatibility semantics. The six remaining
semantic Boolean fields, grouped family, rank map, residual ranks, and HB data
remain explicit. Those six routes still lack complete external semantics and
global routing, so this does not establish route silence, unconditional
ZeroSlack, or polynomial PCCMin.

Canonical Packet colour-route reflection now removes the payload's separate
internal colour bit. Every canonical handle already has a grouped footprint
proved to lie in the family carrier and to contain at least two atoms, so the
active payload computes `colourChecked` from selector-relevant footprint size
while retaining the carrier-sublist theorem, positive charge, internal source
route, table-owned rank, and exact residual descent. The canonical classifier
can return none of `.colour`, `.charge`, `.exactRoute`, or `.rank`; a final
`.descent` route still carries actual nondecrease. This internal eligibility
check is not full external manuscript colour equivalence. The five remaining
semantic Boolean fields, grouped family, rank map, residual ranks, and HB data
remain explicit. Those five routes still lack complete external semantics and
global routing, so this does not establish route silence, unconditional
ZeroSlack, or polynomial PCCMin.

Canonical Packet typed-frontier route reflection now removes the payload's
separate frontier bit. The selected source payload carries explicit source and
selector frontier signatures of one arbitrary decidable-equality type, so the
active payload computes `frontierChecked` from their equality while retaining
canonical colour, positive charge, internal source route, table-owned rank,
and exact residual descent. The `.frontier` route is equivalent to signature
inequality; equal signatures exclude it. The classifier also continues to
exclude `.colour`, `.charge`, `.exactRoute`, and `.rank`, and a final
`.descent` route carries actual nondecrease. The supplied signatures are not
constructed from terminal data or bound to the manuscript BN5 frontier.
Obligation, activation, direction, and budget remain explicit. Those four
remaining routes still lack complete external semantics and global routing,
so this does not establish route silence, unconditional ZeroSlack, or
polynomial PCCMin.

BN5-bound Packet frontier and obligation route reflection now ties both checks
to the typed terminal BN5 coordinate. The active payload compares the exact
source and selector `frontier` and `obligation` projections while retaining
canonical colour, positive charge, the internal source route, table-owned
rank, and exact residual descent. A `.frontier` first route is exact frontier
inequality. An `.obligation` first route carries prior frontier equality and
exact obligation inequality. The classifier also continues to exclude
`.colour`, `.charge`, `.exactRoute`, and `.rank`, while `.descent` carries
actual nondecrease. The BN5 coordinates remain explicit rather than derived
from terminal data. Activation, direction, and budget are the three remaining
fields and routes; they still lack complete external semantics and global
routing. This does not establish route silence, unconditional ZeroSlack, or
polynomial PCCMin.

BN4 activation-exact Packet route reflection now ties the next check to the
activation atoms nested inside the typed source and selector BN5 coordinates.
The active payload compares those atoms while retaining computed BN5 frontier
and obligation checks, canonical colour, positive charge, the internal source
route, table-owned rank, and exact residual descent. The existing BN4 theorem
proves that activation-atom equality is equivalent to equality of the
canonical activation predicates on every cut. An `.activation` first route
carries prior frontier and obligation equality plus exact activation-atom
inequality. The classifier continues to exclude `.colour`, `.charge`,
`.exactRoute`, and `.rank`, while `.descent` carries actual nondecrease. The
coordinates remain explicit rather than derived from terminal data. Direction
and budget are the two remaining fields and routes; they still lack complete
external semantics and global routing. This does not establish route silence,
unconditional ZeroSlack, or polynomial PCCMin.

Typed Packet direction-route reflection now ties the next check to equality of
explicit source and selector values in an arbitrary direction type. The active
payload retains computed BN5 frontier, obligation, and BN4 activation checks,
canonical colour, positive charge, the internal source route, table-owned rank,
and exact residual descent. A `.direction` first route carries prior frontier,
obligation, and activation equality plus exact typed-direction inequality. The
classifier continues to exclude `.colour`, `.charge`, `.exactRoute`, and
`.rank`, while `.descent` carries actual nondecrease. The direction values
remain explicit rather than derived from terminal data and are not a complete
construction of manuscript `Dir(u)`. Budget is the sole remaining supplied
Boolean field and route; it still lacks complete external semantics and global
routing. This does not establish route silence, unconditional ZeroSlack, or
polynomial PCCMin.

Typed Packet budget-route reflection now ties the final supplied Packet check
to equality of explicit source and selector values in an arbitrary budget
type. The active payload retains computed BN5 frontier, obligation, BN4
activation, and typed direction checks, canonical colour, positive charge,
the internal source route, table-owned rank, and exact residual descent. A
`.budget` first route carries prior frontier, obligation, activation, and
direction equality plus exact typed-budget inequality. The classifier
continues to exclude `.colour`, `.charge`, `.exactRoute`, and `.rank`, while
`.descent` carries actual nondecrease. The budget values remain explicit
rather than derived from terminal data and are not a complete construction of
manuscript `Bud(u)`, its budget envelope, BudgetResolve, or HB budget activity.
Every local Packet field is now computed, but external route adequacy and
global route silence remain open. This does not establish unconditional
ZeroSlack or polynomial PCCMin.

Checked Packet budget/HB activity binding now exhaustively requires every
typed budget mismatch at a canonical handle to activate the HB budget node at
the table-owned rank. The existing checked well-founded HB no-outcome closure
forces that activity false, so an accepted binding yields exact typed budget
equality at every handle and excludes the `.budget` first route. The remaining
outcome is frontier, obligation, activation, direction, or exact residual
nondecrease. The binding, rank map, activity environment, dependency table, and
closure premise remain explicit rather than constructed from terminal data;
this is not BudgetResolve, blocker semantic completeness, full Packet
adequacy, or remaining-route exclusion. Unconditional HB negative closure,
ZeroSlack, and polynomial PCCMin remain open.

Checked Packet semantic/HN activity binding now exhaustively requires any
failure of simultaneous frontier, obligation, activation, and direction
agreement at a canonical handle to activate the HN node at the table-owned
rank. The supplied checked well-founded HB no-outcome closure forces that
activity false, so an accepted binding yields all four exact typed equalities
and excludes their first routes. Together with the separately checked
budget/HB binding, positive Packet existence, and executable selector silence,
the sole route is `.descent` and carries exact residual nondecrease. The
semantic/HN binding, typed fields, rank map, activity environment, dependency
table, and closure premise remain explicit rather than constructed from
terminal data. This does not prove HN blocker semantics, semantic dependency
completeness, a decreasing transition, a no-lower contradiction,
unconditional ZeroSlack, or polynomial PCCMin.

Checked Packet descent no-lower binding now exhaustively scans the exact
canonical handle list and accepts precisely when no fully computed Packet
first route is `.descent`. Positive Packet existence together with the checked
semantic/HN and budget/HB bindings, executable selector silence, and checked
well-founded HB no-outcome closure already forces one such residual-
nondecrease route. The local no-lower checker therefore returns `false`, and
an accepted row under the same premises is contradictory. This discharges one
local Packet row only. The family, ranks, typed data, tables, and checks remain
supplied; the complete no-lower ledger, HResolve, BudgetResolve,
normalization, named routes, saturation, replay, unconditional ZeroSlack, and
polynomial PCCMin remain open.

Checked Packet no-lower ledger composition now recomputes those five exact
rows in one Boolean boundary: semantic/HN binding, budget/HB binding,
selector silence, HB no-outcome closure, and Packet descent/no-lower. Its
reflection theorem exposes exact acceptance, and an accepted ledger rules out
a positive Packet conclusion for every supplied arbitrary finite grouped
family. This closes the Packet branch only. The terminal inputs and bindings
remain supplied, while the complete no-lower ledger, HResolve, BudgetResolve,
normalization, other named obstructions, saturation, replay, unconditional
ZeroSlack, and polynomial PCCMin remain open.

Checked finite HResolve coverage now generates one fixed-priority exact, gain,
blocked, or unresolved route row for every member of an arbitrary supplied
finite candidate family. The NoHereditary sidecar checker independently
recomputes candidate uniqueness and all-candidate blocked coverage. Its exact
reflection theorem makes acceptance equivalent to absence of both constructive
routes plus a positive blocker predicate for every listed candidate, and the
generated ledger is sound and complete for that supplied enumeration. The
candidate family and decidable predicates remain explicit inputs. This is not
a construction of the governed hereditary universe, HN grammar or BWL
exactness, H-disjointness, exact-minimum/gain semantics, blocker dependency
semantics, the full HResolve theorem, BudgetResolve, the complete no-lower
ledger, unconditional ZeroSlack, or polynomial PCCMin.

The terminal-derived HResolve support resolver now removes the supplied family
and supplied exact/gain predicates for the canonical terminal support branch.
It enumerates every support seed from the complete primitive-record universe,
proves the family duplicate-free, uses the candidate-derived saturation
system, and classifies each extracted support from its actual residual slack.
Every governed seed is proved either semantically minimum on an exact route or
to admit a strict equivalent gain on a gain route. This is exhaustive reference
computation and may be exponential; it does not implement HN grammar, BWL,
ParseOrExit, H-disjointness, NoHereditary blockers, polynomial HResolve,
BudgetResolve, the complete no-lower ledger, unconditional ZeroSlack, or
polynomial PCCMin.

The terminal budget-envelope resolver now scans that same canonical support
universe under supplied gate and saturated-record caps. Feasibility is not a
caller predicate: candidate-derived saturation must leave at least one gate
and interface coordinate and must satisfy both computed caps. A feasible seed
is routed by actual residual slack to semantic minimality or a strict
equivalent gain. Exhaustive search failure proves a strong `NoBudget` sidecar
for every canonical seed. This remains reference computation and may be
exponential; it is not the manuscript HN/BUD grammar, BWL or budget-envelope
dynamic program, blocker semantics, polynomial BudgetResolve, the complete
no-lower ledger, unconditional ZeroSlack, or polynomial PCCMin.

The terminal budget no-lower ledger now evaluates that envelope for every
canonical support rather than stopping at the first feasible one. Its route
table records exact, strict gain, or `NoBudget` from recomputed evidence, and
its Boolean accepts exactly when every feasible governed support is a semantic
minimum. Acceptance excludes every feasible strict-equivalent-gain witness.
The caps remain supplied and the reference computation may be exponential;
this closes only the finite terminal-derived budget branch, not polynomial
BudgetResolve, Packet or complete no-lower composition, unconditional
ZeroSlack, or polynomial PCCMin.

The terminal Packet-budget no-lower composition now places the canonical
terminal budget-support ledger and the five-row checked Packet ledger behind
one Boolean over the same direct-wire candidate. Exact reflection exposes the
conjunction of both independently checked propositions. Acceptance therefore
makes every budget-feasible governed support a semantic minimum, excludes a
feasible strict-equivalent-gain witness, and excludes a positive Packet over
the supplied grouped family and tables. The caps, Packet family, typed data,
ranks, realizer claims, activity environment, and dependency rows remain
supplied. This is a finite two-branch composition, not the complete no-lower
ledger, a construction of Packet data from terminal data, unconditional
ZeroSlack, or polynomial PCCMin.

The terminal HResolve maximal H-disjoint-family milestone separately
formalizes the family-assembly edge over arbitrary finite supplied hereditary
footprints. Its executable checks cover support, frontier, origin, kernel,
obligation, prefix-tail, charge, and interface noninterference. The selected
family is governed, maximal, duplicate-free, and pairwise H-disjoint: every
rejected governed candidate names a selected blocker and its exact first
interference route. The footprints are not terminal-derived here, and HN,
BWL, ParseOrExit, leaf tightness, the complete `NoHereditary` sidecar, full
HResolve, the complete no-lower ledger, ZeroSlack, and PCCMin remain open.

The terminal HN BWL certified-path-minimum milestone now formalizes exact
four-coordinate lexicographic selection over a nonempty finite supplied path
family. Every path carries a hereditary shape, nonempty block decomposition,
semantic-equivalence proof, and frontier-fidelity proof; cost is derived from
the realized gate count. The selected path is listed and lower-bounds every
governed alternative under an explicit family-completeness premise. The path
family remains supplied. This is not accepted-grammar generation or
completeness, LN confluence, ParseOrExit, leaf tightness, the full BWL theorem,
polynomial HResolve, the complete no-lower ledger, ZeroSlack, or PCCMin.

The terminal HResolve certified-path-family milestone now composes that exact
finite path minimum with maximal eight-domain H-disjoint selection. Every
supplied candidate owns its frontier, footprint, nonempty finite path family,
governed predicate, completeness proof, and path-to-footprint coherence.
Selected candidates expose exact four-coordinate minima with all carried
evidence, while each rejection exposes a selected blocker and exact first
interference route. The proof-bearing candidates remain supplied. This is not
terminal candidate generation, accepted-grammar completeness, LN confluence,
ParseOrExit, leaf tightness, the H0-H4 sidecar, full or polynomial HResolve,
the complete no-lower ledger, ZeroSlack, or PCCMin.

The proof-bearing HResolve ZeroSlack sidecar milestone then upgrades the
report-facing certificate boundary. Instead of accepting HResolve input,
implementation, and `NoHereditary` strings, Lean consumes an arbitrary finite
supplied governed family and the exact Boolean equation returned by the
existing total-coverage checker. Acceptance proves duplicate-free blocked
coverage and excludes exact and gain routes for every listed candidate; the
two route predicates are separately bound to semantic minimum and strict
equivalent gain propositions. The family, implementation map, predicates,
decidability witnesses, and blocker semantics remain supplied. This is not
full or polynomial HResolve, the complete no-lower ledger, unconditional
ZeroSlack, or polynomial PCCMin.

The proof-bearing Budget ZeroSlack sidecar milestone applies the same trust
boundary to `BudgetSidecarCertificate` without duplicating the underlying
resolver. Lean stores the exact equation returned by the existing exhaustive
terminal-envelope search, and reflection excludes every canonical support from
the supplied gate/record caps. Existing exact-slack and positive-slack
reflection theorems provide semantic minimum and strict equivalent gain route
meanings, replacing the former strings. The caps remain supplied and the
support scan, saturation, and reference minimization may be exponential. This
is not the BUD grammar or B0--B4 sidecar, full or polynomial BudgetResolve, the
complete no-lower ledger, unconditional ZeroSlack, or polynomial PCCMin.

The proof-bearing Selector/HB ZeroSlack sidecar milestone then replaces the
two remaining selector-silence and HB-closure string structures without
rerunning the underlying checks. Lean stores the exact executable all-row
selector-silence and ranked no-outcome closure equations. Their existing
strong finite-rank induction proves every canonical selector nonfaithful,
every claim an exact typed bottom, all supplied HN/BUD activity false, and the
dependency relation well founded. The grouped family, realizer and dependency
tables, environment, claims, activity bits, and rank map remain supplied. This
is not blocker semantics, semantic dependency completeness, the BCEL
contradiction, unconditional ZeroSlack, or polynomial PCCMin.

The proof-bearing Packet/budget no-lower ZeroSlack sidecar milestone then
replaces the report-facing no-lower string with the exact executable
same-candidate composition equation. Reflection reuses the existing component
theorems to prove that every governed budget-feasible support is semantic
minimum, no such support has a strict equivalent gain, and the supplied
grouped family has no positive Packet conclusion. The caps,
candidate-derived model, typed Packet data, ranks, claims, activity,
dependencies, and rank maps remain supplied. This is the existing finite
two-branch boundary, not the complete manuscript no-lower ledger,
unconditional ZeroSlack, or polynomial PCCMin.

The proof-bearing BCEL/Packet no-lower ZeroSlack sidecar milestone then
replaces five BCEL contradiction strings with one dependent boundary tied to
that exact M180 certificate. A decidable check establishes that its supplied
grouped family has at least two anchors. If the same family satisfied BCEL
constant activation, the arbitrary-finite BN6 theorem would construct a
positive Packet, contradicting the accepted no-lower branch. The grouped
family and all M180 inputs remain supplied. This does not derive BCELReady or
constant activation from positive residual slack, complete the no-lower
ledger, establish unconditional ZeroSlack, or prove polynomial PCCMin.

The same-family Selector/HB, Packet, and BCEL ZeroSlack coherence milestone
removes the remaining detached certificate seam. It derives the Selector/HB
sidecar from the exact grouped family, computed realizer table, and dependency
table already checked by M180, then combines its silence and closure results
with M180 Packet exclusion and the dependent M181 BCEL contradiction. The
family and all terminal, budget, Packet, realizer, dependency, rank, and BCEL
inputs remain supplied. This does not derive those inputs or constant
activation from positive residual slack, complete the no-lower ledger,
establish unconditional ZeroSlack, or prove polynomial PCCMin.

The checked finite `SaturatePositive`-to-BCEL-ready milestone closes the
upstream local success seam without duplicating either classifier. One Boolean
checker reruns the production finite composite and accepts only its
positive-projection branch with a computed ready anchor nucleus. The result
retains the exact selection equality, safe trace, positive final slack,
positive whole-support defect, nontrivial nucleus, proper-cut equations, and
local BN2 conclusions. Its terminal problem and initial positive premise
remain supplied; local failures are not mapped globally, and BN3--BN6 data,
constant activation, manuscript-wide `SaturatePositive` or `BCELReady`,
ZeroSlack, and polynomial PCCMin remain open.

The same-candidate finite BCEL-ready and Packet carrier-coherence milestone
connects that upstream ready branch to the exact grouped family already
accepted by the Packet/budget no-lower checker. Its dependent terminal problem
uses the same candidate and model. A proved injective and surjective anchor map
and a reflected exact list equality identify the ready nucleus image with the
Packet carrier, transferring the at-least-two bound without a second Boolean.
The existing same-family positive-Packet exclusion then rules out constant
activation. The terminal problem, positive premise, family, map, payloads,
tables, and ranks remain supplied; activation weights are not identified with
projection excess, constant activation is not derived from positive residual
slack, and unconditional ZeroSlack and polynomial PCCMin remain open.

The finite BCEL/Packet activation-coherence obstruction makes that exact
missing equality fail closed. It compares the computed terminal defect with
the Packet cut value and with every canonical nonempty proper-cut activation
weight. If the whole check accepted, mapped-cut coherence would reproduce the
M183 projection equation; M184's same-family Packet exclusion proves that this
cannot happen. A deterministic classifier returns a proof-bearing cut-value
or first proper-cut activation mismatch. This is a diagnostic obstruction, not
a derivation of activation coherence. The terminal and Packet inputs remain
supplied, exhaustive cut enumeration may be exponential, and unconditional
ZeroSlack and polynomial PCCMin remain open.

The reconstruction now also kernel-checks the direct-wire terminal
whole-carrier bridge from report §8. A terminal full realization preserves the
whole implementation's semantics at every input/output coordinate and its
actual gate count. The independently stated attained universal terminal
minimum is equal to the exhaustive reference minimum (`RW-MuBridge`), and a
cheaper whole-span realization gives strict residual descent. Positive slack
is equivalent to existence of such a realization; zero slack is equivalent to
its absence. The quotient/full-mode firewall, proper-support extraction,
SaturatePositive, BCEL/BN2–BN6, selectors, ZeroSlack, and the polynomial
PCCMin route are not supplied by this bridge.

### 5.3 Residual-band minimisation correctness

The central completeness chain is:

```text
positive residual slack
=> positive residual witness
=> saturated BCEL-ready positive nucleus
=> BN2–BN6 packet
=> payload-backed raw selector seed
=> canonical unary handle and exact source-payload materialization
=> exhaustive checked gain or family-local no-gain across the supplied selector universe (formalized)
=> explicit gain-coverage certificate for every strict equivalent implementation (unconstructed premise)
=> source gain or conditional proof-bearing ZeroSlack (current Lean boundary)
=> encoded-size-bounded faithful compatible certificate construction (open)
=> exact charge pairing with an unmatched positive support charge (arithmetic implication formalized; witness construction open)
=> supplied unit-charge replacement blueprint validated constructively across every canonical handle (formalized; blueprint construction open)
=> replacement strict equivalent gain (formalized from validated occurrence accounting and semantics) or typed blocker (typed finite contract formalized)
=> supplied HN/BUD active-dependency closure forces blocker inactivity (formalized for checked tables)
=> explicit global semantic gain exclusion (supplied premise; coverage specialization formalized)
=> faithful lower-seed strong rank induction and supplied-table selector-silence rank closure (formalized conditionally)
=> executable all-row typed-bottom selector-silence scan removes the global no-gain premise (formalized for supplied tables)
=> exhaustive canonical-payload route clearance and exact HB faithfulness binding turn every positive Packet into a faithful handle, contradicting executable selector silence (formalized for supplied data)
=> canonicalize the HB faithfulness table from those payload checks and remove the independent binding premise (formalized for supplied route-clear data)
=> totalize the canonical payload classifier and force one typed first route from every positive Packet under accepted canonical HB selector silence (formalized for supplied data)
=> identify every typed route with its exact earliest supplied-field failure and retain that proof at the positive-Packet/HB endpoint (formalized for supplied data)
=> compute the final descent field from the exact ten-coordinate RankWF relation and retain either an earlier route or actual nondecrease (formalized for supplied ranks; remaining nine fields open)
=> terminal-data construction of route-clear payloads, the grouped family, and the remaining HB tables; external selector compatibility (open)
=> full unconditional HB negative closure (open)
=> ZeroSlack is impossible under positive slack
```

The exact-minimisation theorem also relies on hereditary and budget exact routes. The highest-risk correctness points are completeness claims: every positive residual state must enter some governed case, every failed route must be named, every negative sidecar must be total, and all mutual blocker dependencies must be well-founded.

Primary artefacts:

```text
canonical_proof_report.tex §§7–16
pcc-local-packages0.mjs
pcc-global-proof-dag0.mjs
pcc-pack-sufficiency0.mjs
```

### 5.4 Checker-to-theorem correctness

The repository uses package theorem records, a proof kernel, Sigma instances, and reflection records to assign mathematical meaning to checker acceptance. This refinement boundary is part of the trusted base.

A reviewer must compare, field by field:

```text
mathematical theorem
<-> record schema and required evidence
<-> checker predicate
<-> reflection conclusion
<-> final proof-DAG edge
```

A test that mutates one boolean field demonstrates only that the checker reads that field. It does not demonstrate that the field has an independently justified derivation.

### 5.5 Final complexity-theory implication

The final implication requires:

```text
accepted exact minimiser for the locked instances
+ correct locked threshold
+ polynomial construction and minimisation
+ standard SAT NP-completeness
=> P = NP
```

`pcc-final-framework0.mjs`, `pcc-final0.mjs`, and the final proof-DAG nodes encode this bridge. The final theorem is valid only if the earlier mathematical and checker-soundness obligations are valid.

## 6. Where polynomial time is asserted

Polynomiality is not established merely by storing `polynomial: true` or an exponent in a record. The reviewer must derive each bound from the actual data structures and control flow.

| Polynomiality claim | Repository assertion surface | What must be independently checked |
| --- | --- | --- |
| Boolean-to-NAND conversion | `PreNAND`; `SATDecision.NandConversion`; `SATBounds.Converter` | Output size and runtime as functions of the original input encoding; preservation of the declared output. |
| Locked-word construction | GPack bounds; `SATBounds.LockedBuilder` | Number of slots, macro instances, prefix nodes, outputs, records, and proof objects; bit length of counts. |
| Finite-table evaluation | public schedule, FT rows, truth evaluator | Whether boundary arity is truly fixed/schedule-bounded independently of input; cost of `2^beta`; total number of rows generated. |
| Branch/cycle and unary routing | BC and UN transition systems | State alphabet size, graph size, transition composition, cycle/branch checks, and whether any radius or alphabet grows with input. |
| HN and BUD exact routes | hereditary grammar and budget DP | Grammar/state-graph size, numeric bit complexity, reconstruction cost, and ParseOrExit coverage. |
| BCEL-ready nucleus | residual witness and anchor construction | Whether finding a minimal positive subset enumerates exponentially many anchor subsets; whether anchors are polynomially bounded; how positivity is tested without an exact-minimum oracle. |
| BN2–BN6 | side-tight bases, antichains, matching, cancellation, hypergraph cells | Number and size of bases, minimal-consumer antichains, request atoms, matching graphs, integer masses, and packet cells. |
| Selector enumeration | `K2`, `K3`, `Ksp`; claimed bound `|C|^3 (log |C|)^O(1)` | Handle/payload bit lengths, construction time, duplicate control, and proof that every packet has a selector without exponentially large payload. |
| Realizer and verified gain | Package R and E | Decoder runtime, support/replacement size, charge-ledger size, and verifier runtime. |
| ZeroSlack certificate | rank list, selector-silence logs, sidecars, blocker graph, contradiction DAG | Number of ranks/selectors/candidates, total negative evidence, canonical encoding size, and verification time. |
| Number of descent iterations | global slack law and residual band | Every nonterminal step must lower the same integer residual measure by at least one; normalization must not reset or hide the measure. |
| Package checking | schedule, rows, proof DAG, parser, hashes | Total package byte size, parser/canonicalization cost, proof-DAG traversal, and all integer-operation bit costs. |
| Final SAT algorithm | `CheckSATBounds0`; `Final.PolynomialBound` | A uniform polynomial bound from original input length through conversion, construction, minimisation, and comparison. |

The source contains claimed example exponents in bound records, including converter, minimiser, and final exponents. Those numeric fields are audit targets, not independent derivations.

## 7. Where exact minimisation enters

Exact minimisation appears in several logically different places.

### 7.1 Mathematical definitions

The report defines:

```text
mu(C)      = minimum size of an equivalent closed circuit
mu*(F)     = minimum size of a same-frontier open realization
Lambda(C)  = size(C) - mu(C)
```

These are legitimate mathematical definitions. Mentioning them in theorem statements is not an executable algorithm.

### 7.2 The locked threshold

The SAT reduction is stated directly in terms of the exact value `mu(W_phi)`. An approximation is insufficient because the satisfiable and unsatisfiable cases differ by as little as one gate.

### 7.3 Exact subroutes

HN and BUD are claimed to return exact minima for governed subclasses. Their dynamic programs and completeness conditions must be audited independently. An `ExactRoute` token is not enough; the route must resolve to evidence that the final checker recognizes as an exact minimum.

### 7.4 ZeroSlack

`ZeroSlack` is intended to certify that the current circuit has no positive residual slack. It is an indirect exact-minimum certificate: if sound, `Lambda(C)=0` implies the current circuit is minimum.

This is the most important place to distinguish a derivation from assertion-shaped fields. The certificate must prove that every gain, exact route, selector, hereditary case, budget case, and blocker has been handled soundly and completely.

### 7.5 `PCCMin`

The claimed executable minimiser repeatedly applies verified gains and returns on an exact route or sound `ZeroSlack`. Its polynomial runtime depends on two facts:

1. every nonterminal gain strictly decreases the same residual measure;
2. the starting residual slack is bounded.

### 7.6 SAT comparison

The final decision uses the exact size returned by `PCCMin`:

```text
SAT iff exact_minimum > baseline
```

Any approximate, heuristic, promise-only, or unverified minimum invalidates the comparator.

## 8. Where hidden search or exponential work could enter

| Risk surface | Why it is dangerous | Claimed control | Reviewer inspection target |
| --- | --- | --- | --- |
| Aliases and wrappers around minimisation | A forbidden operation can be renamed. | Expand aliases before classifying executable identifiers. | Alias tables, imported bindings, generated templates, and every call site. |
| Dynamic property access, computed strings, callbacks, or reflection | A syntactic name blacklist may not see a semantically equivalent call. | Restricted first-order executable language is claimed. | Prove the implementation actually forbids or models these JavaScript features; inspect all dynamic dispatch. |
| Reimplementation of exhaustive minimisation without a forbidden name | A brute-force search can avoid names such as `argmin`. | Bounds, finite schedules, and package-specific algorithms are claimed to restrict the computation. | Loop bounds, recursive calls, candidate generation, truth-table enumeration, and search trees. |
| Truth-vector enumeration | `2^beta` is exponential in `beta`. | `beta` is claimed schedule-bounded. | Prove `beta` is a fixed constant or suitably logarithmic and cannot depend privately on input size. |
| Minimal positive nucleus | Selecting an inclusion-minimal positive subset may require checking all anchor subsets. | Finite anchors, rank descent, and certificates are claimed. | Concrete algorithm, number of subsets examined, positivity predicate, and certificate size. |
| Minimal-consumer antichains | A monotone function may have exponentially many minimal true sets. | Schedule-bounded finite request systems and compressed antichain codes are claimed. | Worst-case antichain cardinality and encoding; construction versus mere assertion. |
| All-cut identities | Enumerating all cuts is exponential in anchor count. | BN4 claims activation equality by canonical active-antichain code rather than cut enumeration. | Proof that code equality is equivalent to activation equality and that codes remain polynomial size. |
| Matching and restoration universes | Matching is polynomial only in an explicitly polynomial graph. | BN5/PkgC use finite matching graphs; the current typed PkgC kernels derive the equality-fibre restoration list and a balanced opposite-sign BN4 ledger from an explicit restorer, embed it by exact multiplicity into an explicit ambient ledger, and prove executable residual reduction to the explicit remainder. | Size and construction cost of both vertex sets and all edges, construction and semantic adequacy of the restorer, derivation of the ambient ledger and embedding from the terminal candidate, and proof that the resulting remainder is empty or route-producing. |
| HN/BUD dynamic programs | Dynamic programming can have exponentially many states. | Accepted finite grammars and envelope bounds are claimed. | State-key width, transition count, payload size, and dependence on schedule/runtime integers. |
| Selector universe | Triple and spine payloads can hide large descriptions. The current Lean codec gives each unique position in an explicit finite grouped list one unary bitstring and fails closed on malformed input. The latest scan enumerates every such position and checks every original direct-wire payload in its exact source cell, but the list and candidates are explicit inputs, can be exponential in encoded circuit size, and do not encode or construct manuscript replacements. Family-wide no-gain here is not manuscript selector silence. | Claimed polynomial selector bound and finite payload alphabets. | Bound the explicit list and unary position by encoded circuit size, encode and construct every required replacement payload, prove polynomial generation time, faithfulness, compatibility, typed blocker completeness, and the link from family-local no-gain to rank-ordered selector silence. |
| ZeroSlack negative evidence | Exhaustively proving absence can be larger than the object being checked. | Claimed polynomial-size sidecars, rank lists, selector logs, and proof DAG. | Exact candidate counts and whether one certificate entry covers a class soundly rather than listing exponential cases. |
| Integer arithmetic | Unit-cost arithmetic can hide exponential bit complexity. | Runtime integers are placed in arithmetic cells. | Maximum bit length and cost of addition, comparison, multiplication, encoding, and Presburger checks. |
| Package generation | A fixed package can hide unrecorded precomputation, and an input-dependent package can destroy uniformity. | Generator is untrusted; checker validates materialized output. | Whether the SAT algorithm uses one fixed finite package, how it is accessed, and whether any input-dependent proof search occurs before checking. |
| Canonicalization and hashing | Runtime is linear or worse in object byte size; object size may already be exponential. | Polynomial package and certificate bounds are claimed. | Total bytes, recursion depth, sorting costs, map/set canonicalization, and duplicate resolution. |

## 9. How the checker attempts to rule out hidden minimisation

The repository's control is layered.

### 9.1 Forbidden identifier set

The source includes forbidden names such as:

```text
mu, mu*, mu#, Can, argmin, maxG,
minimumEquivalent, optimalCircuit, exactMinSearch,
canonicalMinimizer, maximizeGain
```

The exact source uses mathematical Unicode names for some entries.

### 9.2 Occurrence classification

Identifier occurrences are intended to be classified as definition/import, sound import, executable call, theorem-only assumption, or emitted token. Forbidden names reject only when they occur in an executable position.

This distinction is necessary: the mathematical definition of `mu` may appear in a theorem, while an executable call to an exact minimiser would be circular.

### 9.3 Expansion before scanning

The package and final records claim expansion of:

```text
macros
aliases
generated templates
imports
```

before the no-hidden-minimisation scan.

### 9.4 Repeated enforcement points

The no-min rule appears at several levels rather than only once:

```text
pcc-core.mjs::CheckNoHiddenMin0
pcc-global-firewalls0.mjs::CheckGlobalFirewalls0
pcc-global-proof-dag0.mjs::CheckGlobalProofDAG0
pcc-gpack0.mjs::CheckGPack0
pcc-final-framework0.mjs
pcc-final0.mjs
pcc-pack-sufficiency0.mjs::CheckPackSufficiency0
pcc-check-pcc-pack-exp0.mjs::CheckPCCPackexp0
pcc-accept-run0.mjs
```

Negative fixtures include executable `minimumEquivalent` occurrences and expanded GPack artefacts.

### 9.5 Supporting controls

The scanner is supplemented by:

- an acyclic import graph and forbidden import edges;
- mode firewalls preventing quotient comparisons from becoming full replacements;
- route-priority checks preventing a constructive gain from being downgraded;
- canonical row keys and duplicate-conflict rejection;
- typed proof references and proof-DAG acyclicity;
- polynomial bounds and schedule checks;
- canonical-byte replay rather than digest-only equality.

### 9.6 Limit of the control

A name-based or AST-shape scanner does not by itself prove polynomial time or absence of exact search. It is sound only if:

1. the executable language is completely identified;
2. all aliases, imports, templates, generated code, and dynamic dispatch are expanded or forbidden;
3. semantically equivalent brute-force search is caught by complexity-bound checks;
4. theorem-only minimum fields cannot be consumed as executable oracle results;
5. every executable module used by the decision path is included in the scan.

These are independent audit obligations.

## 10. Artefacts a reviewer must inspect

### 10.1 Pinned source and artefact coordinates

```bash
git fetch --tags --force
git checkout final-pnp-proof-report-hardened-7072f8d
git rev-parse HEAD

# Expected source commit:
# 7072f8d0bda6d44d240f9bb3fad624fd357e1278
```

For release identity:

```bash
git checkout final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
B=proof-artifacts/final-pnp-proof-report-hardened-7072f8d
sha256sum -c "$B/SHA256SUMS"
sha256sum -c "$B/SHA256SUMS.sha256"
```

### 10.2 Inspection map

| Review question | Required artefacts |
| --- | --- |
| What problem and circuit model are being solved? | `canonical_proof_report.tex` §§1–5; `pcc-core.mjs`; [terminology_crosswalk.md](terminology_crosswalk.md). |
| Does local replacement preserve global semantics and size accounting? | Report §6; `pcc-local-packages0.mjs`; charge/obligation/mode modules and tests. |
| Is every finite/local route complete and polynomial? | Report §§7–15; local-package records; rows; schedule; package-specific tests. |
| Is `ZeroSlack` sound and polynomial-size? | Report §16; `pcc-pack-sufficiency0.mjs`; `pcc-local-packages0.mjs`; `pcc-global-proof-dag0.mjs`; related tests. |
| Does the locked construction preserve SAT and produce the exact threshold? | Report §17 and Appendix A; `pcc-gpack0.mjs`; `test/pcc-gpack0.test.mjs`; G proof-DAG nodes. |
| Do O and G use the same formal framework? | `pcc-final-framework0.mjs`; `test/pcc-final-framework0.test.mjs`. |
| Is the SAT comparator exact and polynomial? | Report §18.4; `CheckSATDecision0`; `CheckSATBounds0`; `pcc-final0.mjs`; their tests. |
| Does package acceptance cover every required theorem and row? | `pcc-pack-sufficiency0.mjs`; `pcc-rows0.mjs`; `pcc-global-proof-dag0.mjs`; `pcc-global-firewalls0.mjs`; package tests. |
| Can hidden minimisation or exponential work enter? | `pcc-core.mjs`; all `FORBIDDEN_EXEC_SYMBOLS` lists; no-min records; import graph; bounds/schedule modules; negative tests. |
| Is the generator genuinely untrusted? | `pcc-generate-pcc-pack0.mjs`; materialized package checkers; acceptance-run and replay modules. |
| Is the accepted package the package named by the final report? | `pcc-check-pcc-pack-exp0.mjs`; `pcc-accept-run0.mjs`; final replay/certificate/release-gate/proof-report modules and tests. |
| Do hashes identify the intended files? | sealed artefact tag, `release-seal.json`, `SHA256SUMS`, `SHA256SUMS.sha256`, and `REPRODUCE.md`. |
| What remains in the trusted base? | [trust_model.md](trust_model.md). |

### 10.3 Minimum evidence for a stage to count as reviewed

For each stage, a reviewer should record:

```text
mathematical statement:
input and output model:
source theorem/section:
record schema:
checker function:
reflection or proof-DAG node:
positive test:
negative or mutation test:
polynomial bound:
independent derivation or counterexample search:
remaining assumption:
```

A source pointer plus a passing test is not a complete review result.

## 11. Recommended validation order

1. Freeze the input model, output convention, size measure, and exact-minimum definition.
2. Audit parser, canonical encoding, row identity, proof-reference resolution, and hash-as-index discipline.
3. Audit the locked-NAND construction and threshold independently on small exhaustive instances.
4. Audit the O/G framework match.
5. Audit the residual-band completeness chain, beginning with Terminal MuBridge and `ZeroSlack`.
6. Derive every claimed polynomial bound from actual loops, state spaces, and encoded sizes.
7. Audit proof-kernel rules and reflection mappings.
8. Audit package coverage and final proof-DAG dependencies.
9. Reproduce the materialized package acceptance and canonical-byte replay.
10. Verify release hashes last; they identify the reviewed bytes but do not validate them.

## 12. Interpretation boundary

This pipeline document does not claim that:

- the locked-NAND reduction is correct;
- `PCCMin` is exact or polynomial;
- the no-hidden-minimisation scan is complete;
- checker acceptance implies the stated mathematical theorem;
- the sealed package has received independent mathematical validation;
- a passing test suite or SHA-256 ledger proves `P = NP`.

It identifies the complete claimed route and the points at which a reviewer can falsify or independently validate it.

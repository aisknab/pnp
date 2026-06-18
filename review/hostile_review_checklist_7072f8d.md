# Hostile Review Checklist: 7072f8d Residual-Hardened PNP Release

Purpose: give reviewers a compact checklist for attacking the release. The checklist is adversarial: every item should be treated as a possible failure point.

## Release boundary

```text
CheckPCCPackexp(GeneratePCCPack())=accept => P = NP
```

Frozen release:

```text
source tag: final-pnp-proof-report-hardened-7072f8d
artifact tag: final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
docs tag: final-pnp-proof-report-docs-hardened-7072f8d-sealed
validation: 1121 tests, 1121 pass, 0 fail
```

## A. Custody and reproducibility

- The source tag must resolve to `7072f8d0bda6d44d240f9bb3fad624fd357e1278`.
- The sealed artifact tag must resolve to a commit containing `proof-artifacts/final-pnp-proof-report-hardened-7072f8d/`.
- `sha256sum -c SHA256SUMS` must pass.
- `sha256sum -c SHA256SUMS.sha256` must pass.
- `release-seal.json` must record validation `1121 / 1121 / 0`.
- The final public theorem must remain conditional on `CheckPCCPackexp(GeneratePCCPack())=accept`.

Failure condition: any tag drift, checksum failure, stale identifier, or unconditional theorem emission.

## B. Locked NAND threshold

Attack theorem:

```text
φ ∉ SAT  => μ(W^NAND_φ) = B^NAND_φ
φ ∈ SAT  => B^NAND_φ + 1 ≤ μ(W^NAND_φ) ≤ B^NAND_φ + 4
```

Check:

- `BaselineDistinct` really proves all exposed baseline functions are distinct nonconstant nonprojections.
- Macro truth signatures match the claimed equality, constant, and NAND-trace functions.
- Duplicate source occurrences cannot identify carrier slots.
- Final lock `z` is not leaked before final output construction.
- Unsat cases cannot realize a cheaper tuple by quotient/profile artifacts.
- Sat cases really have a construction with at most four extra gates.
- The threshold proof reference resolves to accepted non-opaque proof nodes.

Failure condition: a satisfiable or unsatisfiable formula where the threshold equivalence fails.

## C. Terminal MuBridge

Attack obligations:

```text
terminalCarrierPreservesSemantics
terminalizationSizePreserving
closedFullWordRealizesCircuit
quotientEqualityNotConstructive
wholeSpanCheaperImpliesStrictDescent
```

Check:

- Terminalization does not expose proof/profile records as free Boolean outputs.
- Closed full words compile back to whole circuits without hidden size changes.
- Quotient equalities are never used as full replacements.
- Whole-span cheaper realizations lower residual slack strictly.

Failure condition: a whole-span comparison that proves a false descent or silently uses quotient equality.

## D. SaturatePositive

Attack obligations:

```text
transparentSaturationCostBalanced
interfaceExposureRoutesToE
originKernelObligationClosureRouted
projectionPositivityNotLostSilently
firstNontransparentStepRecorded
```

Check:

- Interface exposure cannot increase semantic obligation for free.
- Nontransparent saturation steps route to named outcomes.
- Projection positivity is not silently lost.
- Origin/kernel/obligation closure cannot hide a new cost.

Failure condition: positive residual slack disappears during saturation without a named route.

## E. BCEL-ready positive nucleus

Attack obligations:

```text
positiveResidualWitnessExists
finiteAnchorSetExtracted
booleanAnchorAlgebraOrRoute
minimalPositiveNucleus
properCutConstantEquation
anchorSizeAtLeastTwo
```

Check:

- Positive residual slack always yields a finite anchor set.
- Non-Boolean anchor algebra routes instead of staying silent.
- Minimal positive nucleus really has at least two anchors.
- Every proper-cut equation has the same positive value `D`.

Failure condition: a positive witness with no BCEL-ready nucleus and no earlier route.

## F. BN2 side-tight coherent optima

Attack obligations:

```text
sideTightOnlyNoOverclaim
fourCornerOptimaCarrierCompatible
sideTightCompletionExists
tightBasisValueEqualsDelta
```

Check:

- The proof never uses arbitrary coherent bases as if side-tight.
- Four corner optima share compatible carriers.
- Side-tight completion is actually constructible.
- The side-tight basis value equals `δ_i`.

Failure condition: a non-side-tight basis overclaims a cut value.

## G. BN3 finite request envelopes

Attack obligations:

```text
requestPredicatesStable
minimalConsumerAntichainsExact
jointSideTightRealizability
runtimeIntegersSeparatedFromFiniteState
incidenceAtomsAccountedExactlyOnce
```

Check:

- Minimal-consumer antichains are exact.
- Request predicates are stable under transport.
- Joint side-tight realizability holds simultaneously.
- Runtime integers do not enter finite profile state.
- Every incidence atom is counted once.

Failure condition: a cut incidence omitted, duplicated, or represented only by unsafe enumeration.

## H. BN4 activation-exact cancellation

Attack obligations:

```text
activationByActiveAntichain
activationEqualityWithoutCutEnumeration
sameKeyCancellationExact
noOppositeSignSameKeyResidual
integerMassLedgerExact
```

Check:

- Active-antichain equality really equals activation equality.
- Cut enumeration is not used as a shortcut.
- Same-key cancellation preserves semantic signature and transport type.
- No opposite-sign same-key residual survives.
- Integer mass ledger is exact.

Failure condition: cancellation erases unmatched semantic mass.

## I. BN5/PkgC localization

Attack obligations:

```text
negativeFullResidualLocalized
hallDeficitRoutesNamedOutcome
quotientToFullMatchingKeyPreserving
separatingConsumersSingletonized
unmatchedShadowNotSilent
```

Check:

- Every negative full residual localizes to a shadow graph.
- Hall deficits route to concrete named outcomes.
- Quotient-to-full matching preserves activation-exact keys.
- Separating consumers become singleton-singleton.
- Unmatched shadows never become silent unless truly cut-silent.

Failure condition: a negative residual key remains cut-active in a no-outcome branch.

## J. BN6 packet collapse and selector completeness

Attack obligations:

```text
constantCutHypergraphHypotheses
pairTriFullSpanExhaustive
mixedTripleCaseHandled
packetAtomsHaveSelectorPayloads
selectorUniverseCompleteAndPolynomial
selectorUniverseCompleteForPackets
```

Check:

- V53 is applied only with its exact hypotheses.
- Pair, balanced-triple, and full-span cases are exhaustive.
- The mixed three-anchor case is handled.
- Positive packet atoms retain selector payloads.
- Selector universe `K2 ∪ K3 ∪ Ksp` is polynomial and complete.

Failure condition: a positive packet prototype has no faithful selector and no named route.

## K. Realizer/HB closure

Attack obligations:

```text
realizerBotTyped
realizerBotOnlyHNBUDBlockedOrLowerRank
chargeSurplusInjectionStrict
blockerGraphAcyclicByRank
hbBlockerGraphAcyclic
selectorSilenceRankComplete
hbNoCircularNegativeClosure
```

Check:

- Every `Real(C,K)=⊥` has a typed bot reason.
- Bots are only HN, BUD, or lower-rank faithful-selector blockers.
- Faithful unblocked selectors have strict charge-surplus injections.
- HN/BUD blocker graph decreases rank/tie-break measure.
- Selector silence is recorded rank by rank.
- HN and BUD negatives do not justify each other circularly.

Failure condition: a faithful selector is blocked only by a circular or untyped reason.

## L. ZeroSlack final closure

Attack obligations:

```text
zeroSlackEarlierRoutesExcluded
zeroSlackNoLowerRouteLedgerComplete
zeroSlackFaithfulSelectorExcludedAllRanks
zeroSlackHNBUDBlockersExcludedAllRanks
zeroSlackPositiveSlackContradictionComplete
zeroSlackContradictionFromPositiveSlack
zeroSlackCertificateEncodingPolynomial
zeroSlackCertificatePolynomialSize
```

Check:

- HResolve and BudgetResolve did not emit minimum/gain.
- Every earlier named route is explicitly absent, not merely unsearched.
- Faithful selectors are excluded at all ranks.
- HN/BUD blockers are excluded at all relevant ranks.
- Positive slack forces BCEL nucleus, packet, selector, and contradiction.
- The ZeroSlack certificate is polynomial-size and canonically encoded.

Failure condition: `Λ(C)>0` and the oracle still emits `ZeroSlack`.

## M. Public theorem boundary

Check:

- `CheckPCCPackexp0` accepts the generated package.
- `CheckAcceptRun0` accepts.
- `ReplayAcceptRun0` accepts.
- `EmitFinalVerdict0` emits accept only after replay.
- `CheckFinalPNPCertificate0` accepts.
- `CheckFinalPNPReleaseGate0` accepts.
- `CheckFinalPNPProofReport0` accepts.
- Public conclusion is never emitted before accepted package/replay/certificate linkage.

Failure condition: any public `P = NP` emission before the accepted antecedent chain.

## N. Reviewer report format

```text
claim attacked:
file / theorem / checker:
minimal counterexample or missing obligation:
expected acceptance behavior:
actual acceptance behavior:
suggested patch:
```

The most valuable reports are concrete: a false lemma, a minimal counterexample, or a tamper fixture that should reject but accepts.

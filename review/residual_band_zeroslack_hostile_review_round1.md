# Hostile Mathematical Review Round 2: Residual-Band Minimization and ZeroSlack

Status: **residual-band hardening pass completed; still open for hostile mathematical audit**.

The locked NAND theorem has been split into explicit manuscript and GPack obligations. The residual-band minimization route has now also been split into checker-visible obligations through Terminal MuBridge, SaturatePositive, BCELReady, BN2-BN6, Realizer/HB closure, and ZeroSlack final closure. It remains a major hostile-review target.

## Release context

```text
source commit:
7072f8d0bda6d44d240f9bb3fad624fd357e1278

source tag:
final-pnp-proof-report-hardened-7072f8d

sealed artifact tag:
final-pnp-proof-report-artifacts-hardened-7072f8d-sealed

validation:
1121 tests, 1121 pass, 0 fail
```

Public theorem boundary:

```text
CheckPCCPackexp(GeneratePCCPack())=accept => P = NP
```

## Target theorem block

The manuscript's residual-band route is centered on:

```text
If CheckPCCPackexp(P)=accept and Λ(C0) ≤ O(log |C0|),
then PCCMin_exp(C0) returns an exact minimum equivalent circuit in polynomial time.
```

Operationally:

```text
PCCMin_exp(C0):
  normalize or gain
  run PCCOracle_exp(C)
  if Minimum: return exact minimum
  if Gain: apply strict residual descent
  if ZeroSlack: return C
```

The essential ZeroSlack assertion is:

```text
PCCOracle_exp(C) = ZeroSlack(C,Z) => Λ(C)=0.
```

## Main attack surface

A hostile reviewer should try to produce a circuit with positive residual slack for which every finite route is silent and the oracle incorrectly emits `ZeroSlack`.

The proof must exclude every such circuit by showing that positive residual slack always yields one of:

```text
verified gain
exact route
named obstruction
selector seed
strict residual descent
hereditary active object
budget active object
```

or else a contradiction through the BCEL / packet / selector / HB route.

## Obligation 1: Terminal MuBridge

### Claim

For normalized whole circuits:

```text
μ(C) = μ*_1(F^top,1_C)
```

and whole-span cheaper words give strict residual descent.

### Hostile questions

1. Does terminalization preserve all Boolean outputs and only the relevant full-mode carrier data?
2. Can proof/profile records accidentally become free semantic outputs?
3. Does every closed full word realizing the terminal function compile back into a whole circuit with the same size?
4. Does a cheaper whole-span full word always imply residual slack decreases?
5. Are quotient-mode realizations barred from proving full-mode replacement equality?

### Required strengthening

Make the terminal bridge obligations first-class:

```text
terminalCarrierPreservesSemantics
terminalizationSizePreserving
closedFullWordRealizesCircuit
quotientEqualityNotConstructive
wholeSpanCheaperImpliesStrictDescent
```

## Obligation 2: SaturatePositive

### Claim

Saturation/completion of a positive residual witness preserves positivity or routes the first failure.

### Hostile questions

1. Can adding an exposed interface coordinate increase the open minimum without adding physical support cost?
2. Are exposure failures routed to `E` rather than silently accepted?
3. Are all nontransparent saturation triggers enumerated?
4. Does transparent saturation add the same forced full-mode cost to both support and minimum?
5. Can projection positivity be lost without a named route?

### Required strengthening

Make the exact positivity-preservation cases explicit:

```text
transparentSaturationCostBalanced
interfaceExposureRoutesToE
originKernelObligationClosureRouted
projectionPositivityNotLostSilently
firstNontransparentStepRecorded
```

## Obligation 3: BCEL-ready positive nucleus

### Claim

If `Λ(C)>0` and no earlier route is active, then there exists a BCEL-ready positive nucleus with Boolean anchor algebra and constant-cut equation.

### Hostile questions

1. Why does every positive residual witness have a finite anchor set?
2. Why does minimal positive nucleus have `|A|≥2`?
3. Why is the anchor algebra Boolean after saturation?
4. What happens if `XS ∩ XT` or `XS ∪ XT` triggers non-Boolean completion?
5. Why is every proper cut equation constant with value `D>0`?

### Required strengthening

Make the BCEL readiness obligations explicit:

```text
positiveResidualWitnessExists
finiteAnchorSetExtracted
booleanAnchorAlgebraOrRoute
minimalPositiveNucleus
properCutConstantEquation
anchorSizeAtLeastTwo
```

## Obligation 4: BN2 side-tight coherent optima

### Claim

Every legal saturated projection-compatible square has a side-tight coherent optimum basis, and only side-tight bases may be used to read off `δ_i`.

### Hostile questions

1. Does the proof ever overclaim for arbitrary coherent bases?
2. Is side-tightness constructively certified or merely assumed?
3. Are the optima in all four corners over compatible carriers?
4. Are transport maps preserving frontier order and profile data?
5. Can a cheaper non-side-tight witness escape the finite basis?

### Required strengthening

First-class obligations:

```text
sideTightOnlyNoOverclaim
fourCornerOptimaCarrierCompatible
sideTightCompletionExists
tightBasisValueEqualsDelta
```

## Obligation 5: BN3 finite request envelopes

### Claim

For each mode, finite weighted request systems represent every cut incidence:

```text
δ^cut_i(S,A\S) = Σ_p ν_i(p) r_p(S) r_p(A\S)
```

with stable request predicates and joint realizability.

### Hostile questions

1. Are request predicates monotone and stable under all allowed transports?
2. Are minimal-consumer antichains computed without enumerating all cuts unsafely?
3. Does joint realizability hold simultaneously for all requests?
4. Do runtime integers leak into finite profile state?
5. Is every incidence atom accounted for exactly once?

### Required strengthening

First-class obligations:

```text
requestPredicatesStable
minimalConsumerAntichainsExact
jointSideTightRealizability
runtimeIntegersSeparatedFromFiniteState
incidenceAtomsAccountedExactlyOnce
```

## Obligation 6: BN4 activation-exact cancellation

### Claim

Activation equality is by active-antichain equality, not cut enumeration, and positive/negative same-key cells cancel exactly.

### Hostile questions

1. Is activation-code equality really equivalent to active-antichain equality?
2. Does cancellation ever erase a cell with different full transport type?
3. Are positive and negative masses integer, nonnegative where required, and same-key only?
4. Is cut enumeration avoided as a proof shortcut?
5. Does any residual same-key opposite sign survive?

### Required strengthening

First-class obligations:

```text
activationByActiveAntichain
activationEqualityWithoutCutEnumeration
sameKeyCancellationExact
noOppositeSignSameKeyResidual
integerMassLedgerExact
```

## Obligation 7: BN5 and PkgC localization

### Claim

Every negative full residual and nonsingleton separating-consumer case localizes to a named route or becomes cut-silent.

### Hostile questions

1. Are Hall deficits localized to actual `CritC`, `Q`, `E`, `L`, or `X` rows?
2. Can a negative full residual remain cut-active in a no-outcome branch?
3. Does quotient-to-full matching preserve activation-exact keys?
4. Does PkgC really force singleton-singleton separating consumers?
5. Are all unmatched shadows routed, not ignored?

### Required strengthening

First-class obligations:

```text
negativeFullResidualLocalized
hallDeficitRoutesNamedOutcome
quotientToFullMatchingKeyPreserving
separatingConsumersSingletonized
unmatchedShadowNotSilent
```

## Obligation 8: BN6 packet collapse and selector completeness

### Claim

The nonnegative constant-cut hypergraph collapses to pair, balanced-triple, or full-span packet prototypes, and every positive packet yields a faithful selector seed or a named route.

### Hostile questions

1. Does V53 apply with exactly the needed hypotheses?
2. Are mixed three-anchor cases handled without losing mass?
3. Are packet atoms converted to selector payloads faithfully?
4. Do pair/triple/spine selectors cover all packet prototypes?
5. Is the selector universe polynomially bounded?

### Required strengthening

First-class obligations:

```text
constantCutHypergraphHypotheses
pairTriFullSpanExhaustive
mixedTripleCaseHandled
packetAtomsHaveSelectorPayloads
selectorUniverseCompleteAndPolynomial
```

## Obligation 9: Realizer and HB closure

### Claim

Every faithful selector either produces a verified gain or is blocked by HN/BUD/lower-rank structure; HB rank-negative closure prevents infinite blocking.

### Hostile questions

1. Does `Real(C,K)=⊥` have a typed reason, never an unexplained failure?
2. Does charge-surplus injection prove actual strict saving?
3. Are HN and BUD blocker edges acyclic by a decreasing rank/measure?
4. Does selector silence really cover all ranks?
5. Does the induction combine `NoHereditary`, `NoBudget`, and `NoFaithful` without circularity?

### Required strengthening

First-class obligations:

```text
realizerBotTyped
chargeSurplusInjectionStrict
blockerGraphAcyclicByRank
selectorSilenceRankComplete
HBNoCircularNegativeClosure
```

## Obligation 10: ZeroSlack contradiction

### Claim

If the oracle emits ZeroSlack, then positive residual slack is impossible:

```text
PCCOracle_exp(C)=ZeroSlack(C,Z) => Λ(C)=0
```

### Hostile questions

1. Is every earlier gain/exact/named route excluded by a positive certificate, not by absence of search?
2. Is every faithful selector excluded by a complete rank induction?
3. Are HN/BUD blockers excluded at every relevant rank?
4. Does the contradiction depend on finite search over a polynomial selector universe?
5. Does the proof handle normalized and unnormalized inputs consistently?

### Required strengthening

First-class obligations:

```text
zeroSlackEarlierRoutesExcluded
zeroSlackFaithfulSelectorExcludedAllRanks
zeroSlackHNBUDBlockersExcludedAllRanks
zeroSlackContradictionFromPositiveSlack
zeroSlackCertificatePolynomialSize
```

## Round 2 verdict

The residual-band route is the next major mathematical risk. The current proof architecture is detailed, but a serious reviewer will ask for the ZeroSlack route to be decomposed into named proof obligations, the same way the locked NAND theorem was decomposed.

The highest-risk points are:

```text
1. SaturatePositive and exposure routing.
2. BCEL-ready positive nucleus existence.
3. BN3 joint realizability of finite request envelopes.
4. Selector completeness and realizer charge-surplus.
5. HB negative closure without circular blocker reasoning.
```

## Current hardening status

The 7072f8d release records first-class checker fields for Terminal MuBridge, SaturatePositive, BCEL-ready residual witnesses, BN2, BN3, BN4, BN5/PkgC, BN6, Realizer/HB closure, and ZeroSlack final closure. The next work is hostile external review: produce minimal counterexamples, missing lemmas, or tamper fixtures rather than adding more naming-only obligation fields.

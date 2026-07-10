# Uniform semantic no-hidden-oracle proof surface

> **Historical assertion-checker record:** This UFS coordinate is superseded. Source scanning and
> accepted semantic flags do not prove the absence of every hidden oracle or super-polynomial
> computation. See [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json)
> and [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

Historical coordinate:

```text
PNP-UNIFORM-NO-HIDDEN-ORACLE-SEMANTIC-2026-07-05-01
```

Uniform final soundness obligation:

```text
UFS-006-NoHiddenOracleSemanticCompleteness
```

Historical replay command:

```bash
npm run proof:no-hidden-oracle-semantic -- --historical-replay
```

Direct historical replay command:

```bash
node pcc-no-hidden-oracle-semantic0.mjs --json --historical-replay
```

## Purpose

This surface recorded the sixth historical UFS assertion about the absence of hidden SAT or
exact-minimization oracles, unbounded search, digest shortcuts, and external-review premises.

It depends on the existing source-surface seed audit and upgrades it with a semantic restricted-language closure check over:

```text
proof-development scripts
semantic imports
alias/template/macro expansion discipline
finite iteration and dynamic-programming discipline
hash/digest non-semantic use
external-review non-premise discipline
```

## Required proof obligations

```text
NHS-001-SourceSurfaceSeedAuditAccepted
NHS-002-RestrictedExecutableLanguageClosed
NHS-003-ProofScriptAndImportClosure
NHS-004-MacroTemplateAliasExpansion
NHS-005-ForbiddenIdentifierSemantics
NHS-006-FiniteIterationAndPolynomialBounds
NHS-007-HashDigestNonSemantic
NHS-008-NoExternalReviewPremise
```

## What the historical checker accepted

The checker enforced its implemented source and record predicates against listed oracle-shaped
capabilities. That enforcement did not prove semantic completeness of the scan or polynomial runtime.

## What this does not prove

This checker does not by itself prove SAT in P, activate final theorem emission, or clear unrestricted final soundness. Later checkers still need to bind the complexity implication and release transition.

The historical record kept this boundary:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

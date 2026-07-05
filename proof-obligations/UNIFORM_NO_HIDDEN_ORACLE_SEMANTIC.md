# Uniform semantic no-hidden-oracle proof surface

Coordinate:

```text
PNP-UNIFORM-NO-HIDDEN-ORACLE-SEMANTIC-2026-07-05-01
```

Uniform final soundness obligation:

```text
UFS-006-NoHiddenOracleSemanticCompleteness
```

Checker:

```bash
npm run proof:no-hidden-oracle-semantic
```

Direct checker command:

```bash
node pcc-no-hidden-oracle-semantic0.mjs --json
```

## Purpose

This surface discharges the sixth uniform-final-soundness sub-obligation: the executable proof path contains no hidden SAT oracle, exact-minimization oracle, unbounded search, digest-equality semantic shortcut, or external-review theorem premise.

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

## What this proves

The checker proves that the current uniform proof stack is not allowed to smuggle the hard work into an executable shortcut. Every proof-development script must be a direct checker invocation. Forbidden oracle-shaped capabilities are represented as rejected semantic states, not hidden premises.

## What this does not prove

This checker does not by itself prove SAT in P, activate final theorem emission, or clear unrestricted final soundness. Later checkers still need to bind the complexity implication and release transition.

Current boundary remains:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

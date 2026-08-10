# Finite terminal SaturatePositive composition

`PNP.ResidualTerminalOriginKernelObligationRouting` and
`PNP.ResidualTerminalFiniteSaturatePositive` close the remaining finite local
closure-routing edge and compose the five reconstructed terminal
`RW-SaturatePositive` sub-obligations. The public input is a proof-bearing
problem, not an unproved global positivity assertion.

The reconstruction is anchored to lines 761 through 797 of the pinned legacy
canonical report. That passage separates five obligations: transparent cost
balance, routing of interface exposure to E, routing of origin, kernel, and
obligation closure, explicit projection-positivity loss, and recording the
first remaining nontransparent step. This milestone composes the audited
finite forms of exactly those five obligations.

## Exact closure recognition

An origin, kernel, or obligation event is accepted only when all of the
following executable checks agree:

- the profile coordinate has the claimed origin, kernel, or obligation role;
- the trace event carries the corresponding rule kind;
- its records have one of the two exact gate/profile orientations; and
- the candidate-derived dependency system recomputes the same edge.

The query does not accept a caller-provided dependency certificate. Kind, role,
orientation, or edge tampering returns `none`.

## Safety and deterministic routes

`TerminalOriginKernelObligationClosureSafe` requires three facts for a
recognized event:

- the existing cost classifier proves the event transparent;
- an obligation coordinate is false after the event; and
- if the projection forgets the coordinate, its observed value is identical
  before and after the event.

The classifier checks failures in that order. A routed event contains its exact
coordinate and one of these proof-bearing reasons:

- `nontransparent reason`, retaining the typed cost-balance failure;
- `openObligation`, proving the obligation remains true after the event; or
- `forgottenProfileMismatch`, proving a hidden coordinate changed.

`TerminalOriginKernelObligationClosureRoute.sound` reconstructs the exact
event shape, candidate-derived edge, and semantic failure from the route.

## Exact first composed route

The combined dispatcher checks interface exposure first, then the
origin/kernel/obligation closure, and finally the ordinary cost-balance
fallback. A safe event always contains a transparent cost proof. A rejected
event is one of:

- a proof-bearing local interface E-route;
- a proof-bearing origin/kernel/obligation closure route; or
- an explicitly nontransparent event recognized by neither local query.

The production trace classifier scans in exact event order.
`TerminalFirstSaturationClosureEvent` records the complete safe prefix, the
first routed event, and the remaining suffix. Later events cannot be
substituted for an earlier failure.

## Proof-bearing positive composition

`TerminalFiniteSaturatePositiveProblem` contains:

- an existing `TerminalCandidateBCELAnchorProblem`; and
- a proof that full slack is positive at the normalized initial seed selected
  by that anchor problem.

`classifyTerminalFiniteSaturatePositive` first runs the exact-first closure
router. If every event is safe, their transparent projections feed the existing
linked balance theorem, which preserves positive full slack at the final replay
state. The existing projection firewall then returns either:

- zero whole-support projection defect with an attained quotient minimum and
  checked full lift; or
- positive whole-support projection defect and the existing fail-closed BCEL
  anchor-nucleus outcome.

Otherwise the result retains the exact first interface,
origin/kernel/obligation, or other nontransparent route. Every branch has an
explicit `Sound` proposition, and `TerminalFiniteSaturatePositiveOutcome.sound`
proves it.

## Exact boundary

This milestone formalizes a finite composition of the five reconstructed
terminal sub-obligations. It does not identify the local routes with the
manuscript's complete global outcomes, accept Package E `VerifyDW`, construct a
verified gain, establish global route completeness, prove RankWF, or discharge
the explicit positive starting premise. Accordingly the manuscript-wide
`leanSaturatePositiveFormalized` status remains false. `BCELReady`, ZeroSlack,
PCCMin, polynomial runtime, SAT in P, and `P = NP` also remain open.

## Verification

The public boundary is checked by three independent surfaces:

```text
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalFiniteSaturatePositiveAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalFiniteSaturatePositive.lean
node --test audits/lean-residual-terminal-finite-saturate-positive0.test.mjs
```

The axiom transcript covers all 37 explicit declarations. Their compiled
closures use only `propext` and `Quot.sound` where Lean reports any axioms. No
`Classical.choice`, `sorryAx`, or project-specific axiom enters the milestone.
The executable regression covers all three roles, both orientations, all three
failure reasons, kind tampering, an exact first production route, and the total
composite soundness surface.

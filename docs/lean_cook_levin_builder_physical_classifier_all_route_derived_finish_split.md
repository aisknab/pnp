# Lean Cook-Levin all-route derived-Finish request split

M228 removes M227's staged optional-token request cell from the complete
post-header classifier route. The source is
`lean/PNP/Concrete/CookLevinBuilderPhysicalClassifierAllRouteDerivedFinishSplit.lean`.

## What is constructed

For every verifier-derived post-header coordinate, M228 runs M226's fixed
terminal-joined classifier on a protected workspace containing only a blank
sentinel and the canonical builder word. A fixed 20-rule relay reads the
physical classifier head and crosses the exact blank-free classifier prefix:

- a body terminal writes `bodyPendingSymbol`, which is proved distinct from
  every M217 request symbol; and
- the unique `Finish` terminal writes M217's canonical physical `Finish`
  request.

A fixed 65-rule conditional reflected dispatcher then rejects the explicit
body-pending marker and executes the derived `Finish` request. The complete
collision-free composition has 823 rules. Lean proves over the entire
`Fin bodySlotCount` domain:

- body-or-`Finish` physical terminal classification with `outOfRange`
  excluded;
- absence of a staged request cell in the initial protected workspace;
- exact relay scans for both physical terminal heads;
- collision freedom of the body-pending marker with all request symbols;
- exact body rejection at the pending boundary and exact `Finish` dispatch to
  `emittedPrefix problem (index.val + 1)`;
- exact work-machine and six-for-one compiled traces;
- nonhalting one work step before completion; and
- one verifier-input-size polynomial bound for the complete conditional run.

The 91 public declarations have a complete kernel axiom transcript: 50 have an
empty closure, 18 use only `propext`, and 23 use only `propext` and
`Quot.sound`. None uses `Classical.choice` or a project-specific axiom.

## Public theorem

The certificate-free endpoint is:

```lean
PNP.Concrete.CookLevin.
  BuilderPhysicalClassifierAllRouteDerivedFinishSplit.
  cook_levin_builder_physical_classifier_all_route_derived_finish_split_checked_complete
```

Its only data argument is a `VerifierTableauProblem`. It quantifies internally
over every post-header schedule coordinate. Callers do not supply a coordinate,
route, request, terminal verdict, trace, machine, polynomial, complexity bound,
or success certificate.

## Claim boundary

M228 derives only the unique `Finish` request. Every body route deliberately
halts at the explicit non-request pending marker; the body token or padding
request is not synthesized. The theorem does not connect one coordinate's
final configuration to its successor, implement a repeated physical builder
loop, prove complete builder `FunctionProgram.RawRefinement`, package the
Cook-Levin `PolynomialReduction`, establish concrete NP-hardness or
NP-completeness, put `CNFSAT` in `P`, close a fixed checkpoint or global gate,
create the eligible root theorem, or prove `P = NP`.

Formal artefact coverage is 204 of 206 current scoped publication rows earned.
The separate risk-weighted proof completion estimate remains 35 percent, with a
20 to 40 percent uncertainty range, and zero of five global gates are closed.

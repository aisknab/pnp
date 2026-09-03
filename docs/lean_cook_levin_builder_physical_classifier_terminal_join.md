# Lean Cook-Levin physical classifier terminal join

M226 gives every verifier-derived post-header coordinate one literal,
continuation-ready endpoint after M220's complete physical classifier. The
source is
`lean/PNP/Concrete/CookLevinBuilderPhysicalClassifierTerminalJoin.lean`.

## What is constructed

M220's fixed 711-rule table accepts a body coordinate and rejects the unique
`Finish` coordinate. M226 injectively renames that complete machine into a
protected state namespace and adds one total, symbol-preserving redirect table
at the old rejecting terminal. The redirect has one rule for each of the nine
work symbols and sends the `Finish` tape to the same accepting control state
already reached by body coordinates.

The resulting fixed machine has 720 collision-free rules. Its accepting state
has no outgoing rule, and its distinct rejecting state is an unreachable
reserved namespace value. The construction does not inspect or change the tape
while joining the terminal states.

For every coordinate in the complete post-header schedule and every preserved
workspace, Lean proves:

- M220's typed body-or-`Finish` route agreement;
- exact transport of every underlying classifier transition;
- zero additional work steps for every body coordinate;
- exactly one symbol-preserving redirect for the unique `Finish` coordinate;
- one common accepting final state with the exact classifier terminal tape;
- exact work-machine and six-for-one compiled traces;
- nonhalting one work step before completion; and
- one verifier-input-size polynomial bound for the complete run.

## Public theorem

The certificate-free endpoint is:

```lean
PNP.Concrete.CookLevin.BuilderPhysicalClassifierTerminalJoin.
  cook_levin_builder_physical_classifier_terminal_join_checked_complete
```

Its only data argument is a `VerifierTableauProblem`. The theorem quantifies
internally over every post-header coordinate and arbitrary protected workspace;
callers do not supply a coordinate, route, terminal verdict, trace, machine,
polynomial or success certificate.

## Claim boundary

M226 is a physical control-flow normalizer only. It does not synthesize, stage
or dispatch any body-token or padding request. It does not supersede M223's
separate generated-`Finish` path, connect successive schedule configurations,
implement one repeated raw-machine builder loop, prove builder
`FunctionProgram.RawRefinement`, package the Cook-Levin `PolynomialReduction`,
establish concrete NP-hardness or NP-completeness, put `CNFSAT` in `P`, close a
fixed checkpoint or global gate, create the eligible root theorem, or prove
`P = NP`.

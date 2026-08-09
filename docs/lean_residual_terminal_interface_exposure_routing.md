# Finite terminal interface-exposure routing

`PNP.ResidualTerminalInterfaceExposureRouting` closes the finite terminal form
of `interfaceExposureRoutesToE` over the candidate-derived saturation trace.
The result is deliberately a **transparent-or-local-E** classifier. It is not
a full Package E verifier and does not widen the global theorem boundary.

## Computed interface coordinates

The module recognizes exactly three orientations of an
`interfaceConsumer` event:

- `outgoingCoordinate output`, when the required record is the interface
  output itself;
- `gateMaterializer output gate`, when an existing output coordinate requires
  the candidate's gate source; and
- `boundaryMaterializer output input`, when an existing output coordinate
  requires a boundary source.

The shape query alone is not enough to route an event. The production query
recomputes the candidate-derived dependency system and requires the exact
interface-consumer edge for the event's dependent and required records. A
tampered rule kind or a shape with no such edge fails closed to `none`.

## Step-level dichotomy

For a recognized candidate-derived interface event, Lean reuses the existing
cost-balance classifier. A transparent event returns its complete
`TerminalTransparentSaturationStep` evidence. A nontransparent event returns a
`TerminalInterfaceExposureERoute` containing:

- the exact computed interface coordinate;
- proof that the coordinate query selected it;
- the exact typed nontransparency reason selected by the balance classifier;
  and
- proof that the event is not transparent.

`TerminalInterfaceExposureERoute.sound` reconstructs the event shape and the
actual candidate-derived edge from those fields. The theorem
`terminalInterfaceExposure_transparent_or_eRoute` proves that a recognized
event has no caller-selected third branch.

An outgoing-coordinate event has zero physical event cost. When that event is
transparent, `TerminalInterfaceExposureZeroCostRetract` records the finite
retract branch and proves both zero event cost and preservation of full slack.

## Exact first route

The trace classifier first runs the existing deterministic balance classifier
over the production `terminalSaturateTrace`. If the trace is balanced, it
retains the all-transparent proof. If the first nontransparent event has a
candidate-derived interface-consumer edge, it returns
`TerminalFirstInterfaceExposureRoute`; otherwise it retains the exact failure
as `TerminalFirstNoninterfaceSaturationFailure`.

`TerminalFirstInterfaceExposureRoute.sound` includes the complete trace split,
the transparent prefix, exact interface coordinate and edge, genuine
nontransparency of the event, and equality to the production classifier's
first-failure result. A later interface event cannot be substituted for an
earlier non-interface failure.

## Exact boundary

The local E-route is a proof-bearing exposure-obligation coordinate. It is not
a `VerifyDW` acceptance, a proof of global gain, or a complete Package E
object. This milestone does not formalize
`originKernelObligationClosureRouted`, full `SaturatePositive`, `BCELReady`,
ZeroSlack, PCCMin, polynomial runtime, SAT in P, or `P = NP`. The executable
observer and forgetful projection remain explicit finite-model inputs.

## Verification

The public boundary is checked by all three independent surfaces:

```text
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalInterfaceExposureRoutingAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalInterfaceExposureRouting.lean
node --test audits/lean-residual-terminal-interface-exposure-routing0.test.mjs
```

The axiom transcript covers all 28 explicit declarations. Their compiled
closures use only `propext` and `Quot.sound` where any axioms are reported; no
`Classical.choice`, `sorryAx`, or project-specific axiom enters this milestone.
The executable regression exercises transparent materialization, the zero-cost
outgoing retract, a routed multiple-owner failure, kind tampering, a balanced
trace, an interface first failure, and the non-interface fallback branch.

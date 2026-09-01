# Cook-Levin physical dispatch schedule

M218 composes the fixed M217 optional-token dispatcher across every canonical
post-header schedule opportunity.

For a concrete verifier problem, `physicalOutput` starts at the already
constructed header prefix and recursively applies the exact M217 output action
at each bounded post-header coordinate. Lean proves that every bounded output
equals the canonical emitted prefix and that the final output is exactly
`encodeCNFTokens problem.formula`.

For every coordinate and arbitrary exterior workspace,
`PhysicalStepHolds` exposes the exact work-machine trace, the compiled
six-for-one trace, and the one-step-short nonhalting result with source and
target outputs supplied by that recursive invariant. The public endpoint also
retains M214's independently checked physical route-classifier evidence at
every coordinate.

The total compiled dispatch work is the sum of the exact per-coordinate costs.
It is bounded by the problem-derived body-slot count multiplied by M217's
uniform dispatcher bound, which is one polynomial in the encoded source-input
length.

The theorem is deliberately narrower than a complete raw formula builder. The
request for each coordinate is still obtained from the canonical Lean schedule,
not constructed by a literal raw coordinate selector. Each exact trace starts
from its proved canonical request configuration; the traces are not connected
by one literal looping machine. M218 does not prove builder `RawRefinement`,
package the Cook-Levin `PolynomialReduction`, establish CNFSAT NP-hardness or
NP-completeness, put CNFSAT in P, close a global gate, create the eligible root
theorem, or prove P = NP.

The reviewed endpoint is:

```text
PNP.Concrete.CookLevin.BuilderPhysicalDispatchSchedule.cook_levin_builder_physical_dispatch_schedule_checked_complete
```

The risk-weighted proof-completion estimate remains 35 percent, with the
20 to 40 percent uncertainty range. Formal artefact coverage is tracked
separately and increases only because this new compiled publication row is
earned.

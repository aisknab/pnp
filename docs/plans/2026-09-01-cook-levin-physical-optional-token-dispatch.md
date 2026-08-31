# M217: physical optional-token dispatch

## Selection rationale

M216 proves by structural Lean recursion that every verifier-derived
post-header schedule opportunity produces the complete canonical token stream.
M215 separately proves the exact raw appender trace for every populated entry.
The remaining implementation gap between those results begins at a physical
interface: a literal machine must consume a tape-resident padding-or-token
request and enter the corresponding fixed appender path without a Lean-level
choice of appender state.

M217 closes that reusable request-to-appender edge for every raw input, output
prefix, and member of the complete optional-token alphabet. It is an unbounded
machine interface, not another fixed clause, coordinate, or schedule slot.

## Legacy anchor

The pinned manuscript's final complexity transport requires one uniformly
polynomial Cook--Levin formula builder. The named formal predecessors are:

```text
PNP.Concrete.CookLevin.BuilderPostDividerSelectedTokenLaunch.cook_levin_builder_post_divider_selected_token_launch_checked_complete
PNP.Concrete.CookLevin.BuilderCompleteScheduleIteration.cook_levin_builder_complete_schedule_iteration_checked_complete
```

The authoritative open status edge remains
`reductions-complete-cook-levin-builder`.

## Unbounded abstraction

Define a five-symbol request alphabet containing one padding request and the
four concrete CNF tokens. Place that request in the physical cell immediately
to the left of the canonical token-appender workspace. One fixed finite rule
table must read the cell, restore the builder's left boundary, and then:

- halt with the output prefix unchanged for padding; or
- enter the existing fixed appender state selected by the physical token symbol
  and append exactly that token.

The machine and rule table are independent of the verifier, source input,
coordinate, formula, and output prefix. Its proofs range over all raw inputs,
arbitrary exterior garbage, arbitrary already-emitted token lists, and every
optional token request. A canonical specialization derives the request from
M215's schedule entry at every M216 post-header coordinate.

## Exact theorem boundary

Add `PNP.Concrete.CookLevin.BuilderPhysicalOptionalTokenDispatch` and the public
endpoint:

```text
PNP.Concrete.CookLevin.BuilderPhysicalOptionalTokenDispatch.cook_levin_builder_physical_optional_token_dispatch_checked_complete
```

The endpoint takes only a `VerifierTableauProblem` and proves:

1. the five request symbols are unambiguous and the literal rule table is
   collision-free;
2. every canonical post-header request follows one exact work-machine trace to
   the next canonical emitted prefix;
3. the compiled raw machine follows the corresponding exact six-for-one trace;
4. malformed request symbols and one-step-short valid executions remain
   fail-closed; and
5. every canonical dispatch fits one verifier-derived source-size polynomial.

No coordinate-specific token, route, trace, schedule, precomputed formula, or
success certificate is supplied to the endpoint.

## Downstream blockers preserved

M217 does not claim that the request cell is already produced by a literal raw
coordinate selector. It does not compose M214's classifier tape into this
request cell, iterate this dispatcher in one physical loop, construct the
complete raw formula builder, prove builder `FunctionProgram.RawRefinement`,
or package the Cook--Levin `PolynomialReduction`. Concrete CNFSAT
NP-hardness/NP-completeness transport, deterministic `CNFSAT` in `P`, the
residual-band minimiser, unconditional ZeroSlack, polynomial PCCMin, the
eligible root theorem, and `P = NP` remain open.

The fixed risk-weighted score therefore remains 35 percent with the 20 to 40
percent uncertainty range. Formal artefact coverage is regenerated separately.

## Evidence and release gates

- Build the new module under the pinned Lean toolchain on Atlast.
- Add exact-trace, timeout, malformed-request, rule-count, and polynomial-bound
  regressions plus the declaration-level axiom audit.
- Import the module through the root and theorem inventory, then regenerate the
  canonical inventory, publication map, status, progress ledger, and report.
- Run the normal formal-publication, documentation-link, generated-output, and

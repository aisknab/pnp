# M216: complete Cook-Levin schedule iteration

## Selection rationale

M215 established an exact selected-token launch theorem for every canonical
post-header coordinate, but its endpoint quantified over one coordinate at a
time and explicitly did not iterate the schedule. The highest-value bounded
successor is therefore the first theorem that composes those arbitrary stages
over the complete verifier-derived schedule. This is an unbounded dependency
edge, not another fixed clause, token, or schedule slot.

## Legacy anchor

The named predecessor is:

```text
PNP.Concrete.CookLevin.BuilderPostDividerSelectedTokenLaunch.cook_levin_builder_post_divider_selected_token_launch_checked_complete
```

The authoritative open status edge is the absent complete Cook-Levin builder
and its still-open `reductions-complete-cook-levin-builder` checkpoint.

## Unbounded abstraction

Define a structural recursive runner over an arbitrary natural prefix of the
post-header schedule. At each successor it obtains M215's canonical selected
entry. Padding leaves the output unchanged and a populated entry appends the
selected token. Prove by induction that every bounded run equals the canonical
emitted schedule prefix.

At the verifier-derived `bodySlotCount`, use the exact schedule-length identity
to prove that the recursive result is `encodeCNFTokens problem.formula`.

Define a matching recursive cost accumulator. Prove it is bounded by the
iteration count times M215's uniform per-coordinate polynomial, then instantiate
the complete polynomial schedule count.

## Exact theorem boundary

The public endpoint takes only a `VerifierTableauProblem` and proves:

1. the full recursive pass equals the exact encoded CNF token stream;
2. every coordinate retains M215's physical classifier/appender contract for
   arbitrary workspaces; and
3. aggregate staged compiled work is bounded by one source-size polynomial.

No coordinate, selected token, route, trace, schedule, or formula certificate
is supplied to the endpoint.

## Downstream blockers preserved

M216 does not claim:

- a literal single raw-machine iteration loop;
- a physical tape-to-tape handoff between successive selected stages;
- complete raw formula-builder `RawRefinement`;
- the final encoded output-size bridge;
- a packaged polynomial Cook-Levin reduction;
- concrete CNFSAT NP-hardness or NP-completeness;
- deterministic `CNFSAT` in `P`; or
- `P = NP`.

These remain explicit downstream work. A failure at the general induction or
aggregate bound is a milestone failure and must not be replaced by another
fixed-prefix theorem.

## Evidence and release gates

- Build the new module under the pinned Lean toolchain on Atlast.
- Add a root-import regression covering recursion, prefix equality, complete
  output, aggregate bound, and the exact endpoint.
- Print the axiom closure of every public declaration and reject project axioms,
  `Classical.choice`, `sorryAx`, and unreviewed declaration forms.
- Add hostile mutations for the recursion, full-output equality, polynomial
  multiplication, endpoint inputs, nonclaims, and authority boundary.
- Update the canonical status, theorem inventory, publication map, progress
  history, report, and active documentation mechanically.
- Keep the fixed risk-weighted score at 35% because the complete raw builder
  checkpoint remains open; update formal artefact coverage independently.
- Run one complete capped core verification, then the normal draft PR, manual
  merge, post-merge checks, and one exact clean-merge reproduction.

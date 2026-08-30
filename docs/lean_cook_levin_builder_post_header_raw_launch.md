# Cook-Levin post-header raw launch

Status: machine checked in Lean at M212.

M212 connects the exact interfaces earned at M209 through M211. It reads the
shifted post-header remainder from M209's literal raw terminal configuration,
uses that value to launch M211's fixed unary divider, and recovers every M210
body, finish, and out-of-range classification.

The connection is executable Lean orchestration over the two exact machines.
It deliberately remains narrower than a literal tape-to-tape rewrite: the
divider's canonical input configuration is constructed from the checked
remainder rather than produced by a new raw bridge machine.

## Exact all-coordinate handoff

`recoveredRemainder?` applies M210's checked reader to M209's exact terminal
configuration. It returns `none` precisely for a header coordinate and the
exact shifted natural remainder for every post-header coordinate.

`launch?` is an executable dispatcher. On the header branch it returns
`none`. On every post-header branch it invokes M211's positive-width divider
with the exact problem-derived `formulaTokensPerClause`; that width is proved
strictly positive for every verifier tableau problem.

The public endpoint quantifies over every natural coordinate. It includes the
exact M209 work trace and the exact M211 work trace, so neither a successful
route nor an execution transcript is supplied as a premise.

## Complete M210 route recovery

The terminal divider decoder is proved equal to natural quotient and
remainder. A route-indexed proposition then covers all M210 outcomes:

- a body route returns exactly the typed clause and within-clause coordinates;
- the unique finish route returns the clause-count coordinate and remainder
  zero; and
- an out-of-range route still reconstructs the original index, has a strict
  remainder, and lies beyond the populated clause rectangle.

For every finite coordinate below the complete direct token schedule, M212
also proves that a post-header launch cannot take the out-of-range branch.

## Combined source-size bound

`stagedCompiledSteps` counts the six raw transitions for every M209 work step
and, on a post-header result, the six raw transitions for every M211 divider
work step. `rawTimeBound` adds M209's existing complete-schedule polynomial to
a conservative quadratic term built only from the verifier's terminal-slot and
clause-token polynomials.

The checked theorem proves the combined count is bounded by that single
polynomial in the external source-input length for every in-range natural
coordinate. It performs no subset, support, payload, implementation, or
semantic-reference enumeration.

## Proof authority

The axiom transcript prints all 24 public declarations exactly once. Ten have
empty axiom closure and fourteen use only `propext` and `Quot.sound`. No
declaration reaches `Classical.choice`, a project-specific axiom, `sorry`,
`admit`, `unsafe`, or `native_decide`.

## Claim boundary

M212 does not prove that M209's terminal tape is literally rewritten into
M211's input tape by one raw machine. It does not preserve the surrounding
builder workspace through that future bridge, emit a body or finish token,
append that token to the output, or construct the complete raw formula.

It therefore does not establish complete builder `FunctionProgram.RawRefinement`,
package the concrete Cook-Levin `PolynomialReduction`, prove CNFSAT
NP-hardness or NP-completeness transport, put CNFSAT in P, close a global proof
gate, create `PNP.Main.p_eq_np`, or prove P = NP.

Formal artefact coverage increases by one earned publication row to 188 of
190. The fixed-weight proof-completion estimate remains 35 percent, with the
existing 20 to 40 percent uncertainty range. No fixed checkpoint or global
gate changes state.

## Verification surfaces

- Source: `lean/PNP/Concrete/CookLevinBuilderPostHeaderRawLaunch.lean`
- Regression: `lean-regression/PNPConcreteCookLevinBuilderPostHeaderRawLaunch.lean`
- Axiom audit: `lean-audit/PNPConcreteCookLevinBuilderPostHeaderRawLaunchAxiomAudit.lean`
- Hostile audit: `audits/lean-concrete-cook-levin-builder-post-header-raw-launch0.test.mjs`
- Publication endpoint:
  `PNP.Concrete.CookLevin.BuilderPostHeaderRawLaunch.cook_levin_builder_post_header_raw_launch_checked_complete`

# M256: source-derived constant and unary frontier replacement

## Named manuscript dependency

Follow the pinned canonical manuscript, section 6.1: R7 is unary cut
realization with full-value obligation discharge. Package E requires a proper
support, an actual replacement open word, complete local equality and a strict
physical saving. Sections 4 and 6.2 require actual ownership and matched
Pull/Expand accounting.

M253 already computes a visible predecessor cone and completes its frontier
against every actual observation and consumer, retaining the original exterior
once. It currently takes the replacement and complete local equality as inputs.
M255 derives an actual minimum-size complete unary computational word. M256
closes the dependency between these results: construct a constant or unary
replacement for the computed complete frontier and derive its local equality
before expanding it into the original circuit.

## Baseline and integration point

Verified development parent: 88c0a3f84c5220f3bb0254ab780edd79b3477ca1, tree f22c423b6a09c2aa972d78684ef1360d1d001e51.
Cycle preflight found core main at M249 merge
e32605a435ab990dca4d72c362889099bc4a4973 and draft M250 PR #448;
M251 through M255 are core-verified release successors. PNPLabs main remains
3d62ceb5ab14d51b39bd1a89307dbfb8d5a55226. The development
baseline is M255: formal artefact coverage 231/233, risk-weighted estimate 40%,
uncertainty 20% to 40%, 0/5 global gates, no project axioms, absent eligible root
and false publication gate. PNPLabs retains its coherent M231 public snapshot.

Use one new named checkout with an exact source/toolchain cache match.
Do not change M255 or any inherited theorem merely to simplify the new proof.

## Unbounded construction and exact boundary

Use namespace PNP.DirectWire.WireUnaryFrontier in
lean/PNP/NANDWireUnaryFrontier.lean.

Input is an arbitrary WireCarrier inputs outputs fields and a finite keep mask.
The original program size and every ambient dimension remain arbitrary.
Use the actual M253 records and pulled frontier; no support map, local replacement,
truth table, semantic agreement, order, compiled result or minimizer is an input.

1. Compute the completed frontier's boundary length. Recognize zero or one
   incoming port. A larger boundary is outside this rule and is rejected.
2. For zero inputs, derive a zero-gate constant word from the extracted source.
   For one input, reuse M255's actual constructor through checked dimension
   transport, with the complete frontier as its ordered output word.
3. Prove full open-function equality and minimum gate count for every recognized
   frontier. The unary result costs at most one shared gate; the constant branch
   costs zero. Do not enumerate implementations, supports or candidate minima.
4. Use M253's source-derived primary boundary to obtain actual compiler success.
   Expand the computed replacement against the original exterior. Do not accept
   an external compiler-success certificate or a new local agreement premise.
5. Preserve every ordinary output and computational field for every ambient
   valuation, including forgotten selected fields on the completed frontier and
   fields whose physical producers remain in the exterior.
6. Prove exact replacement-plus-exterior gate accounting and nonincrease.
   The local minimum is not a global minimum over different ambient exteriors.
7. Derive source-exact full R7 discharge witnesses for the original R5 identities
   in the actual expanded program. Padding and same-numbered unrelated gates
   cannot supply these values.
8. Compute proper-gain acceptance from positive original exterior and strict
   local saving. A whole-support saving is not a proper-support result, and
   an already minimal or empty support does not earn a strict gain.

The constructor should expose an option-valued query whose success is equivalent
to the actual completed boundary having at most one port. Every such frontier
must compile; ordinary difficulty is not permission to weaken this to a supplied
agreement or success assumption.

## Required general interface

The accepted-result field theorem must have the following shape, with no
replacement or correctness premise:

```lean
theorem attempt_field {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (result : WireCarrier inputs outputs fields)
    (accepted : attempt carrier keep = some result)
    (valuation : Valuation inputs) (field : Fin fields) :
    result.fieldValue valuation field = carrier.fieldValue valuation field
```

A success-characterization theorem must prove that some result is returned
exactly when (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1.
Provide general ordinary-output, exact accounting, nonincrease, local minimum,
actual source-discharge and proper-gain theorems. Factoring definitions is
permitted; weakening these requirements is not.

## Regression and hostile expectations

Cover constant and unary frontiers in carriers with several ambient inputs,
including a unary boundary at a nonzero original input index. Include forgotten
exterior fields depending on other inputs, forgotten selected negations that
prevent false zero-cost claims, repeated and reordered outputs and fields,
genuine proper savings and full-support/no-saving rejection.

Reject multiboundary reduction, ordinary-only local agreement, supplied source
tables/replacements/agreements/compiler results, wrong input relabelling,
duplicated exterior ownership, free or duplicated negation, omitted field
frontiers, weak or unbound R7 witnesses, narrowed finite-size theorem signatures,
extra assumptions, stale fingerprints and widened publication claims.
Use tiny guarded runtime fixtures; general Lean theorems remain proof authority.

## Dependency contracts before expensive checks

Reconcile the new root import, regression and axiom audit, Lean/JavaScript
reviewed-name producers, publication row and fingerprint keys, status fields,
current documentation, npm script and closed package fixture, verifier list and
exact durable workflow block together. Test isolated package fields while
generated status is unsealed. Run source/root shape and negative contracts first.

Build the actual module and root before imported audits. Freeze source after
exact theorem-type and axiom verification. Generate the complete inventory,
publication seal, progress and canonical report from those bytes. Keep old
checkpoint definitions, old theorem pins and all historical rows unchanged.

Run one combined deduplicated remote suite. Preserve normal PR, manual merge,
post-merge and independent exact-object reproduction gates. A parent-only
reanchor with the same verified tree does not justify another identical proof
or report build.

## Remaining blockers and publication decision

This closes source-derived constant/unary realization for the computed visible
predecessor cone, not every arbitrary ambient support or external-gate boundary.
It does not complete the full manuscript carrier, arbitrary obligation DAGs,
every R5-R8 interaction, all N1-N10 traces, Package E, global routing,
unconditional SaturatePositive/BCELReady/ZeroSlack, exact general PCCMin,
deterministic SAT, the eligible root or encoded-size polynomial runtime,
output and certificate bounds. Finite evaluation is not a polynomial theorem.

No fixed checkpoint or global gate is expected to change.
Publication decision: defer PNPLabs. This is a named computational R7/frontier
integration, not yet a major change to the coherent M231 public bottom line.
Meaningful verified substep notifications remain independent of site cadence.

After full verification, commit a focused core change and queue release behind
M255's actual fully earned merge. Remove task-created temporary artifacts after
their release and retain no competing progress ledger.

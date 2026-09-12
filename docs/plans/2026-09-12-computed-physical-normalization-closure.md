# M248: computed closure of the three physical normalization passes

## Pinned dependency and bounded scope

The pinned manuscript's section 5 Traceable normalization requires a computed
normalization stage, complete ordered-output semantics, non-increasing physical
size, invariant semantic reference minimum and backward transport of gains.
Its R1/R4 structural work and N2 dead-bookkeeping deletion have actual physical
components in M242, M244 and M247. M190 composes a supplied normalizer with a
supplied oracle, but does not construct a common stopping condition for these
three components.

Close that construction edge: derive the first available constant-propagation,
NAND-sharing or output-cone-pruning gain from the current implementation, apply
it and repeat. Stop only after all three computed savings are zero on the same
final implementation. Priority is fixed in that order. This is one arbitrary-
program loop, not a list of hard-coded circuits or supplied gain certificates.

## Exact general targets

Construct a finite trace whose every nonterminal edge is the selected actual
pass with positive savings and no higher-priority available pass. Recurse on
physical gate count, without executing semantic reference minimization.

For all input/output dimensions and every starting implementation, prove:

- The result has identical complete ordered-output semantics.
- Every trace edge strictly decreases physical gate count.
- Final gate count plus the sum of actual pass savings equals initial gate count.
- Iteration count is at most total saved gates and at most initial residual slack.
- All three pass savings are zero on the same final result.
- Re-running the computed loop preserves that result exactly.
- The semantic reference minimum is invariant and residual slack drops by exactly
  the actual saved-gate total.
- The existing normalizer interface surfaces any total strict saving as a gain.

The main theorem quantifies only over the implementation. No normalizer, oracle,
family, precomputed result, stopping premise or correctness certificate is supplied.

## Claim boundary

This is operational quiescence for exactly three physical passes, not semantic
minimality, all R1 identities, complete manuscript N1-N10 normalization or
ZeroSlack. The two-gate NAND(x, NAND(x,x)) fixture must remain quiescent while a
zero-gate constant-true implementation is strictly smaller.

The trace records actual whole-program passes and exact physical savings. It
does not yet construct arbitrary-support Pull/Expand materializer identities,
the complete full-profile carrier or R5/R6-R8 obligation ledger. Those remain
required for the manuscript's complete Traceable normalization theorem and
Package E. The complete PCCMin oracle, unconditional global routes and
uniformly encoded-size polynomial construction/runtime/certificate bounds
remain open. A gate-count iteration bound is not a per-iteration runtime bound.

## Source and expectation changes together

Prepare general theorem-type and axiom expectations alongside the source.
Runtime fixtures must include each of the three actual routes, priority when
multiple routes are available, interacting passes, repeated/input/constant
ordered outputs, empty dimensions, idempotent re-execution and the nonminimum
quiescent example. Keep all fixtures bounded and never execute reference minima.

Hostile source/compiled contracts must reject a dropped pass, wrong priority,
unchecked stopping, fake savings, supplied construction authority, skipped
output preservation, altered fingerprints/axioms and global-completion claims.
Update root imports, reviewed name producers/consumers, durable workflow,
publication, status and documentation as one synchronized interface.

## Verification and release

Use a separate remote checkout, source-tree/toolchain-matched cache and bounded
leaf feedback. Build the explicit root and exact workflow audit/regression block,
derive type fingerprints, freeze proof source, then seal inventory and status.
Reconcile all current generated consumers before focused tests. Run one report
reproduction and one deduplicated standard suite; preserve normal PR/post-merge
and exact-object release boundaries without repeating unchanged-tree proof work.

Release only after the earlier queued milestones are fully earned and reanchor
onto the actual verified parent merge without changing the tested tree.

No fixed checkpoint is expected to close. Proof completion stays 40% with
20% to 40% uncertainty; coverage changes independently. All five global gates
and the eligible root remain open. Publication decision: defer PNPLabs, because
this physical sub-loop does not change the coherent published M231 bottom line.
Notify meaningful verified substeps independently of website cadence.

Remove task-created checkout, helpers, logs and transport files after complete
release verification or completed diagnosis of an abandoned approach.

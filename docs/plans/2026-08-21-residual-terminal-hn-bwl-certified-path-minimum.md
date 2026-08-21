# M175 terminal HN BWL certified-path minimum

## Evidence-led selection

The pinned manuscript's Section 8.1 gives four hereditary shapes (`pair`,
`tripod`, `spine`, and `nf`), a proof-carrying path certificate, and the BWL
objective `(cost, residual rank, frontier deviation, direct-wire code)`.  The
current reconstruction now assembles maximal H-disjoint families, but it does
not yet formalize the finite minimization kernel used once hereditary paths
have been certified.  Audit question AQ-08 identifies exactness over the
accepted grammar as the next BWL-facing obligation before ParseOrExit,
critical-pair confluence, or the H0--H4 sidecar.

M175 therefore closes the exact, deterministic minimization edge over a
supplied nonempty finite family of proof-bearing paths.  It does not assume
that the family is complete unless the caller supplies a separate completeness
proof for the governed path predicate.

## Target

For every direct-wire implementation, expected frontier, and nonempty finite
family of certified hereditary paths:

1. define the four manuscript shape tags;
2. carry a nonempty block decomposition, exact support coverage, semantic
   equivalence, and frontier fidelity in each path certificate;
3. define the exact four-coordinate BWL objective, deriving `cost` from the
   carried implementation rather than accepting a caller-provided value;
4. reflect its lexicographic preorder with an executable Boolean;
5. compute a deterministic minimum of the supplied path list;
6. prove that the result is listed and no listed path has a smaller objective;
   and
7. under an explicit family-completeness premise, lift that lower bound to
   every path satisfying the supplied governed predicate while preserving the
   chosen path's certificate evidence.

The named endpoint is
`PNP.DirectWire.terminal_hn_bwl_certified_path_minimum_complete`.

## Claim boundary

The path family, its governed predicate, and any proof that the family covers
that predicate remain inputs.  M175 does not derive paths from a terminal
candidate; formalize shape-specific grammar soundness or completeness; prove
LN confluence, ParseOrExit, independent leaf tightness, or the full BWL
theorem; solve a leaf; construct the H0--H4 NoHereditary sidecar; or prove a
polynomial path generator or runtime bound.  It does not complete HResolve,
BudgetResolve, the no-lower ledger, unconditional ZeroSlack, PCCMin, concrete
SAT, the root theorem, or project-axiom removal.

## Required evidence

- root import and compiled theorem-inventory inclusion;
- an explicit axiom transcript for every public declaration;
- regression fixtures exercising cost and all three tie-break coordinates,
  all four shape tags, membership, governed-family lifting, semantic fidelity,
  frontier fidelity, and block coverage;
- hostile mutations for caller-supplied cost or success, omitted objective
  coordinates, missing certificate fields, list-minimality without membership,
  hidden completeness, assumptions, fixed family bounds, and claim widening;
- publication-map and formal-status rows with reviewed kernel fingerprints;
- current reconstruction, audit, pipeline, terminology, README, and canonical
  report documentation; and
- durable CI and aggregate-verifier coverage.

## Verification order

Run the focused source audit first.  On the configured remote builder, compile
the new module and root import before its axiom transcript and regression.
Regenerate the compiled theorem inventory, publication payloads, and canonical
report only after the theorem surface stabilizes.  Finish with the complete
core suite and one fresh exact-head reproduction.  PNPLabs will consume those
verified artifacts byte-for-byte and will not run Lean, Lake, or Elan.

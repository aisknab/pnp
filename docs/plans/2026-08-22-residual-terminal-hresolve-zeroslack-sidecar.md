# M177 proof-bearing HResolve ZeroSlack sidecar

## Evidence-led selection

The pinned manuscript's Sections 8.2 and 16 require the `NoHereditary`
result consumed by ZeroSlack to be a total HResolve sidecar whose exact and
gain routes have semantic meaning.  The current reconstruction now has an
executable finite-family HResolve classifier and checked `NoHereditary`
coverage, but `ZeroSlack.HResolveSidecarCertificate` still stores three
uninterpreted strings.  This leaves a direct gap between the checked HResolve
ledger and the proposition consumed by the report-facing contradiction
contract.

M177 replaces those three strings with one proof-bearing, checked boundary.
The certificate carries the governed finite family, its implementation map,
decidable exact/gain/blocker predicates, a successful invocation of the
existing fail-closed `NoHereditary` checker, and semantic soundness proofs for
both constructive predicates.

## Target

For every arbitrary finite HResolve candidate family:

1. store all decidability witnesses as explicit certificate data rather than
   relying on hidden classical choice;
2. require the existing checker to recompute duplicate-free all-blocked
   coverage;
3. bind each exact route to `IsSemanticallyMinimum` for the candidate's
   implementation;
4. bind each gain route to an actual `StrictEquivalentGain` witness;
5. expose the checker's full accepted proposition from the certificate;
6. prove that every governed candidate has neither constructive route; and
7. preserve those exclusions at the semantic implementation boundary.

The named endpoint is
`PNP.hresolve_zeroslack_sidecar_checked_complete`.

## Claim boundary

The candidate family, implementation map, exact/gain/blocker predicates, and
the semantic meaning of the blocker predicate remain supplied.  M177 does not
derive hereditary candidates from terminal data, formalize the HN grammar,
prove BWL/ParseOrExit/leaf tightness, construct the H0--H4 blocker semantics,
complete full or polynomial HResolve, or prove the complete no-lower ledger,
unconditional ZeroSlack, PCCMin, concrete SAT in P, the root theorem, or
project-axiom removal.

## Required evidence

- root import and compiled theorem-inventory inclusion;
- an explicit axiom transcript for every new public declaration;
- a concrete regression with a checked two-candidate sidecar, semantic route
  bindings, exact/gain exclusion, and duplicate/exact/gain/unresolved
  rejection inherited from the underlying checker;
- hostile mutations for retained string handles, caller-supplied acceptance,
  omitted checker binding, missing exact/gain semantics, hidden classical
  choice, assumptions, fixed family bounds, and claim widening;
- publication-map and formal-status rows with reviewed kernel fingerprints;
- current reconstruction, audit, pipeline, terminology, README, and canonical
  report documentation; and
- durable CI and aggregate-verifier coverage.

## Verification order and deduplication

Run lightweight source-shape checks before remote proof feedback.  On the
configured remote builder, compile the new dependency and root once, run its
axiom transcript and regression, reconcile generated publication evidence,
then run the complete core suite and one fresh exact-merge reproduction.  The
PNPLabs phase consumes the verified core artifacts byte-for-byte and must not
invoke Lean, Lake, Elan, or the core proof suite.

# M179 proof-bearing Selector/HB ZeroSlack sidecar

## Evidence-led selection

The pinned manuscript's Sections 14--16 require rank-complete selector silence
and acyclic HN/BUD negative closure before the final ZeroSlack contradiction.
The current reconstruction already has executable typed-realizer and total
exact-rank dependency-table checks whose composition proves those results, but
`ZeroSlack.lean` still stores eight uninterpreted selector/HB strings.  This
leaves an avoidable gap between checked evidence and the proposition consumed
by the report-facing certificate.

M179 replaces both string structures with one proof-bearing checked sidecar.
The certificate carries an arbitrary finite grouped BN6 family, typed-realizer
table, exact-rank HB dependency table, and the two actual checker equations.
The existing finite-rank induction then derives all-selector silence, exact
typed-bottom rows, all-node HN/BUD inactivity, closure validity, and
well-foundedness.

## Legacy anchor and dependency edge

- Legacy anchor: report Sections 14--15 for typed realizer rows, finite rank
  induction, and HN/BUD negative closure; Section 16, where `ZeroSlack`
  consumes those conclusions.
- Closed edge: executable all-row selector-silence check + exact-rank HB
  no-outcome closure -> proof-bearing `SelectorHBZeroSlackSidecarCertificate`
  -> the structured `ZeroSlackCertificate`.
- Unbounded abstraction: arbitrary natural input, output, and finite-rank
  counts; arbitrary finite grouped BN6 families, typed-realizer tables, and
  total dependency tables satisfying the checked equations.

## Exact theorem target

For every `SelectorHBZeroSlackSidecarCertificate`, prove
`PNP.selector_hb_zeroslack_sidecar_checked_complete`: every canonical selector
is nonfaithful, every recorded claim is exactly a typed bottom, the HB table's
rank and local-closure propositions hold, every HN/BUD activity bit is false,
and the dependency relation is well founded.

The certificate must not carry a string proof handle, caller success Boolean,
proof-valued selector-silence field, or proof-valued HB-inactivity field.  Its
accepted proposition must be recovered from the two executable checker
equations and the existing induction theorem.

## Claim boundary and downstream blockers

The grouped family, realizer table, environment, claims, activity bits,
dependency rows, and rank map remain supplied inputs.  M179 does not derive
them from terminal data, prove selector faithfulness or compatibility,
formalize HN/BUD blocker semantics or semantic dependency completeness,
connect silence to the BCEL contradiction, complete the no-lower ledger,
establish unconditional `ZeroSlack`, prove PCCMin exactness or polynomial
runtime, put SAT in P, remove a project assumption, or prove `P = NP`.

## Required evidence

- root import and compiled theorem-inventory inclusion;
- an explicit axiom transcript for every new public declaration;
- a regression retaining all five checked consequences through the new
  certificate boundary;
- hostile mutations for retained strings, caller success flags, supplied
  conclusions, omitted checker bindings, assumptions, fixed dimensions, and
  claim widening;
- publication-map and formal-status rows with reviewed kernel fingerprints;
- current reconstruction, audit, pipeline, terminology, README, and canonical
  report documentation; and
- durable CI and aggregate-verifier coverage.

## Verification order and deduplication

Run lightweight source-shape checks before remote proof feedback.  On the
configured remote builder, compile the new dependency and root once, run its
axiom transcript and regression, reconcile generated publication evidence,
then run the complete core suite and one fresh exact-merge reproduction.  Do
not rerun a targeted command already covered by the unchanged full suite
unless diagnosing a failure.  PNPLabs consumes the exact verified core
artifacts byte-for-byte and must not invoke Lean, Lake, Elan, or the core proof
suite.

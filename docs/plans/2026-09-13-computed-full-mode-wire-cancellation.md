# M254: computed full-mode wire cancellation

## Legacy anchor and the missing dependency

Follow section 6.1 of the manuscript pinned by archive/legacy-v0/ARCHIVE.json:
R5 creates lost-bit obligations, and R6 may cancel one only with a full-mode
witness. Projected equality alone is insufficient. Section 6.2 places obligation
sorting and cancellation in traceable normalization; section 4 requires actual
physical materializer accounting.

M251 computes R5/full-R8 restoration but has no executable R6 cancellation case.
M252 charges a shared materializer for forgotten fields even when an original
ordinary output or kept field already represents the identical wire. M253
provides original-accounted replacement for a complete extracted frontier, but
does not derive the R6 full-mode obligation rule.

The next bounded edge is a source-derived computational R6 case: locate a
retained observation of the exact original wire, reuse its actual replacement
value, and materialize only unresolved forgotten fields. A full-value witness
must be derived for the actual expanded word, not supplied or inferred merely
from quotient padding.

## Preflight and immutable boundaries

The verified development parent is M253 commit
de5e3b7c6ccf5877e230e1c367ea11436b42b9d9, tree
a5a1759db18f836fe4e41b250ae36982c441d56e. Its complete core verification passed.
The latest fully earned main is M248; M249 and subsequent verified changes are
being released in order. Use an independent source/toolchain-matched checkout.
Do not mutate M253 or repeat its unchanged heavyweight verification.

The coherent PNPLabs main remains
3d62ceb5ab14d51b39bd1a89307dbfb8d5a55226 at the M231 public boundary.
There is no website change in this plan.

## Inputs and derived objects

Use namespace PNP.DirectWire.WireMatchedCancellation in
lean/PNP/NANDWireMatchedCancellation.lean.

The computational inputs are an arbitrary finite WireCarrier, a Boolean keep
mask and a replacement carrier. Reuse the exact M252
WireQuotientLift.QuotientAgreement premise for semantic claims: all ordinary
outputs and all kept fields agree for every valuation. Do not strengthen that
premise with forgotten-field equality or a supplied full-result certificate.

1. Enumerate the actual original ordinary outputs and kept computational fields
   in their canonical order. A forgotten field is never a visible representative
   merely because it is present in the exposed full word.
2. Compute a canonical representative for each field by literal equality of
   original Source data. A result records its actual observation index,
   visibility and exact source equality. Do not compare only gate numbers across
   different programs, compare masked false padding, enumerate semantic truth
   tables, accept an observer or accept a caller-selected representative.
3. Derive the representative's full value in a locally quotient-compatible
   replacement from the precise ordinary/kept agreement and original source
   identity. This is an all-valuation full equality, not a quotient-only witness.
4. Compute a resolved keep mask: originally kept fields and forgotten fields
   with a visible representative are resolved. Every other forgotten field
   remains unresolved.
5. Construct one actual missing-wire materializer from the original program for
   unresolved fields only. A completely resolved case may use an explicit
   zero-gate constant carrier, but the absence of unresolved obligations must
   be proved from the computed mask. Otherwise reuse the checked physical
   materializer. No successful result, charge or materializer program is input.
6. Form a visible carrier on the replacement's actual program. Kept fields use
   their replacement source; resolved forgotten fields use their representative
   replacement observation; unresolved padding is not full-value evidence.
7. Join this word with the actual remaining materializer once. Derive every
   ordinary output and every ordered computational field of the result.
8. Construct full-value R6 and R8 discharges bound to the actual expanded source.
   The R6 case must carry the computed original-source match. The R8 case must
   retain the unresolved condition and the actual materializer value witness.

This is a computational wire-identity cancellation rule. It is not a complete
implementation of every manuscript R6 recoding or semantic cancellation case.
A syntactically different but semantically equal wire may safely remain
unresolved; do not replace that distinction with an assumed equality.

## Exact general theorem boundary

Let charge carrier keep be the actual remaining materializer gate count, and
expanded carrier keep replacement be the constructed complete carrier.

The central full-value theorem must have this shape:

```lean
theorem expanded_field
    {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement)
    (valuation : Valuation inputs) (field : Fin fields) :
    (expanded carrier keep replacement).fieldValue valuation field =
      carrier.fieldValue valuation field
```

The exact charge theorem must have this shape:

```lean
theorem expanded_charge
    {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields) :
    (expanded carrier keep replacement).implementation.gateCount =
      replacement.implementation.gateCount + charge carrier keep
```

Also prove ordinary-output equivalence, representative soundness and
completeness for actual visible source matches, source-exact full discharges,
and the fully paid original-cost gain criterion. A gain against the original
requires replacement.gateCount + charge < original.gateCount.

Do not assume that independently normalized materializers are monotonically
ordered by their output sets. Any claimed comparison with M251/M252's charge
needs its own theorem. Exact accounting for the newly constructed word is
required; a universal improvement over the previous materializer is not.

A whole-word strict gain is not automatically a proper-support Package E
certificate. Do not claim VerifyDW acceptance or complete normalization.

## Mixed obligation lifecycle

Generate one R5 creation for every actually forgotten coordinate. Immediately
follow it with the derived full R6 cancellation when a visible representative
exists, or with the actual R8 restoration otherwise.

The event type must bind the actual expanded word; do not relabel an old R8
witness for a different program as an R6 event. Prove that creations and
discharges cover exactly the forgotten coordinates, every full witness has the
original value, and the generated replay closes with no pending obligations.

Validate creation identities across the entire transcript, including already
discharged entries. Reject duplicate creation, discharge-before-creation and
wrong-coordinate discharge. Preserve M251's whole-trace uniqueness boundary;
do not replace it by pending-only uniqueness or modify its existing theorems.
Reuse its public forgotten-coordinate uniqueness facts where applicable.
General R7 and arbitrary dependency DAGs remain open.

## Regressions and hostile contracts

- A lost field identical to an ordinary output, including the M252 tautology
  shape, resolves from the actual output without charging a duplicate wire.
- A lost field identical to a kept field resolves from that kept full value.
- Mixed resolved and unresolved fields retain the actual nonzero materializer;
  verify all ordinary outputs, ordered fields and full discharges.
- Repeated and reordered aliases share physical ownership without sharing or
  replaying an obligation identity.
- Two forgotten fields may not cancel each other merely because their source
  data match when neither has an actual retained representative.
- Matching only masked padding or a gate index in a different program must not
  fabricate a full-value match.
- Cover all-kept/all-forgotten masks, free input and constant sources, no ordinary
  outputs, empty dimensions, fully paid gain success and no-net-gain rejection.
- Kernel-check fixture equivalences and negative boundaries. Runtime executions
  remain bounded regressions, not authority for the general results.
- Reject supplied representatives, observers, materializer weights or global
  correctness, weakened/full-to-quotient witnesses, finite-only interfaces,
  forgotten-ID reuse, wrong source binding, new axioms, stale fingerprints and
  widened publication claims.

If the general construction fails, retain the exact blocker. Do not earn the
milestone by replacing it with fixed instances, an assumption or a caller-
supplied successful result.

## Progress and publication decision

The verified development baseline is M253: formal artefact coverage 229/231,
risk-weighted proof completion 40%, uncertainty 20% to 40%, 0/5 global gates,
no project-specific axioms, absent eligible root and false publication gate.

No fixed checkpoint is expected to close. The full manuscript carrier,
noncomputational profile fields, arbitrary-support N1-N10 transport, R7 and
general obligation dependencies, complete Package E, global routing,
unconditional SaturatePositive/BCELReady/ZeroSlack, exact polynomial PCCMin,
deterministic SAT and the eligible root remain open. A finite source scan or
gate-count identity is not a complete encoded-size polynomial execution theorem.

Publication decision: defer PNPLabs. This computational cancellation component
does not change the current major public bottom line. Continue meaningful
verified-submilestone notifications independently of website cadence.

## Verification and release

Record this plan before implementation. Reconcile theorem-name producers,
exact types, source/root contracts, package scripts and durable workflow in
the same change. While status is unsealed, use only the independent package
positive test and package mutation tests, not the integrated status acceptance
or root-export mutations.

Build the changed dependency and explicit root before imported audits, execute
the exact extracted workflow block, then freeze Lean sources before inventory
sealing. Review every generated status field against its new expectation.
The calendar has advanced to 2026-09-13: preserve every prior coordinate and
history entry while intentionally updating the current last-reviewed date.
Do not reuse a same-date layout assertion unchanged.

Run focused publication and documentation checks before one canonical report
reproduction and one combined deduplicated core suite. Preserve PR, post-merge
and independent exact-object gates. Release after M253's actual fully earned
merge, keeping the verified tree unchanged during one-commit reanchoring.
Clean all task-created temporary artifacts after full release.

# M255: computed unary full-word realization

## Named manuscript dependency

Follow the manuscript pinned by archive/legacy-v0/ARCHIVE.json, section 6.1:
R7 is unary cut realization and must supply a full-mode obligation discharge.
Sections 2 and 4 require ordered interfaces and actual uniquely owned physical
cost. Section 6.2 later transports gains through normalization traces.

M254 constructs full R6/R8 discharges for a supplied locally compatible
replacement. The next missing edge is to construct the replacement and full
agreement for a unary computational cut directly from its actual source.
The existing identity and NOT fixtures and the literal-constant propagation
pass are reused foundations, not new milestone claims.

## Preflight and fixed boundary

Verified development parent: 86ea2bea48bb13ca4619fb890ff9756e1df178e9, tree d55eb553bd6824f804dbc3d9f64a0011fc4a485a.
Use a separate checkout with matching source and pinned toolchain before
seeding its private build cache. Preserve every earlier milestone and source.

Core main is M249 merge e32605a435ab990dca4d72c362889099bc4a4973,
with its final post-merge verification still pending; M248 is the latest fully
earned release. PNPLabs remains at its coherent M231 public snapshot. Do not
repeat unchanged proof or website validation for those earlier objects.

This is a unary-cut rule: one boundary input, arbitrary original gate count,
arbitrary ordered ordinary outputs and arbitrary computational fields.
The fixed input dimension follows the manuscript's unary rule; it is not a
hard-coded program-size or output-slot extension. The downstream edge is
source-derived R7 full-value realization, followed by integration into the
ambient support and complete obligation calculus.

## Input-derived construction

Use namespace PNP.DirectWire.WireUnaryRealization and a new module
lean/PNP/NANDWireUnaryRealization.lean.

The sole semantic construction input is a WireCarrier 1 outputs fields.
The constructor does not accept a replacement, truth-vector table, source
classifier, local agreement, full-result certificate or materializer weight.

1. Expose the actual ordinary outputs and computational fields in order, reusing
   WireCarrier.exposed. Proof-only profile data must not become free outputs.
2. Evaluate each original observation at the two unary valuations. Derive the
   four possible unary value pairs directly from that source.
3. Compute whether any complete observation requires negation of the sole
   boundary input. Include computational fields, not only ordinary outputs.
4. Construct an actual zero-gate word using constants and the input if none
   requires negation. Otherwise use the existing single NOT NAND program and
   share its output among all negated observations. Preserve repetitions and
   order without duplicating the physical NOT gate.
5. Unpack the computed word as a full computational wire carrier. Derive every
   ordinary output and every field value for every unary valuation.
6. Prove the exact zero-or-one gate formula. When negation is required, prove
   that no zero-gate complete realization has the required two values: an
   available zero-gate source is only a constant or the sole input.
7. Obtain the minimum-size lower bound against every equivalent full
   computational carrier, and hence nonincrease against the input carrier.
   Do not claim ordinary-output-only minimality when fields demand a gate.
8. Construct source-exact full R7 discharges for original R5 creations, using
   the computed realization's actual source and the derived all-valuation
   equality. No forgotten-field equality is a constructor premise.
9. Compute the strict-gain query against the actual original gate count.
   A returned result must preserve all full computational values. It is not
   automatically a proper-support Package E certificate.

The two unary valuations are not exhaustive implementation minimization.
Do not call referenceMinimum, allCandidates or a caller-provided minimizer.
Existing recursive Program.eval can repeat source evaluation; a finite
two-valuation construction alone does not establish polynomial encoded runtime.

## Exact theorem interface

The full-value theorem must have this shape:

```lean
theorem realize_field {outputs fields : Nat}
    (carrier : WireCarrier 1 outputs fields)
    (valuation : Valuation 1) (field : Fin fields) :
    (realize carrier).fieldValue valuation field =
      carrier.fieldValue valuation field
```

There must be no supplied agreement or correctness binder.

The minimum theorem must compare all exposed computational observations:

```lean
theorem realize_minimal {outputs fields : Nat}
    (carrier other : WireCarrier 1 outputs fields)
    (sameFull : Equivalent other.exposed.candidate.program
      other.exposed.candidate.directWireWord
      carrier.exposed.candidate.program
      carrier.exposed.candidate.directWireWord) :
    (realize carrier).implementation.gateCount ≤ other.implementation.gateCount
```

The lower bound is mathematical evidence about this complete unary word,
not invocation of the exhaustive reference minimizer. Actual statements may
factor intermediate definitions without weakening either interface.

## Regression and hostile coverage

- Constants and identity realize with zero gates.
- Negation realizes with one actual gate shared across repeated and reordered
  ordinary outputs and computational fields.
- A constant ordinary output with a negated field still requires one gate;
  hiding that field cannot justify a zero-cost full realization.
- A two-gate unary tautology realizes at zero cost, with no supplied replacement.
- Redundant unary programs, mixed fields, all-kept/all-forgotten masks used only
  for R5 identities, no ordinary outputs, no fields and an empty full tuple.
- A singleton NOT input admits no strict gain; a larger equivalent input can.
- R7 witness sources and values refer to the actual new program and the original
  lost coordinate, not a masked word or an unrelated same-numbered gate.
- Reject supplied truth tables, replacements, agreement, result certificates,
  ordinary-only minima, duplicated NOT charges, weak full-value witnesses,
  finite program-size signatures, exhaustive implementation searches, extra
  axioms, stale fingerprints and widened publication claims.
- Probe the smallest executable fixtures under bounded resources before adding
  them to the broad suite. General theorems remain kernel authority; runtime
  fixtures do not replace their proofs.

If any required general theorem fails, retain the exact blocker. Do not replace
it with another fixed instance or a new premise.

## Progress and publication decision

The development baseline is M254: formal artefact coverage 230/232,
risk-weighted proof completion 40%, uncertainty 20% to 40%, 0/5 global gates,
no project-specific axioms, absent eligible root and false publication gate.

A complete unary computational realization does not derive every ambient
support, the full manuscript carrier, every R7 case or arbitrary obligation
DAGs. General Package E acceptance, all-trace N1-N10 transport, global routing,
unconditional SaturatePositive/BCELReady/ZeroSlack, exact general PCCMin,
encoded polynomial bounds, deterministic SAT and the eligible root remain open.
No fixed weighted checkpoint is expected to change.

Publication decision: defer PNPLabs. This is a named computational unary
component, not a new major public bottom line. Keep the M231 public snapshot
coherent and unchanged; notify meaningful verified substeps separately.

## Verification and release

Prepare source, theorem types and hostile contracts together. Reconcile the
explicit root, reviewed-name producers, package fixture and exact durable
workflow before compilation and inventory sealing. Use isolated package checks
while formal status is unsealed.

Build the new dependency and root before imported audits. Run the exact
extracted workflow and type-fingerprint probe, then freeze source before
inventory, status, progress and report generation. Preserve old checkpoint
definitions and all prior progress history.

Run targeted source and compiled/publication checks, one canonical report
reproduction and one combined deduplicated suite. Preserve normal PR checks,
manual merge, post-merge checks and exact-object independent reproduction.
Release only after M254's actual fully earned merge, preserving the verified
tree when reanchoring. Remove task-created temporary artifacts after release.

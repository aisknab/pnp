# M250: computed wire-backed carrier transport

## Legacy anchor and dependency edge

The pinned manuscript in `archive/legacy-v0/ARCHIVE.json`, section 2
Direct-wire words and Compatible replacement, requires the complete carrier's
computational values to survive replacement. Section 4 forbids proof-only
records from supplying free Boolean outputs. Section 5 requires normalization
and splice to preserve the relevant observations and physical accounting.

M248 computes physical normalization and M249 constructs literal arbitrary-
support replacements. They preserve the outputs they are actually given.
Neither supplies the missing representation of an internal wire-backed carrier
field as a required observation. The existing profile firewall instead accepts
an arbitrary observation function. Reconstruct this concrete value-transport
edge; do not present a new observer argument as a derived carrier.

## Actual objects

Define `WireCarrier inputs outputs fields` with an actual
`Implementation inputs outputs` and an ordered tuple
`Fin fields → Source inputs implementation.gateCount`. A field reads that
literal source under the program evaluation. There is no arbitrary observer,
Boolean truth certificate, replacement map, or supplied normalization result.

Internally expose the original output tuple followed by every field source,
without adding a NAND gate. Reconstruct the ordinary outputs and field bindings
from an actual transformed combined word. Prove the exact pack/unpack identity,
not only equal tuple lengths. The public ordinary output dimension is unchanged.

These are wire-backed computational value fields. Their representation does
not derive every noncomputational manuscript record, record role or history,
nor authorize a logical/proof-only record to become a Boolean source.

## Complete general targets

Use the existing actual three-pass normalization on the combined observations,
then recover the ordinary program and field bindings. For every finite number
of inputs, gates, ordinary outputs and fields, establish these public types:

```lean
theorem WireCarrier.normalize_output
    {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (carrier.normalize.implementation.candidate).semantics valuation output =
      carrier.implementation.candidate.semantics valuation output

theorem WireCarrier.normalize_field
    {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (valuation : Valuation inputs) (field : Fin fields) :
    carrier.normalize.fieldValue valuation field =
      carrier.fieldValue valuation field
```

Here `fieldValue` is the literal source evaluation described above and
`normalize` is computed from `runPhysicalNormalization`, not supplied.
Also prove exact gate accounting against the constructed normalization trace,
common quiescence of the combined observations and idempotence. Preserve every
field independently of whether any ordinary output uses its producer.

For arbitrary extracted supports, use the actual combined candidate with the
M249 graph construction and compiler. Required conclusions for every successful
literal splice are:

- every selected producer referenced by any field is in the computed support
  interface, including producers invisible to ordinary outputs;
- equality of the replacement's complete extracted open function preserves
  every ordinary output and every field value, for every input valuation;
- exact exterior/replacement accounting and strict local saving hold for the
  reconstructed ordinary implementation, with no extra field-count charge;
- a replacement matching ordinary outputs but losing a required field is not
  accepted as complete same-carrier open equality; and
- cyclic literal wiring still fails rather than manufacturing a wire value.

The splice field target has the following exact quantified content, with
`exposed` and `spliceResult` defined by those actual constructions:

```lean
theorem WireCarrier.splice_field
    {inputs outputs fields replacementGates : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (replacement : Candidate
      (extractTerminalSupport carrier.exposed.candidate records).boundary.length
      replacementGates
      (extractTerminalSupport carrier.exposed.candidate records).interface.length)
    (sameOpen : replacement.semantics =
      (extractTerminalSupport carrier.exposed.candidate records)
        .extractedCandidate.semantics)
    (compiled : CompiledRawNandGraph
      (ArbitrarySupportSplice.graph carrier.exposed.candidate records replacement))
    (valuation : Valuation inputs) (field : Fin fields) :
    (carrier.spliceResult records replacement compiled).fieldValue valuation field =
      carrier.fieldValue valuation field
```

The compiler itself takes no `compiled` certificate; this theorem applies to
its constructed result. The local open-function premise includes all computed
carrier ports and is not a supplied whole-circuit correctness certificate.

For the production specialization, derive predecessor closure from the actual
combined program and output word. No caller supplies a profile observer,
ordering or acyclicity proof. Additional abstract profile coordinates are empty
because these particular fields are explicitly represented as physical source
observations; this is not a claim that the complete manuscript profile is empty.

This milestone is not earned by pack/unpack wrappers alone: actual
normalization, hidden-field frontier exposure, arbitrary-support splice
preservation and observer-free production compilation must all be proved.

## Remaining boundaries

Do not claim the full manuscript carrier has been derived. Noncomputational
origin/kernel records, obligation creation and discharge under R5/R6-R8, all
materializer ownership and arbitrary-support Pull/Expand identities, complete
Package E and N1-N10, global routing, SaturatePositive, BCELReady, ZeroSlack,
exact PCCMin, encoded-size polynomial bounds and the eligible root remain open.
No minimum or exhaustive reference search belongs in these constructors.

Preserve the existing generic observer-based interfaces and all inherited
theorem statements. Do not weaken a failed general target to a supplied
profile-equality premise, a finite instance or an unverified role tag.

## Source and expectation chain

Prepare the general theorem and axiom contracts together with the source.
Update root imports, reviewed theorem-name producers, fixed package-script
fixtures, durable workflow and verification test lists before their consumers.
Run the root import-closure test in source preflight, including rejection of
unknown external imports. Keep the pinned-toolchain import set exact.

Regressions must cover hidden profile-only producers, overlapping and repeated
field sources, reordered field tuples, primary-input and constant fields, zero
ordinary outputs, zero fields, empty dimensions, actual smaller normalization,
safe and cyclic interleaved splices, larger replacements, and production
saturation. Every executable fixture is bounded; general kernel-checked
theorems remain the authority.

Hostile contracts must reject dropped fields, reordered observations, default
wire values, fake gate charges, supplied observers/maps/results, finite-only or
weakened statements, changed compiled fingerprints/axioms, and widened claims
of complete carrier or obligation-calculus closure.

## Verification and publication

Use the independent source-tree/toolchain-matched remote checkout. After bounded
leaf feedback, build the explicit root, execute the exact workflow block and
audit reviewed types. Freeze proof source before inventory/status generation;
then reconcile focused contracts, documentation and report inputs before one
deduplicated standard suite. Keep normal PR/post-merge and exact-object gates,
reusing unchanged proof/report evidence at the publication boundary.

Release only after preceding queued milestones are fully earned. Reanchor on
the actual verified M249 merge and require the tested tree to stay identical.
Clean all task-created checkouts, fixtures, helpers and logs after release.

M249 verified baseline: formal artefact coverage 225 of 227 scoped rows;
risk-weighted proof completion estimate 40%; uncertainty 20% to 40%; global
gates closed 0 of 5. Derive new coverage from the canonical ledger after the
complete milestone is proved. No fixed weighted checkpoint is expected to
close, so do not award proof-completion credit for the added observations.

Publication decision: defer PNPLabs. This computational-value transport
component does not by itself complete the manuscript carrier or change the
coherent published M231 bottom line. Notify meaningful verified substeps
independently of website cadence.

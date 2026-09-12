# M252: quotient-compatible replacement lifts with matched materializer charge

## Legacy anchor and dependency edge

Use the manuscript pinned by archive/legacy-v0/ARCHIVE.json: section 4
touch-to-charge and common materializer ownership, section 5 full/quotient
firewall, and section 2 compatible replacement and section 6.1 full-mode discharge.
Section 6.2 Traceable normalization requires the same materializer charge on
the reference and replacement sides before a local saving can transport.

M251 computes a full lift of its own actual projected word. The next missing
computational edge is a full lift of an arbitrary quotient-compatible
replacement using that same derived materializer, not an independently
supplied charge or full-field correctness witness.

This is a word-level computational component of the eventual Pull/Expand
construction. It is not yet an embedding of every pulled support into the
original circuit or the complete manuscript normalization theorem. Do not name
the reference lift a complete support Pull map.

## Inputs and exact local premise

Inputs are an actual WireCarrier inputs outputs fields, a Boolean keep mask,
and an actual replacement WireCarrier with the same finite input, ordinary
output and field dimensions.

QuotientAgreement means equality of every ordinary output and every kept
computational field with the computed projected word, for every valuation.
It says nothing about forgotten replacement fields. This is the manuscript's
local same-carrier replacement premise, not an assumed equality of the final
expanded program or a supplied correctness certificate for the construction.
Do not claim an algorithm that discovers equivalent replacements.

Use namespace PNP.DirectWire.WireQuotientLift and new source
lean/PNP/NANDWireQuotientLift.lean. Preserve inherited proof sources.

## Actual constructors

- charge is the actual gate count of the M251 materializer, derived from the
  original program and mask.
- referenceLift is the M251 restored word.
- expanded concatenates the actual replacement and the exact same materializer
  using literal common-input wiring. Kept fields and ordinary outputs come
  from the replacement; forgotten fields come from the materializer.
- A full discharge for a forgotten coordinate must bind its original source
  and the actual expanded source. Do not reuse an R8 record for a different
  restored program by relabelling its target.
- A computed gain query tests the complete expanded gate count against the
  original carrier. Under the local quotient agreement, a returned result
  provides complete ordinary-output and field preservation plus strict gain.

No observer, materializer program, charge ledger, complete expansion equality,
or successful result is supplied. No exhaustive semantic minimization occurs.

## General targets

For arbitrary finite dimensions, all valuations and all ordered fields:

1. Every expanded ordinary output equals its original value under
   QuotientAgreement.
2. Every expanded kept field equals its original value under that agreement;
   every forgotten field is restored from the materializer even without an
   agreement about the replacement's forgotten fields.
3. The reference lift count is exactly projected count plus charge.
4. The expanded count is exactly replacement count plus that identical charge.
5. Therefore the reference-minus-projected and expanded-minus-replacement
   charge differences are identical exact integer identities.
6. Expansion is strictly smaller than the reference lift iff replacement is
   strictly smaller than the projected word.
7. Expansion is strictly smaller than the original iff replacement count plus
   the actual materializer charge is strictly smaller than original count.
8. Each generated full discharge binds the exact expanded wire to the original
   lost coordinate with an all-input value proof.
9. The accepted gain result preserves all computational observations and pays
   the complete physical charge.

The crucial distinction is target identity: a saving against referenceLift is
not automatically a saving against the original carrier. The reference lift
can be larger than the original.


## Exact central theorem types

Use these complete arbitrary-dimension interfaces; do not replace them by finite
instances or a premise asserting the conclusion.

```lean
theorem expanded_field
    {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (same : QuotientAgreement carrier keep replacement)
    (valuation : Valuation inputs) (field : Fin fields) :
    (expanded carrier keep replacement).fieldValue valuation field =
      carrier.fieldValue valuation field

theorem matched_materializer_charge
    {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields) :
    ((referenceLift carrier keep).implementation.gateCount : Int) -
        (WireObligationRestoration.projected carrier keep).implementation.gateCount =
      ((expanded carrier keep replacement).implementation.gateCount : Int) -
        replacement.implementation.gateCount

theorem checkedGain_isSome_iff
    {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (same : QuotientAgreement carrier keep replacement) :
    (checkedGain carrier keep replacement same).isSome = true ↔
      replacement.implementation.gateCount + charge carrier keep <
        carrier.implementation.gateCount
```

Here checkedGain receives the exact local quotient agreement and computes the
complete physical cost decision. It does not compute equivalence by exhaustive
search, discover a replacement, or treat arbitrary equal ordinary outputs as
equality of the kept computational fields.

## Regressions and negative evidence

Use bounded executable fixtures plus kernel-checked general statements.
Runtime checks are not proof authority.

Include a nonzero-charge success, zero-cost input/constant fields, all-kept and
all-forgotten masks, repeated and reordered wires, empty dimensions and a
replacement with deliberately wrong forgotten fields that expansion repairs.

Include the two-gate NAND(x,NAND(x,x)) fixture with the same hidden tautological
wire: the existing physical passes leave a two-gate projected word and a
two-gate materializer. A zero-gate constant-true quotient replacement is smaller
than the projection, yet its expanded result still costs the original two gates.
The original-gain query must reject that as a strict gain.

Reject output or kept-field disagreement, ignored or duplicated materializer
charge, supplied construction authority, relabelled full witnesses, weak or
finite-only theorem types, new axioms, changed fingerprints, and claims of
complete support Pull/Expand, full obligation calculus, Package E or polynomial
PCCMin. Do not weaken an intended theorem or add a missing global premise to
make a failed proof pass.

## Integration, verification and publication

Record this plan in the new checkout before implementation. Update source,
root imports, regression, exact axiom/type audit, theorem-name producers,
package-script fixtures, workflow consumers and source/hostile contracts
together. Run the cheap source/root checks before inventory sealing. Compile
the root, execute the exact extracted workflow block, freeze proof source,
derive fingerprints and inventory, then synchronize status/progress and current
core documentation. Reuse unchanged evidence, run one report reproduction and
one deduplicated core suite, and preserve normal PR/post-merge and exact-object
release boundaries.

The generated M251 development snapshot has formal artefact coverage 227/229,
risk-weighted proof estimate 40%, uncertainty 20-40%, zero of five global gates,
no project-specific axioms, absent eligible root and false publication gate.
No fixed weighted checkpoint is expected to close here. Derive new coverage
only from the authoritative generated ledger.

Publication decision: defer PNPLabs. This word-level computational lift does not
complete arbitrary-support transport, the full carrier, general obligation
calculus or a global proof gate, and does not change the coherent published
M231 bottom line. Send meaningful verified submilestone notifications
independently of website cadence.

Release only after the actual verified M251 merge, reanchoring without changing
the verified tree. Give the run its own source/toolchain-matched checkout and
remove every task-created temporary artifact after complete release.

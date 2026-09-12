# Computed quotient replacement lift with matched costs

M252 is a computational word-level lift. It is not arbitrary-support Pull/Expand,
a complete manuscript carrier or a complete normalization theorem.

Formal artefact coverage: 228 of 230 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

## Specification and local premise

The route follows the manuscript pinned by
[the immutable archive manifest](../archive/legacy-v0/ARCHIVE.json): section 2
compatible replacement, section 4 touch-to-charge and common materializer
ownership, section 5's full/quotient firewall, and sections 6.1 and 6.2 on
full-mode discharge and traceable normalization.

For arbitrary finite input, ordinary-output and computational-field dimensions,
the inputs are the original wire carrier, a keep mask and a replacement carrier.
The local quotient agreement is a premise: the replacement agrees with the
computed projection on every ordinary output and every kept field, for every
valuation. It makes no assertion about forgotten replacement fields and does
not assert correctness of the final expanded word.

The construction does not discover a replacement or prove this local agreement.
The full expansion equality and lost-field witnesses are derived, not supplied.
No observer, materializer program, charge ledger or successful result is supplied.

## Actual construction and exact cost

The hidden-wire materializer is computed from the original program and mask
using the existing physical normalization. The reference lift appends this
materializer to the computed projection. The expansion appends the identical
materializer to the replacement, using literal common-input wiring.

Ordinary outputs and kept fields come from the replacement. Forgotten fields
come from the actual materializer. A shared materializer is paid once even when
several lost fields refer to the same wire.

Write Q for the projected gate count, R for replacement count and D for the
actual shared materializer count.

| Word or comparison | Exact gate-count statement |
| --- | --- |
| Reference lift | Q + D |
| Replacement expansion | R + D |
| Matched integer differences | (Q + D) - Q = (R + D) - R = D |
| Saving against the lifted reference | R < Q |
| Strict gain against the original | R + D < original gate count |

The reference lift can exceed the original gate count. Therefore a relative
saving is not necessarily an original-circuit gain. The computed gain query
tests the last inequality, retains the local quotient agreement, and returns
ordinary-output equivalence together with preservation of every computational
field and the exact paid cost.

The two-gate NAND(x, NAND(x,x)) regression makes the distinction concrete. Its
projected word and hidden tautology materializer each cost two gates. A zero-gate
constant-true replacement saves against the four-gate reference lift, but its
two-gate expansion does not beat the original. The strict-gain query rejects it.
A separate three-gate case accepts an actual one-gate expansion after paying its
nonzero materializer.

## Full-value discharge

Every lost-field discharge binds the original R5 source to the actual expanded
source at that coordinate. Its all-valuation full-value witness comes from the
literal hidden-wire materializer. It is not a relabelled R8 witness for a
different reference program. No agreement about the replacement's forgotten
field values is required.

## Reviewed general interfaces

All seventeen interfaces are built from the explicit PNP root, with exact
reviewed kernel-type fingerprints and dependencies propext and Quot.sound.

| Exact declaration | Checked interface |
| --- | --- |
| `PNP.DirectWire.WireQuotientLift.expanded_reference` | Expanding the computed projection is exactly the reference lift. |
| `PNP.DirectWire.WireQuotientLift.referenceLift_charge` | The reference lift pays projected cost plus the actual materializer. |
| `PNP.DirectWire.WireQuotientLift.expanded_charge` | The replacement expansion pays replacement cost plus the same materializer. |
| `PNP.DirectWire.WireQuotientLift.referenceLift_charge_difference` | The reference-minus-projected charge is an exact integer identity. |
| `PNP.DirectWire.WireQuotientLift.expanded_charge_difference` | The expanded-minus-replacement charge is an exact integer identity. |
| `PNP.DirectWire.WireQuotientLift.matched_materializer_charge` | The two exact materializer cost differences agree. |
| `PNP.DirectWire.WireQuotientLift.relative_saving_iff` | Relative savings compare expansion with the lifted reference, not the original. |
| `PNP.DirectWire.WireQuotientLift.original_gain_iff` | Original gains separately require the complete expanded cost to be smaller. |
| `PNP.DirectWire.WireQuotientLift.expanded_output` | Every ordinary output is preserved under the local quotient agreement. |
| `PNP.DirectWire.WireQuotientLift.expanded_kept_field` | Every kept computational field is preserved under that agreement. |
| `PNP.DirectWire.WireQuotientLift.expanded_forgotten_field` | Every forgotten field is restored without a premise about its replacement value. |
| `PNP.DirectWire.WireQuotientLift.expanded_field` | Every ordered computational field is preserved under the local agreement. |
| `PNP.DirectWire.WireQuotientLift.expanded_equivalent` | The expanded and original ordinary-output words are equivalent. |
| `PNP.DirectWire.WireQuotientLift.discharge_source_exact` | Each discharge identifies the actual expanded source at the lost coordinate. |
| `PNP.DirectWire.WireQuotientLift.discharge_full_value` | Every discharge source has the original full value for every valuation. |
| `PNP.DirectWire.WireQuotientLift.checkedGain_isSome_iff` | The computed gain query accepts exactly the fully paid original-cost inequality. |
| `PNP.DirectWire.WireQuotientLift.CheckedGain.checked` | An accepted gain carries complete equivalence, field preservation and exact cost. |

The [Lean source](../lean/PNP/NANDWireQuotientLift.lean),
[root-importing regressions](../lean-regression/PNPWireQuotientLift.lean),
[exact axiom audit](../lean-audit/PNPWireQuotientLiftAxiomAudit.lean) and
[publication contracts](../audits/lean-wire-quotient-lift0.test.mjs) retain the
same conservative boundary. The [recorded plan](./plans/2026-09-12-computed-quotient-replacement-lift.md)
states the original dependency edge and remaining obligations.

## Regression and hostile evidence

Fixtures cover nonzero-charge success, a relative saving with no original gain,
all-kept and all-forgotten masks, repaired wrong forgotten values, shared,
repeated and ordered fields, zero-gate input/constant fields, no ordinary outputs
and empty dimensions. Kernel-checked negative examples reject wrong ordinary
outputs and wrong kept fields. Runtime execution is test evidence, not theorem
authority.

Contracts reject omitted charges, a reference lift falsely identified with the
original, weakened local agreement, unbound full witnesses, supplied global
authority, weakened or finite-only interfaces, new axioms, fingerprint drift
and widened publication claims.

## Remaining boundary and publication decision

This is a computational word-level quotient lift, not arbitrary-support Pull/Expand or an embedding of the reference lift into the original circuit. The keep mask, replacement and local quotient agreement are inputs; the construction does not discover replacements or derive that local agreement. The lifted reference can exceed the original gate count, and a relative saving can leave no original gain. It does not complete the manuscript carrier, R6/R7 and general obligation-dependency DAG calculus, N1-N10, Package E, global routing, unconditional SaturatePositive, BCELReady or ZeroSlack, exact PCCMin or total encoded-size polynomial construction, runtime, output and certificate bounds. No fixed weighted checkpoint or global gate closes. Deterministic CNFSAT in P and the eligible root remain absent, and P = NP is not proved.

No fixed checkpoint or global gate closes. Publication decision: defer PNPLabs.
The existing M231 site pin remains coherent while core work continues toward
arbitrary-support transport, the complete obligation calculus, Package E and
the global proof obligations. Neither an iteration bound nor finite termination
would establish polynomial execution of the complete construction.

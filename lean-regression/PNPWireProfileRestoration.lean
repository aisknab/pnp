import PNP

namespace PNP.DirectWire.WireProfileRestorationRegression

open WireProfile WireProfileRestoration

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    projectionDefect carrier keep ≤ WireQuotientLift.charge carrier keep :=
  projectionDefect_le_charge carrier keep

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (paidWitness carrier keep).implementation.gateCount =
      fullMinimum carrier +
        (WireQuotientLift.charge carrier keep - projectionDefect carrier keep) :=
  paidWitness_exact_overhead carrier keep

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    reclaimed carrier keep ≤
      WireQuotientLift.charge carrier keep - projectionDefect carrier keep :=
  reclaimed_le_overhead carrier keep

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (normalizedWitness carrier keep).implementation.gateCount =
      fullMinimum carrier +
        (WireQuotientLift.charge carrier keep - projectionDefect carrier keep -
          reclaimed carrier keep) :=
  normalizedWitness_exact_overhead carrier keep

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (checkedGain carrier keep).isSome = true ↔
      WireQuotientLift.charge carrier keep - projectionDefect carrier keep -
        reclaimed carrier keep < carrier.implementation.gateCount - fullMinimum carrier :=
  checkedGain_isSome_iff carrier keep

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (valuation : Valuation inputs) (output : Fin outputs) :
    (normalizedWitness carrier keep).implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output :=
  ((full_iff carrier _).1 (normalizedWitness_fullEquivalent carrier keep)).1
    valuation output

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (valuation : Valuation inputs) (field : Fin fields) :
    (normalizedWitness carrier keep).fieldValue valuation field =
      carrier.fieldValue valuation field :=
  ((full_iff carrier _).1 (normalizedWitness_fullEquivalent carrier keep)).2
    valuation field


example {outputs fields : Nat} (carrier : WireCarrier 1 outputs fields) :
    fullMinimum carrier = (WireUnaryRealization.realize carrier).implementation.gateCount :=
  unary_fullMinimum carrier

example {outputs fields : Nat} (carrier : WireCarrier 1 outputs fields) :
    (WireUnaryRealization.realize carrier).implementation.gateCount <
        carrier.implementation.gateCount ↔ 0 < fullSlack carrier :=
  unary_smaller_iff_fullSlack_positive carrier

private def notProgram : Program 1 1 :=
  .snoc .empty ⟨.input 0, .input 0⟩

private def hiddenNot : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord notProgram ⟨fun _ => .input 0⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def duplicateNotProgram : Program 1 2 :=
  .snoc (.snoc .empty ⟨.input 0, .input 0⟩) ⟨.input 0, .input 0⟩

private def duplicateNot : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord duplicateNotProgram
        ⟨fun _ => .gate ⟨0, by decide⟩⟩).toImplementation
    source := fun _ => .gate ⟨1, by decide⟩ }

private def emptyCarrier : WireCarrier 0 0 0 :=
  { implementation := (Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩).toImplementation
    source := Fin.elim0 }

/-- These guarded executable fixtures test actual computations. They do not
create theorem authority or replace the general kernel-checked contracts above. -/
private def checkCase {inputs outputs fields : Nat} (label : String)
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (expected : List Nat) (gainExpected : Bool) : IO Unit := do
  let metrics := [carrier.implementation.gateCount, quotientMinimum carrier keep,
    fullMinimum carrier, WireQuotientLift.charge carrier keep,
    (paidWitness carrier keep).implementation.gateCount,
    (normalizedWitness carrier keep).implementation.gateCount,
    overhead carrier keep, reclaimed carrier keep, remainingOverhead carrier keep]
  if metrics != expected then
    throw (IO.userError s!"{label}: restoration metrics mismatch: {metrics}")
  if (checkedGain carrier keep).isSome != gainExpected then
    throw (IO.userError s!"{label}: final gain decision mismatch")
  IO.println s!"restoration-case-passed: {label}"

def run : IO Unit := do
  checkCase "hidden value requires payment; no saving" hiddenNot (fun _ => false)
    [1, 0, 1, 1, 1, 1, 0, 0, 0] false
  checkCase "shared value: paid candidate is not a gain; normalization recovers overhead"
    duplicateNot (fun _ => false) [2, 1, 1, 1, 2, 1, 1, 1, 0] true
  checkCase "empty dimensions" emptyCarrier Fin.elim0 [0, 0, 0, 0, 0, 0, 0, 0, 0] false
  IO.println "restoration-regressions-passed: 3 guarded executable cases"

end PNP.DirectWire.WireProfileRestorationRegression

def main : IO Unit := PNP.DirectWire.WireProfileRestorationRegression.run

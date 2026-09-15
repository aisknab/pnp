/-
Copyright (c) 2026 PNP Labs.

Arbitrary-dimension computed R7 dependency contracts and an adversarial
Boolean-sound compiler record. These checks do not claim that raw-history
R7 discharge or complete Package E has already been integrated.
-/

import PNP.NANDWireUnaryCausalBounds

open PNP PNP.DirectWire

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0))
    (small : (WireUnaryArbitrarySupport.pulled carrier records).boundary.length ≤ 1)
    (labels : Fin inputs → Nat) :
    (WireUnaryArbitrarySupport.expanded carrier records small).CausalBounds labels
      (CausalBound.outputLevel carrier.implementation.candidate labels)
      (carrier.fieldLevel labels) :=
  WireUnaryCausalBound.expanded_causalBounds carrier records small labels

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0))
    (realized : WireCarrier inputs outputs fields)
    (accepted : WireUnaryArbitrarySupport.attempt carrier records = some realized)
    (labels : Fin inputs → Nat) :
    realized.CausalBounds labels
      (CausalBound.outputLevel carrier.implementation.candidate labels)
      (carrier.fieldLevel labels) :=
  WireUnaryCausalBound.attempt_causalBounds carrier records realized accepted labels

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0))
    (small : (WireUnaryArbitrarySupport.pulled carrier records).boundary.length ≤ 1) :
    ArbitrarySupportSplice.compile carrier.exposed.candidate records
        (WireUnaryArbitrarySupport.replacement carrier records small).candidate =
      some (WireUnaryArbitrarySupport.compiled carrier records small) :=
  WireUnaryCausalBound.compiled_spec carrier records small

namespace PNP.DirectWire.ComputedR7CausalRegression

private def constantGraph : RawNandGraph 1 1 :=
  ⟨fun _ => ⟨.constant false, .constant false⟩⟩

/-- Boolean soundness can conceal a real, unnecessary physical dependency. -/
private def booleanSoundButDependent : CompiledRawNandGraph constantGraph where
  count := 1
  program := (.empty : Program 1 0).snoc ⟨.input fin1Zero, .constant false⟩
  position := fun _ => fin1Zero
  count_eq := rfl
  position_injective := by
    intro left right _same
    apply Fin.ext
    have leftBound := left.isLt
    have rightBound := right.isLt
    omega
  ordered := by
    intro producer consumer dependency
    rcases dependency with left | right
    · cases left
    · cases right
  sound := by
    intro input values equations node
    have actual := equations node
    change values node = boolNand false false at actual
    change boolNand (input fin1Zero) false = values node
    rw [actual]
    cases input fin1Zero <;> rfl

private theorem original_zero_cap :
    RawNandCausalBound.GraphBounds constantGraph (fun _ => 1) (fun _ => 0) := by
  intro node
  exact Nat.le_refl 0

example : CausalBound.levels booleanSoundButDependent.program (fun _ => 1)
    (booleanSoundButDependent.position fin1Zero) = 1 := rfl

example : ¬(∀ node, CausalBound.levels booleanSoundButDependent.program (fun _ => 1)
    (booleanSoundButDependent.position node) ≤ 0) := by
  intro bounded
  have invalid := bounded fin1Zero
  change 1 ≤ 0 at invalid
  omega

/-- The actual-result premise of the compiler theorem is indispensable. -/
example : compileRawNandGraph constantGraph ≠ some booleanSoundButDependent := by
  intro accepted
  have invalid := RawNandCausalBound.compile_bounds constantGraph booleanSoundButDependent
    accepted (fun _ => 1) (fun _ => 0) original_zero_cap fin1Zero
  change 1 ≤ 0 at invalid
  omega

end PNP.DirectWire.ComputedR7CausalRegression

import PNP.Concrete.NativeNormalization.MeasuredWitness

namespace PNP.Concrete.NativeNormalization.MeasuredSourceRecovery

open PNP.Concrete MeasuredReach NativeContext NativeBasis NativeEquations
open MeasuredOperations MeasuredSourceCache

abbrev Cache (F : CNFFormula) :=
  Built (NativeTseitin.frontend F) (NativeFrontend.frontend_three F)

/-- Restore discarded variables, then retain exactly the original declared input width. -/
def finish (F : CNFFormula) (b : Cache F) (a : BitString) : Measured BitString :=
  let expanded := MeasuredCutRecovery.recover b.context.toCutData a
  let original := MeasuredBits.project F.variableCount expanded.value
  ⟨original.value,expanded.cost+original.cost+1⟩

theorem finish_value (F : CNFFormula) (b : Cache F) (a : BitString) :
    (finish F b a).value =
      NativeTseitin.recoverOriginal F (b.context.toCutData.recover a) := by
  simp only [finish,MeasuredBits.recoverOriginal_value,MeasuredCutRecovery.recover_value]

theorem finish_length (F : CNFFormula) (b : Cache F) (a : BitString) :
    (finish F b a).value.length = F.variableCount :=
  MeasuredBits.project_length _ _

def finishBound (B A : Nat) : Nat :=
  MeasuredCutRecovery.recoverBound B A+MeasuredBits.projectBound B+1

theorem finish_cost (F : CNFFormula) (b : Cache F) (a : BitString) (B A : Nat)
    (size : (NativeTseitin.frontend F).clauses.length+
      (NativeTseitin.frontend F).variableCount ≤ B)
    (width : F.variableCount ≤ B) (ha : a.length ≤ A) :
    (finish F b a).cost ≤ finishBound B A := by
  have shape : ∀ i, (CNFCore.clause (NativeTseitin.frontend F) i).length ≤ 3 := by
    intro i
    exact Nat.le_of_eq
      (NativeTseitin.frontend_shape F _ (CNFCore.source_member (NativeTseitin.frontend F) i)).1
  have he := MeasuredCutRecovery.recover_cost b.context.toCutData a shape B A size ha
  have hp := MeasuredBits.project_cost F.variableCount
    (MeasuredCutRecovery.recover b.context.toCutData a).value B width
  simp only [finish,finishBound]
  omega

/-- Translate the computed candidate. It is a model only after its clause check succeeds. -/
def candidate (F : CNFFormula) (b : Cache F) : Measured BitString :=
  let dense := MeasuredCandidate.assignment (MeasuredCache.operations b.data)
  let original := finish F b dense.value
  ⟨original.value,dense.cost+original.cost+1⟩

theorem candidate_value (F : CNFFormula) (b : Cache F) :
    (candidate F b).value = NativeTseitin.recoverOriginal F
      (b.context.toCutData.recover (List.ofFn (NativeBasis.sigma (MeasuredCache.selection b.data)))) := by
  simp only [candidate,finish_value,MeasuredCandidate.assignment_value,MeasuredCache.selection_eq]

theorem candidate_length (F : CNFFormula) (b : Cache F) :
    (candidate F b).value.length = F.variableCount := finish_length _ _ _

def candidateBound (B : Nat) : Nat :=
  MeasuredCandidate.assignmentBound B (B+1) B B+finishBound B B+1

theorem candidate_cost (F : CNFFormula) (b : Cache F) (B : Nat)
    (size : (NativeTseitin.frontend F).clauses.length+
      (NativeTseitin.frontend F).variableCount ≤ B)
    (width : F.variableCount ≤ B) : (candidate F b).cost ≤ candidateBound B := by
  have dims := MeasuredRun.built_dimensions b B size
  have bounds := cached_operations_bounded b B size
  have hd := MeasuredCandidate.assignment_cost (MeasuredCache.operations b.data)
    B (B+1) B B B dims.1 bounds
  have hlen : (MeasuredCandidate.assignment (MeasuredCache.operations b.data)).value.length = b.columns := by
    rw [MeasuredCandidate.assignment_value,List.length_ofFn]
  have hf := finish_cost F b (MeasuredCandidate.assignment (MeasuredCache.operations b.data)).value
    B B size width (by rw [hlen]; exact dims.1)
  simp only [candidate,candidateBound]
  omega

/-- This recovers a proposed witness; it does not search for one or assert its validity. -/
def witness (F : CNFFormula) (b : Cache F) (failed : Fin b.rows) (a : BitString) :
    Measured BitString :=
  let dense := MeasuredWitness.fromBits (MeasuredCache.operations b.data) failed a
  let original := finish F b dense.value
  ⟨original.value,dense.cost+original.cost+1⟩

theorem witness_value (F : CNFFormula) (b : Cache F) (failed : Fin b.rows) (a : BitString) :
    (witness F b failed a).value = NativeTseitin.recoverOriginal F
      (b.context.toCutData.recover (List.ofFn
        (recovered (MeasuredCache.selection b.data) failed (MeasuredBits.rowValues b.rows a)).x)) := by
  simp only [witness,finish_value,MeasuredWitness.fromBits_value,MeasuredCache.selection_eq]

theorem witness_length (F : CNFFormula) (b : Cache F) (failed : Fin b.rows) (a : BitString) :
    (witness F b failed a).value.length = F.variableCount := finish_length _ _ _

def witnessBound (B : Nat) : Nat :=
  MeasuredWitness.recoverBound B (B+1) B B B (2*B+4)+finishBound B B+1

theorem witness_cost (F : CNFFormula) (b : Cache F) (failed : Fin b.rows) (a : BitString)
    (B : Nat) (size : (NativeTseitin.frontend F).clauses.length+
      (NativeTseitin.frontend F).variableCount ≤ B)
    (width : F.variableCount ≤ B) : (witness F b failed a).cost ≤ witnessBound B := by
  have dims := MeasuredRun.built_dimensions b B size
  have bounds := cached_operations_bounded b B size
  have hd := MeasuredWitness.fromBits_cost (MeasuredCache.operations b.data) failed a
    B (B+1) B B B dims.1 dims.2 bounds
  have hf := finish_cost F b
    (MeasuredWitness.fromBits (MeasuredCache.operations b.data) failed a).value B B size width
    (by rw [MeasuredWitness.fromBits_length]; exact dims.1)
  simp only [witness,witnessBound]
  omega

theorem decoded_candidate_cost (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) (b : Cache F) :
    (candidate F b).cost ≤ candidateBound (21*bits.length+9) := by
  have sizes := MeasuredFrontendCost.frontend_encoded_counts bits F decoded
  have width := CNFCore.decoded_width_bound bits F decoded
  exact candidate_cost F b (21*bits.length+9) (by omega) (by omega)

theorem decoded_witness_cost (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) (b : Cache F) (failed : Fin b.rows) (a : BitString) :
    (witness F b failed a).cost ≤ witnessBound (21*bits.length+9) := by
  have sizes := MeasuredFrontendCost.frontend_encoded_counts bits F decoded
  have width := CNFCore.decoded_width_bound bits F decoded
  exact witness_cost F b failed a (21*bits.length+9) (by omega) (by omega)


end PNP.Concrete.NativeNormalization.MeasuredSourceRecovery

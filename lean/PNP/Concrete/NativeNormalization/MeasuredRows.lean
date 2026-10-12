import PNP.Concrete.NativeNormalization.MeasuredCandidate

namespace PNP.Concrete.NativeNormalization.MeasuredRows

open MeasuredReach MeasuredOperations NativeBasis NativeEquations

def variableRow {S : Selection n c} (ops : Operations S) (v : Fin n) : Measured (Row c) :=
  let owner := ops.owner v
  let slot := ops.slot v
  ⟨(owner.value,decide (slot.value = .last)),owner.cost+slot.cost+2⟩

theorem variableRow_value {S : Selection n c} (ops : Operations S) (failed : Fin c) (v : Fin n) :
    (variableRow ops v).value = NativeCoefficients.variableRow S failed v := by
  simp only [variableRow,ops.owner_eq,ops.slot_eq,NativeCoefficients.variableRow,NativeBasis.row]

theorem variableRow_cost {S : Selection n c} (ops : Operations S) (L O D M : Nat)
    (bounds : Bounded ops L O D M) (v : Fin n) :
    (variableRow ops v).cost ≤ O+D+2 := by
  have ho := bounds.2.1 v
  have hd := bounds.2.2.1 v
  simp only [variableRow]
  omega

def auxiliaryRow {S : Selection n c} (ops : Operations S) (i : Fin c) : Measured (Row c) :=
  let mode := ops.mode i
  ⟨(i,decide (mode.value ≠ some .last)),mode.cost+2⟩

theorem auxiliaryRow_value {S : Selection n c} (ops : Operations S) (failed i : Fin c) :
    (auxiliaryRow ops i).value = NativeCoefficients.auxiliaryRow S failed i := by
  simp only [auxiliaryRow,ops.mode_eq,NativeCoefficients.auxiliaryRow,NativeBasis.row]

theorem auxiliaryRow_cost {S : Selection n c} (ops : Operations S) (L O D M : Nat)
    (bounds : Bounded ops L O D M) (i : Fin c) :
    (auxiliaryRow ops i).cost ≤ M+2 := by
  have hm := bounds.2.2.2 i
  simp only [auxiliaryRow]
  omega

def extraRow (failed : Fin c) : Measured (Row c) := ⟨(failed,false),1⟩

theorem extraRow_value (S : Selection n c) (failed : Fin c) :
    (extraRow failed).value = NativeCoefficients.extraRow S failed := rfl

theorem extraRow_cost (failed : Fin c) : (extraRow failed).cost = 1 := rfl


end PNP.Concrete.NativeNormalization.MeasuredRows

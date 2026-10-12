import PNP.Concrete.NativeNormalization.MeasuredRunCorrectness

namespace PNP.Concrete.NativeNormalization.MeasuredProducer

open PNP.Concrete MeasuredReach NativeBasis NativeEquations NativeSparseSystem
open MeasuredRunCorrectness

inductive Result where
  | model (assignment : BitString)
  | system (rows : Nat) (data : System rows) (recoverModel : BitString → Measured BitString)

def Correct (F : CNFFormula) : Result → Prop
  | .model a => F.Satisfied a
  | .system c D liftModel =>
      (F.Satisfiable ↔ ∃ a : BitString, a.length = 2*c ∧ D.Satisfied (MeasuredBits.rowValues c a)) ∧
      (∀ a, D.Satisfied (MeasuredBits.rowValues c a) → F.Satisfied (liftModel a).value) ∧
      c = (CNFCore.positions (NativeTseitin.frontend F)).length ∧
      NativeFrontend.SparseBounds D ∧
      (∀ a, (liftModel a).value.length = F.variableCount)

/-- Finish the existing dense candidate once; a system branch only constructs a recovery closure. -/
def finish (F : CNFFormula) (b : MeasuredSourceRecovery.Cache F) :
    MeasuredRun.Output b.rows → Measured Result
  | .candidate a =>
      let original := MeasuredSourceRecovery.finish F b a
      ⟨.model original.value,original.cost+1⟩
  | .system failed D =>
      ⟨.system b.rows D (MeasuredSourceRecovery.witness F b failed),1⟩

theorem finish_correct (F : CNFFormula) (b : MeasuredSourceRecovery.Cache F)
    (r : MeasuredRun.Output b.rows)
    (h : CoreCorrect (NativeTseitin.frontend F) (MeasuredCache.selection b.data)
      b.context.toCutData.recover r) : Correct F (finish F b r).value := by
  cases r with
  | candidate a =>
      change F.Satisfied (MeasuredSourceRecovery.finish F b a).value
      rw [MeasuredSourceRecovery.finish_value]
      exact NativeTseitin.frontend_recovery F _ h
  | system failed D =>
      obtain ⟨he,hr,hb⟩ := h
      refine ⟨((NativeTseitin.frontend_satisfiable_iff F).symm.trans he).trans
        (MeasuredRowEncoding.system_iff D),?_,b.rows_eq,hb,?_⟩
      · intro a ha
        rw [MeasuredSourceRecovery.witness_value]
        exact NativeTseitin.frontend_recovery F _
          (hr (MeasuredBits.rowValues b.rows a) ha)
      · intro a
        exact MeasuredSourceRecovery.witness_length F b failed a

/-- Fully source-derived formula interface. Input decoding and frontend conversion work
are still outside this source-operation account and must be added separately. -/
def produce (F : CNFFormula) : Measured Result :=
  let prepared := MeasuredRun.fromSource F
  let result := finish F prepared.value.cache prepared.value.output
  ⟨result.value,prepared.cost+result.cost+1⟩

theorem produce_correct (F : CNFFormula) : Correct F (produce F).value :=
  finish_correct F _ _ (MeasuredRunCorrectness.source_correct F)

def finishBound (B : Nat) : Nat := MeasuredSourceRecovery.finishBound B B+1

theorem finish_cost (F : CNFFormula) (b : MeasuredSourceRecovery.Cache F)
    (r : MeasuredRun.Output b.rows) (B : Nat)
    (size : (NativeTseitin.frontend F).clauses.length+
      (NativeTseitin.frontend F).variableCount ≤ B)
    (width : F.variableCount ≤ B) (sized : Sized b.columns r) :
    (finish F b r).cost ≤ finishBound B := by
  cases r with
  | candidate a =>
      have dims := MeasuredRun.built_dimensions b B size
      have ha : a.length ≤ B := by
        have he : a.length = b.columns := sized
        omega
      have h := MeasuredSourceRecovery.finish_cost F b a B B size width ha
      simp only [finish,finishBound]
      omega
  | system failed D =>
      simp only [finish,finishBound]
      omega

def RecoveryBound (B : Nat) : Result → Prop
  | .model _ => True
  | .system _ _ recover => ∀ a, (recover a).cost ≤ MeasuredSourceRecovery.witnessBound B

theorem finish_recovery_bound (F : CNFFormula) (b : MeasuredSourceRecovery.Cache F)
    (r : MeasuredRun.Output b.rows) (B : Nat)
    (size : (NativeTseitin.frontend F).clauses.length+
      (NativeTseitin.frontend F).variableCount ≤ B)
    (width : F.variableCount ≤ B) : RecoveryBound B (finish F b r).value := by
  cases r with
  | candidate a => trivial
  | system failed D =>
      intro a
      exact MeasuredSourceRecovery.witness_cost F b failed a B size width

def produceBound (B : Nat) : Nat :=
  MeasuredRun.sourceBound B+MeasuredSourceRecovery.finishBound B B+2

theorem decoded_produce_cost (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    (produce F).cost ≤ produceBound (21*bits.length+9) := by
  let prepared := MeasuredRun.fromSource F
  let B := 21*bits.length+9
  have hp : prepared.cost ≤ MeasuredRun.sourceBound B :=
    MeasuredRun.decoded_fromSource_cost bits F decoded
  have sizes := MeasuredFrontendCost.frontend_encoded_counts bits F decoded
  have width := CNFCore.decoded_width_bound bits F decoded
  have hf := finish_cost F prepared.value.cache prepared.value.output B
    (by dsimp [B]; omega) (by dsimp [B]; omega) (MeasuredRunCorrectness.source_size F)
  change prepared.cost+(finish F prepared.value.cache prepared.value.output).cost+1 ≤ produceBound B
  unfold produceBound finishBound at *
  omega

theorem decoded_recovery_bound (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    RecoveryBound (21*bits.length+9) (produce F).value := by
  have sizes := MeasuredFrontendCost.frontend_encoded_counts bits F decoded
  have width := CNFCore.decoded_width_bound bits F decoded
  exact finish_recovery_bound F _ _ (21*bits.length+9) (by omega) (by omega)


end PNP.Concrete.NativeNormalization.MeasuredProducer

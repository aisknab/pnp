import PNP.Concrete.NativeNormalization.MeasuredRawFrontend

namespace PNP.Concrete.NativeNormalization.MeasuredSharedProducer

open PNP.Concrete MeasuredReach NativeSource MeasuredSourceCache
open MeasuredRunCorrectness

/-- G is prebuilt runtime data. No canonical frontend is recomputed here. -/
def recover (F G : CNFFormula) (three : ThreeCore G) (b : Built G three)
    (a : BitString) : Measured BitString :=
  let expanded := MeasuredCutRecovery.recover b.context.toCutData a
  let original := MeasuredBits.project F.variableCount expanded.value
  ⟨original.value,expanded.cost+original.cost+1⟩

def witness (F G : CNFFormula) (three : ThreeCore G) (b : Built G three)
    (failed : Fin b.rows) (a : BitString) : Measured BitString :=
  let dense := MeasuredWitness.fromBits (MeasuredCache.operations b.data) failed a
  let original := recover F G three b dense.value
  ⟨original.value,dense.cost+original.cost+1⟩

theorem recover_canonical (F : CNFFormula) (b : MeasuredSourceRecovery.Cache F)
    (a : BitString) :
    recover F (NativeTseitin.frontend F) (NativeFrontend.frontend_three F) b a =
      MeasuredSourceRecovery.finish F b a := rfl

theorem witness_canonical (F : CNFFormula) (b : MeasuredSourceRecovery.Cache F)
    (failed : Fin b.rows) (a : BitString) :
    witness F (NativeTseitin.frontend F) (NativeFrontend.frontend_three F) b failed a =
      MeasuredSourceRecovery.witness F b failed a := rfl

def finish (F G : CNFFormula) (three : ThreeCore G) (b : Built G three) :
    MeasuredRun.Output b.rows → Measured MeasuredProducer.Result
  | .candidate a =>
      let original := recover F G three b a
      ⟨.model original.value,original.cost+1⟩
  | .system failed D => ⟨.system b.rows D (witness F G three b failed),1⟩

theorem finish_canonical (F : CNFFormula) (b : MeasuredSourceRecovery.Cache F)
    (r : MeasuredRun.Output b.rows) :
    finish F (NativeTseitin.frontend F) (NativeFrontend.frontend_three F) b r =
      MeasuredProducer.finish F b r := by
  cases r <;> rfl

theorem finish_correct (F G : CNFFormula) (same : G = NativeTseitin.frontend F)
    (three : ThreeCore G) (b : Built G three) (r : MeasuredRun.Output b.rows)
    (h : CoreCorrect G (MeasuredCache.selection b.data) b.context.toCutData.recover r) :
    MeasuredProducer.Correct F (finish F G three b r).value := by
  subst G
  rw [finish_canonical]
  exact MeasuredProducer.finish_correct F b r h

theorem finish_cost (F G : CNFFormula) (same : G = NativeTseitin.frontend F)
    (three : ThreeCore G) (b : Built G three) (r : MeasuredRun.Output b.rows)
    (B : Nat) (size : G.clauses.length+G.variableCount ≤ B)
    (width : F.variableCount ≤ B) (sized : Sized b.columns r) :
    (finish F G three b r).cost ≤ MeasuredProducer.finishBound B := by
  subst G
  rw [finish_canonical]
  exact MeasuredProducer.finish_cost F b r B size width sized

theorem finish_recovery_bound (F G : CNFFormula) (same : G = NativeTseitin.frontend F)
    (three : ThreeCore G) (b : Built G three) (r : MeasuredRun.Output b.rows)
    (B : Nat) (size : G.clauses.length+G.variableCount ≤ B)
    (width : F.variableCount ≤ B) :
    MeasuredProducer.RecoveryBound B (finish F G three b r).value := by
  subst G
  rw [finish_canonical]
  exact MeasuredProducer.finish_recovery_bound F b r B size width

def fromCache (F G : CNFFormula) (three : ThreeCore G) (b : Built G three) :
    Measured MeasuredProducer.Result :=
  let run := MeasuredRun.run (MeasuredCache.operations b.data)
  let result := finish F G three b run.value
  ⟨result.value,run.cost+result.cost+1⟩

theorem fromCache_correct (F G : CNFFormula) (same : G = NativeTseitin.frontend F)
    (three : ThreeCore G) (b : Built G three) :
    MeasuredProducer.Correct F (fromCache F G three b).value :=
  finish_correct F G same three b _ (cache_run_correct G three b)

theorem fromCache_cost (F G : CNFFormula) (same : G = NativeTseitin.frontend F)
    (three : ThreeCore G) (b : Built G three)
    (B : Nat) (size : G.clauses.length+G.variableCount ≤ B)
    (width : F.variableCount ≤ B) :
    (fromCache F G three b).cost ≤
      MeasuredRun.runBound B (B+1) B B B+MeasuredProducer.finishBound B+1 := by
  have dims := MeasuredRun.built_dimensions b B size
  have bounds := cached_operations_bounded b B size
  have hr := MeasuredRun.run_cost (MeasuredCache.operations b.data)
    B (B+1) B B B dims.1 dims.2 bounds
  have hf := finish_cost F G same three b _ B size width
    (run_size (MeasuredCache.operations b.data))
  simp only [fromCache]
  omega

theorem fromCache_recovery_bound (F G : CNFFormula) (same : G = NativeTseitin.frontend F)
    (three : ThreeCore G) (b : Built G three)
    (B : Nat) (size : G.clauses.length+G.variableCount ≤ B)
    (width : F.variableCount ≤ B) :
    MeasuredProducer.RecoveryBound B (fromCache F G three b).value :=
  finish_recovery_bound F G same three b _ B size width

/-- This proof is erased; runtime consumers receive the measured value itself. -/
theorem built_three (F : CNFFormula) : ThreeCore (MeasuredRawFrontend.build F).value := by
  rw [MeasuredRawFrontend.build_value]
  exact NativeFrontend.frontend_three F

/-- The only frontend construction call. Its value is shared with every later
stage and with captured recovery. Costs are source operations, not bit runtime. -/
def produce (F : CNFFormula) : Measured MeasuredProducer.Result :=
  let frontend := MeasuredRawFrontend.build F
  let cache := MeasuredSourceCache.build frontend.value (built_three F)
  let result := fromCache F frontend.value (built_three F) cache.value
  ⟨result.value,frontend.cost+cache.cost+result.cost+2⟩

theorem produce_correct (F : CNFFormula) :
    MeasuredProducer.Correct F (produce F).value :=
  fromCache_correct F (MeasuredRawFrontend.build F).value (MeasuredRawFrontend.build_value F)
    (built_three F) (MeasuredSourceCache.build (MeasuredRawFrontend.build F).value (built_three F)).value

def constructionPolynomial : NatPolynomial :=
  .add (.add MeasuredRawFrontend.workPolynomial
    MeasuredProducerPolynomial.constructionPolynomial) (.constant 1)

theorem constructionPolynomial_eval (m : Nat) :
    constructionPolynomial.eval m =
      MeasuredRawFrontend.workPolynomial.eval m+MeasuredProducer.produceBound (21*m+9)+1 := rfl

theorem decoded_construction_polynomial (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    (produce F).cost ≤ constructionPolynomial.eval bits.length := by
  let frontend := MeasuredRawFrontend.build F
  let cache := MeasuredSourceCache.build frontend.value (built_three F)
  let B := 21*bits.length+9
  have same : frontend.value = NativeTseitin.frontend F := MeasuredRawFrontend.build_value F
  have shape : ∀ i, (CNFCore.clause frontend.value i).length ≤ 3 := by
    rw [same]
    intro i
    exact Nat.le_of_eq
      (NativeTseitin.frontend_shape F _ (CNFCore.source_member (NativeTseitin.frontend F) i)).1
  have sizes := MeasuredFrontendCost.frontend_encoded_counts bits F decoded
  have sourceWidth := CNFCore.decoded_width_bound bits F decoded
  have size : frontend.value.clauses.length+frontend.value.variableCount ≤ B := by
    rw [same]
    dsimp [B]
    omega
  have width : F.variableCount ≤ B := by dsimp [B]; omega
  have hf := MeasuredRawFrontend.decoded_build_polynomial bits F decoded
  have hc : cache.cost ≤ MeasuredSourceCache.buildBound B :=
    MeasuredSourceCache.build_cost frontend.value (built_three F) shape B size
  have hr := fromCache_cost F frontend.value same (built_three F) cache.value B size width
  change frontend.cost+cache.cost+(fromCache F frontend.value (built_three F) cache.value).cost+2 ≤ _
  rw [constructionPolynomial_eval]
  change frontend.cost ≤ MeasuredRawFrontend.workPolynomial.eval bits.length at hf
  change _ ≤ MeasuredRawFrontend.workPolynomial.eval bits.length+MeasuredProducer.produceBound B+1
  unfold MeasuredProducer.produceBound MeasuredRun.sourceBound MeasuredProducer.finishBound at *
  omega

theorem decoded_recovery_bound (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    MeasuredProducer.RecoveryBound (21*bits.length+9) (produce F).value := by
  have same := MeasuredRawFrontend.build_value F
  have sizes := MeasuredFrontendCost.frontend_encoded_counts bits F decoded
  have width := CNFCore.decoded_width_bound bits F decoded
  apply fromCache_recovery_bound F _ same
  · rw [same]; omega
  · omega

theorem decoded_callback_polynomial (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    MeasuredProducerPolynomial.CallbackBound bits.length (produce F).value := by
  have h := decoded_recovery_bound bits F decoded
  cases he : (produce F).value with
  | model a => trivial
  | system c D recover =>
      rw [he] at h
      simpa only [MeasuredProducerPolynomial.CallbackBound,MeasuredProducer.RecoveryBound,
        MeasuredRecoveryPolynomial.witnessPolynomial_eval] using h

theorem decoded_verified (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    MeasuredProducer.Correct F (produce F).value ∧
      (produce F).cost ≤ constructionPolynomial.eval bits.length ∧
      MeasuredProducerPolynomial.CallbackBound bits.length (produce F).value :=
  ⟨produce_correct F,decoded_construction_polynomial bits F decoded,
    decoded_callback_polynomial bits F decoded⟩


end PNP.Concrete.NativeNormalization.MeasuredSharedProducer

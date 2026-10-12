import PNP.Concrete.NativeNormalization.MeasuredCompilationExecution

namespace PNP.Concrete.NativeNormalization.MeasuredRawCompiler

open PNP.Concrete CNFToNAND MeasuredReach

def finish (inputs : Nat) (gates : List LockedNAND.RawGate) :
    LockedNAND.RawSource → Measured LockedNAND.RawCircuit
  | .gate index => ⟨⟨inputs,gates,.gate index⟩,5⟩
  | .input index =>
      let size := MeasuredAccess.length gates
      let joined := MeasuredCollections.append gates
        [⟨.input index,.constant true⟩,⟨.gate size.value,.gate size.value⟩]
      ⟨⟨inputs,joined.value,.gate (size.value+1)⟩,size.cost+joined.cost+10⟩
  | .constant value =>
      let size := MeasuredAccess.length gates
      let joined := MeasuredCollections.append gates
        [⟨.constant (!value),.constant (!value)⟩]
      ⟨⟨inputs,joined.value,.gate size.value⟩,size.cost+joined.cost+10⟩

theorem finish_value (inputs : Nat) (gates : List LockedNAND.RawGate)
    (output : LockedNAND.RawSource) :
    some (finish inputs gates output).value = finalizeCompilation inputs ⟨gates,[output]⟩ := by
  cases output with
  | gate index => rfl
  | input index =>
      simp only [finish,MeasuredAccess.length_value,MeasuredCollections.append_value]
      rfl
  | constant value =>
      cases value <;>
        simp only [finish,MeasuredAccess.length_value,MeasuredCollections.append_value] <;> rfl

theorem finish_cost (inputs : Nat) (gates : List LockedNAND.RawGate)
    (output : LockedNAND.RawSource) :
    (finish inputs gates output).cost ≤ 2*gates.length+12 := by
  cases output with
  | gate index => simp only [finish]; omega
  | input index =>
      simp only [finish,MeasuredAccess.length_cost,MeasuredCollections.append_cost]
      omega
  | constant value =>
      simp only [finish,MeasuredAccess.length_cost,MeasuredCollections.append_cost]
      omega

def finalize (inputs : Nat) (s : CompilationState) : Measured (Option LockedNAND.RawCircuit) :=
  match s.stack with
  | [output] =>
      let result := finish inputs s.gates output
      ⟨some result.value,result.cost+2⟩
  | _ => ⟨none,3⟩

theorem finalize_value (inputs : Nat) (s : CompilationState) :
    (finalize inputs s).value = finalizeCompilation inputs s := by
  rcases s with ⟨gates,stack⟩
  cases stack with
  | nil => rfl
  | cons output rest =>
      cases rest with
      | nil => exact finish_value inputs gates output
      | cons next rest => rfl

theorem finalize_cost (inputs : Nat) (s : CompilationState) :
    (finalize inputs s).cost ≤ 2*s.gates.length+14 := by
  rcases s with ⟨gates,stack⟩
  cases stack with
  | nil => simp only [finalize]; omega
  | cons output rest =>
      cases rest with
      | nil =>
          have h := finish_cost inputs gates output
          simp only [finalize]
          omega
      | cons next rest => simp only [finalize]; omega

def execute (F : CNFFormula) : Measured (Option LockedNAND.RawCircuit) :=
  let plan := MeasuredCompilationPlan.formula F
  let executed := MeasuredCompilationExecution.run plan.value ⟨[],[]⟩
  match executed.value with
  | none => ⟨none,plan.cost+executed.cost+1⟩
  | some state =>
      let result := finalize F.variableCount state
      ⟨result.value,plan.cost+executed.cost+result.cost+1⟩

theorem execute_value (F : CNFFormula) : (execute F).value = executeFormulaPlan F := by
  simp only [execute,executeFormulaPlan,MeasuredCompilationExecution.run_value,
    MeasuredCompilationPlan.formula_value]
  cases runCompilationPlan (formulaPlan F) ⟨[],[]⟩ <;> simp only [finalize_value]

theorem execute_exact (F : CNFFormula) : (execute F).value = some (compileFormula F) :=
  (execute_value F).trans (executeFormulaPlan_exact F)

def executeBound (B : Nat) : Nat :=
  MeasuredCompilationPlan.workBound B+(2*B+14)*B+2*B+17

theorem execute_cost (F : CNFFormula) (B : Nat)
    (size : MeasuredCompilationPlan.workSize F.clauses ≤ B)
    (planSize : (formulaPlan F).length ≤ B) : (execute F).cost ≤ executeBound B := by
  let plan := MeasuredCompilationPlan.formula F
  let executed := MeasuredCompilationExecution.run plan.value ⟨[],[]⟩
  have hp : plan.cost ≤ MeasuredCompilationPlan.workBound B+1 :=
    Nat.le_trans (MeasuredCompilationPlan.formula_cost F)
      (Nat.add_le_add_right (MeasuredCompilationPlan.workBound_mono _ _ size) 1)
  have hn : plan.value.length ≤ B := by
    simpa only [plan,MeasuredCompilationPlan.formula_value] using planSize
  have hr := MeasuredCompilationExecution.run_cost_budget plan.value ⟨[],[]⟩ B (by simpa using hn)
  have hm := Nat.mul_le_mul_left (2*B+14) hn
  have runBound : executed.cost ≤ (2*B+14)*B+1 := by
    dsimp only [executed]
    omega
  cases hs : executed.value with
  | none =>
      change (match executed.value with
        | none => (⟨none,plan.cost+executed.cost+1⟩ : Measured (Option LockedNAND.RawCircuit))
        | some state => let result := finalize F.variableCount state
          ⟨result.value,plan.cost+executed.cost+result.cost+1⟩).cost ≤ executeBound B
      rw [hs]
      dsimp only
      unfold executeBound
      omega
  | some state =>
      have hg := MeasuredCompilationExecution.run_growth plan.value ⟨[],[]⟩ state hs
      have hf := finalize_cost F.variableCount state
      change (match executed.value with
        | none => (⟨none,plan.cost+executed.cost+1⟩ : Measured (Option LockedNAND.RawCircuit))
        | some state => let result := finalize F.variableCount state
          ⟨result.value,plan.cost+executed.cost+result.cost+1⟩).cost ≤ executeBound B
      rw [hs]
      dsimp only
      unfold executeBound
      simp only [List.length_nil,Nat.zero_add] at hg
      omega

/-- The default branch is unreachable on every formula by execute_exact, proved
internally. It supplies no semantic premise to callers. -/
def build (F : CNFFormula) : Measured LockedNAND.RawCircuit :=
  let result := execute F
  ⟨result.value.getD ⟨F.variableCount,[],.constant false⟩,result.cost+1⟩

theorem build_value (F : CNFFormula) : (build F).value = compileFormula F := by
  simp only [build,execute_exact,Option.getD_some]

theorem decoded_build_cost (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    (build F).cost ≤ executeBound (5*bits.length+1)+1 :=
  Nat.add_le_add_right (execute_cost F _
    (MeasuredCompilationPlan.decoded_size bits F decoded)
    (formulaPlan_length_le_encoded_bits bits F decoded)) 1

def workPolynomial : NatPolynomial :=
  let size : NatPolynomial := .add (.mul (.constant 5) .variable) (.constant 1)
  .add (.add (.add MeasuredCompilationPlan.workPolynomial
    (.mul (.add (.mul (.constant 2) size) (.constant 14)) size))
    (.mul (.constant 2) size)) (.constant 17)

theorem workPolynomial_eval (m : Nat) :
    workPolynomial.eval m = executeBound (5*m+1)+1 := by
  change MeasuredCompilationPlan.workPolynomial.eval m+
    (2*(5*m+1)+14)*(5*m+1)+2*(5*m+1)+17 = _
  rw [MeasuredCompilationPlan.workPolynomial_eval]
  unfold executeBound
  omega

theorem decoded_build_polynomial (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    (build F).cost ≤ workPolynomial.eval bits.length := by
  rw [workPolynomial_eval]
  exact decoded_build_cost bits F decoded


end PNP.Concrete.NativeNormalization.MeasuredRawCompiler

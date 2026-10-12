import PNP.Concrete.NativeNormalization.MeasuredCompilationPlan

namespace PNP.Concrete.NativeNormalization.MeasuredCompilationExecution

open PNP.Concrete CNFToNAND MeasuredReach

def emit (state : CompilationState) (left right : LockedNAND.RawSource)
    (rest : List LockedNAND.RawSource) : Measured CompilationState :=
  let size := MeasuredAccess.length state.gates
  let joined := MeasuredCollections.append state.gates [⟨left,right⟩]
  ⟨⟨joined.value,.gate size.value::rest⟩,size.cost+joined.cost+8⟩

theorem emit_value (s : CompilationState) (l r : LockedNAND.RawSource)
    (rest : List LockedNAND.RawSource) :
    (emit s l r rest).value = ⟨s.gates++[⟨l,r⟩],.gate s.gates.length::rest⟩ := by
  simp only [emit,MeasuredCollections.append_value,MeasuredAccess.length_value]

theorem emit_cost (s : CompilationState) (l r : LockedNAND.RawSource)
    (rest : List LockedNAND.RawSource) : (emit s l r rest).cost = 2*s.gates.length+10 := by
  simp only [emit,MeasuredCollections.append_cost,MeasuredAccess.length_cost]
  omega

theorem emit_gates_length (s : CompilationState) (l r : LockedNAND.RawSource)
    (rest : List LockedNAND.RawSource) :
    (emit s l r rest).value.gates.length = s.gates.length+1 := by
  rw [emit_value]
  simp only [List.length_append,List.length_cons,List.length_nil]

def step (action : CompilationAction) (s : CompilationState) :
    Measured (Option CompilationState) :=
  match action with
  | .push source => ⟨some ⟨s.gates,source::s.stack⟩,4⟩
  | .negate =>
      match s.stack with
      | [] => ⟨none,3⟩
      | source::rest =>
          let result := emit s source source rest
          ⟨some result.value,result.cost+2⟩
  | .nand =>
      match s.stack with
      | right::left::rest =>
          let result := emit s left right rest
          ⟨some result.value,result.cost+3⟩
      | _ => ⟨none,3⟩

theorem step_value (action : CompilationAction) (s : CompilationState) :
    (step action s).value = action.step s := by
  rcases s with ⟨gates,stack⟩
  cases action with
  | push source => rfl
  | negate =>
      cases stack with
      | nil => rfl
      | cons source rest => simp only [step,emit_value]; rfl
  | nand =>
      cases stack with
      | nil => rfl
      | cons right rest =>
          cases rest with
          | nil => rfl
          | cons left rest => simp only [step,emit_value]; rfl

theorem step_cost (action : CompilationAction) (s : CompilationState) :
    (step action s).cost ≤ 2*s.gates.length+13 := by
  rcases s with ⟨gates,stack⟩
  cases action with
  | push source => simp only [step]; omega
  | negate =>
      cases stack with
      | nil => simp only [step]; omega
      | cons source rest => simp only [step,emit_cost]; omega
  | nand =>
      cases stack with
      | nil => simp only [step]; omega
      | cons right rest =>
          cases rest with
          | nil => simp only [step]; omega
          | cons left rest => simp only [step,emit_cost]; omega

theorem step_growth (action : CompilationAction) (s next : CompilationState)
    (h : (step action s).value = some next) : next.gates.length ≤ s.gates.length+1 := by
  rcases s with ⟨gates,stack⟩
  cases action with
  | push source =>
      cases h
      exact Nat.le_succ _
  | negate =>
      cases stack with
      | nil => cases h
      | cons source rest =>
          have he : (emit ⟨gates,source::rest⟩ source source rest).value = next :=
            Option.some.inj h
          rw [← he,emit_gates_length]
          exact Nat.le_refl _
  | nand =>
      cases stack with
      | nil => cases h
      | cons right rest =>
          cases rest with
          | nil => cases h
          | cons left rest =>
              have he : (emit ⟨gates,right::left::rest⟩ left right rest).value = next :=
                Option.some.inj h
              rw [← he,emit_gates_length]
              exact Nat.le_refl _

def run : List CompilationAction → CompilationState → Measured (Option CompilationState)
  | [],s => ⟨some s,1⟩
  | action::rest,s =>
      let checked := step action s
      match checked.value with
      | none => ⟨none,checked.cost+1⟩
      | some next =>
          let tail := run rest next
          ⟨tail.value,checked.cost+tail.cost+1⟩

theorem run_value (actions : List CompilationAction) (s : CompilationState) :
    (run actions s).value = runCompilationPlan actions s := by
  induction actions generalizing s with
  | nil => rfl
  | cons action rest ih =>
      simp only [run,runCompilationPlan,← step_value action s]
      cases (step action s).value with
      | none => rfl
      | some next => exact ih next

theorem run_growth (actions : List CompilationAction) (s final : CompilationState)
    (h : (run actions s).value = some final) :
    final.gates.length ≤ s.gates.length+actions.length := by
  induction actions generalizing s final with
  | nil => cases h; exact Nat.le_refl _
  | cons action rest ih =>
      cases hs : (step action s).value with
      | none => simp only [run,hs] at h; cases h
      | some next =>
          have tail : (run rest next).value = some final := by
            simpa only [run,hs] using h
          have hg := step_growth action s next hs
          have ht := ih next final tail
          simp only [List.length_cons]
          omega

theorem run_cost_budget (actions : List CompilationAction) (s : CompilationState)
    (B : Nat) (budget : s.gates.length+actions.length ≤ B) :
    (run actions s).cost ≤ (2*B+14)*actions.length+1 := by
  induction actions generalizing s with
  | nil => exact Nat.le_refl _
  | cons action rest ih =>
      have hc := step_cost action s
      have hg : s.gates.length ≤ B := by
        simp only [List.length_cons] at budget
        omega
      cases hs : (step action s).value with
      | none =>
          simp only [run,hs,List.length_cons,Nat.mul_succ]
          omega
      | some next =>
          have growth := step_growth action s next hs
          have nextBudget : next.gates.length+rest.length ≤ B := by
            simp only [List.length_cons] at budget
            omega
          have ht := ih next nextBudget
          simp only [run,hs,List.length_cons,Nat.mul_succ]
          omega

theorem run_cost (actions : List CompilationAction) (s : CompilationState) :
    (run actions s).cost ≤
      (2*(s.gates.length+actions.length)+14)*actions.length+1 :=
  run_cost_budget actions s _ (Nat.le_refl _)


end PNP.Concrete.NativeNormalization.MeasuredCompilationExecution

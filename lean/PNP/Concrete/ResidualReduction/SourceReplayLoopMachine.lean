import PNP.Concrete.ResidualReduction.SourceReplayLoopFields

/-! Literal all-input history replay loop. A protected unary countdown is
outside the complete thirty-register step workspace. Rejection clears the
countdown, so no later record can overwrite a failed validity flag. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayLoopMachine
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.SourceReplayLoopFields

def full (r : Store 30) (count : Nat) : Store 31 :=
  Frame.join r (.cons (List.replicate count true) .nil)
private theorem count_read (r : Store 30) (count : Nat) :
    (full r count).get 30 = List.replicate count true :=
  Frame.get_frame r (.cons (List.replicate count true) .nil) 0
def work (count : Nat) (input point : BitString) (recover good : Bool) : Store 31 :=
  full (SourceReplayStepState.work input point recover good) count
def finalState (recover : Bool) (r : Result) : Store 31 :=
  work 0 r.input r.point recover r.valid
def lift (b : Block 30) : Block 31 := Frame.block 1 b
theorem lift_exec {b : Block 30} {before after : Store 30} {used : Nat}
    (h : Exec b before used after) (count : Nat) :
    Exec (lift b) (full before count) used (full after count) :=
  Frame.execution h (.cons (List.replicate count true) .nil)

private theorem pop_exec (count : Nat) (input point : BitString) (recover : Bool) :
    Exec (.action (.pop (30 : Fin 31))) (work (count + 1) input point recover true) 1
      (work count input point recover true) := by
  simp only [work,full,List.replicate_succ]
  exact .action _ _
private theorem clear_valid_exec (count : Nat) (input point : BitString) (recover : Bool) :
    Exec (.action (.clear (28 : Fin 31))) (work count input point recover true) 1
      (work count input point recover false) := .action _ _

def check : Block 31 := .branch 28 (.action (.clear 30)) (.action (.clear 30)) .skip
def body : Block 31 := .seq (.action (.pop 30)) <|
  .seq (.action (.clear 28)) <| .seq (lift SourceReplayStepMachine.block) check

theorem body_success (count : Nat) (input point cursor output : BitString) (recover : Bool)
    (accepted : SourceReplayStepMachine.answer recover input point = some (cursor,output)) :
    Exec body (work (count + 1) input point recover true)
      (SourceReplayStepMachine.fuel recover input point + 4) (work count cursor output recover true) := by
  have parsed : Exec (lift SourceReplayStepMachine.block) (work count input point recover false)
      (SourceReplayStepMachine.fuel recover input point) (work count cursor output recover true) := by
    have h := lift_exec (SourceReplayStepMachine.block_exec recover input point) count
    rw [SourceReplayStepMachine.result_contract,accepted] at h
    exact h
  have read : (work count cursor output recover true).get 28 = [true] := rfl
  have checked : Exec check (work count cursor output recover true) 2 (work count cursor output recover true) :=
    Exec.one read (.skip _)
  have cost : SourceReplayStepMachine.fuel recover input point + 4 =
      1 + (1 + (SourceReplayStepMachine.fuel recover input point + 2)) := by omega
  simpa only [body,cost] using Exec.seq (pop_exec count input point recover)
    (Exec.seq (clear_valid_exec count input point recover) (Exec.seq parsed checked))

theorem body_failure (count : Nat) (input point : BitString) (recover : Bool)
    (rejected : SourceReplayStepMachine.answer recover input point = none) :
    Exec body (work (count + 1) input point recover true)
      (SourceReplayStepMachine.fuel recover input point + 4)
      (work 0 (SourceReplayRecordFields.rest input) point recover false) := by
  have parsed : Exec (lift SourceReplayStepMachine.block) (work count input point recover false)
      (SourceReplayStepMachine.fuel recover input point)
      (work count (SourceReplayRecordFields.rest input) point recover false) := by
    have h := lift_exec (SourceReplayStepMachine.block_exec recover input point) count
    rw [SourceReplayStepMachine.result_contract,rejected] at h
    exact h
  have read : (work count (SourceReplayRecordFields.rest input) point recover false).get 28 = [] := rfl
  have cleared : Exec (.action (.clear (30 : Fin 31)))
      (work count (SourceReplayRecordFields.rest input) point recover false) 1
      (work 0 (SourceReplayRecordFields.rest input) point recover false) := .action _ _
  have checked : Exec check (work count (SourceReplayRecordFields.rest input) point recover false) 2
      (work 0 (SourceReplayRecordFields.rest input) point recover false) := Exec.empty read cleared
  have cost : SourceReplayStepMachine.fuel recover input point + 4 =
      1 + (1 + (SourceReplayStepMachine.fuel recover input point + 2)) := by omega
  simpa only [body,cost] using Exec.seq (pop_exec count input point recover)
    (Exec.seq (clear_valid_exec count input point recover) (Exec.seq parsed checked))

def block : Block 31 := .loop 30 body
def fuel (recover : Bool) : Nat → BitString → BitString → Nat
  | 0,_,_ => 1
  | count + 1,input,point =>
    1 + ((SourceReplayStepMachine.fuel recover input point + 4) +
      match SourceReplayStepMachine.answer recover input point with
      | none => 1
      | some (cursor,output) => fuel recover count cursor output)

theorem block_exec (recover : Bool) (count : Nat) (input point : BitString) :
    Exec block (work count input point recover true) (fuel recover count input point)
      (finalState recover (scan recover count input point)) := by
  induction count generalizing input point with
  | zero => exact Exec.loopStop (count_read _ 0)
  | succ count ih =>
    have read : (work (count + 1) input point recover true).get 30 = true :: List.replicate count true := by
      simp only [work,count_read,List.replicate_succ]
    cases first : SourceReplayStepMachine.answer recover input point with
    | none =>
      have stopped : Exec block (work 0 (SourceReplayRecordFields.rest input) point recover false) 1
          (work 0 (SourceReplayRecordFields.rest input) point recover false) := Exec.loopStop (count_read _ 0)
      have checked := Exec.loopStep (source := (30 : Fin 31)) read
        (body_failure count input point recover first) stopped
      simpa only [block,fuel,scan,first,finalState] using checked
    | some pair =>
      rcases pair with ⟨cursor,output⟩
      have checked := Exec.loopStep (source := (30 : Fin 31)) read
        (body_success count input point cursor output recover first) (ih cursor output)
      simpa only [block,fuel,scan,first] using checked

def allowance (length witness : Nat) : Nat :=
  50 * length * length + 228 * length + 4 * witness + 411

theorem allowance_mono {a b x y : Nat} (length : a ≤ b) (witness : x ≤ y) :
    allowance a x ≤ allowance b y := by
  have square := Nat.mul_le_mul length length
  simp only [allowance,Nat.mul_assoc]
  omega

theorem fuel_bound (recover : Bool) (count : Nat) (input point : BitString) :
    fuel recover count input point ≤ count * allowance input.length (point.length + count) + 1 := by
  induction count generalizing input point with
  | zero => simp only [fuel,Nat.zero_mul,Nat.zero_add,Nat.le_refl]
  | succ count ih =>
    have single := SourceReplayStepMachine.fuel_bound recover input point
    have budget : SourceReplayStepMachine.fuel recover input point + 5 ≤
        allowance input.length (point.length + (count + 1)) := by
      unfold allowance
      omega
    cases first : SourceReplayStepMachine.answer recover input point with
    | none =>
      simp only [fuel,first,Nat.add_mul,Nat.one_mul]
      omega
    | some pair =>
      rcases pair with ⟨cursor,output⟩
      obtain ⟨rest,size⟩ := SourceReplayStepMachine.answer_bounds recover input point cursor output first
      have growth : output.length + count ≤ point.length + (count + 1) := by
        cases recover <;> simp only [Bool.false_eq_true,↓reduceIte] at size <;> omega
      have later := ih cursor output
      have product := Nat.mul_le_mul_left count (allowance_mono rest growth)
      simp only [fuel,first,Nat.add_mul,Nat.one_mul]
      omega

end PNP.Concrete.ResidualReduction.SourceReplayLoopMachine

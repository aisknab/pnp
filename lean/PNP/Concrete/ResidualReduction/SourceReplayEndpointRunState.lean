import PNP.Concrete.ResidualReduction.SourceReplayEndpointLoad

/-! Fixed forty-register replay-execution state. The existing thirty-one
register loop is extended by four temporary words and the five protected
endpoint fields. Register 32 is a cursor backup during witness checks. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEndpointRunState
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence (Registers)

structure Parameters where
  recover : Bool
  original : Nat
  terminal : Nat
  witness : BitString

def saved (p : Parameters) (good : Bool) : SourceReplayEndpointState.Saved :=
  ⟨[p.recover],List.replicate p.original true,p.witness,SourceReplayRecordState.flag good,
    List.replicate p.terminal true⟩
def middle (backup : BitString) : Store 4 := .cons [] (.cons backup (.cons [] (.cons [] .nil)))
def enclose (r : Store 31) (backup : BitString) (p : Parameters) (good : Bool) : Store 40 :=
  SourceReplayEndpointState.full (Frame.join r (middle backup)) (saved p good)
def framed (r : Registers) (count : Nat) (point : BitString) (p : Parameters) (loopGood : Bool) : Store 31 :=
  SourceReplayLoopMachine.full (SourceReplayStepState.full r SourceReplayStepState.emptyReplay
    SourceReplayRecordState.emptySaved ⟨point,p.recover,loopGood,[]⟩) count
def full (r : Registers) (count : Nat) (point backup : BitString) (p : Parameters) (loopGood good : Bool) : Store 40 :=
  enclose (framed r count point p loopGood) backup p good
def work (count : Nat) (input point : BitString) (p : Parameters) (loopGood good : Bool) : Store 40 :=
  full (SourceReplayState.blank input []) count point [] p loopGood good

def lift31 (b : Block 31) : Block 40 := SourceReplayEndpointState.lift35 (Frame.block 4 b)
theorem lift31_exec {b : Block 31} {before after : Store 31} {used : Nat}
    (h : Exec b before used after) (backup : BitString) (p : Parameters) (good : Bool) :
    Exec (lift31 b) (enclose before backup p good) used (enclose after backup p good) :=
  SourceReplayEndpointState.lift35_exec (Frame.execution h (middle backup)) (saved p good)
def core9 (b : Block 9) : Block 40 :=
  lift31 (SourceReplayLoopMachine.lift (SourceReplayStepState.core9 b))
theorem core9_exec {b : Block 9} {before after : Registers} {used : Nat}
    (h : Exec b before.store used after.store) (count : Nat) (point backup : BitString)
    (p : Parameters) (loopGood good : Bool) :
    Exec (core9 b) (full before count point backup p loopGood good) used
      (full after count point backup p loopGood good) :=
  lift31_exec (SourceReplayLoopMachine.lift_exec
    (SourceReplayStepState.core9_exec h SourceReplayStepState.emptyReplay
      SourceReplayRecordState.emptySaved ⟨point,p.recover,loopGood,[]⟩) count) backup p good

theorem read_input (r : Registers) (count : Nat) (point backup : BitString)
    (p : Parameters) (loopGood good : Bool) :
    (full r count point backup p loopGood good).get 0 = r.input := rfl
theorem read_point (r : Registers) (count : Nat) (point backup : BitString)
    (p : Parameters) (loopGood good : Bool) :
    (full r count point backup p loopGood good).get 26 = point := rfl
theorem read_loop_valid (r : Registers) (count : Nat) (point backup : BitString)
    (p : Parameters) (loopGood good : Bool) :
    (full r count point backup p loopGood good).get 28 = SourceReplayRecordState.flag loopGood := rfl
theorem read_mode (r : Registers) (count : Nat) (point backup : BitString)
    (p : Parameters) (loopGood good : Bool) :
    (full r count point backup p loopGood good).get 35 = [p.recover] :=
  SourceReplayEndpointState.read_mode _ (saved p good)
theorem read_valid (r : Registers) (count : Nat) (point backup : BitString)
    (p : Parameters) (loopGood good : Bool) :
    (full r count point backup p loopGood good).get 38 = SourceReplayRecordState.flag good :=
  SourceReplayEndpointState.read_valid _ (saved p good)

def guard (index : Fin 40) : Block 40 := SourceReplayEndpointState.guard index
theorem guard_exec (r : Registers) (count : Nat) (point backup : BitString)
    (p : Parameters) (loopGood good accepted : Bool) (index : Fin 40)
    (read : (full r count point backup p loopGood good).get index = SourceReplayRecordState.flag accepted) :
    Exec (guard index) (full r count point backup p loopGood good) 2
      (full r count point backup p loopGood (good && accepted)) := by
  have checked := SourceReplayEndpointState.guard_exec
    (Frame.join (framed r count point p loopGood) (middle backup)) (saved p good) index accepted read
  have fields : SourceReplayEndpointState.restrict (saved p good) accepted = saved p (good && accepted) := by
    cases good <;> cases accepted <;> rfl
  rw [fields] at checked
  exact checked

def clear9 : Block 40 := core9 (SourceChartedSuccessorWords.clearAll 9)
theorem clear9_exec (r : Registers) (count : Nat) (point backup : BitString)
    (p : Parameters) (loopGood good : Bool) :
    Exec clear9 (full r count point backup p loopGood good) 10
      (full (SourceReplayState.blank [] []) count point backup p loopGood good) :=
  core9_exec (SourceChartedSuccessorWords.clearAll_exec r.store) count point backup p loopGood good

theorem backup_exec (input point : BitString) (count : Nat) (p : Parameters) (loopGood good : Bool) :
    Exec (.action (.copy (32 : Fin 40) 0)) (work count input point p loopGood good) 1
      (full (SourceReplayState.blank input []) count point input p loopGood good) := .action _ _
theorem point_exec (input point : BitString) (count : Nat) (p : Parameters) (loopGood good : Bool) :
    Exec (.action (.copy (0 : Fin 40) 26))
      (full (SourceReplayState.blank input []) count point input p loopGood good) 1
      (full (SourceReplayState.blank point []) count point input p loopGood good) := .action _ _
theorem restore_exec (input point : BitString) (count : Nat) (p : Parameters) (loopGood good : Bool) :
    Exec (.seq (.action (.copy (0 : Fin 40) 32)) (.action (.clear 32)))
      (full (SourceReplayState.blank [] []) count point input p loopGood good) 2
      (work count input point p loopGood good) := by
  have restored : Exec (.action (.copy (0 : Fin 40) 32))
      (full (SourceReplayState.blank [] []) count point input p loopGood good) 1
      (full (SourceReplayState.blank input []) count point input p loopGood good) := .action _ _
  exact Exec.seq restored (.action _ _)

theorem clear_count_exec (input point : BitString) (count : Nat) (p : Parameters) (loopGood good : Bool) :
    Exec (.action (.clear (30 : Fin 40))) (work count input point p loopGood good) 1
      (work 0 input point p loopGood good) := .action _ _
theorem begin_loop_exec (input point : BitString) (count : Nat) (p : Parameters) (good : Bool) :
    Exec (.action (.push (28 : Fin 40) true)) (work count input point p false good) 1
      (work count input point p true good) := by
  have checked := Exec.action (.push (28 : Fin 40) true) (work count input point p false good)
  simp only [Action.update,Action.instruction,Instruction.update,work,
    read_loop_valid,SourceReplayRecordState.flag] at checked
  exact checked

end PNP.Concrete.ResidualReduction.SourceReplayEndpointRunState

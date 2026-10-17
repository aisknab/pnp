import PNP.Concrete.ResidualReduction.SourceReplayEndpointFields

/-! Protected state for closed replay input loading. The lower thirty-five
registers are the existing strict saved-data reader. The outer fields remain
outside that workspace: direction, original dimension, witness, cumulative
validity and terminal dimension. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEndpointState
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks

structure Saved where
  mode : BitString
  dimension : BitString
  witness : BitString
  valid : BitString
  terminal : BitString
def Saved.store (s : Saved) : Store 5 :=
  .cons s.mode (.cons s.dimension (.cons s.witness (.cons s.valid (.cons s.terminal .nil))))
def emptySaved : Saved := ⟨[],[],[],[],[]⟩
def full (r : Store 35) (s : Saved) : Store 40 := Frame.join r s.store
def work (input : BitString) (s : Saved) : Store 40 := full (SourceReplayDataMachine.initial input) s
def initial (input : BitString) : Store 40 := work input emptySaved
def extend14 (r : Store 14) : Store 35 := Frame.join r (Store.empty 21)
def parser (r : Store 14) (s : Saved) : Store 40 := full (extend14 r) s
def lift35 (b : Block 35) : Block 40 := Frame.block 5 b
def lift14 (b : Block 14) : Block 40 := lift35 (Frame.block 21 b)

theorem lift35_exec {b : Block 35} {before after : Store 35} {used : Nat}
    (h : Exec b before used after) (s : Saved) :
    Exec (lift35 b) (full before s) used (full after s) := Frame.execution h s.store
theorem lift14_exec {b : Block 14} {before after : Store 14} {used : Nat}
    (h : Exec b before used after) (s : Saved) :
    Exec (lift14 b) (parser before s) used (parser after s) :=
  lift35_exec (Frame.execution h (Store.empty 21)) s

private theorem set_frame {extra count : Nat} (r : Store count) (s : Store extra)
    (destination : Fin extra) (value : BitString) :
    (Frame.join r s).set (Frame.frameIndex count destination) value =
      Frame.join r (s.set destination value) := by
  induction r with
  | nil =>
    have position : Frame.frameIndex 0 destination = destination := by
      apply Fin.ext
      simp only [Frame.frameIndex,Nat.zero_add]
    rw [position]
    rfl
  | @cons count first rest ih =>
    have position : Frame.frameIndex (count + 1) destination = (Frame.frameIndex count destination).succ := by
      apply Fin.ext
      change count + 1 + destination.val = count + destination.val + 1
      omega
    rw [position]
    exact congrArg (Store.cons first) ih

theorem copy_saved_exec (r : Store 35) (s : Saved) (destination : Fin 5) (source : Fin 35)
    (value : BitString) (after : Saved) (read : r.get source = value)
    (write : s.store.set destination value = after.store) :
    Exec (.action (.copy (Frame.frameIndex 35 destination) (Frame.index 5 source)))
      (full r s) 1 (full r after) := by
  have checked := Exec.action (.copy (Frame.frameIndex 35 destination) (Frame.index 5 source)) (full r s)
  simpa only [Action.update,Action.instruction,Instruction.update,full,Frame.get_core,set_frame,read,write] using checked

theorem copy_core_exec (r : Store 35) (s : Saved) (destination : Fin 35) (source : Fin 5)
    (value : BitString) (after : Store 35) (read : s.store.get source = value)
    (write : r.set destination value = after) :
    Exec (.action (.copy (Frame.index 5 destination) (Frame.frameIndex 35 source)))
      (full r s) 1 (full after s) := by
  have checked := Exec.action (.copy (Frame.index 5 destination) (Frame.frameIndex 35 source)) (full r s)
  simpa only [Action.update,Action.instruction,Instruction.update,full,Frame.get_frame,Frame.set_core,read,write] using checked

theorem clear_saved_exec (r : Store 35) (s : Saved) (destination : Fin 5) (after : Saved)
    (write : s.store.set destination [] = after.store) :
    Exec (.action (.clear (Frame.frameIndex 35 destination))) (full r s) 1 (full r after) := by
  have checked := Exec.action (.clear (Frame.frameIndex 35 destination)) (full r s)
  simpa only [Action.update,Action.instruction,Instruction.update,full,set_frame,write] using checked

theorem read_mode (r : Store 35) (s : Saved) : (full r s).get 35 = s.mode :=
  Frame.get_frame r s.store 0
theorem read_dimension (r : Store 35) (s : Saved) : (full r s).get 36 = s.dimension :=
  Frame.get_frame r s.store 1
theorem read_witness (r : Store 35) (s : Saved) : (full r s).get 37 = s.witness :=
  Frame.get_frame r s.store 2
theorem read_valid (r : Store 35) (s : Saved) : (full r s).get 38 = s.valid :=
  Frame.get_frame r s.store 3
theorem read_terminal (r : Store 35) (s : Saved) : (full r s).get 39 = s.terminal :=
  Frame.get_frame r s.store 4

def restrict (s : Saved) (good : Bool) : Saved := {s with valid := if good then s.valid else []}
def guard (index : Fin 40) : Block 40 := .branch index (.action (.clear 38)) (.action (.clear 38)) .skip
theorem guard_exec (r : Store 35) (s : Saved) (index : Fin 40) (good : Bool)
    (read : (full r s).get index = SourceReplayRecordState.flag good) :
    Exec (guard index) (full r s) 2 (full r (restrict s good)) := by
  cases good with
  | false => exact Exec.empty read (clear_saved_exec r s 3 {s with valid := []} rfl)
  | true => exact Exec.one read (.skip _)

def clearWork : Block 40 := lift35 (SourceChartedSuccessorWords.clearAll 35)
theorem clearWork_exec (r : Store 35) (s : Saved) : Exec clearWork (full r s) 36 (work [] s) :=
  lift35_exec (SourceChartedSuccessorWords.clearAll_exec r) s

def fromParser (s : SourceReplayParserState.Saved) : Saved :=
  ⟨s.mode,s.dimension,s.witness,s.valid,[]⟩

end PNP.Concrete.ResidualReduction.SourceReplayEndpointState

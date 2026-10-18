import PNP.Concrete.ResidualReduction.SourceHistoryEncoding

/-! One fixed workspace with protected current input and accumulated history.
Only the original bitstring is present initially. All later fields are filled
by concrete instructions from parsed or returned bytes. -/

namespace PNP.Concrete.ResidualReduction.SourceHistoryState
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceHistoryEncoding

structure Saved where
  current : BitString
  dimension : BitString
  rows : BitString
  history : BitString
  count : BitString
  step : BitString
  active : BitString

def Saved.store (s : Saved) : Store 7 :=
  .cons s.current <| .cons s.dimension <| .cons s.rows <| .cons s.history <|
    .cons s.count <| .cons s.step (.cons s.active .nil)
def emptySaved : Saved := ⟨[],[],[],[],[],[],[]⟩
def full (r : Store 56) (s : Saved) : Store 63 := Frame.join r s.store
def withCore (r : Registers) (s : Saved) : Store 63 :=
  full (Frame.join r.store (Store.empty 47)) s
def work (input out : BitString) (s : Saved) : Store 63 :=
  withCore {SourceScalarState.work input with output := out} s
def initial (input : BitString) : Store 63 := work input [] emptySaved
def core (b : Block 9) : Block 63 := Frame.block 7 (Frame.block 47 b)
def use56 (b : Block 56) : Block 63 := Frame.block 7 b

theorem core_exec {b : Block 9} {r out : Registers} {ticks : Nat}
    (h : Exec b r.store ticks out.store) (s : Saved) :
    Exec (core b) (withCore r s) ticks (withCore out s) :=
  Frame.execution (Frame.execution h (Store.empty 47)) s.store
theorem use56_exec {b : Block 56} {r out : Store 56} {ticks : Nat}
    (h : Exec b r ticks out) (s : Saved) :
    Exec (use56 b) (full r s) ticks (full out s) := Frame.execution h s.store
theorem query_initial (input : BitString) (s : Saved) :
    full (SourceOriginalSuccessorState.initial input) s = work input [] s := rfl

inductive Field where
  | current | dimension | rows | history | count | step | active
def Field.index : Field → Fin 7
  | .current => 0 | .dimension => 1 | .rows => 2 | .history => 3
  | .count => 4 | .step => 5 | .active => 6
def Field.slot (field : Field) : Fin 63 := Frame.frameIndex 56 field.index
def Field.word : Field → Saved → BitString
  | .current,s => s.current | .dimension,s => s.dimension | .rows,s => s.rows
  | .history,s => s.history | .count,s => s.count | .step,s => s.step | .active,s => s.active
def fieldSet : Field → Saved → BitString → Saved
  | .current,s,w => {s with current := w} | .dimension,s,w => {s with dimension := w}
  | .rows,s,w => {s with rows := w} | .history,s,w => {s with history := w}
  | .count,s,w => {s with count := w} | .step,s,w => {s with step := w}
  | .active,s,w => {s with active := w}

theorem field_get (field : Field) (r : Store 56) (s : Saved) :
    (full r s).get field.slot = field.word s := by
  rw [full,Field.slot,Frame.get_frame]
  cases field <;> rfl
theorem working_get (r : Store 56) (s : Saved) (i : Fin 56) :
    (full r s).get (Frame.index 7 i) = r.get i := Frame.get_core r s.store i

private theorem set_frame {extra count : Nat} (r : Store count) (s : Store extra)
    (i : Fin extra) (word : BitString) :
    (Frame.join r s).set (Frame.frameIndex count i) word = Frame.join r (s.set i word) := by
  induction r with
  | nil =>
    have position : Frame.frameIndex 0 i = i := by
      apply Fin.ext
      exact Nat.zero_add i.val
    rw [position]
    rfl
  | @cons count first rest ih =>
    have position : Frame.frameIndex (count + 1) i = (Frame.frameIndex count i).succ := by
      apply Fin.ext
      change count + 1 + i.val = count + i.val + 1
      omega
    rw [position]
    exact congrArg (Store.cons first) ih

theorem field_set (field : Field) (r : Store 56) (s : Saved) (word : BitString) :
    (full r s).set field.slot word = full r (fieldSet field s word) := by
  rw [full,Field.slot,set_frame]
  cases field <;> rfl
theorem field_push_exec (field : Field) (r : Store 56) (s : Saved) (bit : Bool) :
    Exec (.action (.push field.slot bit)) (full r s) 1
      (full r (fieldSet field s (bit :: field.word s))) := by
  simpa only [Action.update,Action.instruction,Instruction.update,field_get,field_set] using
    Exec.action (.push field.slot bit) (full r s)
theorem field_clear_exec (field : Field) (r : Store 56) (s : Saved) :
    Exec (.action (.clear field.slot)) (full r s) 1 (full r (fieldSet field s [])) := by
  simpa only [Action.update,Action.instruction,Instruction.update,field_set] using
    Exec.action (.clear field.slot) (full r s)
theorem field_pop_exec (field : Field) (r : Store 56) (s : Saved) :
    Exec (.action (.pop field.slot)) (full r s) 1
      (full r (fieldSet field s (field.word s).tail)) := by
  simpa only [Action.update,Action.instruction,Instruction.update,field_get,field_set] using
    Exec.action (.pop field.slot) (full r s)

def save (field : Field) (i : Fin 56) : Block 63 :=
  .action (.copy field.slot (Frame.index 7 i))
theorem save_exec (field : Field) (i : Fin 56) (r : Store 56) (s : Saved) :
    Exec (save field i) (full r s) 1 (full r (fieldSet field s (r.get i))) := by
  cases field <;> exact SourceLinePullback.copy_to_saved r s.store _ i

def reset : Block 63 := use56 (SourceChartedSuccessorWords.clearAll 56)
theorem reset_exec (r : Store 56) (s : Saved) :
    Exec reset (full r s) 57 (work [] [] s) :=
  Frame.execution (SourceChartedSuccessorWords.clearAll_exec r) s.store

def prepend (field : Field) : Block 63 :=
  .seq (.action (.copy 5 field.slot)) (core SourceChartedSuccessorWords.prepend)
theorem prepend_exec (field : Field) (s : Saved) (out : BitString) :
    Exec (prepend field) (work [] out s) (8 * (field.word s).length + 10)
      (work [] (field.word s ++ out) s) := by
  let r := SourceScalarState.work []
  have load : Exec (.action (.copy (5 : Fin 63) field.slot)) (work [] out s) 1
      (withCore (SourceChartedSuccessorWords.prependReady r (field.word s) out) s) := by
    cases field <;> exact .action _ _
  have run := core_exec (SourceChartedSuccessorWords.prepend_exec r (field.word s) out) s
  have cost : 8 * (field.word s).length + 10 = 1 + (8 * (field.word s).length + 9) := by omega
  simpa only [prepend,cost,work,r,SourceScalarState.work,SourceChartedSuccessorWords.prepended] using
    Exec.seq load run

def data {n : Nat} (F : Family n) (h : List SourceChain.StepRecord) : Saved :=
  ⟨packet F,List.replicate n true,List.replicate F.length true,
    (records h).reverse,List.replicate h.length true,[],[true]⟩
def stopped (s : Saved) : Saved := {s with step := [],active := []}

end PNP.Concrete.ResidualReduction.SourceHistoryState

import PNP.Concrete.ResidualReduction.SourceNativeTermsInput

/-! Shared literal system-conversion workspace and protected source/buffers.
The first fourteen registers are scratch. The protected frame retains the
actual dimension, unread source, loop counts and row bytes across each call. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeSystemState
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence

structure Saved where
  dimension : BitString
  stream : BitString
  pending : BitString
  total : BitString
  rows : BitString
  products : BitString
  left : BitString
  constant : BitString
  active : BitString
  payload : BitString

def Saved.store (s : Saved) : Store 10 :=
  .cons s.dimension <| .cons s.stream <| .cons s.pending <| .cons s.total <|
    .cons s.rows <| .cons s.products <| .cons s.left <| .cons s.constant <|
    .cons s.active (.cons s.payload .nil)
def emptySaved : Saved := ⟨[],[],[],[],[],[],[],[],[],[]⟩
def full (r : Store 14) (s : Saved) : Store 24 := Frame.join r s.store
def withCore (r : Registers) (s : Saved) : Store 24 := full (Frame.join r.store (Store.empty 5)) s
def withLabel (r : Store 10) (s : Saved) : Store 24 := full (Frame.join r (Store.empty 4)) s
def work (input out : BitString) (s : Saved) : Store 24 :=
  withCore {SourceScalarState.work input with output := out} s
def initial (input : BitString) : Store 24 := work input [] emptySaved
def core (b : Block 9) : Block 24 := Frame.block 10 (Frame.block 5 b)
def use14 (b : Block 14) : Block 24 := Frame.block 10 b
def use10 (b : Block 10) : Block 24 := Frame.block 10 (Frame.block 4 b)

theorem core_exec {b : Block 9} {r out : Registers} {ticks : Nat}
    (checked : Exec b r.store ticks out.store) (s : Saved) :
    Exec (core b) (withCore r s) ticks (withCore out s) :=
  Frame.execution (Frame.execution checked (Store.empty 5)) s.store
theorem use14_exec {b : Block 14} {r out : Store 14} {ticks : Nat}
    (checked : Exec b r ticks out) (s : Saved) :
    Exec (use14 b) (full r s) ticks (full out s) := Frame.execution checked s.store
theorem use10_exec {b : Block 10} {r out : Store 10} {ticks : Nat}
    (checked : Exec b r ticks out) (s : Saved) :
    Exec (use10 b) (withLabel r s) ticks (withLabel out s) :=
  Frame.execution (Frame.execution checked (Store.empty 4)) s.store

inductive Field where
  | dimension | stream | pending | total | rows | products | left | constant | active | payload
def Field.index : Field → Fin 10
  | .dimension => 0 | .stream => 1 | .pending => 2 | .total => 3 | .rows => 4
  | .products => 5 | .left => 6 | .constant => 7 | .active => 8 | .payload => 9
def Field.slot (field : Field) : Fin 24 := Frame.frameIndex 14 field.index
def Field.word : Field → Saved → BitString
  | .dimension,s => s.dimension | .stream,s => s.stream | .pending,s => s.pending
  | .total,s => s.total | .rows,s => s.rows | .products,s => s.products
  | .left,s => s.left | .constant,s => s.constant | .active,s => s.active | .payload,s => s.payload
def fieldSet : Field → Saved → BitString → Saved
  | .dimension,s,w => {s with dimension := w} | .stream,s,w => {s with stream := w}
  | .pending,s,w => {s with pending := w} | .total,s,w => {s with total := w}
  | .rows,s,w => {s with rows := w} | .products,s,w => {s with products := w}
  | .left,s,w => {s with left := w} | .constant,s,w => {s with constant := w}
  | .active,s,w => {s with active := w} | .payload,s,w => {s with payload := w}

theorem field_get (field : Field) (r : Store 14) (s : Saved) :
    (full r s).get field.slot = field.word s := by
  rw [full,Field.slot,Frame.get_frame]
  cases field <;> rfl
theorem working_get (r : Store 14) (s : Saved) (i : Fin 14) :
    (full r s).get (Frame.index 10 i) = r.get i := Frame.get_core r s.store i

private theorem set_frame {count extra : Nat} (r : Store count) (s : Store extra)
    (i : Fin extra) (word : BitString) :
    (Frame.join r s).set (Frame.frameIndex count i) word = Frame.join r (s.set i word) := by
  induction r with
  | nil =>
    have position : Frame.frameIndex 0 i = i := by apply Fin.ext; exact Nat.zero_add i.val
    rw [position]
    rfl
  | @cons count first rest ih =>
    have position : Frame.frameIndex (count + 1) i = (Frame.frameIndex count i).succ := by
      apply Fin.ext
      change count + 1 + i.val = count + i.val + 1
      omega
    rw [position]
    exact congrArg (Store.cons first) ih

theorem field_set (field : Field) (r : Store 14) (s : Saved) (word : BitString) :
    (full r s).set field.slot word = full r (fieldSet field s word) := by
  rw [full,Field.slot,set_frame]
  cases field <;> rfl
def push (field : Field) (bit : Bool) : Block 24 := .action (.push field.slot bit)
def clear (field : Field) : Block 24 := .action (.clear field.slot)
def pop (field : Field) : Block 24 := .action (.pop field.slot)
theorem push_exec (field : Field) (r : Store 14) (s : Saved) (bit : Bool) :
    Exec (push field bit) (full r s) 1 (full r (fieldSet field s (bit :: field.word s))) := by
  simpa only [push,Action.update,Action.instruction,Instruction.update,field_get,field_set] using
    Exec.action (.push field.slot bit) (full r s)
theorem clear_exec (field : Field) (r : Store 14) (s : Saved) :
    Exec (clear field) (full r s) 1 (full r (fieldSet field s [])) := by
  simpa only [clear,Action.update,Action.instruction,Instruction.update,field_set] using
    Exec.action (.clear field.slot) (full r s)
theorem pop_exec (field : Field) (r : Store 14) (s : Saved) :
    Exec (pop field) (full r s) 1 (full r (fieldSet field s (field.word s).tail)) := by
  simpa only [pop,Action.update,Action.instruction,Instruction.update,field_get,field_set] using
    Exec.action (.pop field.slot) (full r s)

def save (field : Field) (i : Fin 14) : Block 24 :=
  .action (.copy field.slot (Frame.index 10 i))
def load (field : Field) (i : Fin 14) : Block 24 :=
  .action (.copy (Frame.index 10 i) field.slot)
theorem save_exec (field : Field) (r : Store 14) (s : Saved) (i : Fin 14) :
    Exec (save field i) (full r s) 1 (full r (fieldSet field s (r.get i))) := by
  cases field <;> exact SourceLinePullback.copy_to_saved r s.store _ i
theorem load_exec (field : Field) (r : Store 14) (s : Saved) (i : Fin 14) :
    Exec (load field i) (full r s) 1 (full (r.set i (field.word s)) s) := by
  cases field <;> exact SourceLinePullback.copy_from_saved r s.store i _

def reset : Block 24 := use14 (SourceChartedSuccessorWords.clearAll 14)
theorem reset_exec (r : Store 14) (s : Saved) : Exec reset (full r s) 15 (work [] [] s) :=
  Frame.execution (SourceChartedSuccessorWords.clearAll_exec r) s.store
def restore : Block 24 := load .stream 0
theorem restore_exec (s : Saved) : Exec restore (work [] [] s) 1 (work s.stream [] s) := by
  exact .action _ _
def clean : Block 24 := .seq reset restore
theorem clean_exec (r : Store 14) (s : Saved) :
    Exec clean (full r s) 16 (work s.stream [] s) := Exec.seq (reset_exec r s) (restore_exec s)

def reject : Block 24 := .seq (clear .active) (.seq (clear .pending) clean)
theorem reject_exec (r : Store 14) (s : Saved) :
    Exec reject (full r s) 18 (work s.stream [] {s with active := [],pending := []}) := by
  have first := clear_exec .active r s
  have second := clear_exec .pending r {s with active := []}
  have last := clean_exec r {s with active := [],pending := []}
  exact Exec.seq first (Exec.seq second last)

end PNP.Concrete.ResidualReduction.SourceNativeSystemState

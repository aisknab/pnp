import PNP.Concrete.ResidualReduction.SourceRawSelector
import PNP.Concrete.ResidualReduction.SourceChartSelectedFamily
import PNP.Concrete.ResidualReduction.SourceChartedSuccessorBounds

/-! Protected original-source data around a reusable workspace. Every protected
word starts empty and is filled by a literal instruction. No selected witness,
chart or transformed family is installed in the initial machine state. -/

namespace PNP.Concrete.ResidualReduction.SourceOriginalSuccessorState
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction

structure Saved where
  source : BitString
  choice : BitString
  dimension : BitString
  rows : BitString
  normals : BitString
  weights : BitString
  pivot : BitString
  tail : BitString

def Saved.store (s : Saved) : Store 8 :=
  .cons s.source <| .cons s.choice <| .cons s.dimension <| .cons s.rows <|
    .cons s.normals <| .cons s.weights <| .cons s.pivot (.cons s.tail .nil)
def emptySaved : Saved := ⟨[],[],[],[],[],[],[],[]⟩
def full (r : Store 48) (s : Saved) : Store 56 := Frame.join r s.store
def withCore (r : Registers) (s : Saved) : Store 56 :=
  full (Frame.join r.store (Store.empty 39)) s
def work (input out : BitString) (s : Saved) : Store 56 :=
  withCore {SourceScalarState.work input with output := out} s
def initial (input : BitString) : Store 56 := work input [] emptySaved
def core (b : Block 9) : Block 56 := Frame.block 8 (Frame.block 39 b)
def use48 (b : Block 48) : Block 56 := Frame.block 8 b
def use15 (b : Block 15) : Block 56 := Frame.block 8 (Frame.block 33 b)
def use29 (b : Block 29) : Block 56 := Frame.block 8 (Frame.block 19 b)
def state15 (r : Store 15) (s : Saved) : Store 56 := full (Frame.join r (Store.empty 33)) s
def state29 (r : Store 29) (s : Saved) : Store 56 := full (Frame.join r (Store.empty 19)) s

theorem core_exec {b : Block 9} {r out : Registers} {ticks : Nat}
    (h : Exec b r.store ticks out.store) (s : Saved) :
    Exec (core b) (withCore r s) ticks (withCore out s) :=
  Frame.execution (Frame.execution h (Store.empty 39)) s.store
theorem use48_exec {b : Block 48} {r out : Store 48} {ticks : Nat}
    (h : Exec b r ticks out) (s : Saved) :
    Exec (use48 b) (full r s) ticks (full out s) := Frame.execution h s.store
theorem use15_exec {b : Block 15} {r out : Store 15} {ticks : Nat}
    (h : Exec b r ticks out) (s : Saved) :
    Exec (use15 b) (state15 r s) ticks (state15 out s) :=
  Frame.execution (Frame.execution h (Store.empty 33)) s.store
theorem use29_exec {b : Block 29} {r out : Store 29} {ticks : Nat}
    (h : Exec b r ticks out) (s : Saved) :
    Exec (use29 b) (state29 r s) ticks (state29 out s) :=
  Frame.execution (Frame.execution h (Store.empty 19)) s.store

inductive Field where
  | source | choice | dimension | rows | normals | weights | pivot | tail
def Field.index : Field → Fin 8
  | .source => 0 | .choice => 1 | .dimension => 2 | .rows => 3
  | .normals => 4 | .weights => 5 | .pivot => 6 | .tail => 7
def Field.slot (field : Field) : Fin 56 := Frame.frameIndex 48 field.index
def Field.word : Field → Saved → BitString
  | .source,s => s.source | .choice,s => s.choice | .dimension,s => s.dimension | .rows,s => s.rows
  | .normals,s => s.normals | .weights,s => s.weights | .pivot,s => s.pivot | .tail,s => s.tail
def fieldSet : Field → Saved → BitString → Saved
  | .source,s,w => {s with source := w} | .choice,s,w => {s with choice := w}
  | .dimension,s,w => {s with dimension := w} | .rows,s,w => {s with rows := w}
  | .normals,s,w => {s with normals := w} | .weights,s,w => {s with weights := w}
  | .pivot,s,w => {s with pivot := w} | .tail,s,w => {s with tail := w}

theorem field_get (field : Field) (r : Store 48) (s : Saved) :
    (full r s).get field.slot = field.word s := by
  rw [full,Field.slot,Frame.get_frame]
  cases field <;> rfl
theorem working_get (r : Store 48) (s : Saved) (i : Fin 48) :
    (full r s).get (Frame.index 8 i) = r.get i := Frame.get_core r s.store i

def save (field : Field) (i : Fin 48) : Block 56 :=
  .action (.copy field.slot (Frame.index 8 i))
theorem save_exec (field : Field) (i : Fin 48) (r : Store 48) (s : Saved) :
    Exec (save field i) (full r s) 1 (full r (fieldSet field s (r.get i))) := by
  cases field <;> exact SourceLinePullback.copy_to_saved r s.store _ i

def reset : Block 56 := use48 (SourceChartedSuccessorWords.clearAll 48)
theorem reset_exec (r : Store 48) (s : Saved) :
    Exec reset (full r s) 49 (work [] [] s) :=
  Frame.execution (SourceChartedSuccessorWords.clearAll_exec r) s.store
def failure : Block 56 := .seq reset (.action (.push 8 false))
theorem failure_exec (r : Store 48) (s : Saved) :
    Exec failure (full r s) 50 (work [] [false] s) :=
  Exec.seq (reset_exec r s) (.action _ _)

def prepend (field : Field) : Block 56 :=
  .seq (.action (.copy 5 field.slot)) (core SourceChartedSuccessorWords.prepend)
theorem prepend_exec (field : Field) (s : Saved) (out : BitString) :
    Exec (prepend field) (work [] out s) (8 * (field.word s).length + 10)
      (work [] (field.word s ++ out) s) := by
  let r := SourceScalarState.work []
  have load : Exec (.action (.copy (5 : Fin 56) field.slot)) (work [] out s) 1
      (withCore (SourceChartedSuccessorWords.prependReady r (field.word s) out) s) := by
    cases field <;> exact .action _ _
  have run := core_exec (SourceChartedSuccessorWords.prepend_exec r (field.word s) out) s
  have cost : 8 * (field.word s).length + 10 = 1 + (8 * (field.word s).length + 9) := by omega
  simpa only [prepend,cost,work,r,SourceScalarState.work,SourceChartedSuccessorWords.prepended] using
    Exec.seq load run

def toInput : Block 56 := .seq (.action (.copy 0 8)) (.action (.clear 8))
theorem toInput_exec (word : BitString) (s : Saved) :
    Exec toInput (work [] word s) 2 (work word [] s) := Exec.seq (.action _ _) (.action _ _)

def stepCodec (n m : Nat) : Codec (Option (SourceClosure.ConstructedStep n m)) :=
  MatrixSolutionEncoding.optionCodec (SourceEncoding.stepCodec n m)

theorem step_none (n m : Nat) : (stepCodec n m).encode none = [false] := rfl
theorem step_some {n m : Nat} (s : SourceClosure.ConstructedStep n m) :
    (stepCodec n m).encode (some s) = true :: ((SourceEncoding.pointCodec m).encode s.weights ++
      (natural s.pivot.val ++ ((SourceEncoding.pointCodec n).encode s.tail ++
        (SourceEncoding.familyCodec n).encode s.output))) := rfl

end PNP.Concrete.ResidualReduction.SourceOriginalSuccessorState

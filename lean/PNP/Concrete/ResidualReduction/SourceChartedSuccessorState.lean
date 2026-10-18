import PNP.Concrete.ResidualReduction.SourceChartedSuccessorWords
import PNP.Concrete.ResidualReduction.SourceScalarFamily
import PNP.Concrete.ResidualReduction.SourceComputedTailInstructions
import PNP.Concrete.ResidualReduction.SourceFamilyReductionRaw

/-! One reusable workspace and six protected words for the charted successor.
The scalar and tail fields are initially empty and populated only by verified
component executions. No precomputed mathematical result enters startup. -/

namespace PNP.Concrete.ResidualReduction.SourceChartedSuccessorState
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions

structure Saved where
  dimension : BitString
  pivot : BitString
  normals : BitString
  family : BitString
  quadratic : BitString
  tail : BitString
def Saved.store (s : Saved) : Store 6 :=
  .cons s.dimension <| .cons s.pivot <| .cons s.normals <| .cons s.family <|
    .cons s.quadratic (.cons s.tail .nil)
def emptySaved : Saved := ⟨[],[],[],[],[],[]⟩
def full (r : Store 23) (s : Saved) : Store 29 := Frame.join r s.store
def withCore (r : Registers) (s : Saved) : Store 29 := full (Frame.join r.store (Store.empty 14)) s
def work (input out : BitString) (s : Saved) : Store 29 :=
  withCore {SourceScalarState.work input with output := out} s
def initial (input : BitString) : Store 29 := work input [] emptySaved

def core (b : Block 9) : Block 29 := Frame.block 6 (Frame.block 14 b)
def use16 (b : Block 16) : Block 29 := Frame.block 6 (Frame.block 7 b)
def use18 (b : Block 18) : Block 29 := Frame.block 6 (Frame.block 5 b)
def use19 (b : Block 19) : Block 29 := Frame.block 6 (Frame.block 4 b)
def use23 (b : Block 23) : Block 29 := Frame.block 6 b
def state16 (r : Store 16) (s : Saved) : Store 29 := full (Frame.join r (Store.empty 7)) s
def state18 (r : Store 18) (s : Saved) : Store 29 := full (Frame.join r (Store.empty 5)) s
def state19 (r : Store 19) (s : Saved) : Store 29 := full (Frame.join r (Store.empty 4)) s

theorem core_exec {b : Block 9} {r out : Registers} {ticks : Nat}
    (h : Exec b r.store ticks out.store) (s : Saved) :
    Exec (core b) (withCore r s) ticks (withCore out s) :=
  Frame.execution (Frame.execution h (Store.empty 14)) s.store
theorem use16_exec {b : Block 16} {r out : Store 16} {ticks : Nat}
    (h : Exec b r ticks out) (s : Saved) :
    Exec (use16 b) (state16 r s) ticks (state16 out s) :=
  Frame.execution (Frame.execution h (Store.empty 7)) s.store
theorem use18_exec {b : Block 18} {r out : Store 18} {ticks : Nat}
    (h : Exec b r ticks out) (s : Saved) :
    Exec (use18 b) (state18 r s) ticks (state18 out s) :=
  Frame.execution (Frame.execution h (Store.empty 5)) s.store
theorem use19_exec {b : Block 19} {r out : Store 19} {ticks : Nat}
    (h : Exec b r ticks out) (s : Saved) :
    Exec (use19 b) (state19 r s) ticks (state19 out s) :=
  Frame.execution (Frame.execution h (Store.empty 4)) s.store
theorem use23_exec {b : Block 23} {r out : Store 23} {ticks : Nat}
    (h : Exec b r ticks out) (s : Saved) :
    Exec (use23 b) (full r s) ticks (full out s) := Frame.execution h s.store

def reset : Block 29 := use23 (SourceChartedSuccessorWords.clearAll 23)
theorem reset_exec (r : Store 23) (s : Saved) : Exec reset (full r s) 24 (work [] [] s) :=
  Frame.execution (SourceChartedSuccessorWords.clearAll_exec r) s.store

inductive Field where
  | dimension | pivot | normals | family | quadratic | tail
def Field.slot : Field → Fin 29
  | .dimension => 23 | .pivot => 24 | .normals => 25
  | .family => 26 | .quadratic => 27 | .tail => 28
def Field.word : Field → Saved → BitString
  | .dimension,s => s.dimension | .pivot,s => s.pivot | .normals,s => s.normals
  | .family,s => s.family | .quadratic,s => s.quadratic | .tail,s => s.tail

def prepend (field : Field) : Block 29 :=
  .seq (.action (.copy 5 field.slot)) (core SourceChartedSuccessorWords.prepend)
theorem prepend_exec (field : Field) (s : Saved) (out : BitString) :
    Exec (prepend field) (work [] out s) (8 * (field.word s).length + 10)
      (work [] (field.word s ++ out) s) := by
  let r := SourceScalarState.work []
  have load : Exec (.action (.copy (5 : Fin 29) field.slot)) (work [] out s) 1
      (withCore (SourceChartedSuccessorWords.prependReady r (field.word s) out) s) := by
    cases field <;> exact .action _ _
  have run := core_exec (SourceChartedSuccessorWords.prepend_exec r (field.word s) out) s
  have cost : 8 * (field.word s).length + 10 = 1 + (8 * (field.word s).length + 9) := by omega
  simpa only [prepend,cost,work,r,SourceScalarState.work,
    SourceChartedSuccessorWords.prepended] using Exec.seq load run

def dimensionHeader : Block 29 := .seq (.action (.push 8 false)) (prepend .dimension)
theorem dimensionHeader_exec (n : Nat) (s : Saved) (out : BitString) :
    Exec dimensionHeader (work [] out {s with dimension := List.replicate n true}) (8 * n + 11)
      (work [] (natural n ++ out) {s with dimension := List.replicate n true}) := by
  let saved := {s with dimension := List.replicate n true}
  have push : Exec (.action (.push (8 : Fin 29) false)) (work [] out saved) 1
      (work [] (false :: out) saved) := .action _ _
  have prepend := prepend_exec Field.dimension saved (false :: out)
  have cost : 8 * n + 11 = 1 + (8 * n + 10) := by omega
  simpa only [dimensionHeader,cost,Field.word,saved,List.length_replicate,
    natural,List.append_assoc,List.singleton_append] using Exec.seq push prepend

def toInput : Block 29 := .seq (.action (.copy 0 8)) (.action (.clear 8))
theorem toInput_exec (word : BitString) (s : Saved) :
    Exec toInput (work [] word s) 2 (work word [] s) := Exec.seq (.action _ _) (.action _ _)

def normalsCodec (n : Nat) : Codec (Option (Affine (n + 1) × Affine (n + 1))) :=
  MatrixSolutionEncoding.optionCodec (pairCodec (SourceEncoding.affineCodec (n + 1))
    (SourceEncoding.affineCodec (n + 1)))
def data {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : Saved :=
  ⟨List.replicate n true,List.replicate k.val true,(normalsCodec n).encode normals,
    (SourceEncoding.familyCodec (n + 1)).encode F,[],[]⟩
def candidate {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : TailForm n :=
  SourceComputedTailEncoding.computed (scalar F).2 k normals
def result {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : Option (Family n) :=
  let t := candidate F k normals
  if SourceCoefficientGateState.checks (scalar F).1 (scalar F).2 t then t.reduce F else none

theorem result_chart {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (c : Fin (n + 1) × Point n) (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    result (chartRows (SourceBalance.markSource F w) c.1 c.2) c.1 normals =
      contract (SourceBalance.markSource F w) c.1 c.2 (SourceClosure.computedTail F w c normals) := by
  rw [SourceCoefficientGateState.contract_eq]
  rfl

end PNP.Concrete.ResidualReduction.SourceChartedSuccessorState

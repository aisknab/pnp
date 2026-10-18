import PNP.Concrete.ResidualReduction.SourceChartedSuccessorScalar

/-! Construct the candidate from the scalar just computed from the family.
The head is skipped by a counted read; original normal bytes and the remaining
quadratic coefficients form the existing candidate constructor's exact input. -/

namespace PNP.Concrete.ResidualReduction.SourceChartedSuccessorTail
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceChartedSuccessorState

def prepareTail : Block 29 := .seq (.action (.copy 0 27)) <|
  .seq (.action (.copy 2 23)) (.action (.push 2 true))
def tailOutput : Block 29 := .seq (.action (.copy 8 0)) (.action (.clear 0))
def loadTail : Block 29 := .seq prepareTail <| .seq (core dropLoop) tailOutput
def loadFuel (n : Nat) : Nat := 3 * n + 9

theorem load_exec {n : Nat} (h : Affine n) (q : Quadratic n) (s : Saved) :
    Exec loadTail (work [] [] {s with dimension := List.replicate n true,quadratic := SourceQuadraticEncoding.word (n := n + 1) (h,q)}) (loadFuel n)
      (work [] (SourceQuadraticEncoding.word q) {s with dimension := List.replicate n true,quadratic := SourceQuadraticEncoding.word (n := n + 1) (h,q)}) := by
  let saved := {s with dimension := List.replicate n true,quadratic := SourceQuadraticEncoding.word (n := n + 1) (h,q)}
  let loaded := {SourceScalarState.work (affineWord h ++ SourceQuadraticEncoding.word q) with remaining := List.replicate (n + 1) true}
  let tail := SourceScalarState.work (SourceQuadraticEncoding.word q)
  have prepare : Exec prepareTail (work [] [] saved) 3 (withCore loaded saved) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have drop : Exec dropLoop loaded.store (3 * (n + 1) + 1) tail.store := by
    simpa only [loaded,tail,SourceScalarState.work,affineWord_length] using
      drop_exec (SourceScalarState.work []) (affineWord h) (SourceQuadraticEncoding.word q)
  have output : Exec tailOutput (withCore tail saved) 2
      (work [] (SourceQuadraticEncoding.word q) saved) := Exec.seq (.action _ _) (.action _ _)
  have cost : loadFuel n = 3 + ((3 * (n + 1) + 1) + 2) := by unfold loadFuel; omega
  simpa only [loadTail,cost,saved] using Exec.seq prepare (Exec.seq (core_exec drop saved) output)

theorem constructor_packet {n : Nat} (q : Quadratic n)
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    SourceComputedTailEncoding.packet q normals =
      (normalsCodec n).encode normals ++ SourceQuadraticEncoding.word q := rfl

def prepareCall : Block 29 := .seq toInput <|
  .seq (.action (.copy 1 23)) (.action (.copy 16 24))

theorem prepareCall_exec {n : Nat} (k : Fin (n + 1)) (input : BitString) (s : Saved) :
    Exec prepareCall (work [] input {s with dimension := List.replicate n true,pivot := List.replicate k.val true}) 4
      (state19 (SourceComputedTailState.initial input k)
        {s with dimension := List.replicate n true,pivot := List.replicate k.val true}) := by
  let saved := {s with dimension := List.replicate n true,pivot := List.replicate k.val true}
  have prepare : Exec (.seq (.action (.copy (1 : Fin 29) 23)) (.action (.copy 16 24)))
      (work input [] saved) 2 (state19 (SourceComputedTailState.initial input k) saved) :=
    Exec.seq (.action _ _) (.action _ _)
  exact Exec.seq (toInput_exec input saved) prepare

def save : Block 29 := .seq (.action (.copy 28 8)) reset
theorem save_exec {n : Nat} (q : Quadratic n) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) (s : Saved) :
    Exec save (state19 (SourceComputedTailInstructions.finished q k normals) s) 25
      (work [] [] {s with tail := (SourceComputedTailEncoding.codec n).encode (SourceComputedTailEncoding.computed q k normals)}) := by
  let saved := {s with tail := (SourceComputedTailEncoding.codec n).encode (SourceComputedTailEncoding.computed q k normals)}
  have copy : Exec (.action (.copy (28 : Fin 29) 8))
      (state19 (SourceComputedTailInstructions.finished q k normals) s) 1
      (state19 (SourceComputedTailInstructions.finished q k normals) saved) := .action _ _
  have clear := reset_exec
    (Frame.join (SourceComputedTailInstructions.finished q k normals) (Store.empty 4)) saved
  exact Exec.seq copy clear

def retained {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : Saved :=
  {SourceChartedSuccessorScalar.computed F k normals with tail := (SourceComputedTailEncoding.codec n).encode (candidate F k normals)}
def block : Block 29 := .seq loadTail <| .seq (prepend .normals) <|
  .seq prepareCall <| .seq (use19 SourceComputedTailInstructions.block) save
def fuel {n : Nat} (k : Fin (n + 1)) (normals : Option (Affine (n + 1) × Affine (n + 1))) : Nat :=
  loadFuel n + ((8 * ((normalsCodec n).encode normals).length + 10) +
    (4 + (SourceComputedTailInstructions.fuel n k.val normals.isSome + 25)))

theorem block_exec {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    Exec block (work [] [] (SourceChartedSuccessorScalar.computed F k normals)) (fuel k normals)
      (work [] [] (retained F k normals)) := by
  let saved := SourceChartedSuccessorScalar.computed F k normals
  let q := (scalar F).2
  let input := SourceComputedTailEncoding.packet q normals
  have load := load_exec (scalar F).1 q (data F k normals)
  have bytes := prepend_exec Field.normals saved (SourceQuadraticEncoding.word q)
  have prepare := prepareCall_exec k input saved
  have construct := use19_exec (SourceComputedTailInstructions.block_exec q k normals) saved
  have store := save_exec q k normals saved
  have eta : SourceQuadraticEncoding.word (n := n + 1) ((scalar F).1,(scalar F).2) =
      SourceQuadraticEncoding.word (scalar F) := by cases scalar F; rfl
  simp only [data,q,eta] at load
  simp only [Field.word,saved,SourceChartedSuccessorScalar.computed,data,← constructor_packet] at bytes
  simp only [saved,SourceChartedSuccessorScalar.computed,data] at prepare
  simpa only [block,fuel,input,q,saved,retained,candidate,SourceChartedSuccessorScalar.computed,data] using
    Exec.seq load (Exec.seq bytes (Exec.seq prepare (Exec.seq construct store)))

end PNP.Concrete.ResidualReduction.SourceChartedSuccessorTail

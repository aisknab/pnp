import PNP.Concrete.ResidualReduction.SourceChartedSuccessorGate

/-! Dispatch the actual gate result. Only its true branch constructs and runs
the complete family reducer. A failed check and a failed row reduction both
remain the existing unknown/none result, without an unsatisfiability claim. -/

namespace PNP.Concrete.ResidualReduction.SourceChartedSuccessorFinish
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChartedSuccessorState
open PNP.Concrete.ResidualReduction.SourceChartedSuccessorGate (decision)

def checkedCore {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : Store 23 :=
  Frame.join (SourceCoefficientGateState.finished (scalar F).1 (scalar F).2 (candidate F k normals) [])
    (Store.empty 5)
theorem initial_eq (input : BitString) (s : Saved) :
    full (SourceFamilyReductionLoad.initial input) s = work input [] s := rfl

def prepare : Block 29 := .seq (.action (.copy 8 26)) <|
  .seq (prepend .tail) <| .seq dimensionHeader toInput
def prepareFuel {n : Nat} (t : TailForm n) : Nat :=
  8 * ((SourceComputedTailEncoding.codec n).encode t).length + 8 * n + 24

theorem prepare_exec {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    Exec prepare (work [] [] (SourceChartedSuccessorTail.retained F k normals))
      (prepareFuel (candidate F k normals))
      (full (SourceFamilyReductionLoad.initial
        (SourceFamilyReductionEncoding.packet (candidate F k normals) F))
        (SourceChartedSuccessorTail.retained F k normals)) := by
  let saved := SourceChartedSuccessorTail.retained F k normals
  let tail := (SourceComputedTailEncoding.codec n).encode (candidate F k normals)
  let family := (SourceEncoding.familyCodec (n + 1)).encode F
  have copy : Exec (.action (.copy (8 : Fin 29) 26)) (work [] [] saved) 1 (work [] family saved) := .action _ _
  have bytes := prepend_exec Field.tail saved family
  have dimension := dimensionHeader_exec n saved (tail ++ family)
  have input := toInput_exec (SourceFamilyReductionEncoding.packet (candidate F k normals) F) saved
  simp only [Field.word,saved,SourceChartedSuccessorTail.retained] at bytes
  simp only [saved,SourceChartedSuccessorTail.retained,SourceChartedSuccessorScalar.computed,data] at dimension
  have cost : prepareFuel (candidate F k normals) =
      1 + ((8 * tail.length + 10) + ((8 * n + 11) + 2)) := by unfold prepareFuel; dsimp only [tail]; omega
  rw [initial_eq]
  simpa only [prepare,cost,SourceFamilyReductionEncoding.packet,SourceFamilyReductionEncoding.inputCodec,
    tail,family,saved,SourceChartedSuccessorTail.retained,SourceChartedSuccessorScalar.computed,data] using
    Exec.seq copy (Exec.seq bytes (Exec.seq dimension input))

def successStore {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : Store 29 :=
  full (SourceFamilyReductionState.finished (candidate F k normals) []
    ((SourceFamilyReductionEncoding.codec n).encode ((candidate F k normals).reduce F)))
    (SourceChartedSuccessorTail.retained F k normals)
def success : Block 29 := .seq reset <| .seq prepare (use23 SourceFamilyReductionRaw.block)
def successFuel {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : Nat :=
  24 + (prepareFuel (candidate F k normals) + SourceFamilyReductionRaw.fuel (candidate F k normals) F)

theorem success_exec {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    Exec success (SourceChartedSuccessorGate.checked F k normals) (successFuel F k normals)
      (successStore F k normals) := by
  let saved := SourceChartedSuccessorTail.retained F k normals
  have clear := reset_exec (checkedCore F k normals) saved
  have reduce := use23_exec (SourceFamilyReductionRaw.block_exec (candidate F k normals) F []) saved
  simp only [List.append_nil] at reduce
  exact Exec.seq clear (Exec.seq (prepare_exec F k normals) reduce)

def failure : Block 29 := .seq reset (.action (.push 8 false))
theorem failure_exec (r : Store 23) (s : Saved) :
    Exec failure (full r s) 25 (work [] [false] s) :=
  Exec.seq (reset_exec r s) (.action _ _)

def finished {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : Store 29 :=
  if decision F k normals then successStore F k normals
  else work [] [false] (SourceChartedSuccessorTail.retained F k normals)
def block : Block 29 := .branch 8 failure failure success
def fuel {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : Nat :=
  1 + if decision F k normals then successFuel F k normals else 25

theorem block_exec {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    Exec block (SourceChartedSuccessorGate.checked F k normals) (fuel F k normals) (finished F k normals) := by
  cases branch : decision F k normals with
  | false =>
    simp only [fuel,finished,branch,Bool.false_eq_true,↓reduceIte]
    apply Exec.zero (source := (8 : Fin 29))
    · rw [SourceChartedSuccessorGate.output_get,branch]
    · exact failure_exec (checkedCore F k normals) (SourceChartedSuccessorTail.retained F k normals)
  | true =>
    simp only [fuel,finished,branch,↓reduceIte]
    apply Exec.one (source := (8 : Fin 29))
    · rw [SourceChartedSuccessorGate.output_get,branch]
    · exact success_exec F k normals

theorem output_eq {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    (finished F k normals).get 8 = (SourceFamilyReductionEncoding.codec n).encode (result F k normals) := by
  change (finished F k normals).get 8 = (SourceFamilyReductionEncoding.codec n).encode
    (if decision F k normals then (candidate F k normals).reduce F else none)
  cases branch : decision F k normals <;> simp only [finished,branch,Bool.false_eq_true,↓reduceIte] <;> rfl

theorem output_decode {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    (SourceFamilyReductionEncoding.codec n).decode ((finished F k normals).get 8) = some (result F k normals) := by
  rw [output_eq]
  exact decode_encode _ _

end PNP.Concrete.ResidualReduction.SourceChartedSuccessorFinish

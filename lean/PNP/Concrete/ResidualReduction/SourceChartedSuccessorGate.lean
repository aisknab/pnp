import PNP.Concrete.ResidualReduction.SourceChartedSuccessorTail

/-! Run both exact coefficient gates on the actual computed scalar and tail.
Packet construction consists only of checked byte transfers. The original
family and computed candidate remain protected for the subsequent reduction. -/

namespace PNP.Concrete.ResidualReduction.SourceChartedSuccessorGate
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChartedSuccessorState

theorem initial_eq (input : BitString) (s : Saved) :
    state18 (SourceCoefficientGateRaw.initial input) s = work input [] s := rfl

def prepare : Block 29 := .seq (.action (.copy 8 28)) <|
  .seq (prepend .quadratic) <| .seq dimensionHeader toInput
def prepareFuel (n : Nat) : Nat := 8 * quadraticBits (n + 1) + 8 * n + 24

theorem prepare_exec {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    Exec prepare (work [] [] (SourceChartedSuccessorTail.retained F k normals)) (prepareFuel n)
      (state18 (SourceCoefficientGateRaw.initial
        (SourceCoefficientGateRaw.packet (scalar F) (candidate F k normals)))
        (SourceChartedSuccessorTail.retained F k normals)) := by
  let saved := SourceChartedSuccessorTail.retained F k normals
  let tail := (SourceComputedTailEncoding.codec n).encode (candidate F k normals)
  let q := SourceQuadraticEncoding.word (scalar F)
  have copy : Exec (.action (.copy (8 : Fin 29) 28)) (work [] [] saved) 1 (work [] tail saved) := .action _ _
  have prepend := prepend_exec Field.quadratic saved tail
  have dimension := dimensionHeader_exec n saved (q ++ tail)
  have input := toInput_exec (SourceCoefficientGateRaw.packet (scalar F) (candidate F k normals)) saved
  simp only [Field.word,saved,SourceChartedSuccessorTail.retained,
    SourceChartedSuccessorScalar.computed,data,SourceQuadraticEncoding.word_length] at prepend
  simp only [saved,SourceChartedSuccessorTail.retained,SourceChartedSuccessorScalar.computed,data] at dimension
  have cost : prepareFuel n =
      1 + ((8 * quadraticBits (n + 1) + 10) + ((8 * n + 11) + 2)) := by unfold prepareFuel; omega
  rw [initial_eq]
  simpa only [prepare,cost,SourceCoefficientGateRaw.packet,q,tail,saved,
    SourceChartedSuccessorTail.retained,SourceChartedSuccessorScalar.computed,data] using
    Exec.seq copy (Exec.seq prepend (Exec.seq dimension input))

def decision {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : Bool :=
  SourceCoefficientGateState.checks (scalar F).1 (scalar F).2 (candidate F k normals)
def checked {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : Store 29 :=
  state18 (SourceCoefficientGateState.finished (scalar F).1 (scalar F).2 (candidate F k normals) [])
    (SourceChartedSuccessorTail.retained F k normals)
def block : Block 29 := .seq prepare (use18 SourceCoefficientGateRaw.block)
def fuel {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : Nat :=
  prepareFuel n + SourceCoefficientGateRaw.fuel (candidate F k normals)

theorem block_exec {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    Exec block (work [] [] (SourceChartedSuccessorTail.retained F k normals)) (fuel F k normals)
      (checked F k normals) := by
  have compare := use18_exec (SourceCoefficientGateRaw.block_exec (scalar F) (candidate F k normals) [])
    (SourceChartedSuccessorTail.retained F k normals)
  simp only [List.append_nil] at compare
  exact Exec.seq (prepare_exec F k normals) compare

theorem output_get {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    (checked F k normals).get 8 = [decision F k normals] := rfl

end PNP.Concrete.ResidualReduction.SourceChartedSuccessorGate

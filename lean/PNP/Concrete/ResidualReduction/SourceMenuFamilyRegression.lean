import PNP.Concrete.ResidualReduction.SourceMenuFamily
import Lean

/-! Boundary regressions and compiled axiom guards for candidate construction.
These finite examples exercise the general proofs; they are not publication
rows or evidence of a completed sorted selector or unconditional solver. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuFamily.Regression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.CoefficientComparison
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceChain

private def a : Affine 2 := (true, (false, false))
private def b : Affine 2 := (false, (true, false))
private def c : Affine 2 := (true, (true, false))
private def aConstant : Affine 2 := (true, (false, true))
private def bConstant : Affine 2 := (false, (true, true))
private def zeroConstant : Affine 2 := (false, (false, true))
private def ab : Row 2 := ⟨true, a, b⟩
private def bc : Row 2 := ⟨false, b, c⟩
private def constants : Row 2 := ⟨false, aConstant, bConstant⟩
private def repeated : Row 2 := ⟨true, a, aConstant⟩
private def zeroLeft : Row 2 := ⟨false, zeroConstant, b⟩
private def zeroRight : Row 2 := ⟨true, a, zeroConstant⟩
private def dirty : SourceMenuRow.Saved := ⟨[true, false], [false, true, false], [true]⟩
private def abBytes : BitString := [true, true, false, false, true, false, true, false, false]
private def bcBytes : BitString := [true, false, false, true, true, false, false, true, false]

example : rowNormals ab = [a, b, c] := rfl
example : rowNormals constants = [a, b, c] := rfl
example : rowNormals repeated = [] := rfl
example : rowNormals zeroLeft = [] := rfl
example : rowNormals zeroRight = [] := rfl
example : rowNormals (n := 0) ⟨true, true, false⟩ = [] := rfl
example : rowNormals (n := 1) ⟨true, (true, true), (true, false)⟩ = [] := rfl
example : SourceMenuBytes.eligible [true, false] [false, true] = true := rfl
example : SourceMenuBytes.eligible [] [] = false := rfl
example : SourceMenuBytes.eligible [true, false] [true, false] = false := rfl
example : SourceMenuBytes.eligible [false, false] [true, false] = false := rfl
example : bytes [ab] = abBytes := rfl
example : bytes [bc] = bcBytes := rfl
example : bytes [ab, bc] = bcBytes ++ abBytes := rfl
example : bytes [bc, ab] = abBytes ++ bcBytes := rfl
example : bytes [ab, repeated, constants] = abBytes ++ abBytes := rfl
example : bytes [zeroLeft, zeroRight, repeated] = [] := rfl
example : sourceMenu [ab, bc, constants] = [a, b, c] := rfl
example : sourceMenu [bc, ab, repeated] = [a, b, c] := rfl
example : planeMenu [a, b, c] = [(b, a), (c, a), (c, b)] := rfl

private def Produces {n : Nat} (F : Family n) (accumulator word : BitString) : Prop :=
  ∃ used after, Exec block (initial F accumulator dirty) used after ∧
    after.get 7 = word ∧ used ≤ (43 * n + 53) * F.length + 7

private theorem produces {n : Nat} (F : Family n) (accumulator word : BitString)
    (expected : bytes F ++ accumulator = word) : Produces F accumulator word := by
  obtain ⟨used, last, checked, bound⟩ := block_exec F accumulator dirty
  exact ⟨used, terminal n (bytes F ++ accumulator) last, checked, expected, bound⟩

example : Produces ([] : Family 0) [] [] := produces _ _ _ rfl
example : Produces ([] : Family 2) [true, false] [true, false] := produces _ _ _ rfl
example : Produces (n := 0) [⟨false, false, true⟩, ⟨true, true, true⟩] [true] [true] :=
  produces _ _ _ rfl
example : Produces (n := 1) [⟨true, (true, true), (true, false)⟩] [] [] := produces _ _ _ rfl
example : Produces [ab] [] abBytes := produces _ _ _ rfl
example : Produces [constants] [] abBytes := produces _ _ _ rfl
example : Produces [repeated] [false, true] [false, true] := produces _ _ _ rfl
example : Produces [zeroLeft, zeroRight] [true, false] [true, false] := produces _ _ _ rfl
example : Produces [ab, bc] [] (bcBytes ++ abBytes) := produces _ _ _ rfl
example : Produces [bc, ab] [] (abBytes ++ bcBytes) := produces _ _ _ rfl
example : Produces [ab, repeated, constants] [true, false] (abBytes ++ abBytes ++ [true, false]) :=
  produces _ _ _ rfl

-- Literal compiled instruction checks exercise the real codec's unary header.
example : (BitRegister.run program 8 ⟨.running 0, initial ([] : Family 2) [true, false] dirty⟩).store.get 7 =
    [true, false] := rfl
private def ProgramProduces {n : Nat} (F : Family n) (accumulator word : BitString) : Prop :=
  ∃ used last, BitRegister.run program (used + 1) ⟨.running 0, initial F accumulator dirty⟩ =
    ⟨.accepted, terminal n word last⟩ ∧ used + 1 ≤ (43 * n + 53) * F.length + 8
private theorem program_produces {n : Nat} (F : Family n) (accumulator word : BitString)
    (expected : bytes F ++ accumulator = word) : ProgramProduces F accumulator word := by
  obtain ⟨used, last, checked, _, bound⟩ := program_run F accumulator dirty
  rw [expected] at checked
  exact ⟨used, last, checked, bound⟩
example : ProgramProduces [ab] [] abBytes := program_produces _ _ _ rfl
example : ProgramProduces [constants] [] abBytes := program_produces _ _ _ rfl
example : ProgramProduces [ab, bc] [true] (bcBytes ++ abBytes ++ [true]) :=
  program_produces _ _ _ rfl
example : (SourceEncoding.familyCodec 2).encode [ab, bc] =
    [true, true, false] ++ ((SourceEncoding.rowCodec 2).encode ab ++ (SourceEncoding.rowCodec 2).encode bc) := rfl

-- General statements retain unbounded dimensions, source rows and accumulators.
example {n : Nat} (F : Family n) (accumulator : BitString) (s : SourceMenuRow.Saved) :
    ∃ used last, Exec block (initial F accumulator s) used
      (terminal n (bytes F ++ accumulator) last) ∧ used ≤ (43 * n + 53) * F.length + 7 :=
  block_exec F accumulator s
example {n : Nat} (F : Family n) : (bytes F).length ≤ (n + 1) * (3 * F.length) :=
  bytes_bound F
example {n : Nat} (F : Family n) :
    (F.flatMap rowNormals).reverse.foldl (fun menu x => insertNormal x menu) [] = sourceMenu F :=
  source_menu_link F
example {n : Nat} (r : Row n) (accumulator : BitString) :
    SourceMenuRow.cost r accumulator ≤ 43 * n + 49 := SourceMenuRow.cost_bound r accumulator
example {n : Nat} (r : Row n) (accumulator : BitString) :
    (SourceMenuCandidates.result (normalBits r.left) (normalBits r.right) accumulator).store.get 8 =
      matrixBits (rowNormals r).reverse ++ accumulator := SourceMenuCandidates.row_output r accumulator

run_cmd do
  for name in [
    ``SourceMenuBytes.homogeneous_zero,
    ``SourceMenuBytes.homogeneous_cons,
    ``SourceMenuBytes.normalBits_homogeneous,
    ``SourceMenuBytes.normalBits_add,
    ``SourceMenuBytes.homogeneous_add,
    ``SourceMenuBytes.homogeneous_bytes,
    ``SourceMenuBytes.homogeneous_sum_bytes,
    ``SourceMenuBytes.zero_test,
    ``SourceMenuBytes.equality_test,
    ``SourceMenuBytes.reversed_row_bytes,
    ``SourceMenuScan.markLeft_exec,
    ``SourceMenuScan.markRight_exec,
    ``SourceMenuScan.markXor_exec,
    ``SourceMenuScan.pair_exec,
    ``SourceMenuScan.body_exec,
    ``SourceMenuScan.result_cons,
    ``SourceMenuScan.loop_exec,
    ``SourceMenuScan.fuel_bound,
    ``SourceMenuCandidates.reverse_exec,
    ``SourceMenuCandidates.emit_exec,
    ``SourceMenuCandidates.gate_exec,
    ``SourceMenuCandidates.block_exec,
    ``SourceMenuCandidates.result_output,
    ``SourceMenuCandidates.cost_bound,
    ``SourceMenuCandidates.row_output,
    ``SourceMenuCandidates.row_exec,
    ``SourceMenuCandidates.row_cost_bound,
    ``SourceMenuCandidates.program_run,
    ``SourceMenuRowInput.affine_payload,
    ``SourceMenuRowInput.coefficient_exec,
    ``SourceMenuRowInput.block_exec,
    ``SourceMenuRow.capture_exec,
    ``SourceMenuRow.prepare_exec,
    ``SourceMenuRow.handoff_exec,
    ``SourceMenuRow.restore_exec,
    ``SourceMenuRow.block_exec,
    ``SourceMenuRow.cost_bound,
    ``SourceMenuFamily.headerLoop_exec,
    ``SourceMenuFamily.header_exec,
    ``SourceMenuFamily.rowLoop_exec,
    ``SourceMenuFamily.block_exec,
    ``SourceMenuFamily.candidate_count,
    ``SourceMenuFamily.bytes_bound,
    ``SourceMenuFamily.reversed_fold,
    ``SourceMenuFamily.source_menu_link,
    ``SourceMenuFamily.program_run] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceMenuScan.loop_exec
#print axioms PNP.Concrete.ResidualReduction.SourceMenuCandidates.row_output
#print axioms PNP.Concrete.ResidualReduction.SourceMenuRow.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceMenuFamily.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceMenuFamily.bytes_bound
#print axioms PNP.Concrete.ResidualReduction.SourceMenuFamily.source_menu_link
#print axioms PNP.Concrete.ResidualReduction.SourceMenuFamily.program_run

end PNP.Concrete.ResidualReduction.SourceMenuFamily.Regression

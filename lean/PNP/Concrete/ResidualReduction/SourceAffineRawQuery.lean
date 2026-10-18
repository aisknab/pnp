import PNP.Concrete.ResidualReduction.SourceAffineSolverBridge
import PNP.Concrete.ResidualReduction.SourcePolynomialMatrix
import PNP.Concrete.ResidualReduction.MatrixPolynomialSolver

/-! One fixed literal affine-query program on arbitrary input bitstrings.
It constructs its equation matrix, solves it, transfers the actual retained
map into the complete search, and returns canonical optional witness bytes.
All malformed input, missing solutions and unsuccessful searches are charged. -/

namespace PNP.Concrete.ResidualReduction.SourceAffineRawQuery
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceAffineInput

def answer (input : BitString) : BitString :=
  match codec.decode input with
  | none => [false]
  | some ⟨n, F⟩ => (SourceAffineOutput.witnessCodec F.length n).encode (SourceClosure.sourceAffineQuery F)
theorem answer_canonical (n : Nat) (F : Family n) :
    answer (codec.encode ⟨n, F⟩) = (SourceAffineOutput.witnessCodec F.length n).encode (SourceClosure.sourceAffineQuery F) := by
  rw [answer, roundtrip]
theorem answer_malformed (input : BitString) (invalid : codec.decode input = none) : answer input = [false] := by
  rw [answer, invalid]

def matrixLength (L : Nat) : Nat := (L + 1) + (L * L + 1) + (L + 1) * (L * L)
def budget (L : Nat) : Nat :=
  SourcePolynomialMatrix.sourceFuel.eval L + MatrixPolynomialSolver.sourceFuel.eval (matrixLength L) +
    SourceAffineOutput.originalInputBudget L + 31

def process : Block 22 := .seq prepareSolver (.seq (SourceAffineOutput.lift12 MatrixEncodedSolver.block) select)
def gate : Block 22 := .branch 20 .skip process process
def block : Block 22 := .seq source (.seq inspectMatrix gate)

theorem process_exec {n : Nat} (F : Family n) :
    ∃ used after, Exec process (matrixReady F).store used after ∧
      after.get 8 = (SourceAffineOutput.witnessCodec F.length n).encode (SourceClosure.sourceAffineQuery F) ∧
      used ≤ MatrixEncodedSolver.validFuel F.length (SourceClosure.affineMaskRows F) + 28 +
        SourceAffineOutput.originalInputBudget (codec.encode ⟨n, F⟩).length := by
  obtain ⟨used, after, selected, bytes, bound⟩ := select_exec F
  refine ⟨13 + (MatrixEncodedSolver.validFuel F.length (SourceClosure.affineMaskRows F) + used), after,
    Exec.seq (prepare_valid F) (Exec.seq (solver_exec F) selected), bytes, ?_⟩
  omega

theorem valid_exec (n : Nat) (F : Family n) :
    ∃ used after, Exec block (rawStart (codec.encode ⟨n, F⟩)).store used after ∧
      after.get 8 = (SourceAffineOutput.witnessCodec F.length n).encode (SourceClosure.sourceAffineQuery F) ∧
      used ≤ budget (codec.encode ⟨n, F⟩).length := by
  obtain ⟨used, after, processed, bytes, bound⟩ := process_exec F
  obtain ⟨bit, rest, head⟩ := matrix_tail_nonempty F
  have read : (matrixReady F).store.get 20 = bit :: rest := head
  have checked : Exec gate (matrixReady F).store (1 + used) after := Exec.nonempty read processed
  refine ⟨SourceEncodedMatrix.validFuel n F + (2 + (1 + used)), after,
    Exec.seq (source_valid n F) (Exec.seq (inspect_valid F) checked), bytes, ?_⟩
  let L := (codec.encode ⟨n, F⟩).length
  have constructor : SourceEncodedMatrix.validFuel n F ≤ SourcePolynomialMatrix.sourceFuel.eval L := by
    rw [SourcePolynomialMatrix.sourceFuel_eval]
    exact Nat.le_trans (SourceEncodedMatrix.validFuel_bound n F) (Nat.le_succ _)
  have solver : MatrixEncodedSolver.validFuel F.length (SourceClosure.affineMaskRows F) ≤
      MatrixPolynomialSolver.sourceFuel.eval (matrixLength L) := by
    have inputBound : (affineMatrixPacket F).length ≤ matrixLength L := affineMatrixPacket_bound n F
    have phase : MatrixEncodedSolver.validFuel F.length (SourceClosure.affineMaskRows F) ≤
        MatrixPolynomialSolver.sourceFuel.eval (affineMatrixPacket F).length := by
      rw [MatrixPolynomialSolver.sourceFuel_eval]
      exact Nat.le_trans (MatrixEncodedSolver.validFuel_bound F.length (SourceClosure.affineMaskRows F)) (Nat.le_succ _)
    exact Nat.le_trans phase (NatPolynomial.eval_mono _ inputBound)
  dsimp only [L] at constructor solver
  unfold budget
  omega

theorem malformed_exec (input : BitString) (invalid : codec.decode input = none) :
    ∃ used after, Exec block (rawStart input).store used after ∧ after.get 8 = answer input ∧ used ≤ budget input.length := by
  obtain ⟨used, after, constructed, bound, bytes⟩ := source_exec input
  have output : (SourceAffineOutput.core (fromSource after)).core.output = [false] := by
    rw [bytes, SourceFamilyInput.matrixEncoded_malformed input invalid]
  have inspected := inspectMatrix_exec (fromSource after)
  rw [output] at inspected
  let stopped := withScratch (fromSource after) []
  have checked : Exec gate stopped.store 2 stopped.store := Exec.empty (source := (20 : Fin 22)) rfl (.skip _)
  refine ⟨used + (2 + 2), stopped.store, Exec.seq constructed (Exec.seq inspected checked), ?_, ?_⟩
  · rw [answer_malformed input invalid]
    exact output
  · unfold budget
    rw [SourcePolynomialMatrix.sourceFuel_eval]
    omega

theorem block_exec (input : BitString) :
    ∃ used after, Exec block (rawStart input).store used after ∧ after.get 8 = answer input ∧ used ≤ budget input.length := by
  cases decoded : codec.decode input with
  | none => exact malformed_exec input decoded
  | some problem =>
    rcases problem with ⟨n, F⟩
    have bytes := (canonical input ⟨n, F⟩).mp decoded
    rw [← bytes, answer_canonical]
    exact valid_exec n F

theorem answer_length (input : BitString) : (answer input).length ≤ 2 * input.length + 1 := by
  cases decoded : codec.decode input with
  | none => rw [answer_malformed input decoded]; simp only [List.length_cons, List.length_nil]; omega
  | some problem =>
    rcases problem with ⟨n, F⟩
    have bytes := (canonical input ⟨n, F⟩).mp decoded
    rw [← bytes, answer_canonical]
    have result := SourceAffineOutput.witness_bytes_bound F.length n (SourceClosure.sourceAffineQuery F)
    have dimension := dimension_bound n F
    have rows := rowCount_bound n F
    omega

end PNP.Concrete.ResidualReduction.SourceAffineRawQuery

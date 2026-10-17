import PNP.Concrete.ResidualReduction.SourceAffineEncodedSearch
import PNP.Concrete.ResidualReduction.SourceEncodedMatrix
import PNP.Concrete.ResidualReduction.MatrixEncodedSolver

/-! Literal source-constructor to solver handoff. A fixed register frame
preserves the original source bytes and dimension. Scratch resets and matrix
packet transfers are instructions with explicit costs, not semantic callbacks. -/

namespace PNP.Concrete.ResidualReduction.SourceAffineInput
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceAffineOutput (core setCore setRegisters lift12 lift12_exec)

def emptyFrame : Store 6 := .cons [] (.cons [] (.cons [] (.cons [] (.cons [] (.cons [] .nil)))))
def fromSource (r : SourceMatrixPacket.State) : SourceAffineSearch.State :=
  ⟨⟨⟨⟨r.core.core, r.core.source⟩, r.core.outer, r.core.inner, r.rows⟩, [], [], [], [], []⟩, []⟩
theorem fromSource_store (r : SourceMatrixPacket.State) :
    (fromSource r).store = Frame.join r.store emptyFrame := rfl
def source : Block 22 := Frame.block 6 SourceEncodedMatrix.block
def rawStart (input : BitString) : SourceAffineSearch.State := fromSource (SourceFamilyLoader.rawStart input)

theorem source_exec (input : BitString) :
    ∃ used after, Exec source (rawStart input).store used (fromSource after).store ∧
      used ≤ SourceEncodedMatrix.sourceBudget input.length ∧
      (core (fromSource after)).core.output = SourceFamilyInput.matrixEncoded input := by
  obtain ⟨used, after, checked, bound, output⟩ := SourceEncodedMatrix.block_exec input
  exact ⟨used, after, Frame.execution checked emptyFrame, bound, output⟩
theorem source_valid (n : Nat) (F : Family n) :
    Exec source (rawStart (codec.encode ⟨n, F⟩)).store (SourceEncodedMatrix.validFuel n F)
      (fromSource (SourceMatrixPacket.result F)).store :=
  Frame.execution (SourceEncodedMatrix.valid_exec n F) emptyFrame

def withScratch (r : SourceAffineSearch.State) (word : BitString) : SourceAffineSearch.State :=
  {r with core := {r.core with remaining := word}}
def inspectMatrix : Block 22 := .seq (.action (.copy 20 8)) (.action (.pop 20))
theorem inspectMatrix_exec (r : SourceAffineSearch.State) :
    Exec inspectMatrix r.store 2 (withScratch r (core r).core.output.tail).store := by
  let copied := withScratch r (core r).core.output
  have first : Exec (.action (.copy (20 : Fin 22) 8)) r.store 1 copied.store := .action _ _
  have second : Exec (.action (.pop (20 : Fin 22))) copied.store 1 (withScratch r (core r).core.output.tail).store := .action _ _
  exact Exec.seq first second

def matrixReady {n : Nat} (F : Family n) : SourceAffineSearch.State :=
  withScratch (fromSource (SourceMatrixPacket.result F)) (affineMatrixPacket F).tail
theorem constructed_output {n : Nat} (F : Family n) :
    (core (fromSource (SourceMatrixPacket.result F))).core.output = affineMatrixPacket F :=
  SourceMatrixPacket.result_output F
theorem inspect_valid {n : Nat} (F : Family n) :
    Exec inspectMatrix (fromSource (SourceMatrixPacket.result F)).store 2 (matrixReady F).store := by
  simpa only [constructed_output, matrixReady] using inspectMatrix_exec (fromSource (SourceMatrixPacket.result F))

theorem matrix_tail_nonempty {n : Nat} (F : Family n) : ∃ bit rest, (affineMatrixPacket F).tail = bit :: rest := by
  have length : 2 ≤ (affineMatrixPacket F).length := by
    rw [affineMatrixPacket, MatrixInputEncoding.codec_length]
    omega
  cases bytes : affineMatrixPacket F with
  | nil => exfalso; simp only [bytes, List.length_nil] at length; omega
  | cons first rest =>
    cases rest with
    | nil => exfalso; simp only [bytes, List.length_cons, List.length_nil] at length; omega
    | cons bit tail => exact ⟨bit, tail, rfl⟩

def resetData : Block 12 := .seq (.action (.copy 0 8)) <| .seq (.action (.clear 1)) <|
  .seq (.action (.clear 2)) (.action (.clear 3))
def resetFlags : Block 12 := .seq (.action (.clear 4)) <| .seq (.action (.clear 5)) <|
  .seq (.action (.clear 6)) (.action (.clear 7))
def resetTail : Block 12 := .seq (.action (.clear 8)) <| .seq (.action (.clear 9)) <|
  .seq (.action (.clear 10)) (.action (.clear 11))
def resetCore : Block 12 := .seq resetData (.seq resetFlags resetTail)

theorem resetCore_exec (r : MatrixReconstruction.State) :
    Exec resetCore r.store 12 (MatrixInputHeaders.start r.core.output).store := by
  let data : MatrixReconstruction.State := {r with core := {r.core with input := r.core.output, target := [], remaining := [], excess := []}}
  let flags : MatrixReconstruction.State := {data with core := {data.core with sign := [], mode := [], active := [], reserved := []}}
  have first : Exec resetData r.store 4 data.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have second : Exec resetFlags data.store 4 flags.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have third : Exec resetTail flags.store 4 (MatrixInputHeaders.start r.core.output).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  exact Exec.seq first (Exec.seq second third)

def protectDimension (r : SourceAffineSearch.State) : SourceAffineSearch.State :=
  {r with core := {r.core with core := {r.core.core with dimension := (core r).width}}}
def prepareSolver : Block 22 := .seq (.action (.copy 14 9)) (lift12 resetCore)
def prepared (r : SourceAffineSearch.State) : SourceAffineSearch.State :=
  setCore (protectDimension r) (MatrixInputHeaders.start (core r).core.output)
theorem prepareSolver_exec (r : SourceAffineSearch.State) :
    Exec prepareSolver r.store 13 (prepared r).store := by
  have saved : Exec (.action (.copy (14 : Fin 22) 9)) r.store 1 (protectDimension r).store := .action _ _
  have reset : Exec (lift12 resetCore) (protectDimension r).store 12 (prepared r).store :=
    lift12_exec resetCore (protectDimension r) 12 _ (resetCore_exec (core r))
  exact Exec.seq saved reset

/-- The ten protected words preserve the original source and constructor state.
Only the first twelve registers are given to the verified linear solver. -/
def saved {n : Nat} (F : Family n) (state : MatrixReconstruction.State) : SourceAffineSearch.State :=
  ⟨⟨⟨⟨state, familyBits F⟩, [], List.replicate n true, List.replicate F.length true⟩,
      [], [], [], [], (affineMatrixPacket F).tail⟩, []⟩
def solverStart {n : Nat} (F : Family n) : SourceAffineSearch.State :=
  saved F (MatrixInputHeaders.start (affineMatrixPacket F))
def solverResult {n : Nat} (F : Family n) : SourceAffineSearch.State :=
  saved F (MatrixSolutionInstructions.result F.length (SourceClosure.affineMaskRows F))

theorem prepared_eq {n : Nat} (F : Family n) : prepared (matrixReady F) = solverStart F := by
  have output : (core (matrixReady F)).core.output = affineMatrixPacket F := constructed_output F
  rw [prepared, output]
  rfl
theorem prepare_valid {n : Nat} (F : Family n) :
    Exec prepareSolver (matrixReady F).store 13 (solverStart F).store := by
  rw [← prepared_eq]
  exact prepareSolver_exec (matrixReady F)
theorem solver_exec {n : Nat} (F : Family n) :
    Exec (lift12 MatrixEncodedSolver.block) (solverStart F).store
      (MatrixEncodedSolver.validFuel F.length (SourceClosure.affineMaskRows F)) (solverResult F).store :=
  lift12_exec _ (solverStart F) _ _ (MatrixEncodedSolver.valid_exec F.length (SourceClosure.affineMaskRows F))

theorem solver_output {n : Nat} (F : Family n) :
    (core (solverResult F)).core.output =
      (MatrixSolutionEncoding.solutionCodec F.length).encode (solve F.length (SourceClosure.affineMaskRows F)) :=
  MatrixSolutionInstructions.result_output F.length (SourceClosure.affineMaskRows F)

theorem result_some (m : Nat) (rows : System m) (s : Space m) (computed : solve m rows = some s) :
    MatrixSolutionInstructions.result m rows = MatrixSolutionSerialization.result s := by
  have exactSpace := MatrixReconstruction.computedSpace_exact m rows
  have same : MatrixReconstruction.computedSpace m rows = s := by
    cases feasible : satisfies (MatrixSweep.residue m rows) () with
    | false =>
      rw [computed, feasible] at exactSpace
      cases exactSpace
    | true =>
      rw [computed, feasible] at exactSpace
      exact (Option.some.inj exactSpace).symm
  simp only [MatrixSolutionInstructions.result, computed, Option.isSome, if_true, same]

end PNP.Concrete.ResidualReduction.SourceAffineInput

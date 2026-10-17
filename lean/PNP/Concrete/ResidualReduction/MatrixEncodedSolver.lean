import PNP.Concrete.ResidualReduction.MatrixInputPreparation

/-! A closed finite-register solver on arbitrary canonical matrix input.
Malformed headers, truncated rows, and trailing bytes terminate with the failure
tag. Valid input is loaded, solved, and serialized by the actual finite program.
The uniform source bound counts every branch and the complete solver execution. -/

namespace PNP.Concrete.ResidualReduction.MatrixEncodedSolver
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixReconstruction
open PNP.Concrete.ResidualReduction.MatrixInputEncoding
open PNP.Concrete.ResidualReduction.MatrixInputFields

def failure : Block 12 := .seq (.action (.clear 8)) (.action (.push 8 false))
def failed (r : State) : State := {r with core := {r.core with output := [false]}}

theorem failure_exec (r : State) : Exec failure r.store 2 (failed r).store :=
  Exec.seq (.action _ _) (.action _ _)

def solveBlock : Block 12 :=
  .seq MatrixInputPreparation.block MatrixSolutionInstructions.phase
def endCheck : Block 12 := .branch 0 solveBlock failure failure
def payloadCheck : Block 12 := .branch 5 failure failure endCheck
def parsed : Block 12 :=
  .seq MatrixInputPayload.seed (.seq MatrixInputPayload.block payloadCheck)
def selection : Block 12 := .branch 4 failure failure parsed
def block : Block 12 := .seq MatrixInputHeaders.block selection

def solverBound (length : Nat) : Nat :=
  80 * length * length * (length + 1) + 5 * length +
    (50 * (length + 2) * (length + 1) + 1) * length + 3 * length + 20

theorem solver_bound (n : Nat) (rows : System n) (length : Nat)
    (dimension : n ≤ length) (count : rows.length ≤ length) :
    MatrixSolutionInstructions.phaseFuel n rows ≤ solverBound length := by
  have checked := MatrixSolutionInstructions.phaseFuel_bound n rows
  have forward : 80 * n * n * (rows.length + 1) ≤ 80 * length * length * (length + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 80 dimension) dimension)
      (Nat.succ_le_succ count)
  have back : (50 * (n + 2) * (n + 1) + 1) * n ≤
      (50 * (length + 2) * (length + 1) + 1) * length :=
    Nat.mul_le_mul (Nat.add_le_add_right
      (Nat.mul_le_mul (Nat.mul_le_mul_left 50 (by omega)) (by omega)) 1) dimension
  unfold solverBound
  omega

def sourceBudget (length : Nat) : Nat :=
  (8 * length + 20) + (1 + (5 + (MatrixInputPayload.fuel length length +
    (2 + ((4 * length + 6) + solverBound length)))))

theorem complete_check (n : Nat) (rows : System n) :
    Exec payloadCheck (MatrixInputPayload.result n rows.length (matrixBits rows)).store
      (2 + ((4 * (matrixBits rows).length + 6) + MatrixSolutionInstructions.phaseFuel n rows))
      (MatrixSolutionInstructions.result n rows).store := by
  have complete := MatrixInputPayload.result_complete n rows.length (matrixBits rows)
    (matrixBits_length rows)
  have flag : (MatrixInputPayload.result n rows.length (matrixBits rows)).store.get 5 = [true] := by
    rw [complete]
    rfl
  have empty : (MatrixInputPayload.result n rows.length (matrixBits rows)).store.get 0 = [] := by
    rw [complete]
    rfl
  have cost : 2 + ((4 * (matrixBits rows).length + 6) + MatrixSolutionInstructions.phaseFuel n rows) =
      1 + (1 + ((4 * (matrixBits rows).length + 6) + MatrixSolutionInstructions.phaseFuel n rows)) := by omega
  rw [cost]
  exact Exec.one flag (Exec.empty empty
    (Exec.seq (MatrixInputPreparation.matrix_exec n rows) (MatrixSolutionInstructions.phase_exec n rows)))

theorem short_check (n count : Nat) (input : BitString)
    (short : ¬ (n + 1) * count ≤ input.length) :
    Exec payloadCheck (MatrixInputPayload.result n count input).store 3
      (failed (MatrixInputPayload.result n count input)).store := by
  have flag : (MatrixInputPayload.result n count input).store.get 5 = [] := by
    change (if (n + 1) * count ≤ input.length then [true] else []) = []
    rw [if_neg short]
  exact Exec.empty flag (failure_exec _)

theorem extra_check (n count : Nat) (input : BitString)
    (enough : (n + 1) * count ≤ input.length)
    (wrong : input.length ≠ (n + 1) * count) :
    Exec payloadCheck (MatrixInputPayload.result n count input).store 4
      (failed (MatrixInputPayload.result n count input)).store := by
  have flag : (MatrixInputPayload.result n count input).store.get 5 = [true] := by
    change (if (n + 1) * count ≤ input.length then [true] else []) = [true]
    rw [if_pos enough]
  have nonempty : input.drop ((n + 1) * count) ≠ [] := by
    intro empty
    have bound := List.drop_eq_nil_iff.mp empty
    omega
  cases tail : input.drop ((n + 1) * count) with
  | nil => exact (nonempty tail).elim
  | cons bit rest =>
    cases bit
    · have read : (MatrixInputPayload.result n count input).store.get 0 = false :: rest := tail
      exact Exec.one flag (Exec.zero read (failure_exec _))
    · have read : (MatrixInputPayload.result n count input).store.get 0 = true :: rest := tail
      exact Exec.one flag (Exec.one read (failure_exec _))

def validFuel (n : Nat) (rows : System n) : Nat :=
  MatrixInputHeaders.fuel (codec.encode ⟨n, rows⟩) +
    (1 + (5 + (MatrixInputPayload.fuel n rows.length +
      (2 + ((4 * (matrixBits rows).length + 6) + MatrixSolutionInstructions.phaseFuel n rows)))))

theorem valid_exec (n : Nat) (rows : System n) :
    Exec block (MatrixInputHeaders.start (codec.encode ⟨n, rows⟩)).store (validFuel n rows)
      (MatrixSolutionInstructions.result n rows).store := by
  let input := codec.encode ⟨n, rows⟩
  have success : (fields input).terminated = true := by rw [canonical_fields]
  have seed : Exec MatrixInputPayload.seed (MatrixInputHeaders.result input).store 5
      (MatrixInputPayload.start n rows.length (matrixBits rows)).store := by
    simpa only [input, canonical_fields] using MatrixInputPayload.seed_exec input success
  have flag : (MatrixInputHeaders.result input).store.get 4 = [true] := by
    change (if (fields input).terminated then [true] else []) = [true]
    rw [success]
    rfl
  exact Exec.seq (MatrixInputHeaders.block_exec input)
    (Exec.one flag (Exec.seq seed (Exec.seq (MatrixInputPayload.block_exec n rows.length (matrixBits rows))
      (complete_check n rows))))

theorem validFuel_bound (n : Nat) (rows : System n) :
    validFuel n rows ≤ sourceBudget (codec.encode ⟨n, rows⟩).length := by
  have dimension := dimension_bound n rows
  have count := rowCount_bound n rows
  have payload := payload_bound n rows
  have header := MatrixInputHeaders.fuel_bound (codec.encode ⟨n, rows⟩)
  have read := MatrixInputPayload.fuel_input_bound n rows.length (codec.encode ⟨n, rows⟩).length
    dimension count
  have solve := solver_bound n rows (codec.encode ⟨n, rows⟩).length dimension count
  unfold validFuel sourceBudget
  omega

theorem failed_header (input : BitString) (bad : (fields input).terminated = false) :
    ∃ fuel : Nat, ∃ after : State, Exec block (MatrixInputHeaders.start input).store fuel after.store ∧
      fuel ≤ sourceBudget input.length ∧ after.core.output = solveEncoded input := by
  have flag : (MatrixInputHeaders.result input).store.get 4 = [] := by
    change (if (fields input).terminated then [true] else []) = []
    rw [bad]
    rfl
  refine ⟨MatrixInputHeaders.fuel input + 3, failed (MatrixInputHeaders.result input),
    Exec.seq (MatrixInputHeaders.block_exec input) (Exec.empty flag (failure_exec _)), ?_, ?_⟩
  · have header := MatrixInputHeaders.fuel_bound input
    unfold sourceBudget
    omega
  · rw [solveEncoded, decode_none_header input bad]
    rfl

theorem failed_payload (input : BitString) (success : (fields input).terminated = true)
    (wrong : (fields input).payload.length ≠ ((fields input).dimension + 1) * (fields input).rows) :
    ∃ fuel : Nat, ∃ after : State, Exec block (MatrixInputHeaders.start input).store fuel after.store ∧
      fuel ≤ sourceBudget input.length ∧ after.core.output = solveEncoded input := by
  let f := fields input
  let loaded := MatrixInputPayload.result f.dimension f.rows f.payload
  have rejected : ∃ fuel, Exec payloadCheck loaded.store fuel (failed loaded).store ∧ fuel ≤ 4 := by
    by_cases enough : (f.dimension + 1) * f.rows ≤ f.payload.length
    · exact ⟨4, extra_check f.dimension f.rows f.payload enough wrong, Nat.le_refl 4⟩
    · exact ⟨3, short_check f.dimension f.rows f.payload enough, by decide⟩
  obtain ⟨lastFuel, last, lastBound⟩ := rejected
  have flag : (MatrixInputHeaders.result input).store.get 4 = [true] := by
    change (if (fields input).terminated then [true] else []) = [true]
    rw [success]
    rfl
  refine ⟨MatrixInputHeaders.fuel input + (1 + (5 + (MatrixInputPayload.fuel f.dimension f.rows + lastFuel))),
    failed loaded, Exec.seq (MatrixInputHeaders.block_exec input)
      (Exec.one flag (Exec.seq (MatrixInputPayload.seed_exec input success)
        (Exec.seq (MatrixInputPayload.block_exec f.dimension f.rows f.payload) last))), ?_, ?_⟩
  · have sizes := size_bounds input
    have header := MatrixInputHeaders.fuel_bound input
    have read := MatrixInputPayload.fuel_input_bound f.dimension f.rows input.length sizes.1 sizes.2.1
    unfold sourceBudget
    omega
  · rw [solveEncoded, decode_none_length input wrong]
    rfl

theorem block_exec (input : BitString) :
    ∃ fuel : Nat, ∃ after : State, Exec block (MatrixInputHeaders.start input).store fuel after.store ∧
      fuel ≤ sourceBudget input.length ∧ after.core.output = solveEncoded input := by
  cases success : (fields input).terminated with
  | false => exact failed_header input success
  | true =>
    by_cases length : (fields input).payload.length = ((fields input).dimension + 1) * (fields input).rows
    · obtain ⟨rows, _, _, bytes⟩ := valid_payload input success length
      generalize nEq : (fields input).dimension = n at rows bytes
      rw [← bytes]
      refine ⟨validFuel n rows, MatrixSolutionInstructions.result n rows,
        valid_exec n rows, validFuel_bound n rows, ?_⟩
      rw [solveEncoded_valid]
      exact MatrixSolutionInstructions.result_output n rows
    · exact failed_payload input success length

end PNP.Concrete.ResidualReduction.MatrixEncodedSolver

import PNP.Concrete.ResidualReduction.MatrixEncodedSolver

/-! A reusable literal matrix-input boundary. The consumer is a fixed finite
instruction block, never an executable semantic callback. Its specification
and cost appear only in execution theorems. Every header, payload, truncation
and trailing-byte check is performed before the consumer is entered. -/

namespace PNP.Concrete.ResidualReduction.MatrixInputConsumer
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixReconstruction
open PNP.Concrete.ResidualReduction.MatrixInputEncoding
open PNP.Concrete.ResidualReduction.MatrixInputFields
open PNP.Concrete.ResidualReduction.MatrixEncodedSolver (failure failed failure_exec)

def endCheck (consumer : Block 12) : Block 12 :=
  .branch 0 (.seq MatrixInputPreparation.block consumer) failure failure
def payloadCheck (consumer : Block 12) : Block 12 := .branch 5 failure failure (endCheck consumer)
def parsed (consumer : Block 12) : Block 12 :=
  .seq MatrixInputPayload.seed (.seq MatrixInputPayload.block (payloadCheck consumer))
def selection (consumer : Block 12) : Block 12 := .branch 4 failure failure (parsed consumer)
def block (consumer : Block 12) : Block 12 := .seq MatrixInputHeaders.block (selection consumer)

def loadFuel (n : Nat) (rows : System n) : Nat :=
  MatrixInputHeaders.fuel (codec.encode ⟨n, rows⟩) +
    (1 + (5 + (MatrixInputPayload.fuel n rows.length + (2 + (4 * (matrixBits rows).length + 6)))))
def loadBudget (L : Nat) : Nat :=
  (8 * L + 20) + (1 + (5 + (MatrixInputPayload.fuel L L + (2 + (4 * L + 6)))))

theorem complete_check (consumer : Block 12) (n : Nat) (rows : System n) (used : Nat) (after : State)
    (checked : Exec consumer (MatrixSolutionInstructions.start n rows).store used after.store) :
    Exec (payloadCheck consumer) (MatrixInputPayload.result n rows.length (matrixBits rows)).store
      (2 + ((4 * (matrixBits rows).length + 6) + used)) after.store := by
  have complete := MatrixInputPayload.result_complete n rows.length (matrixBits rows) (matrixBits_length rows)
  have flag : (MatrixInputPayload.result n rows.length (matrixBits rows)).store.get 5 = [true] := by rw [complete]; rfl
  have empty : (MatrixInputPayload.result n rows.length (matrixBits rows)).store.get 0 = [] := by rw [complete]; rfl
  have run : Exec (payloadCheck consumer) (MatrixInputPayload.result n rows.length (matrixBits rows)).store
      (1 + (1 + ((4 * (matrixBits rows).length + 6) + used))) after.store :=
    Exec.one flag (Exec.empty empty (Exec.seq (MatrixInputPreparation.matrix_exec n rows) checked))
  have cost : 2 + ((4 * (matrixBits rows).length + 6) + used) =
      1 + (1 + ((4 * (matrixBits rows).length + 6) + used)) := by omega
  rw [cost]
  exact run

theorem valid_exec (consumer : Block 12) (n : Nat) (rows : System n) (used : Nat) (after : State)
    (checked : Exec consumer (MatrixSolutionInstructions.start n rows).store used after.store) :
    Exec (block consumer) (MatrixInputHeaders.start (codec.encode ⟨n, rows⟩)).store
      (loadFuel n rows + used) after.store := by
  let input := codec.encode ⟨n, rows⟩
  have success : (fields input).terminated = true := by rw [canonical_fields]
  have seed : Exec MatrixInputPayload.seed (MatrixInputHeaders.result input).store 5
      (MatrixInputPayload.start n rows.length (matrixBits rows)).store := by
    simpa only [input, canonical_fields] using MatrixInputPayload.seed_exec input success
  have flag : (MatrixInputHeaders.result input).store.get 4 = [true] := by
    change (if (fields input).terminated then [true] else []) = [true]
    rw [success]
    rfl
  have run : Exec (block consumer) (MatrixInputHeaders.start input).store
      (MatrixInputHeaders.fuel input + (1 + (5 + (MatrixInputPayload.fuel n rows.length + (2 + ((4 * (matrixBits rows).length + 6) + used)))))) after.store :=
    Exec.seq (MatrixInputHeaders.block_exec input)
    (Exec.one flag (Exec.seq seed (Exec.seq (MatrixInputPayload.block_exec n rows.length (matrixBits rows))
      (complete_check consumer n rows used after checked))))
  simpa only [block, selection, parsed, loadFuel, input, Nat.add_assoc] using run

theorem loadFuel_bound (n : Nat) (rows : System n) : loadFuel n rows ≤ loadBudget (codec.encode ⟨n, rows⟩).length := by
  have header := MatrixInputHeaders.fuel_bound (codec.encode ⟨n, rows⟩)
  have payload := payload_bound n rows
  have read := MatrixInputPayload.fuel_input_bound n rows.length (codec.encode ⟨n, rows⟩).length
    (dimension_bound n rows) (rowCount_bound n rows)
  unfold loadFuel loadBudget
  omega

theorem short_check (consumer : Block 12) (n count : Nat) (input : BitString)
    (short : ¬ (n + 1) * count ≤ input.length) :
    Exec (payloadCheck consumer) (MatrixInputPayload.result n count input).store 3
      (failed (MatrixInputPayload.result n count input)).store := by
  have flag : (MatrixInputPayload.result n count input).store.get 5 = [] := by
    change (if (n + 1) * count ≤ input.length then [true] else []) = []
    rw [if_neg short]
  exact Exec.empty flag (failure_exec _)
theorem extra_check (consumer : Block 12) (n count : Nat) (input : BitString)
    (enough : (n + 1) * count ≤ input.length) (wrong : input.length ≠ (n + 1) * count) :
    Exec (payloadCheck consumer) (MatrixInputPayload.result n count input).store 4
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

def encodedValue (value : (n : Nat) → System n → BitString) (input : BitString) : BitString :=
  match codec.decode input with
  | none => [false]
  | some ⟨n, rows⟩ => value n rows

theorem failed_header (consumer : Block 12) (value : (n : Nat) → System n → BitString)
    (input : BitString) (bad : (fields input).terminated = false) :
    ∃ used : Nat, ∃ after : State, Exec (block consumer) (MatrixInputHeaders.start input).store used after.store ∧
      used ≤ loadBudget input.length ∧ after.core.output = encodedValue value input := by
  have flag : (MatrixInputHeaders.result input).store.get 4 = [] := by
    change (if (fields input).terminated then [true] else []) = []
    rw [bad]
    rfl
  refine ⟨MatrixInputHeaders.fuel input + 3, failed (MatrixInputHeaders.result input),
    Exec.seq (MatrixInputHeaders.block_exec input) (Exec.empty flag (failure_exec _)), ?_, ?_⟩
  · have header := MatrixInputHeaders.fuel_bound input
    unfold loadBudget
    omega
  · rw [encodedValue, decode_none_header input bad]
    rfl

theorem failed_payload (consumer : Block 12) (value : (n : Nat) → System n → BitString)
    (input : BitString) (success : (fields input).terminated = true)
    (wrong : (fields input).payload.length ≠ ((fields input).dimension + 1) * (fields input).rows) :
    ∃ used : Nat, ∃ after : State, Exec (block consumer) (MatrixInputHeaders.start input).store used after.store ∧
      used ≤ loadBudget input.length ∧ after.core.output = encodedValue value input := by
  let f := fields input
  let loaded := MatrixInputPayload.result f.dimension f.rows f.payload
  have rejected : ∃ used, Exec (payloadCheck consumer) loaded.store used (failed loaded).store ∧ used ≤ 4 := by
    by_cases enough : (f.dimension + 1) * f.rows ≤ f.payload.length
    · exact ⟨4, extra_check consumer f.dimension f.rows f.payload enough wrong, Nat.le_refl 4⟩
    · exact ⟨3, short_check consumer f.dimension f.rows f.payload enough, by decide⟩
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
    unfold loadBudget
    omega
  · rw [encodedValue, decode_none_length input wrong]
    rfl

/-- The consumer specification is proved separately for the actual fixed
block. Neither this proposition nor value becomes a machine instruction. -/
theorem block_exec (consumer : Block 12) (value : (n : Nat) → System n → BitString) (consumerBudget : Nat → Nat)
    (ready : ∀ n rows, ∃ used : Nat, ∃ after : State,
      Exec consumer (MatrixSolutionInstructions.start n rows).store used after.store ∧
      used ≤ consumerBudget (codec.encode ⟨n, rows⟩).length ∧ after.core.output = value n rows)
    (input : BitString) :
    ∃ used : Nat, ∃ after : State, Exec (block consumer) (MatrixInputHeaders.start input).store used after.store ∧
      used ≤ loadBudget input.length + consumerBudget input.length ∧ after.core.output = encodedValue value input := by
  cases success : (fields input).terminated with
  | false =>
    obtain ⟨used, after, run, bound, output⟩ := failed_header consumer value input success
    exact ⟨used, after, run, by omega, output⟩
  | true =>
    by_cases length : (fields input).payload.length = ((fields input).dimension + 1) * (fields input).rows
    · obtain ⟨rows, _, _, bytes⟩ := valid_payload input success length
      generalize nEq : (fields input).dimension = n at rows bytes
      rw [← bytes]
      obtain ⟨used, after, checked, bound, output⟩ := ready n rows
      refine ⟨loadFuel n rows + used, after, valid_exec consumer n rows used after checked,
        Nat.add_le_add (loadFuel_bound n rows) bound, ?_⟩
      rw [encodedValue, roundtrip]
      exact output
    · obtain ⟨used, after, run, bound, output⟩ := failed_payload consumer value input success length
      exact ⟨used, after, run, by omega, output⟩

end PNP.Concrete.ResidualReduction.MatrixInputConsumer

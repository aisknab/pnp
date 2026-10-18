import PNP.Concrete.ResidualReduction.SourceFamilyLoader

/-! A closed source-derived matrix constructor on arbitrary input bitstrings.
Its polynomial source bound includes all parsing and rejection branches,
coefficient reads, both unbounded coordinate loops, and canonical output.
No equation matrix or family correctness certificate is supplied. -/

namespace PNP.Concrete.ResidualReduction.SourceEncodedMatrix
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixPacket (State setCore lift12)
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceFamilyInput (matrixEncoded)
open PNP.Concrete.ResidualReduction.MatrixInputFields (fields size_bounds)

def failure : Block 16 := .seq (.action (.clear 8)) (.action (.push 8 false))
def failed (r : State) : State := setCore r {r.core.core.core with output := [false]}
theorem failure_exec (r : State) : Exec failure r.store 2 (failed r).store :=
  Exec.seq (.action _ _) (.action _ _)

def construct : Block 16 := .seq SourceFamilyLoader.prepare SourceMatrixPacket.block
def endCheck : Block 16 := .branch 0 construct failure failure
def payloadCheck : Block 16 := .branch 5 failure failure endCheck
def parsed : Block 16 := .seq SourceFamilyLoader.seed (.seq SourceFamilyLoader.block payloadCheck)
def selection : Block 16 := .branch 4 failure failure parsed
def block : Block 16 := .seq (lift12 MatrixInputHeaders.block) selection

theorem loaderFuel_bound (n count length : Nat) (dimension : n ≤ length) (rows : count ≤ length) :
    SourceFamilyLoader.fuel n count ≤ SourceFamilyLoader.fuel length length := by
  have counter := Nat.mul_le_mul (show 3 * (2 * n + 3) + 4 ≤ 3 * (2 * length + 3) + 4 by omega) rows
  have payload := Nat.mul_le_mul (show 2 * n + 3 ≤ 2 * length + 3 by omega) rows
  unfold SourceFamilyLoader.fuel
  omega

def sourceBudget (length : Nat) : Nat := (8 * length + 20) +
  (1 + ((3 * length + 12) + (SourceFamilyLoader.fuel length length +
    (2 + ((4 * length + 5) + SourceMatrixPacket.budget length length)))))

theorem complete_check (n : Nat) (F : Family n) :
    Exec payloadCheck (SourceFamilyLoader.result n F.length (familyBits F)).store
      (2 + ((4 * (familyBits F).length + 5) + SourceMatrixPacket.fuel n F.length))
      (SourceMatrixPacket.result F).store := by
  have complete := SourceFamilyLoader.result_complete n F.length (familyBits F) (familyBits_length F)
  have flag : (SourceFamilyLoader.result n F.length (familyBits F)).store.get 5 = [true] := by
    rw [complete]; rfl
  have empty : (SourceFamilyLoader.result n F.length (familyBits F)).store.get 0 = [] := by
    rw [complete]; rfl
  have prepare : Exec SourceFamilyLoader.prepare (SourceFamilyLoader.result n F.length (familyBits F)).store
      (4 * (familyBits F).length + 5) (SourceMatrixPacket.inputState F).store := by
    rw [complete, ← SourceFamilyLoader.prepared_family]
    exact SourceFamilyLoader.prepare_exec n F.length (familyBits F)
  have cost : 2 + ((4 * (familyBits F).length + 5) + SourceMatrixPacket.fuel n F.length) =
      1 + (1 + ((4 * (familyBits F).length + 5) + SourceMatrixPacket.fuel n F.length)) := by omega
  rw [cost]
  exact Exec.one flag (Exec.empty empty (Exec.seq prepare (SourceMatrixPacket.block_exec F)))

theorem short_check (n count : Nat) (input : BitString)
    (short : ¬ (2 * n + 3) * count ≤ input.length) :
    Exec payloadCheck (SourceFamilyLoader.result n count input).store 3
      (failed (SourceFamilyLoader.result n count input)).store := by
  have flag : (SourceFamilyLoader.result n count input).store.get 5 = [] := by
    change (if (2 * n + 3) * count ≤ input.length then [true] else []) = []
    rw [if_neg short]
  exact Exec.empty flag (failure_exec _)

theorem extra_check (n count : Nat) (input : BitString)
    (enough : (2 * n + 3) * count ≤ input.length) (wrong : input.length ≠ (2 * n + 3) * count) :
    Exec payloadCheck (SourceFamilyLoader.result n count input).store 4
      (failed (SourceFamilyLoader.result n count input)).store := by
  have flag : (SourceFamilyLoader.result n count input).store.get 5 = [true] := by
    change (if (2 * n + 3) * count ≤ input.length then [true] else []) = [true]
    rw [if_pos enough]
  have nonempty : input.drop ((2 * n + 3) * count) ≠ [] := by
    intro empty
    have bound := List.drop_eq_nil_iff.mp empty
    omega
  cases tail : input.drop ((2 * n + 3) * count) with
  | nil => exact (nonempty tail).elim
  | cons bit rest =>
    cases bit
    · have read : (SourceFamilyLoader.result n count input).store.get 0 = false :: rest := tail
      exact Exec.one flag (Exec.zero read (failure_exec _))
    · have read : (SourceFamilyLoader.result n count input).store.get 0 = true :: rest := tail
      exact Exec.one flag (Exec.one read (failure_exec _))

def validFuel (n : Nat) (F : Family n) : Nat := MatrixInputHeaders.fuel (codec.encode ⟨n, F⟩) +
  (1 + ((3 * n + 12) + (SourceFamilyLoader.fuel n F.length +
    (2 + ((4 * (familyBits F).length + 5) + SourceMatrixPacket.fuel n F.length)))))

theorem valid_exec (n : Nat) (F : Family n) :
    Exec block (SourceFamilyLoader.rawStart (codec.encode ⟨n, F⟩)).store (validFuel n F)
      (SourceMatrixPacket.result F).store := by
  let input := codec.encode ⟨n, F⟩
  have success : (fields input).terminated = true := by rw [SourceFamilyInput.canonical_fields]
  have seed : Exec SourceFamilyLoader.seed (SourceFamilyLoader.rawHeaders input).store (3 * n + 12)
      (SourceFamilyLoader.start n F.length (familyBits F)).store := by
    rw [SourceFamilyLoader.headers_valid input success, SourceFamilyInput.canonical_fields]
    exact SourceFamilyLoader.seed_exec n F.length (familyBits F)
  have flag : (SourceFamilyLoader.rawHeaders input).store.get 4 = [true] := by
    change (if (fields input).terminated then [true] else []) = [true]
    rw [success]; rfl
  exact Exec.seq (SourceFamilyLoader.headers_exec input)
    (Exec.one flag (Exec.seq seed (Exec.seq (SourceFamilyLoader.block_exec n F.length (familyBits F))
      (complete_check n F))))

theorem validFuel_bound (n : Nat) (F : Family n) : validFuel n F ≤ sourceBudget (codec.encode ⟨n, F⟩).length := by
  have dimension := dimension_bound n F
  have count := rowCount_bound n F
  have payload : (familyBits F).length ≤ (codec.encode ⟨n, F⟩).length := by
    rw [familyBits_length, codec_length]; omega
  have header := MatrixInputHeaders.fuel_bound (codec.encode ⟨n, F⟩)
  have read := loaderFuel_bound n F.length (codec.encode ⟨n, F⟩).length dimension count
  have matrix := SourceMatrixPacket.original_input_fuel_bound n F
  unfold validFuel sourceBudget
  omega

theorem failed_header (input : BitString) (bad : (fields input).terminated = false) :
    ∃ fuel : Nat, ∃ after : State, Exec block (SourceFamilyLoader.rawStart input).store fuel after.store ∧
      fuel ≤ sourceBudget input.length ∧ after.core.core.core.output = matrixEncoded input := by
  have flag : (SourceFamilyLoader.rawHeaders input).store.get 4 = [] := by
    change (if (fields input).terminated then [true] else []) = []
    rw [bad]; rfl
  refine ⟨MatrixInputHeaders.fuel input + 3, failed (SourceFamilyLoader.rawHeaders input),
    Exec.seq (SourceFamilyLoader.headers_exec input) (Exec.empty flag (failure_exec _)), ?_, ?_⟩
  · have header := MatrixInputHeaders.fuel_bound input
    unfold sourceBudget
    omega
  · rw [matrixEncoded, SourceFamilyInput.decode_none_header input bad]
    rfl

theorem failed_payload (input : BitString) (success : (fields input).terminated = true)
    (wrong : (fields input).payload.length ≠ (2 * (fields input).dimension + 3) * (fields input).rows) :
    ∃ fuel : Nat, ∃ after : State, Exec block (SourceFamilyLoader.rawStart input).store fuel after.store ∧
      fuel ≤ sourceBudget input.length ∧ after.core.core.core.output = matrixEncoded input := by
  let f := fields input
  let loaded := SourceFamilyLoader.result f.dimension f.rows f.payload
  have rejected : ∃ fuel, Exec payloadCheck loaded.store fuel (failed loaded).store ∧ fuel ≤ 4 := by
    by_cases enough : (2 * f.dimension + 3) * f.rows ≤ f.payload.length
    · exact ⟨4, extra_check f.dimension f.rows f.payload enough wrong, Nat.le_refl 4⟩
    · exact ⟨3, short_check f.dimension f.rows f.payload enough, by decide⟩
  obtain ⟨lastFuel, last, lastBound⟩ := rejected
  have seed : Exec SourceFamilyLoader.seed (SourceFamilyLoader.rawHeaders input).store (3 * f.dimension + 12)
      (SourceFamilyLoader.start f.dimension f.rows f.payload).store := by
    rw [SourceFamilyLoader.headers_valid input success]
    exact SourceFamilyLoader.seed_exec f.dimension f.rows f.payload
  have flag : (SourceFamilyLoader.rawHeaders input).store.get 4 = [true] := by
    change (if (fields input).terminated then [true] else []) = [true]
    rw [success]; rfl
  refine ⟨MatrixInputHeaders.fuel input + (1 + ((3 * f.dimension + 12) + (SourceFamilyLoader.fuel f.dimension f.rows + lastFuel))),
    failed loaded, Exec.seq (SourceFamilyLoader.headers_exec input)
      (Exec.one flag (Exec.seq seed (Exec.seq (SourceFamilyLoader.block_exec f.dimension f.rows f.payload) last))), ?_, ?_⟩
  · have sizes := size_bounds input
    have header := MatrixInputHeaders.fuel_bound input
    have read := loaderFuel_bound f.dimension f.rows input.length sizes.1 sizes.2.1
    unfold sourceBudget
    dsimp only [f] at *
    omega
  · rw [matrixEncoded, SourceFamilyInput.decode_none_length input wrong]
    rfl

theorem block_exec (input : BitString) :
    ∃ fuel : Nat, ∃ after : State, Exec block (SourceFamilyLoader.rawStart input).store fuel after.store ∧
      fuel ≤ sourceBudget input.length ∧ after.core.core.core.output = matrixEncoded input := by
  cases success : (fields input).terminated with
  | false => exact failed_header input success
  | true =>
    by_cases length : (fields input).payload.length = (2 * (fields input).dimension + 3) * (fields input).rows
    · obtain ⟨F, _, _, bytes⟩ := SourceFamilyInput.valid_payload input success length
      generalize nEq : (fields input).dimension = n at F bytes
      rw [← bytes]
      refine ⟨validFuel n F, SourceMatrixPacket.result F, valid_exec n F, validFuel_bound n F, ?_⟩
      rw [SourceFamilyInput.matrixEncoded_canonical]
      exact SourceMatrixPacket.result_output F
    · exact failed_payload input success length

end PNP.Concrete.ResidualReduction.SourceEncodedMatrix

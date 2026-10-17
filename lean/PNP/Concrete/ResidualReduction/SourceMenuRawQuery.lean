import PNP.Concrete.ResidualReduction.SourceMenuInput
import PNP.Concrete.ResidualReduction.SourceEncodedMatrix

/-! Closed raw-input execution of the source-derived sorted-menu constructor.
Every input branch is charged: both unary headers, exact row payload length,
menu generation, sorting, counted serialization, and malformed-input rejection.
Only the loader and failure block are reused from the matrix constructor. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuRaw
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceMatrixPacket (State)
open PNP.Concrete.ResidualReduction.MatrixInputFields (fields size_bounds)
open PNP.Concrete.ResidualReduction.SourceEncodedMatrix (failure failed failure_exec loaderFuel_bound)
open PNP.Concrete.ResidualReduction.SourceMenuInput (answer)

def endCheck : Block 16 := .branch 0 construct failure failure
def payloadCheck : Block 16 := .branch 5 failure failure endCheck
def parsed : Block 16 := .seq SourceFamilyLoader.seed (.seq SourceFamilyLoader.block payloadCheck)
def selection : Block 16 := .branch 4 failure failure parsed
def block : Block 16 := .seq (SourceMatrixPacket.lift12 MatrixInputHeaders.block) selection
def sourceBudget (L : Nat) : Nat := (8 * L + 20) +
  (1 + ((3 * L + 12) + (SourceFamilyLoader.fuel L L + (2 + constructBudget L))))

theorem complete_check (n : Nat) (F : Family n) :
    ∃ used after, Exec payloadCheck (SourceFamilyLoader.result n F.length (familyBits F)).store
      (2 + used) after ∧ after.get 8 = MatrixInputEncoding.codec.encode ⟨n, SourceChain.sourceMenu F⟩ ∧
      used ≤ constructBudget (codec.encode ⟨n, F⟩).length := by
  have complete := SourceFamilyLoader.result_complete n F.length (familyBits F) (familyBits_length F)
  obtain ⟨used, after, checked, output, bound⟩ := construct_exec F
  refine ⟨used, after, ?_, output, bound⟩
  have cost : 2 + used = 1 + (1 + used) := by omega
  rw [complete, cost]
  exact Exec.one rfl (Exec.empty rfl checked)

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

theorem valid_exec (n : Nat) (F : Family n) :
    ∃ used after, Exec block (SourceFamilyLoader.rawStart (codec.encode ⟨n, F⟩)).store used after ∧
      used ≤ sourceBudget (codec.encode ⟨n, F⟩).length ∧
      after.get 8 = MatrixInputEncoding.codec.encode ⟨n, SourceChain.sourceMenu F⟩ := by
  let input := codec.encode ⟨n, F⟩
  have success : (fields input).terminated = true := by rw [SourceFamilyInput.canonical_fields]
  have seed : Exec SourceFamilyLoader.seed (SourceFamilyLoader.rawHeaders input).store (3 * n + 12)
      (SourceFamilyLoader.start n F.length (familyBits F)).store := by
    rw [SourceFamilyLoader.headers_valid input success, SourceFamilyInput.canonical_fields]
    exact SourceFamilyLoader.seed_exec n F.length (familyBits F)
  have flag : (SourceFamilyLoader.rawHeaders input).store.get 4 = [true] := by
    change (if (fields input).terminated then [true] else []) = [true]
    rw [success]; rfl
  obtain ⟨used, after, checked, output, bound⟩ := complete_check n F
  refine ⟨MatrixInputHeaders.fuel input + (1 + ((3 * n + 12) +
      (SourceFamilyLoader.fuel n F.length + (2 + used)))), after,
    Exec.seq (SourceFamilyLoader.headers_exec input)
      (Exec.one flag (Exec.seq seed (Exec.seq (SourceFamilyLoader.block_exec n F.length (familyBits F)) checked))),
    ?_, output⟩
  have header := MatrixInputHeaders.fuel_bound input
  have dimension := dimension_bound n F
  have loader := loaderFuel_bound n F.length input.length
    (dimension_bound n F) (rowCount_bound n F)
  unfold sourceBudget
  dsimp only [input] at *
  omega

theorem failed_header (input : BitString) (bad : (fields input).terminated = false) :
    ∃ used after, Exec block (SourceFamilyLoader.rawStart input).store used after ∧
      used ≤ sourceBudget input.length ∧ after.get 8 = answer input := by
  have flag : (SourceFamilyLoader.rawHeaders input).store.get 4 = [] := by
    change (if (fields input).terminated then [true] else []) = []
    rw [bad]; rfl
  refine ⟨MatrixInputHeaders.fuel input + 3, (failed (SourceFamilyLoader.rawHeaders input)).store,
    Exec.seq (SourceFamilyLoader.headers_exec input) (Exec.empty flag (failure_exec _)), ?_, ?_⟩
  · have header := MatrixInputHeaders.fuel_bound input
    unfold sourceBudget
    omega
  · rw [SourceMenuInput.answer_malformed input (SourceFamilyInput.decode_none_header input bad)]
    rfl

theorem failed_payload (input : BitString) (success : (fields input).terminated = true)
    (wrong : (fields input).payload.length ≠ (2 * (fields input).dimension + 3) * (fields input).rows) :
    ∃ used after, Exec block (SourceFamilyLoader.rawStart input).store used after ∧
      used ≤ sourceBudget input.length ∧ after.get 8 = answer input := by
  let f := fields input
  let loaded := SourceFamilyLoader.result f.dimension f.rows f.payload
  have rejected : ∃ used, Exec payloadCheck loaded.store used (failed loaded).store ∧ used ≤ 4 := by
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
  refine ⟨MatrixInputHeaders.fuel input + (1 + ((3 * f.dimension + 12) +
      (SourceFamilyLoader.fuel f.dimension f.rows + lastFuel))), (failed loaded).store,
    Exec.seq (SourceFamilyLoader.headers_exec input)
      (Exec.one flag (Exec.seq seed (Exec.seq (SourceFamilyLoader.block_exec f.dimension f.rows f.payload) last))),
    ?_, ?_⟩
  · have sizes := size_bounds input
    have header := MatrixInputHeaders.fuel_bound input
    have loader := loaderFuel_bound f.dimension f.rows input.length sizes.1 sizes.2.1
    unfold sourceBudget constructBudget
    dsimp only [f] at *
    omega
  · rw [SourceMenuInput.answer_malformed input (SourceFamilyInput.decode_none_length input wrong)]
    rfl

theorem block_exec (input : BitString) :
    ∃ used after, Exec block (SourceFamilyLoader.rawStart input).store used after ∧
      used ≤ sourceBudget input.length ∧ after.get 8 = answer input := by
  cases success : (fields input).terminated with
  | false => exact failed_header input success
  | true =>
    by_cases length : (fields input).payload.length = (2 * (fields input).dimension + 3) * (fields input).rows
    · obtain ⟨F, _, _, bytes⟩ := SourceFamilyInput.valid_payload input success length
      generalize nEq : (fields input).dimension = n at F bytes
      rw [← bytes, SourceMenuInput.answer_canonical]
      exact valid_exec n F
    · exact failed_payload input success length

end PNP.Concrete.ResidualReduction.SourceMenuRaw

import PNP.Concrete.ResidualReduction.SourcePlaneRawBridge

/-! Complete raw-input plane-query execution. The existing parser's literal
blocks are reused with a protected normal-count word. Both malformed data and
wrong normal counts are charged, as are construction, search and output lift. -/

namespace PNP.Concrete.ResidualReduction.SourcePlaneRaw
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirectionInput
open PNP.Concrete.ResidualReduction.SourceDirectionLoader
open PNP.Concrete.ResidualReduction.SourceDirectionInstructions (State solver small)
open PNP.Concrete.ResidualReduction.SourcePlaneInput (answer)
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding (codec)

def endCheck : Block 29 := .branch 0 construct failure failure
def familyCheck : Block 29 := .branch 5 failure failure endCheck
def familyParsed : Block 29 := .seq (lift (loader SourceFamilyLoader.seed))
  (.seq (lift (loader SourceFamilyLoader.block)) familyCheck)
def familySelection : Block 29 := .branch 4 failure failure familyParsed
def readFamily : Block 29 := .seq (lift preserve) (.seq (lift (small MatrixStrictHeader.block)) familySelection)
def normalSelection : Block 29 := .branch 5 failure failure readFamily
def normalParsed : Block 29 := .seq (lift (solver MatrixInputPayload.seed))
  (.seq (lift (solver MatrixInputPayload.block)) normalSelection)
def selection : Block 29 := .branch 4 failure failure normalParsed
def block : Block 29 := .seq (lift (solver MatrixInputHeaders.block)) (.seq saveCount selection)
def start (input : BitString) : Store 29 := framed (rawStart input) 0

def completionBudget (L : Nat) : Nat := 2 + constructBudget L
def familyBudget (L : Nat) : Nat := 1 + ((3 * L + 12) +
  (SourceFamilyLoader.fuel L L + completionBudget L))
def normalBudget (L : Nat) : Nat := 1 + (5 + ((4 * L + 9) + familyBudget L))
def selectionBudget (L : Nat) : Nat := 1 + (5 + (MatrixInputPayload.fuel L L + normalBudget L))
def sourceBudget (L : Nat) : Nat := (8 * L + 20) + (1 + selectionBudget L)

theorem complete_check {n : Nat} (F : Family n) (U : System n) :
    ∃ used after, Exec familyCheck
        (framed (familyDone (codec.encode ⟨n, U, F⟩)) (first (codec.encode ⟨n, U, F⟩)).rows) used after ∧
      used ≤ completionBudget (codec.encode ⟨n, U, F⟩).length ∧
      after.get 8 = answer (codec.encode ⟨n, U, F⟩) := by
  rw [familyDone_canonical, canonical_first]
  obtain ⟨used, after, checked, output, bound⟩ := construct_exec F U
  refine ⟨2 + used, after, ?_, ?_, ?_⟩
  · have cost : 2 + used = 1 + (1 + used) := by omega
    rw [cost]
    exact Exec.one rfl (Exec.empty rfl checked)
  · unfold completionBudget
    omega
  · rw [SourcePlaneInput.answer_canonical]
    exact output

theorem short_check (input : BitString)
    (short : ¬ (2 * (first input).dimension + 3) * (header input).count ≤ (header input).rest.length) :
    Exec familyCheck (framed (familyDone input) (first input).rows) 3
      (framed (SourceDirectionRaw.failed (familyDone input)) (first input).rows) := by
  have flag : (framed (familyDone input) (first input).rows).get 5 = [] := by
    change (if (2 * (first input).dimension + 3) * (header input).count ≤ (header input).rest.length then [true] else []) = []
    rw [if_neg short]
  exact Exec.empty flag (failure_exec _ _)
theorem extra_check (input : BitString)
    (enough : (2 * (first input).dimension + 3) * (header input).count ≤ (header input).rest.length)
    (wrong : (header input).rest.length ≠ (2 * (first input).dimension + 3) * (header input).count) :
    Exec familyCheck (framed (familyDone input) (first input).rows) 4
      (framed (SourceDirectionRaw.failed (familyDone input)) (first input).rows) := by
  have flag : (framed (familyDone input) (first input).rows).get 5 = [true] := by
    change (if (2 * (first input).dimension + 3) * (header input).count ≤ (header input).rest.length then [true] else []) = [true]
    rw [if_pos enough]
  have nonempty : (header input).rest.drop ((2 * (first input).dimension + 3) * (header input).count) ≠ [] := by
    intro empty
    have bound := List.drop_eq_nil_iff.mp empty
    omega
  cases tail : (header input).rest.drop ((2 * (first input).dimension + 3) * (header input).count) with
  | nil => exact (nonempty tail).elim
  | cons bit rest =>
    cases bit
    · have read : (framed (familyDone input) (first input).rows).get 0 = false :: rest := tail
      exact Exec.one flag (Exec.zero read (failure_exec _ _))
    · have read : (framed (familyDone input) (first input).rows).get 0 = true :: rest := tail
      exact Exec.one flag (Exec.one read (failure_exec _ _))

theorem family_check_exec (input : BitString) (top : (first input).terminated = true)
    (enough : normalSize input ≤ (first input).payload.length) (last : (header input).terminated = true) :
    ∃ used after, Exec familyCheck (framed (familyDone input) (first input).rows) used after ∧
      used ≤ completionBudget input.length ∧ after.get 8 = answer input := by
  by_cases length : (header input).rest.length = (2 * (first input).dimension + 3) * (header input).count
  · obtain ⟨U, F, _, _, _, _, bytes⟩ := valid_input input ⟨top, enough, last, length⟩
    generalize dimension : (first input).dimension = n at U F bytes
    rw [← bytes]
    exact complete_check F U
  · have rejected : ∃ used, Exec familyCheck (framed (familyDone input) (first input).rows) used
        (framed (SourceDirectionRaw.failed (familyDone input)) (first input).rows) ∧ used ≤ 4 := by
      by_cases sufficient : (2 * (first input).dimension + 3) * (header input).count ≤ (header input).rest.length
      · exact ⟨4, extra_check input sufficient length, Nat.le_refl 4⟩
      · exact ⟨3, short_check input sufficient, by decide⟩
    obtain ⟨used, checked, bound⟩ := rejected
    refine ⟨used, framed (SourceDirectionRaw.failed (familyDone input)) (first input).rows, checked, ?_, ?_⟩
    · unfold completionBudget constructBudget
      omega
    · rw [SourcePlaneInput.answer_malformed input (decode_none_family_length input length)]
      rfl

theorem family_selection_exec (input : BitString) (top : (first input).terminated = true)
    (enough : normalSize input ≤ (first input).payload.length) :
    ∃ used after, Exec familySelection (framed (readHeaderResult input) (first input).rows) used after ∧
      used ≤ familyBudget input.length ∧ after.get 8 = answer input := by
  cases success : (header input).terminated with
  | false =>
    have flag : (framed (readHeaderResult input) (first input).rows).get 4 = [] := by
      change (if (header input).terminated then [true] else []) = []
      rw [success]; rfl
    refine ⟨3, framed (SourceDirectionRaw.failed (readHeaderResult input)) (first input).rows,
      Exec.empty flag (failure_exec _ _), ?_, ?_⟩
    · unfold familyBudget
      omega
    · rw [SourcePlaneInput.answer_malformed input (decode_none_family_header input success)]
      rfl
  | true =>
    obtain ⟨lastFuel, after, checked, bound, output⟩ := family_check_exec input top enough success
    have flag : (framed (readHeaderResult input) (first input).rows).get 4 = [true] := by
      change (if (header input).terminated then [true] else []) = [true]
      rw [success]; rfl
    refine ⟨1 + ((3 * (first input).dimension + 12) +
      (SourceFamilyLoader.fuel (first input).dimension (header input).count + lastFuel)), after,
      Exec.one flag (Exec.seq (lift_exec _ _ _ _ _ (family_seed_exec input success))
        (Exec.seq (lift_exec _ _ _ _ _ (family_payload_exec input)) checked)), ?_, output⟩
    have sizes := SourceDirectionInput.size_bounds input
    have read := SourceEncodedMatrix.loaderFuel_bound (first input).dimension (header input).count
      input.length sizes.1 sizes.2.2.1
    unfold familyBudget
    omega

theorem normal_selection_exec (input : BitString) (top : (first input).terminated = true) :
    ∃ used after, Exec normalSelection (framed (normalDone input) (first input).rows) used after ∧
      used ≤ normalBudget input.length ∧ after.get 8 = answer input := by
  by_cases enough : normalSize input ≤ (first input).payload.length
  · obtain ⟨lastFuel, after, checked, bound, output⟩ := family_selection_exec input top enough
    have flag : (framed (normalDone input) (first input).rows).get 5 = [true] := by
      change (if normalSize input ≤ (first input).payload.length then [true] else []) = [true]
      rw [if_pos enough]
    refine ⟨1 + (5 + (MatrixStrictHeader.blockFuel (familyTail input) + lastFuel)), after,
      Exec.one flag (Exec.seq (lift_exec _ _ _ _ _ (preserve_exec input))
        (Exec.seq (lift_exec _ _ _ _ _ (family_header_exec input)) checked)), ?_, output⟩
    have sizes := SourceDirectionInput.size_bounds input
    have headerCost := MatrixStrictHeader.blockFuel_bound (familyTail input)
    unfold normalBudget
    omega
  · have flag : (framed (normalDone input) (first input).rows).get 5 = [] := by
      change (if normalSize input ≤ (first input).payload.length then [true] else []) = []
      rw [if_neg enough]
    refine ⟨3, framed (SourceDirectionRaw.failed (normalDone input)) (first input).rows,
      Exec.empty flag (failure_exec _ _), ?_, ?_⟩
    · unfold normalBudget
      omega
    · rw [SourcePlaneInput.answer_malformed input (decode_none_normals input enough)]
      rfl

theorem selection_exec (input : BitString) :
    ∃ used after, Exec selection (framed (rawHeaders input) (first input).rows) used after ∧
      used ≤ selectionBudget input.length ∧ after.get 8 = answer input := by
  cases success : (first input).terminated with
  | false =>
    have flag : (framed (rawHeaders input) (first input).rows).get 4 = [] := by
      change (if (first input).terminated then [true] else []) = []
      rw [success]; rfl
    refine ⟨3, framed (SourceDirectionRaw.failed (rawHeaders input)) (first input).rows,
      Exec.empty flag (failure_exec _ _), ?_, ?_⟩
    · unfold selectionBudget
      omega
    · rw [SourcePlaneInput.answer_malformed input (decode_none_header input success)]
      rfl
  | true =>
    obtain ⟨lastFuel, after, checked, bound, output⟩ := normal_selection_exec input success
    have flag : (framed (rawHeaders input) (first input).rows).get 4 = [true] := by
      change (if (first input).terminated then [true] else []) = [true]
      rw [success]; rfl
    refine ⟨1 + (5 + (MatrixInputPayload.fuel (first input).dimension (first input).rows + lastFuel)),
      after, Exec.one flag (Exec.seq (lift_exec _ _ _ _ _ (normal_seed_exec input success))
        (Exec.seq (lift_exec _ _ _ _ _ (normal_payload_exec input)) checked)), ?_, output⟩
    have sizes := SourceDirectionInput.size_bounds input
    have read := MatrixInputPayload.fuel_input_bound (first input).dimension (first input).rows
      input.length sizes.1 sizes.2.1
    unfold selectionBudget
    omega

theorem block_exec (input : BitString) :
    ∃ used after, Exec block (start input) used after ∧
      used ≤ sourceBudget input.length ∧ after.get 8 = answer input := by
  obtain ⟨lastFuel, after, checked, bound, output⟩ := selection_exec input
  refine ⟨MatrixInputHeaders.fuel input + (1 + lastFuel), after,
    Exec.seq (lift_exec _ _ _ 0 _ (headers_exec input)) (Exec.seq (saveCount_exec input) checked), ?_, output⟩
  have headerCost := MatrixInputHeaders.fuel_bound input
  unfold sourceBudget
  omega

end PNP.Concrete.ResidualReduction.SourcePlaneRaw

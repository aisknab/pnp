import PNP.Concrete.ResidualReduction.SourceDirectionLoader
import PNP.Concrete.ResidualReduction.SourceDirectionBudget
import PNP.Concrete.ResidualReduction.SourceEncodedMatrix

/-! The complete direction construction from arbitrary raw bitstrings.
Parsing, malformed-input rejection, both computed kernels, all source-derived
constraints and output serialization are included in the source bound. -/

namespace PNP.Concrete.ResidualReduction.SourceDirectionRaw
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceDirectionInput
open PNP.Concrete.ResidualReduction.SourceDirectionLoader
open PNP.Concrete.ResidualReduction.SourceDirectionInstructions (State core setCore solver small)

def failure : Block 20 := .seq (.action (.clear 8)) (.action (.push 8 false))
def failed (r : State) : State := setCore r {(core r) with core := {(core r).core with output := [false]}}
theorem failure_exec (r : State) : Exec failure r.store 2 (failed r).store :=
  Exec.seq (.action _ _) (.action _ _)
theorem failed_output (r : State) : (failed r).store.get 8 = [false] := rfl

def construct : Block 20 := .seq finish SourceDirectionInstructions.block
def endCheck : Block 20 := .branch 0 construct failure failure
def familyCheck : Block 20 := .branch 5 failure failure endCheck
def familyParsed : Block 20 := .seq (loader SourceFamilyLoader.seed)
  (.seq (loader SourceFamilyLoader.block) familyCheck)
def familySelection : Block 20 := .branch 4 failure failure familyParsed
def readFamily : Block 20 := .seq preserve (.seq (small MatrixStrictHeader.block) familySelection)
def normalSelection : Block 20 := .branch 5 failure failure readFamily
def normalParsed : Block 20 := .seq (solver MatrixInputPayload.seed)
  (.seq (solver MatrixInputPayload.block) normalSelection)
def selection : Block 20 := .branch 4 failure failure normalParsed
def block : Block 20 := .seq (solver MatrixInputHeaders.block) selection

def completionBudget (L : Nat) : Nat := 2 + ((8 * L + 18) + SourceDirectionBudget.budget L)
def familyBudget (L : Nat) : Nat := 1 + ((3 * L + 12) +
  (SourceFamilyLoader.fuel L L + completionBudget L))
def normalBudget (L : Nat) : Nat := 1 + (5 + ((4 * L + 9) + familyBudget L))
def selectionBudget (L : Nat) : Nat := 1 + (5 + (MatrixInputPayload.fuel L L + normalBudget L))
def sourceBudget (L : Nat) : Nat := (8 * L + 20) + selectionBudget L

theorem complete_check {n : Nat} (F : Family n) (U : System n) :
    Exec familyCheck (familyDone (SourceDirectionEncoding.codec.encode ⟨n, U, F⟩)).store
      (2 + (finishFuel F U + SourceDirectionInstructions.fuel F U))
      (SourceDirectionInstructions.result F U).store := by
  rw [familyDone_canonical]
  have cost : 2 + (finishFuel F U + SourceDirectionInstructions.fuel F U) =
      1 + (1 + (finishFuel F U + SourceDirectionInstructions.fuel F U)) := by omega
  rw [cost]
  exact Exec.one rfl (Exec.empty rfl (Exec.seq (finish_exec F U) (SourceDirectionInstructions.block_exec F U)))

theorem completion_bound {n : Nat} (F : Family n) (U : System n) :
    2 + (finishFuel F U + SourceDirectionInstructions.fuel F U) ≤
      completionBudget (SourceDirectionEncoding.codec.encode ⟨n, U, F⟩).length := by
  have family := SourceDirectionEncoding.family_payload_bound n F U
  have normals := SourceDirectionEncoding.normals_payload_bound n F U
  have calculation := SourceDirectionBudget.fuel_bound F U
  unfold finishFuel completionBudget
  omega

theorem short_check (input : BitString)
    (short : ¬ (2 * (first input).dimension + 3) * (header input).count ≤ (header input).rest.length) :
    Exec familyCheck (familyDone input).store 3 (failed (familyDone input)).store := by
  have flag : (familyDone input).store.get 5 = [] := by
    change (if (2 * (first input).dimension + 3) * (header input).count ≤ (header input).rest.length then [true] else []) = []
    rw [if_neg short]
  exact Exec.empty flag (failure_exec _)
theorem extra_check (input : BitString)
    (enough : (2 * (first input).dimension + 3) * (header input).count ≤ (header input).rest.length)
    (wrong : (header input).rest.length ≠ (2 * (first input).dimension + 3) * (header input).count) :
    Exec familyCheck (familyDone input).store 4 (failed (familyDone input)).store := by
  have flag : (familyDone input).store.get 5 = [true] := by
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
    · have read : (familyDone input).store.get 0 = false :: rest := tail
      exact Exec.one flag (Exec.zero read (failure_exec _))
    · have read : (familyDone input).store.get 0 = true :: rest := tail
      exact Exec.one flag (Exec.one read (failure_exec _))

theorem family_check_exec (input : BitString) (top : (first input).terminated = true)
    (enough : normalSize input ≤ (first input).payload.length) (last : (header input).terminated = true) :
    ∃ fuel : Nat, ∃ after : State, Exec familyCheck (familyDone input).store fuel after.store ∧
      fuel ≤ completionBudget input.length ∧ after.store.get 8 = directionEncoded input := by
  by_cases length : (header input).rest.length = (2 * (first input).dimension + 3) * (header input).count
  · obtain ⟨U, F, _, _, _, _, bytes⟩ := valid_input input ⟨top, enough, last, length⟩
    generalize dimension : (first input).dimension = n at U F bytes
    rw [← bytes]
    refine ⟨2 + (finishFuel F U + SourceDirectionInstructions.fuel F U),
      SourceDirectionInstructions.result F U, complete_check F U, completion_bound F U, ?_⟩
    rw [directionEncoded_canonical]
    exact SourceDirectionInstructions.result_output F U
  · have rejected : ∃ fuel, Exec familyCheck (familyDone input).store fuel (failed (familyDone input)).store ∧ fuel ≤ 4 := by
      by_cases sufficient : (2 * (first input).dimension + 3) * (header input).count ≤ (header input).rest.length
      · exact ⟨4, extra_check input sufficient length, Nat.le_refl 4⟩
      · exact ⟨3, short_check input sufficient, by decide⟩
    obtain ⟨fuel, checked, bound⟩ := rejected
    refine ⟨fuel, failed (familyDone input), checked, ?_, ?_⟩
    · unfold completionBudget
      omega
    · rw [directionEncoded, decode_none_family_length input length]
      rfl

theorem family_selection_exec (input : BitString) (top : (first input).terminated = true)
    (enough : normalSize input ≤ (first input).payload.length) :
    ∃ fuel : Nat, ∃ after : State, Exec familySelection (readHeaderResult input).store fuel after.store ∧
      fuel ≤ familyBudget input.length ∧ after.store.get 8 = directionEncoded input := by
  cases success : (header input).terminated with
  | false =>
    have flag : (readHeaderResult input).store.get 4 = [] := by
      change (if (header input).terminated then [true] else []) = []
      rw [success]; rfl
    refine ⟨3, failed (readHeaderResult input), Exec.empty flag (failure_exec _), ?_, ?_⟩
    · unfold familyBudget
      omega
    · rw [directionEncoded, decode_none_family_header input success]
      rfl
  | true =>
    obtain ⟨lastFuel, after, checked, bound, output⟩ := family_check_exec input top enough success
    have flag : (readHeaderResult input).store.get 4 = [true] := by
      change (if (header input).terminated then [true] else []) = [true]
      rw [success]; rfl
    refine ⟨1 + ((3 * (first input).dimension + 12) +
      (SourceFamilyLoader.fuel (first input).dimension (header input).count + lastFuel)), after,
      Exec.one flag (Exec.seq (family_seed_exec input success)
        (Exec.seq (family_payload_exec input) checked)), ?_, output⟩
    have sizes := SourceDirectionInput.size_bounds input
    have read := SourceEncodedMatrix.loaderFuel_bound (first input).dimension (header input).count
      input.length sizes.1 sizes.2.2.1
    unfold familyBudget
    omega

theorem normal_selection_exec (input : BitString) (top : (first input).terminated = true) :
    ∃ fuel : Nat, ∃ after : State, Exec normalSelection (normalDone input).store fuel after.store ∧
      fuel ≤ normalBudget input.length ∧ after.store.get 8 = directionEncoded input := by
  by_cases enough : normalSize input ≤ (first input).payload.length
  · obtain ⟨lastFuel, after, checked, bound, output⟩ := family_selection_exec input top enough
    have flag : (normalDone input).store.get 5 = [true] := by
      change (if normalSize input ≤ (first input).payload.length then [true] else []) = [true]
      rw [if_pos enough]
    refine ⟨1 + (5 + (MatrixStrictHeader.blockFuel (familyTail input) + lastFuel)), after,
      Exec.one flag (Exec.seq (preserve_exec input) (Exec.seq (family_header_exec input) checked)), ?_, output⟩
    have sizes := SourceDirectionInput.size_bounds input
    have headerCost := MatrixStrictHeader.blockFuel_bound (familyTail input)
    unfold normalBudget
    omega
  · have flag : (normalDone input).store.get 5 = [] := by
      change (if normalSize input ≤ (first input).payload.length then [true] else []) = []
      rw [if_neg enough]
    refine ⟨3, failed (normalDone input), Exec.empty flag (failure_exec _), ?_, ?_⟩
    · unfold normalBudget
      omega
    · rw [directionEncoded, decode_none_normals input enough]
      rfl

theorem selection_exec (input : BitString) :
    ∃ fuel : Nat, ∃ after : State, Exec selection (rawHeaders input).store fuel after.store ∧
      fuel ≤ selectionBudget input.length ∧ after.store.get 8 = directionEncoded input := by
  cases success : (first input).terminated with
  | false =>
    have flag : (rawHeaders input).store.get 4 = [] := by
      change (if (first input).terminated then [true] else []) = []
      rw [success]; rfl
    refine ⟨3, failed (rawHeaders input), Exec.empty flag (failure_exec _), ?_, ?_⟩
    · unfold selectionBudget
      omega
    · rw [directionEncoded, decode_none_header input success]
      rfl
  | true =>
    obtain ⟨lastFuel, after, checked, bound, output⟩ := normal_selection_exec input success
    have flag : (rawHeaders input).store.get 4 = [true] := by
      change (if (first input).terminated then [true] else []) = [true]
      rw [success]; rfl
    refine ⟨1 + (5 + (MatrixInputPayload.fuel (first input).dimension (first input).rows + lastFuel)),
      after, Exec.one flag (Exec.seq (normal_seed_exec input success)
        (Exec.seq (normal_payload_exec input) checked)), ?_, output⟩
    have sizes := SourceDirectionInput.size_bounds input
    have read := MatrixInputPayload.fuel_input_bound (first input).dimension (first input).rows
      input.length sizes.1 sizes.2.1
    unfold selectionBudget
    omega

theorem block_exec (input : BitString) :
    ∃ fuel : Nat, ∃ after : State, Exec block (rawStart input).store fuel after.store ∧
      fuel ≤ sourceBudget input.length ∧ after.store.get 8 = directionEncoded input := by
  obtain ⟨lastFuel, after, checked, bound, output⟩ := selection_exec input
  refine ⟨MatrixInputHeaders.fuel input + lastFuel, after, Exec.seq (headers_exec input) checked, ?_, output⟩
  have headerCost := MatrixInputHeaders.fuel_bound input
  unfold sourceBudget
  omega

end PNP.Concrete.ResidualReduction.SourceDirectionRaw

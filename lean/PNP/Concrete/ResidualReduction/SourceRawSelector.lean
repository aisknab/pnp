import PNP.Concrete.ResidualReduction.SourceSelectorInput
import PNP.Concrete.ResidualReduction.SourceEncodedMatrix

/-! Closed affine-first source selection on arbitrary bitstrings. Headers and
the exact row payload are checked before any mathematical query. Successful
inputs produce the canonical optional Choice; rejected inputs produce only
the absent marker. Absence does not assert satisfiability or ZeroSlack. -/

namespace PNP.Concrete.ResidualReduction.SourceRawSelector
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (codec familyBits)
open PNP.Concrete.ResidualReduction.SourceMatrixPacket (State)
open PNP.Concrete.ResidualReduction.SourceSelectorInput
open PNP.Concrete.ResidualReduction.SourceSelectorState (full)
open PNP.Concrete.ResidualReduction.MatrixInputFields (fields size_bounds)
open PNP.Concrete.ResidualReduction.SourceEncodedMatrix (failed loaderFuel_bound)

def answer (input : BitString) : BitString :=
  match codec.decode input with
  | none => [false]
  | some ⟨n,F⟩ => (SourceChoiceEncoding.codec n F.length).encode (SourceWitnessSelection.choose F)
theorem answer_canonical (n : Nat) (F : Family n) :
    answer (codec.encode ⟨n,F⟩) =
      (SourceChoiceEncoding.codec n F.length).encode (SourceWitnessSelection.choose F) := by
  simp only [answer,SourceMatrixEncoding.roundtrip]
theorem answer_malformed (input : BitString) (invalid : codec.decode input = none) :
    answer input = [false] := by simp only [answer,invalid]

def process : Block 48 := .seq construct <|
  .seq SourceSelectorDispatch.block SourceChoiceOutput.block
def processPolynomial : NatPolynomial := .add constructPolynomial
  (.add SourceSelectorDispatch.costPolynomial SourceChoiceOutput.costPolynomial)

theorem process_exec {n : Nat} (F : Family n) :
    ∃ used after, Exec process
      (loaded (SourceFamilyLoader.validated n F.length (familyBits F)).store (codec.encode ⟨n,F⟩)) used after ∧
      after.get 8 = (SourceChoiceEncoding.codec n F.length).encode (SourceWitnessSelection.choose F) ∧
      used ≤ processPolynomial.eval (codec.encode ⟨n,F⟩).length := by
  have prepared := construct_exec F
  obtain ⟨queryUsed,r,d,t,s,queried,correct,queryBound⟩ :=
    SourceSelectorDispatch.block_exec F (SourceChoiceOutput.core (headerResult n)) [] [] [] emptyHeld
  obtain ⟨outputUsed,after,encoded,bytes,outputBound⟩ :=
    SourceChoiceOutput.block_exec F (SourceSelectorResult.select F) r d t s correct
  refine ⟨constructCost n F.length (familyBits F).length + (queryUsed + outputUsed),after,
    Exec.seq prepared (Exec.seq queried encoded),?_,?_⟩
  · rw [bytes,SourceChoiceEncoding.selected_bytes]
  · have prepareBound := construct_bound F
    simp only [processPolynomial,NatPolynomial.eval_add]
    omega

def failure : Block 48 := Frame.block 32 SourceEncodedMatrix.failure
theorem loader_get (r : Store 16) (input : BitString) (i : Fin 16) :
    (loaded r input).get (Frame.index 32 i) = r.get i := by
  rw [loaded_eq]
  exact Frame.get_core r (loaderFrame input) i
theorem failure_exec (r : State) (input : BitString) :
    Exec failure (loaded r.store input) 2 (loaded (failed r).store input) := by
  simpa only [failure,loaded_eq] using Frame.execution (SourceEncodedMatrix.failure_exec r) (loaderFrame input)
theorem failure_output (r : State) (input : BitString) :
    (loaded (failed r).store input).get 8 = [false] := by
  exact (loader_get (failed r).store input (8 : Fin 16)).trans rfl

def endCheck : Block 48 := .branch 0 process failure failure
def payloadCheck : Block 48 := .branch 5 failure failure endCheck
def parsed : Block 48 := .seq (Frame.block 32 SourceFamilyLoader.seed) <|
  .seq (Frame.block 32 SourceFamilyLoader.block) payloadCheck
def selection : Block 48 := .branch 4 failure failure parsed
def headers : Block 48 := Frame.block 32 (SourceMatrixPacket.lift12 MatrixInputHeaders.block)
def block : Block 48 := .seq retain (.seq headers selection)
def sourceBudget (L : Nat) : Nat := 1 + ((8 * L + 20) +
  (1 + ((3 * L + 12) + (SourceFamilyLoader.fuel L L + (2 + processPolynomial.eval L)))))

theorem headers_exec (input : BitString) :
    Exec headers (loaded (SourceFamilyLoader.rawStart input).store input) (MatrixInputHeaders.fuel input)
      (loaded (SourceFamilyLoader.rawHeaders input).store input) := by
  simpa only [headers,loaded_eq] using Frame.execution (SourceFamilyLoader.headers_exec input) (loaderFrame input)

theorem complete_check (n : Nat) (F : Family n) :
    ∃ used after, Exec payloadCheck
      (loaded (SourceFamilyLoader.result n F.length (familyBits F)).store (codec.encode ⟨n,F⟩))
      (2 + used) after ∧
      after.get 8 = (SourceChoiceEncoding.codec n F.length).encode (SourceWitnessSelection.choose F) ∧
      used ≤ processPolynomial.eval (codec.encode ⟨n,F⟩).length := by
  have complete := SourceFamilyLoader.result_complete n F.length (familyBits F)
    (SourceMatrixEncoding.familyBits_length F)
  obtain ⟨used,after,checked,output,bound⟩ := process_exec F
  refine ⟨used,after,?_,output,bound⟩
  have cost : 2 + used = 1 + (1 + used) := by omega
  rw [complete,cost]
  exact Exec.one rfl (Exec.empty rfl checked)

theorem short_check (n count : Nat) (payload input : BitString)
    (short : ¬ (2 * n + 3) * count ≤ payload.length) :
    Exec payloadCheck (loaded (SourceFamilyLoader.result n count payload).store input) 3
      (loaded (failed (SourceFamilyLoader.result n count payload)).store input) := by
  have flag : (SourceFamilyLoader.result n count payload).store.get 5 = [] := by
    change (if (2 * n + 3) * count ≤ payload.length then [true] else []) = []
    rw [if_neg short]
  exact Exec.empty ((loader_get _ input 5).trans flag) (failure_exec _ input)

theorem extra_check (n count : Nat) (payload input : BitString)
    (enough : (2 * n + 3) * count ≤ payload.length)
    (wrong : payload.length ≠ (2 * n + 3) * count) :
    Exec payloadCheck (loaded (SourceFamilyLoader.result n count payload).store input) 4
      (loaded (failed (SourceFamilyLoader.result n count payload)).store input) := by
  have flag : (SourceFamilyLoader.result n count payload).store.get 5 = [true] := by
    change (if (2 * n + 3) * count ≤ payload.length then [true] else []) = [true]
    rw [if_pos enough]
  have nonempty : payload.drop ((2 * n + 3) * count) ≠ [] := by
    intro empty
    have bound := List.drop_eq_nil_iff.mp empty
    omega
  cases tail : payload.drop ((2 * n + 3) * count) with
  | nil => exact (nonempty tail).elim
  | cons bit rest =>
    have read : (SourceFamilyLoader.result n count payload).store.get 0 = bit :: rest := tail
    cases bit
    · exact Exec.one ((loader_get _ input 5).trans flag)
        (Exec.zero ((loader_get _ input 0).trans read) (failure_exec _ input))
    · exact Exec.one ((loader_get _ input 5).trans flag)
        (Exec.one ((loader_get _ input 0).trans read) (failure_exec _ input))

theorem valid_exec (n : Nat) (F : Family n) :
    ∃ used after, Exec block (rawStart (codec.encode ⟨n,F⟩)) used after ∧
      used ≤ sourceBudget (codec.encode ⟨n,F⟩).length ∧
      after.get 8 = (SourceChoiceEncoding.codec n F.length).encode (SourceWitnessSelection.choose F) := by
  let input := codec.encode ⟨n,F⟩
  have success : (fields input).terminated = true := by rw [SourceFamilyInput.canonical_fields]
  have seed : Exec SourceFamilyLoader.seed (SourceFamilyLoader.rawHeaders input).store (3 * n + 12)
      (SourceFamilyLoader.start n F.length (familyBits F)).store := by
    rw [SourceFamilyLoader.headers_valid input success,SourceFamilyInput.canonical_fields]
    exact SourceFamilyLoader.seed_exec n F.length (familyBits F)
  have flag : (SourceFamilyLoader.rawHeaders input).store.get 4 = [true] := by
    change (if (fields input).terminated then [true] else []) = [true]
    rw [success]; rfl
  have seedLift := Frame.execution seed (loaderFrame input)
  have loadLift := Frame.execution (SourceFamilyLoader.block_exec n F.length (familyBits F)) (loaderFrame input)
  simp only [← loaded_eq] at seedLift loadLift
  obtain ⟨used,after,checked,output,bound⟩ := complete_check n F
  refine ⟨1 + (MatrixInputHeaders.fuel input + (1 + ((3 * n + 12) +
    (SourceFamilyLoader.fuel n F.length + (2 + used))))),after,
    Exec.seq (retain_exec input) (Exec.seq (headers_exec input)
      (Exec.one ((loader_get _ input 4).trans flag) (Exec.seq seedLift (Exec.seq loadLift checked)))),
    ?_,output⟩
  have header := MatrixInputHeaders.fuel_bound input
  have dimension := SourceMatrixEncoding.dimension_bound n F
  have loader := loaderFuel_bound n F.length input.length
    (SourceMatrixEncoding.dimension_bound n F) (SourceMatrixEncoding.rowCount_bound n F)
  unfold sourceBudget
  dsimp only [input] at *
  omega

theorem failed_header (input : BitString) (bad : (fields input).terminated = false) :
    ∃ used after, Exec block (rawStart input) used after ∧
      used ≤ sourceBudget input.length ∧ after.get 8 = answer input := by
  have flag : (SourceFamilyLoader.rawHeaders input).store.get 4 = [] := by
    change (if (fields input).terminated then [true] else []) = []
    rw [bad]; rfl
  refine ⟨1 + (MatrixInputHeaders.fuel input + 3),
    loaded (failed (SourceFamilyLoader.rawHeaders input)).store input,
    Exec.seq (retain_exec input) (Exec.seq (headers_exec input)
      (Exec.empty ((loader_get _ input 4).trans flag) (failure_exec _ input))),?_,?_⟩
  · have header := MatrixInputHeaders.fuel_bound input
    unfold sourceBudget
    omega
  · rw [answer_malformed input (SourceFamilyInput.decode_none_header input bad)]
    exact failure_output _ input

theorem failed_payload (input : BitString) (success : (fields input).terminated = true)
    (wrong : (fields input).payload.length ≠ (2 * (fields input).dimension + 3) * (fields input).rows) :
    ∃ used after, Exec block (rawStart input) used after ∧
      used ≤ sourceBudget input.length ∧ after.get 8 = answer input := by
  let f := fields input
  let rejected := SourceFamilyLoader.result f.dimension f.rows f.payload
  have rejectedRun : ∃ used, Exec payloadCheck (loaded rejected.store input) used
      (loaded (failed rejected).store input) ∧ used ≤ 4 := by
    by_cases enough : (2 * f.dimension + 3) * f.rows ≤ f.payload.length
    · exact ⟨4,extra_check f.dimension f.rows f.payload input enough wrong,Nat.le_refl 4⟩
    · exact ⟨3,short_check f.dimension f.rows f.payload input enough,by decide⟩
  obtain ⟨lastFuel,last,lastBound⟩ := rejectedRun
  have seed : Exec SourceFamilyLoader.seed (SourceFamilyLoader.rawHeaders input).store (3 * f.dimension + 12)
      (SourceFamilyLoader.start f.dimension f.rows f.payload).store := by
    rw [SourceFamilyLoader.headers_valid input success]
    exact SourceFamilyLoader.seed_exec f.dimension f.rows f.payload
  have flag : (SourceFamilyLoader.rawHeaders input).store.get 4 = [true] := by
    change (if (fields input).terminated then [true] else []) = [true]
    rw [success]; rfl
  have seedLift := Frame.execution seed (loaderFrame input)
  have loadLift := Frame.execution (SourceFamilyLoader.block_exec f.dimension f.rows f.payload) (loaderFrame input)
  simp only [← loaded_eq] at seedLift loadLift
  refine ⟨1 + (MatrixInputHeaders.fuel input + (1 + ((3 * f.dimension + 12) +
    (SourceFamilyLoader.fuel f.dimension f.rows + lastFuel)))),loaded (failed rejected).store input,
    Exec.seq (retain_exec input) (Exec.seq (headers_exec input)
      (Exec.one ((loader_get _ input 4).trans flag) (Exec.seq seedLift (Exec.seq loadLift last)))),?_,?_⟩
  · have sizes := size_bounds input
    have header := MatrixInputHeaders.fuel_bound input
    have loader := loaderFuel_bound f.dimension f.rows input.length sizes.1 sizes.2.1
    unfold sourceBudget
    have positive : 2 ≤ processPolynomial.eval input.length := by
      simp only [processPolynomial,constructPolynomial,NatPolynomial.eval_add,NatPolynomial.eval_linear]
      omega
    dsimp only [f] at *
    omega
  · rw [answer_malformed input (SourceFamilyInput.decode_none_length input wrong)]
    exact failure_output _ input

theorem block_exec (input : BitString) :
    ∃ used after, Exec block (rawStart input) used after ∧
      used ≤ sourceBudget input.length ∧ after.get 8 = answer input := by
  cases success : (fields input).terminated with
  | false => exact failed_header input success
  | true =>
    by_cases length : (fields input).payload.length = (2 * (fields input).dimension + 3) * (fields input).rows
    · obtain ⟨F,_,_,bytes⟩ := SourceFamilyInput.valid_payload input success length
      generalize nEq : (fields input).dimension = n at F bytes
      rw [← bytes,answer_canonical]
      exact valid_exec n F
    · exact failed_payload input success length

theorem answer_length (input : BitString) : (answer input).length ≤ 4 * input.length + 4 := by
  cases decoded : codec.decode input with
  | none => rw [answer_malformed input decoded]; simp only [List.length_cons,List.length_nil]; omega
  | some problem =>
    rcases problem with ⟨n,F⟩
    have bytes := (SourceMatrixEncoding.canonical input ⟨n,F⟩).mp decoded
    rw [← bytes,answer_canonical]
    exact SourceChoiceEncoding.selected_output_bound F

end PNP.Concrete.ResidualReduction.SourceRawSelector

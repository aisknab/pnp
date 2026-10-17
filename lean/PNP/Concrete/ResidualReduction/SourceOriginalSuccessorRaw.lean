import PNP.Concrete.ResidualReduction.SourceOriginalSuccessorBounds

/-! One closed original-input successor. Selection, chart discovery, checked
reduction and complete step serialization are actual component executions.
Malformed inputs and zero-dimensional sources return absence; absence never
asserts unsatisfiability or completeness of the stopped-core solver. -/

namespace PNP.Concrete.ResidualReduction.SourceOriginalSuccessorRaw
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceWitnessSelection
open PNP.Concrete.ResidualReduction.SourceOriginalSuccessorState
open PNP.Concrete.ResidualReduction.SourceOriginalSuccessorBounds
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (codec)

def acceptedChart : Block 56 := .seq SourceOriginalSuccessorChart.capture <|
  .seq SourceOriginalSuccessorApply.block SourceOriginalSuccessorOutput.block
def chartCheck : Block 56 := .branch 8 failure failure acceptedChart
def construct : Block 56 := .seq SourceOriginalSuccessorChoice.block <|
  .seq SourceOriginalSuccessorChart.block chartCheck
def dimensionCheck : Block 56 := .branch 50 failure failure construct
def parsed : Block 56 := .seq SourceOriginalSuccessorInput.headers dimensionCheck
def dispatch : Block 56 := .branch 49 failure failure parsed
def block : Block 56 := .seq SourceOriginalSuccessorInput.select dispatch

def canonicalAnswer : (n : Nat) → Family n → BitString
  | 0,_ => [false]
  | n + 1,F => (stepCodec n F.length).encode (SourceChain.globalStep F)
def answer (input : BitString) : BitString :=
  match codec.decode input with
  | none => [false]
  | some ⟨n,F⟩ => canonicalAnswer n F
def budget (L : Nat) : Nat := SourceRawSelector.sourceBudget L + 51 + postBudget L

theorem answer_canonical (n : Nat) (F : Family n) :
    answer (codec.encode ⟨n,F⟩) = canonicalAnswer n F := by
  simp only [answer,SourceMatrixEncoding.roundtrip]
theorem answer_malformed (input : BitString) (h : codec.decode input = none) :
    answer input = [false] := by simp only [answer,h]
theorem canonical_none (n : Nat) (F : Family n) (h : choose F = none) :
    canonicalAnswer n F = [false] := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [canonicalAnswer,SourceWitnessSelection.global_exact,h,Option.bind,step_none]

theorem construct_chosen {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) (h : SourceBalance.chooseChart w.direction = some c) :
    Exec construct (work [] [] (SourceOriginalSuccessorChoice.before F w)) (constructFuel F w c)
      (SourceOriginalSuccessorOutput.finished F w c) := by
  have checked : Exec chartCheck (SourceOriginalSuccessorChart.success F w c)
      (1 + (53 + (SourceOriginalSuccessorApply.fuel F w c + SourceOriginalSuccessorOutput.fuel F w c)))
      (SourceOriginalSuccessorOutput.finished F w c) :=
    Exec.one (SourceOriginalSuccessorChart.success_output F w c)
      (Exec.seq (SourceOriginalSuccessorChart.capture_exec F w c)
        (Exec.seq (SourceOriginalSuccessorApply.block_exec F w c)
          (SourceOriginalSuccessorOutput.block_exec F w c)))
  exact Exec.seq (SourceOriginalSuccessorChoice.block_exec F w)
    (Exec.seq (SourceOriginalSuccessorChart.chosen_exec F w c h) checked)

theorem construct_absent {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (h : SourceBalance.chooseChart w.direction = none) :
    Exec construct (work [] [] (SourceOriginalSuccessorChoice.before F w))
      (SourceOriginalSuccessorChoice.fuel F w + ((5 * (n + 1) + 12) + 51))
      (work [] [false] (SourceOriginalSuccessorChoice.loaded F w)) := by
  let r := Frame.join (SourceChartStream.full {SourceChartSelection.absent (n + 1) with output := [false]}
    (SourceChartSelectedFamily.saved F w.weights)) (Store.empty 33)
  have checked : Exec chartCheck (SourceOriginalSuccessorChart.absent F w) 51
      (work [] [false] (SourceOriginalSuccessorChoice.loaded F w)) :=
    Exec.zero (SourceOriginalSuccessorChart.absent_output F w)
      (failure_exec r (SourceOriginalSuccessorChoice.loaded F w))
  exact Exec.seq (SourceOriginalSuccessorChoice.block_exec F w)
    (Exec.seq (SourceOriginalSuccessorChart.absent_exec F w h) checked)

theorem construct_exec {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length) :
    ∃ used after, Exec construct (work [] [] (SourceOriginalSuccessorChoice.before F w)) used after ∧
      1 + (SourceOriginalSuccessorInput.headersFuel (n + 1) F.length + (1 + used)) ≤
        postBudget (codec.encode ⟨n + 1,F⟩).length ∧
      after.get 8 = (stepCodec n F.length).encode (build F w) := by
  cases chart : SourceBalance.chooseChart w.direction with
  | none =>
    refine ⟨SourceOriginalSuccessorChoice.fuel F w + ((5 * (n + 1) + 12) + 51),
      work [] [false] (SourceOriginalSuccessorChoice.loaded F w),
      construct_absent F w chart,absent_chart_bound F w,?_⟩
    simp only [build,SourceClosure.buildStep,chart,Option.bind]
    rfl
  | some c =>
    refine ⟨constructFuel F w c,SourceOriginalSuccessorOutput.finished F w c,
      construct_chosen F w c chart,positive_bound F w c,?_⟩
    rw [SourceOriginalSuccessorOutput.output_eq,SourceOriginalSuccessorOutput.stepResult_build F w c chart]

theorem dispatch_absent (input : BitString) :
    Exec dispatch (work [] [] (SourceOriginalSuccessorInput.selected input [false])) 51
      (work [] [false] (SourceOriginalSuccessorInput.selected input [false])) :=
  Exec.zero rfl (failure_exec (Frame.join (SourceScalarState.work []).store (Store.empty 39))
    (SourceOriginalSuccessorInput.selected input [false]))

theorem dispatch_valid (n : Nat) (F : Family n) :
    ∃ used after, Exec dispatch
      (work [] [] (SourceOriginalSuccessorInput.selected (codec.encode ⟨n,F⟩)
        ((SourceChoiceEncoding.codec n F.length).encode (choose F)))) used after ∧
      used ≤ postBudget (codec.encode ⟨n,F⟩).length ∧ after.get 8 = canonicalAnswer n F := by
  cases selected : choose F with
  | none =>
    refine ⟨51,work [] [false] (SourceOriginalSuccessorInput.selected (codec.encode ⟨n,F⟩) [false]),
      dispatch_absent _,failure_bound _,?_⟩
    rw [canonical_none n F selected]
    rfl
  | some w =>
    cases n with
    | zero =>
      let word := (SourceChoiceEncoding.codec 0 F.length).encode (some w)
      let s := SourceOriginalSuccessorInput.data F word
      let r := Frame.join (SourceScalarState.work []).store (Store.empty 39)
      have stopped : Exec dimensionCheck (work [] [] s) 51 (work [] [false] s) :=
        Exec.empty rfl (failure_exec r s)
      have checked : Exec dispatch
          (work [] [] (SourceOriginalSuccessorInput.selected (codec.encode ⟨0,F⟩) word))
          (1 + (SourceOriginalSuccessorInput.headersFuel 0 F.length + 51)) (work [] [false] s) :=
        Exec.one rfl (Exec.seq (SourceOriginalSuccessorInput.headers_exec F word) stopped)
      exact ⟨_,_,checked,zero_bound F,rfl⟩
    | succ n =>
      obtain ⟨used,after,run,bound,output⟩ := construct_exec F w
      let word := (SourceChoiceEncoding.codec (n + 1) F.length).encode (some w)
      have flag : (work [] [] (SourceOriginalSuccessorChoice.before F w)).get 50 =
          true :: List.replicate n true := by
        change List.replicate (n + 1) true = true :: List.replicate n true
        rw [List.replicate_succ]
      have checked : Exec dispatch
          (work [] [] (SourceOriginalSuccessorInput.selected (codec.encode ⟨n + 1,F⟩) word))
          (1 + (SourceOriginalSuccessorInput.headersFuel (n + 1) F.length + (1 + used))) after :=
        Exec.one rfl (Exec.seq (SourceOriginalSuccessorInput.headers_exec F word) (Exec.one flag run))
      refine ⟨_,_,checked,bound,?_⟩
      simpa only [canonicalAnswer,SourceWitnessSelection.global_exact,selected,Option.bind] using output

theorem valid_exec (n : Nat) (F : Family n) :
    ∃ used after, Exec block (SourceOriginalSuccessorState.initial (codec.encode ⟨n,F⟩)) used after ∧
      used ≤ budget (codec.encode ⟨n,F⟩).length ∧ after.get 8 = canonicalAnswer n F := by
  obtain ⟨selection,selectRun,selectBound⟩ := SourceOriginalSuccessorInput.select_exec (codec.encode ⟨n,F⟩)
  rw [SourceRawSelector.answer_canonical] at selectRun
  obtain ⟨used,after,run,bound,output⟩ := dispatch_valid n F
  refine ⟨selection + used,after,Exec.seq selectRun run,?_,output⟩
  unfold budget
  omega

theorem malformed_exec (input : BitString) (h : codec.decode input = none) :
    ∃ used after, Exec block (SourceOriginalSuccessorState.initial input) used after ∧
      used ≤ budget input.length ∧ after.get 8 = answer input := by
  obtain ⟨selection,run,bound⟩ := SourceOriginalSuccessorInput.select_exec input
  rw [SourceRawSelector.answer_malformed input h] at run
  have post := dispatch_absent input
  refine ⟨selection + 51,_,Exec.seq run post,?_,?_⟩
  · have failure := failure_bound input.length
    unfold budget
    omega
  · rw [answer_malformed input h]
    rfl

theorem block_exec (input : BitString) :
    ∃ used after, Exec block (SourceOriginalSuccessorState.initial input) used after ∧
      used ≤ budget input.length ∧ after.get 8 = answer input := by
  cases decoded : codec.decode input with
  | none => exact malformed_exec input decoded
  | some problem =>
    rcases problem with ⟨n,F⟩
    have bytes := (SourceMatrixEncoding.canonical input ⟨n,F⟩).mp decoded
    rw [← bytes,answer_canonical]
    exact valid_exec n F

end PNP.Concrete.ResidualReduction.SourceOriginalSuccessorRaw

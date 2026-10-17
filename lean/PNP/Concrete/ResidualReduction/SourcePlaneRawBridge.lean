import PNP.Concrete.ResidualReduction.SourcePlaneInput
import PNP.Concrete.ResidualReduction.SourceDirectionRaw

/-! Literal framing and handoff from the existing raw packet parser.
The parsed normal count is retained independently of parser scratch space.
The family count is copied before the finishing handoff clears its source. -/

namespace PNP.Concrete.ResidualReduction.SourcePlaneRaw
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirectionInput
open PNP.Concrete.ResidualReduction.SourceDirectionLoader
open PNP.Concrete.ResidualReduction.SourceDirectionInstructions (State)
open PNP.Concrete.ResidualReduction.SourcePlaneInput (answer answerFor)
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding (codec)

def counterFrame (count : Nat) : Store 9 := .cons (List.replicate count true) (Store.empty 8)
def framed (r : State) (count : Nat) : Store 29 := Frame.join r.store (counterFrame count)
def lift (body : Block 20) : Block 29 := Frame.block 9 body
theorem lift_exec (body : Block 20) (r after : State) (count fuel : Nat)
    (checked : Exec body r.store fuel after.store) :
    Exec (lift body) (framed r count) fuel (framed after count) := Frame.execution checked (counterFrame count)
theorem framed_output (r : State) (count : Nat) : (framed r count).get 8 = r.store.get 8 := rfl

def failure : Block 29 := lift SourceDirectionRaw.failure
theorem failure_exec (r : State) (count : Nat) :
    Exec failure (framed r count) 2 (framed (SourceDirectionRaw.failed r) count) :=
  lift_exec _ r _ count 2 (SourceDirectionRaw.failure_exec r)
theorem failed_output (r : State) (count : Nat) :
    (framed (SourceDirectionRaw.failed r) count).get 8 = [false] := rfl

def saveCount : Block 29 := .action (.copy 20 1)
theorem saveCount_exec (input : BitString) :
    Exec saveCount (framed (rawHeaders input) 0) 1 (framed (rawHeaders input) (first input).rows) := .action _ _
theorem popCount_exec (r : State) (count : Nat) :
    Exec (.action (.pop (20 : Fin 29))) (framed r (count + 1)) 1 (framed r count) := .action _ _

def countGate (next : Block 29) : Block 29 := .branch 20 failure failure <|
  .seq (.action (.pop 20)) <| .branch 20 failure failure <|
    .seq (.action (.pop 20)) (.branch 20 next failure failure)
theorem countGate_two (next : Block 29) (r : State) (used : Nat) (after : Store 29)
    (checked : Exec next (framed r 0) used after) :
    Exec (countGate next) (framed r 2) (5 + used) after := by
  have cost : 5 + used = 1 + (1 + (1 + (1 + (1 + used)))) := by omega
  rw [cost]
  exact Exec.one rfl (Exec.seq (popCount_exec r 1)
    (Exec.one rfl (Exec.seq (popCount_exec r 0) (Exec.empty rfl checked))))
theorem countGate_wrong (next : Block 29) (r : State) (count : Nat) (wrong : count ≠ 2) :
    ∃ used after, Exec (countGate next) (framed r count) used after ∧
      after.get 8 = [false] ∧ used ≤ 7 := by
  cases count with
  | zero => exact ⟨3, framed (SourceDirectionRaw.failed r) 0, Exec.empty rfl (failure_exec r 0), rfl, by decide⟩
  | succ count =>
    cases count with
    | zero =>
      exact ⟨5, framed (SourceDirectionRaw.failed r) 0,
        Exec.one rfl (Exec.seq (popCount_exec r 0) (Exec.empty rfl (failure_exec r 0))), rfl, by decide⟩
    | succ count =>
      cases count with
      | zero => exact (wrong rfl).elim
      | succ rest =>
        exact ⟨7, framed (SourceDirectionRaw.failed r) (rest + 1),
          Exec.one rfl (Exec.seq (popCount_exec r (rest + 2))
            (Exec.one rfl (Exec.seq (popCount_exec r (rest + 1)) (Exec.one rfl (failure_exec r (rest + 1)))))),
          rfl, Nat.le_refl 7⟩

def rowFrame {n : Nat} (F : Family n) : Store 9 :=
  .cons [] (.cons [] (SourcePlanePipeline.initialData F).store)
def captureRows : Block 29 := .action (.copy 27 15)
theorem captureRows_exec {n : Nat} (F : Family n) (a b : Affine n) :
    Exec captureRows (framed (validated F [a, b]) 0) 1
      (Frame.join (validated F [a, b]).store (rowFrame F)) := .action _ _
theorem finish_exec {n : Nat} (F : Family n) (a b : Affine n) :
    Exec (lift SourceDirectionLoader.finish) (Frame.join (validated F [a, b]).store (rowFrame F))
      (finishFuel F [a, b]) (SourcePlanePipeline.start F a b) :=
  Frame.execution (SourceDirectionLoader.finish_exec F [a, b]) (rowFrame F)

def continuation : Block 29 := .seq captureRows
  (.seq (lift SourceDirectionLoader.finish) SourcePlanePreparedQuery.block)
def construct : Block 29 := countGate continuation
def constructBudget (L : Nat) : Nat := 7 + (8 * L + 18) + SourcePlanePreparedQuery.costPolynomial.eval L

theorem construct_pair {n : Nat} (F : Family n) (a b : Affine n) :
    ∃ used after, Exec construct (framed (validated F [a, b]) 2) used after ∧
      after.get 8 = answerFor F [a, b] ∧
      used ≤ constructBudget (codec.encode ⟨n, [a, b], F⟩).length := by
  obtain ⟨used, after, checked, output, bound⟩ := SourcePlanePreparedQuery.block_exec F a b
  have moved := Exec.seq (captureRows_exec F a b) (Exec.seq (finish_exec F a b) checked)
  refine ⟨5 + (1 + (finishFuel F [a, b] + used)), after, countGate_two continuation _ _ _ moved, output, ?_⟩
  have family := SourceDirectionEncoding.family_payload_bound n F [a, b]
  have normals := SourceDirectionEncoding.normals_payload_bound n F [a, b]
  unfold constructBudget finishFuel
  omega
theorem construct_wrong {n : Nat} (F : Family n) (U : System n) (wrong : U.length ≠ 2) :
    ∃ used after, Exec construct (framed (validated F U) U.length) used after ∧
      after.get 8 = answerFor F U ∧ used ≤ constructBudget (codec.encode ⟨n, U, F⟩).length := by
  obtain ⟨used, after, checked, output, bound⟩ := countGate_wrong continuation (validated F U) U.length wrong
  rw [SourcePlaneInput.answerFor_wrong_count F U wrong]
  refine ⟨used, after, checked, output, ?_⟩
  unfold constructBudget
  omega
theorem construct_exec {n : Nat} (F : Family n) (U : System n) :
    ∃ used after, Exec construct (framed (validated F U) U.length) used after ∧
      after.get 8 = answerFor F U ∧ used ≤ constructBudget (codec.encode ⟨n, U, F⟩).length := by
  cases U with
  | nil => exact construct_wrong F [] (by simp only [List.length_nil]; omega)
  | cons a U =>
    cases U with
    | nil => exact construct_wrong F [a] (by simp only [List.length_cons, List.length_nil]; omega)
    | cons b U =>
      cases U with
      | nil => exact construct_pair F a b
      | cons c U => exact construct_wrong F (a :: b :: c :: U) (by simp only [List.length_cons]; omega)

end PNP.Concrete.ResidualReduction.SourcePlaneRaw

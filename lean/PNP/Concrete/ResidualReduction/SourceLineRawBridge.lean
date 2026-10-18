import PNP.Concrete.ResidualReduction.SourceLineInput
import PNP.Concrete.ResidualReduction.SourceDirectionRaw

/-! Literal raw-parser framing and handoff. The header count is protected
through payload parsing; the source row count is captured before the common
finishing loader clears it. No derived map or witness is supplied. -/

namespace PNP.Concrete.ResidualReduction.SourceLineRaw
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirectionInput
open PNP.Concrete.ResidualReduction.SourceDirectionLoader
open PNP.Concrete.ResidualReduction.SourceDirectionInstructions (State)
open PNP.Concrete.ResidualReduction.SourceLineInput (answer answerFor)
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding (codec)

def counterFrame (count : Nat) : Store 18 := .cons (List.replicate count true) (Store.empty 17)
def framed (r : State) (count : Nat) : Store 38 := Frame.join r.store (counterFrame count)
def lift (body : Block 20) : Block 38 := Frame.block 18 body
theorem lift_exec (body : Block 20) (r after : State) (count fuel : Nat)
    (checked : Exec body r.store fuel after.store) :
    Exec (lift body) (framed r count) fuel (framed after count) := Frame.execution checked (counterFrame count)
theorem framed_output (r : State) (count : Nat) : (framed r count).get 8 = r.store.get 8 := rfl
def failure : Block 38 := lift SourceDirectionRaw.failure
theorem failure_exec (r : State) (count : Nat) :
    Exec failure (framed r count) 2 (framed (SourceDirectionRaw.failed r) count) :=
  lift_exec _ r _ count 2 (SourceDirectionRaw.failure_exec r)
theorem failed_output (r : State) (count : Nat) :
    (framed (SourceDirectionRaw.failed r) count).get 8 = [false] := rfl

def saveCount : Block 38 := .action (.copy 20 1)
theorem saveCount_exec (input : BitString) :
    Exec saveCount (framed (rawHeaders input) 0) 1 (framed (rawHeaders input) (first input).rows) := .action _ _
theorem popCount_exec (r : State) (count : Nat) :
    Exec (.action (.pop (20 : Fin 38))) (framed r (count + 1)) 1 (framed r count) := .action _ _
def countGate (next : Block 38) : Block 38 := .branch 20 failure failure <|
  .seq (.action (.pop 20)) (.branch 20 next failure failure)
theorem countGate_one (next : Block 38) (r : State) (used : Nat) (after : Store 38)
    (checked : Exec next (framed r 0) used after) :
    Exec (countGate next) (framed r 1) (3 + used) after := by
  have cost : 3 + used = 1 + (1 + (1 + used)) := by omega
  rw [cost]
  exact Exec.one rfl (Exec.seq (popCount_exec r 0) (Exec.empty rfl checked))
theorem countGate_wrong (next : Block 38) (r : State) (count : Nat) (wrong : count ≠ 1) :
    ∃ used after, Exec (countGate next) (framed r count) used after ∧
      after.get 8 = [false] ∧ used ≤ 5 := by
  cases count with
  | zero => exact ⟨3, framed (SourceDirectionRaw.failed r) 0, Exec.empty rfl (failure_exec r 0), rfl, by decide⟩
  | succ count =>
    cases count with
    | zero => exact (wrong rfl).elim
    | succ rest =>
      exact ⟨5, framed (SourceDirectionRaw.failed r) (rest + 1),
        Exec.one rfl (Exec.seq (popCount_exec r (rest + 1)) (Exec.one rfl (failure_exec r (rest + 1)))),
        rfl, Nat.le_refl 5⟩

def rowFrame {n : Nat} (F : Family n) : Store 18 :=
  .cons [] (.cons (List.replicate F.length true) (.cons [] (.cons [] SourceLinePullback.initialData.store)))
def captureRows : Block 38 := .action (.copy 21 15)
theorem captureRows_exec {n : Nat} (F : Family n) (a : Affine n) :
    Exec captureRows (framed (validated F [a]) 0) 1
      (Frame.join (validated F [a]).store (rowFrame F)) := .action _ _
theorem finish_exec {n : Nat} (F : Family n) (a : Affine n) :
    Exec (lift SourceDirectionLoader.finish) (Frame.join (validated F [a]).store (rowFrame F))
      (finishFuel F [a]) (SourceLinePullback.start F a) :=
  Frame.execution (SourceDirectionLoader.finish_exec F [a]) (rowFrame F)

def continuation : Block 38 := .seq captureRows
  (.seq (lift SourceDirectionLoader.finish) SourceLinePreparedQuery.block)
def construct : Block 38 := countGate continuation
def constructBudget (L : Nat) : Nat := 5 + (8 * L + 18) + SourceLinePreparedQuery.costPolynomial.eval L
theorem construct_single {n : Nat} (F : Family n) (a : Affine n) :
    ∃ used after, Exec construct (framed (validated F [a]) 1) used after ∧
      after.get 8 = answerFor F [a] ∧
      used ≤ constructBudget (codec.encode ⟨n, [a], F⟩).length := by
  have checked := SourceLinePreparedQuery.block_exec F a
  have moved := Exec.seq (captureRows_exec F a) (Exec.seq (finish_exec F a) checked)
  refine ⟨3 + (1 + (finishFuel F [a] + SourceLinePreparedQuery.fuel F a)), SourceLinePreparedQuery.result F a,
    countGate_one continuation _ _ _ moved, SourceLinePreparedQuery.result_output F a, ?_⟩
  have bound := SourceLinePreparedQuery.original_input_bound F a
  have family := SourceDirectionEncoding.family_payload_bound n F [a]
  have normals := SourceDirectionEncoding.normals_payload_bound n F [a]
  unfold constructBudget finishFuel
  omega
theorem construct_wrong {n : Nat} (F : Family n) (U : System n) (wrong : U.length ≠ 1) :
    ∃ used after, Exec construct (framed (validated F U) U.length) used after ∧
      after.get 8 = answerFor F U ∧ used ≤ constructBudget (codec.encode ⟨n, U, F⟩).length := by
  obtain ⟨used, after, checked, output, bound⟩ := countGate_wrong continuation (validated F U) U.length wrong
  rw [SourceLineInput.answerFor_wrong_count F U wrong]
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
    | nil => exact construct_single F a
    | cons b U => exact construct_wrong F (a :: b :: U) (by simp only [List.length_cons]; omega)

end PNP.Concrete.ResidualReduction.SourceLineRaw

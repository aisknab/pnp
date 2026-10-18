import PNP.Concrete.ResidualReduction.SourceNativeEnvelopeState

/-! Exact native reduction-output prefix. The original dimension remains in a
protected register while the history machine reduces the working dimension.
The prefix is written by literal instructions, including its unary delimiter. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeEnvelopeOutput
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.SourceNativeEnvelopeState

def reverseDimension : Block 64 := .seq (.action (.copy 3 63)) (core ClauseQuery.reverseLoop)

theorem reverse_exec (input out dimension : BitString) :
    Exec reverseDimension (work input out dimension) (4 * dimension.length + 2)
      (work input (dimension.reverse ++ out) dimension) := by
  let base := {SourceScalarState.work input with output := out}
  let ready := {base with excess := dimension}
  have first : Exec (.action (.copy (3 : Fin 64) 63)) (work input out dimension) 1
      (frame (SourceHistoryState.withCore ready SourceHistoryState.emptySaved) dimension) := .action _ _
  have last : Exec ClauseQuery.reverseLoop ready.store (4 * dimension.length + 1)
      ({base with excess := [],output := dimension.reverse ++ out}).store :=
    ClauseQuery.reverse_exec base dimension
  have cost : 4 * dimension.length + 2 = 1 + (4 * dimension.length + 1) := by omega
  simpa only [reverseDimension,cost,base,ready,work,SourceHistoryState.work,SourceScalarState.work]
    using Exec.seq first (core_exec last dimension)

def success : Block 64 := .seq (.action (.pop 0))
  (.seq (.action (.copy 8 0))
    (.seq (.action (.clear 0))
      (.seq (.action (.push 8 false))
        (.seq reverseDimension (.seq (.action (.push 8 true)) (.action (.push 8 true)))))))
def encoded (data dimension : BitString) : BitString :=
  true :: true :: (dimension.reverse ++ false :: data)

theorem success_exec (data dimension : BitString) :
    Exec success (work (true :: data) [] dimension) (4 * dimension.length + 8)
      (work [] (encoded data dimension) dimension) := by
  have a : Exec (.action (.pop (0 : Fin 64))) (work (true :: data) [] dimension) 1
      (work data [] dimension) := .action _ _
  have b : Exec (.action (.copy (8 : Fin 64) 0)) (work data [] dimension) 1
      (work data data dimension) := .action _ _
  have c : Exec (.action (.clear (0 : Fin 64))) (work data data dimension) 1
      (work [] data dimension) := .action _ _
  have d : Exec (.action (.push (8 : Fin 64) false)) (work [] data dimension) 1
      (work [] (false :: data) dimension) := .action _ _
  have e := reverse_exec [] (false :: data) dimension
  have f : Exec (.action (.push (8 : Fin 64) true))
      (work [] (dimension.reverse ++ false :: data) dimension) 1
      (work [] (true :: (dimension.reverse ++ false :: data)) dimension) := .action _ _
  have g : Exec (.action (.push (8 : Fin 64) true))
      (work [] (true :: (dimension.reverse ++ false :: data)) dimension) 1
      (work [] (encoded data dimension) dimension) := .action _ _
  have cost : 4 * dimension.length + 8 =
      1 + (1 + (1 + (1 + ((4 * dimension.length + 2) + (1 + 1))))) := by omega
  simpa only [success,cost] using Exec.seq a (Exec.seq b (Exec.seq c
    (Exec.seq d (Exec.seq e (Exec.seq f g)))))

def reject : Block 64 := .action (.push 8 false)
def block : Block 64 := .branch 0 reject reject success
def output (input dimension : BitString) : BitString :=
  match input with
  | true :: data => encoded data dimension
  | _ => [false]
def result (input dimension : BitString) : Store 64 :=
  match input with
  | true :: _ => work [] (output input dimension) dimension
  | _ => work input [false] dimension
def fuel (input dimension : BitString) : Nat :=
  match input with
  | true :: _ => 4 * dimension.length + 9
  | _ => 2

theorem block_exec (input dimension : BitString) :
    Exec block (work input [] dimension) (fuel input dimension) (result input dimension) := by
  cases input with
  | nil => exact Exec.empty rfl (.action _ _)
  | cons bit data =>
    cases bit with
    | false => exact Exec.zero rfl (.action _ _)
    | true =>
      have cost : 4 * dimension.length + 9 = 1 + (4 * dimension.length + 8) := by omega
      simpa only [block,fuel,result,output,cost] using Exec.one rfl (success_exec data dimension)

theorem result_output (input dimension : BitString) :
    (result input dimension).get 8 = output input dimension := by
  cases input with
  | nil => rfl
  | cons bit data => cases bit <;> rfl
theorem fuel_bound (input dimension : BitString) :
    fuel input dimension ≤ 4 * dimension.length + 9 := by
  cases input with
  | nil => simp only [fuel]; omega
  | cons bit data =>
    cases bit with
    | false => simp only [fuel]; omega
    | true => exact Nat.le_refl _

end PNP.Concrete.ResidualReduction.SourceNativeEnvelopeOutput

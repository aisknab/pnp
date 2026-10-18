import PNP.Concrete.ResidualReduction.SourceHistoryState

/-! Retain the actual source and returned step in chronological history order.
The accumulator is reversed bytes, not a list supplied to the machine. -/

namespace PNP.Concrete.ResidualReduction.SourceHistoryRecord
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceHistoryEncoding
open PNP.Concrete.ResidualReduction.SourceHistoryState

def before {n : Nat} (F : Family (n + 1)) (h : List SourceChain.StepRecord)
    (s : ConstructedStep n F.length) : Saved :=
  {data F h with step := true :: (SourceEncoding.stepCodec n F.length).encode s}
def untagged {n : Nat} (F : Family (n + 1)) (h : List SourceChain.StepRecord)
    (s : ConstructedStep n F.length) : Saved :=
  {data F h with step := (SourceEncoding.stepCodec n F.length).encode s}
def after {n : Nat} (F : Family (n + 1)) (h : List SourceChain.StepRecord)
    (s : ConstructedStep n F.length) : Saved :=
  {data F (h ++ [⟨n,F,s⟩]) with step := (SourceEncoding.stepCodec n F.length).encode s}

def loadPrefix : Block 63 := .seq (.action (.copy 3 56)) <|
  .seq (.action (.pop 3)) (.action (.copy 8 59))
def loadStep : Block 63 := .action (.copy 3 61)
def finish : Block 63 := .seq (.action (.copy 59 8)) <|
  .seq (.action (.clear 8)) (.action (.push 60 true))
def block : Block 63 := .seq (.action (.pop 61)) <| .seq loadPrefix <|
  .seq (core ClauseQuery.reverseLoop) <| .seq loadStep <|
  .seq (core ClauseQuery.reverseLoop) finish
def fuel {n : Nat} (F : Family (n + 1)) (s : ConstructedStep n F.length) : Nat :=
  4 * (recordPrefix F).length + 4 * ((SourceEncoding.stepCodec n F.length).encode s).length + 10

theorem block_exec {n : Nat} (F : Family (n + 1)) (h : List SourceChain.StepRecord)
    (s : ConstructedStep n F.length) :
    Exec block (work [] [] (before F h s)) (fuel F s) (work [] [] (after F h s)) := by
  let held := untagged F h s
  let base := SourceScalarState.work []
  let loaded := {base with excess := recordPrefix F,output := (records h).reverse}
  let first := {base with output := (recordPrefix F).reverse ++ (records h).reverse}
  let second := {first with excess := (SourceEncoding.stepCodec n F.length).encode s}
  let done := {base with output := (records (h ++ [(⟨n,F,s⟩ : SourceChain.StepRecord)])).reverse}
  have strip : Exec (.action (.pop (61 : Fin 63))) (work [] [] (before F h s)) 1
      (work [] [] held) := .action _ _
  have load : Exec loadPrefix (work [] [] held) 3 (withCore loaded held) := by
    simp only [held,untagged,data,positive_packet]
    exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have firstRun : Exec (core ClauseQuery.reverseLoop) (withCore loaded held)
      (4 * (recordPrefix F).length + 1) (withCore first held) := by
    simpa only [loaded,first,base,SourceScalarState.work] using
      core_exec (ClauseQuery.reverse_exec {base with output := (records h).reverse} (recordPrefix F)) held
  have next : Exec loadStep (withCore first held) 1 (withCore second held) := .action _ _
  have secondRun : Exec (core ClauseQuery.reverseLoop) (withCore second held)
      (4 * ((SourceEncoding.stepCodec n F.length).encode s).length + 1) (withCore done held) := by
    simpa only [second,first,done,base,SourceScalarState.work,record_accumulator] using
      core_exec (ClauseQuery.reverse_exec first ((SourceEncoding.stepCodec n F.length).encode s)) held
  have endRun : Exec finish (withCore done held) 3 (work [] [] (after F h s)) := by
    let middle := {held with history := (records (h ++ [(⟨n,F,s⟩ : SourceChain.StepRecord)])).reverse}
    have store : Exec (.action (.copy (59 : Fin 63) 8)) (withCore done held) 1
        (withCore done middle) := .action _ _
    have clear : Exec (.action (.clear (8 : Fin 63))) (withCore done middle) 1
        (work [] [] middle) := .action _ _
    have count : Exec (.action (.push (60 : Fin 63) true)) (work [] [] middle) 1
        (work [] [] (after F h s)) := by
      have checked := field_push_exec Field.count
        (Frame.join (SourceScalarState.work []).store (Store.empty 47)) middle true
      have slot : Field.count.slot = (60 : Fin 63) := rfl
      rw [slot] at checked
      simpa only [work,withCore,SourceScalarState.work,Field.word,fieldSet,after,middle,held,untagged,
        data,List.length_append,List.length_cons,List.length_nil,List.replicate_succ] using checked
    exact Exec.seq store (Exec.seq clear count)
  have cost : fuel F s = 1 + (3 + ((4 * (recordPrefix F).length + 1) +
      (1 + ((4 * ((SourceEncoding.stepCodec n F.length).encode s).length + 1) + 3)))) := by
    unfold fuel
    omega
  simpa only [block,cost] using Exec.seq strip (Exec.seq load
    (Exec.seq firstRun (Exec.seq next (Exec.seq secondRun endRun))))

end PNP.Concrete.ResidualReduction.SourceHistoryRecord

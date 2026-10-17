import PNP.Concrete.ResidualReduction.SourceHistoryLoop

/-! Serialize the terminal source and the actual complete history. No semantic
lift function is transmitted; the checked source/step records retain the data
needed by the existing reconstruction theorem. -/

namespace PNP.Concrete.ResidualReduction.SourceHistoryOutput
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceHistoryEncoding
open PNP.Concrete.ResidualReduction.SourceHistoryState

def block : Block 63 := .seq (.action (.copy 3 59)) <| .seq (core ClauseQuery.reverseLoop) <|
  .seq (.action (.push 8 false)) <| .seq (prepend .count) (prepend .current)
def fuel {n : Nat} (F : Family n) (h : List SourceChain.StepRecord) : Nat :=
  4 * (records h).length + 8 * h.length + 8 * (packet F).length + 23
def bytes {n : Nat} (F : Family n) (h : List SourceChain.StepRecord) : BitString :=
  SourceEncoding.dataCodec.encode ⟨n,F,h⟩

theorem block_exec {n : Nat} (F : Family n) (h : List SourceChain.StepRecord) :
    Exec block (work [] [] (stopped (data F h))) (fuel F h)
      (work [] (bytes F h) (stopped (data F h))) := by
  let saved := stopped (data F h)
  let base := SourceScalarState.work []
  let loaded := {base with excess := (records h).reverse}
  have load : Exec (.action (.copy (3 : Fin 63) 59)) (work [] [] saved) 1
      (withCore loaded saved) := .action _ _
  have reverse : Exec (core ClauseQuery.reverseLoop) (withCore loaded saved)
      (4 * (records h).length + 1) (work [] (records h) saved) := by
    simpa only [loaded,work,base,SourceScalarState.work,List.length_reverse,List.reverse_reverse,List.append_nil] using
      core_exec (ClauseQuery.reverse_exec base (records h).reverse) saved
  have delimiter : Exec (.action (.push (8 : Fin 63) false)) (work [] (records h) saved) 1
      (work [] (false :: records h) saved) := .action _ _
  have count : Exec (prepend .count) (work [] (false :: records h) saved) (8 * h.length + 10)
      (work [] (natural h.length ++ records h) saved) := by
    simpa only [Field.word,saved,stopped,data,List.length_replicate,natural,List.append_assoc,
      List.singleton_append] using prepend_exec Field.count saved (false :: records h)
  have current : Exec (prepend .current) (work [] (natural h.length ++ records h) saved)
      (8 * (packet F).length + 10) (work [] (bytes F h) saved) := by
    simpa only [Field.word,saved,stopped,data,bytes,data_bits] using
      prepend_exec Field.current saved (natural h.length ++ records h)
  have cost : fuel F h = 1 + ((4 * (records h).length + 1) +
      (1 + ((8 * h.length + 10) + (8 * (packet F).length + 10)))) := by
    unfold fuel
    omega
  simpa only [block,cost] using Exec.seq load (Exec.seq reverse
    (Exec.seq delimiter (Exec.seq count current)))

theorem fuel_bound {n : Nat} (F : Family n) (h : List SourceChain.StepRecord) :
    fuel F h ≤ 8 * (bytes F h).length + 23 := by
  have size : (bytes F h).length = (packet F).length + (h.length + 1) + (records h).length := by
    simp only [bytes,data_bits,List.length_append,natural_length]
    omega
  rw [size]
  unfold fuel
  omega

def complete : Block 63 := .seq SourceHistoryLoop.block block
theorem complete_exec (n : Nat) (F : Family n) :
    ∃ used, Exec complete (work [] [] (data F [])) used
      (work [] (SourceEncoding.dataCodec.encode (SourceEncoding.toData (SourceChain.reduce n F)))
        (SourceHistoryLoop.finished n F [])) ∧
      used ≤ SourceHistoryLoop.fuel n F +
        fuel (SourceChain.reduce n F).core (SourceChain.reduce n F).history := by
  obtain ⟨used,loop,bound⟩ := SourceHistoryLoop.block_exec n F []
  have emit := block_exec (SourceChain.reduce n F).core (SourceChain.reduce n F).history
  simp only [SourceHistoryLoop.finished,List.nil_append] at loop ⊢
  refine ⟨used + fuel (SourceChain.reduce n F).core (SourceChain.reduce n F).history,?_,by omega⟩
  exact Exec.seq loop emit

end PNP.Concrete.ResidualReduction.SourceHistoryOutput

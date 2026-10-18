import PNP.Concrete.ResidualReduction.SourceHistoryAdvance

/-! Invoke the verified original-input successor without exposing the saved
history to its workspace. The selected step is captured from its real output. -/

namespace PNP.Concrete.ResidualReduction.SourceHistoryQuery
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceHistoryEncoding
open PNP.Concrete.ResidualReduction.SourceHistoryState

def queried (s : Saved) : Saved :=
  {s with step := SourceOriginalSuccessorRaw.answer s.current}
def block : Block 63 := .seq (.action (.copy 0 56)) <|
  .seq (use56 SourceOriginalSuccessorRaw.block) <| .seq (save .step 8) reset

theorem block_exec (s : Saved) :
    ∃ used, Exec block (work [] [] s) used (work [] [] (queried s)) ∧
      used ≤ SourceOriginalSuccessorRaw.budget s.current.length + 59 := by
  obtain ⟨used,after,run,bound,output⟩ := SourceOriginalSuccessorRaw.block_exec s.current
  have load : Exec (.action (.copy (0 : Fin 63) 56)) (work [] [] s) 1
      (work s.current [] s) := .action _ _
  have query := use56_exec run s
  rw [query_initial] at query
  have store := save_exec Field.step 8 after s
  rw [output] at store
  have clear := reset_exec after (queried s)
  refine ⟨1 + (used + (1 + 57)),?_,by omega⟩
  simpa only [block,fieldSet,queried] using Exec.seq load (Exec.seq query (Exec.seq store clear))

theorem queried_positive {n : Nat} (F : Family (n + 1)) (h : List SourceChain.StepRecord) :
    queried (data F h) = {data F h with step :=
      (SourceOriginalSuccessorState.stepCodec n F.length).encode (SourceChain.globalStep F)} := by
  have output := SourceOriginalSuccessorRaw.answer_canonical (n + 1) F
  change SourceOriginalSuccessorRaw.answer (packet F) = _ at output
  simp only [queried,data,output,SourceOriginalSuccessorRaw.canonicalAnswer]

def stop : Block 63 := .seq (.action (.clear 61)) (.action (.clear 62))
theorem stop_exec (s : Saved) :
    Exec stop (work [] [] s) 2 (work [] [] (stopped s)) := by
  let r := Frame.join (SourceScalarState.work []).store (Store.empty 47)
  have first := field_clear_exec Field.step r s
  have last := field_clear_exec Field.active r (fieldSet .step s [])
  have stepSlot : Field.step.slot = (61 : Fin 63) := rfl
  have activeSlot : Field.active.slot = (62 : Fin 63) := rfl
  rw [stepSlot] at first
  rw [activeSlot] at last
  simpa only [stop,stopped,fieldSet,work,withCore,SourceScalarState.work,r] using Exec.seq first last

end PNP.Concrete.ResidualReduction.SourceHistoryQuery

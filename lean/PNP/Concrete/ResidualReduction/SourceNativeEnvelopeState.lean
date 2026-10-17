import PNP.Concrete.ResidualReduction.SourceNativeSystemPolynomial

/-! One fixed workspace for native packets and the complete history machine.
The extra register protects the original dimension while the history runner
uses its own sixty-three-register workspace. Relays preserve only the actual
output bytes as the next sole input and explicitly clear every scratch word. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeEnvelopeState
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence

def frame (r : Store 63) (dimension : BitString) : Store 64 :=
  Frame.join r (.cons dimension .nil)
def work (input out dimension : BitString) : Store 64 :=
  frame (SourceHistoryState.work input out SourceHistoryState.emptySaved) dimension
def initial (input : BitString) : Store 64 := work input [] []
def core (b : Block 9) : Block 64 := Frame.block 1 (SourceHistoryState.core b)
theorem core_exec {b : Block 9} {before after : Registers} {ticks : Nat}
    (checked : Exec b before.store ticks after.store) (dimension : BitString) :
    Exec (core b)
      (frame (SourceHistoryState.withCore before SourceHistoryState.emptySaved) dimension) ticks
      (frame (SourceHistoryState.withCore after SourceHistoryState.emptySaved) dimension) :=
  Frame.execution (SourceHistoryState.core_exec checked SourceHistoryState.emptySaved) (.cons dimension .nil)

def relayIndices : List (Fin 63) := (List.finRange 62).map Fin.succ
private theorem relay_zero_missing : (0 : Fin 63) ∉ relayIndices := by
  intro present
  rcases List.mem_map.mp present with ⟨i,_,same⟩
  have impossible := congrArg Fin.val same
  change i.val + 1 = 0 at impossible
  omega
private theorem relay_successor_present (i : Fin 62) : i.succ ∈ relayIndices :=
  List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩

theorem relay_cleared (r : Store 63) :
    SourceChartedSuccessorWords.cleared r relayIndices = SourceHistoryState.initial (r.get 0) := by
  apply Store.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [SourceChartedSuccessorWords.cleared_get,if_neg relay_zero_missing]
    rfl
  · rw [SourceChartedSuccessorWords.cleared_get,if_pos (relay_successor_present j)]
    change [] = (Store.empty 62).get j
    exact (SourceChartedSuccessorWords.empty_get 62 j).symm

def relay63 : Block 63 :=
  .seq (.action (.copy 0 8)) (SourceChartedSuccessorWords.clearList relayIndices)
theorem relay63_exec (r : Store 63) :
    Exec relay63 r 64 (SourceHistoryState.initial (r.get 8)) := by
  have first : Exec (.action (.copy (0 : Fin 63) 8)) r 1 (r.set 0 (r.get 8)) := .action _ _
  have last := SourceChartedSuccessorWords.clear_exec (r.set 0 (r.get 8)) relayIndices
  rw [relay_cleared] at last
  simpa only [relay63,relayIndices,List.length_map,List.length_finRange,Store.get_set,↓reduceIte] using
    Exec.seq first last

def relay : Block 64 := Frame.block 1 relay63
theorem relay_exec (r : Store 63) (dimension : BitString) :
    Exec relay (frame r dimension) 64 (work (r.get 8) [] dimension) :=
  Frame.execution (relay63_exec r) (.cons dimension .nil)

def captureDimension : Block 64 := .action (.copy 63 14)
theorem capture_exec (r : Store 63) (dimension : BitString) :
    Exec captureDimension (frame r dimension) 1 (frame r (r.get 14)) :=
  SourceLinePullback.copy_to_saved r (.cons dimension .nil) 0 14

def system : Block 64 := Frame.block 1 (Frame.block 39 SourceNativeSystemInput.block)
def systemResult (input : BitString) : Store 63 :=
  Frame.join (SourceNativeSystemState.work (SourceNativeSystemParse.result input).stream
    (SourceNativeSystemInput.answer input) (SourceNativeSystemParse.result input)) (Store.empty 39)

theorem system_exec (input dimension : BitString) :
    Exec system (work input [] dimension) (SourceNativeSystemInput.fuel input)
      (frame (systemResult input) dimension) :=
  Frame.execution (Frame.execution (SourceNativeSystemInput.block_exec input) (Store.empty 39))
    (.cons dimension .nil)
theorem system_output (input : BitString) :
    (systemResult input).get 8 = SourceNativeSystemInput.answer input := rfl
theorem system_dimension (input : BitString) :
    (systemResult input).get 14 = (SourceNativeSystemParse.result input).dimension := rfl

def history : Block 64 := Frame.block 1 SourceHistoryRaw.block
theorem history_exec (input dimension : BitString) :
    ∃ used after, Exec history (work input [] dimension) used (frame after dimension) ∧
      used ≤ SourceHistoryRaw.budget input.length ∧ after.get 8 = SourceHistoryRaw.answer input := by
  obtain ⟨used,after,checked,bound,output⟩ := SourceHistoryRaw.block_exec input
  exact ⟨used,after,Frame.execution checked (.cons dimension .nil),bound,output⟩

end PNP.Concrete.ResidualReduction.SourceNativeEnvelopeState

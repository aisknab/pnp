import PNP.Concrete.ResidualReduction.SourceSelectionFrame
import PNP.Concrete.ResidualReduction.SourceAffineRawQuery
import PNP.Concrete.ResidualReduction.SourcePlaneRawQuery
import PNP.Concrete.ResidualReduction.SourceLineRawQuery

/-! Three closed query programs share one working prefix. Each invocation clears
arbitrary prior query state, reloads the retained packet, and saves its exact
answer outside the working registers. No previous query can supply stale data. -/

namespace PNP.Concrete.ResidualReduction.SourceSelectionQueryCall
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks

def affine : Block 38 := Frame.block 16 SourceAffineRawQuery.block
def plane : Block 38 := Frame.block 9 SourcePlaneRaw.block
def line : Block 38 := SourceLineRaw.block

theorem affine_exec (input : BitString) :
    ∃ used after, Exec affine ((Store.empty 38).set 0 input) used after ∧
      after.get 8 = SourceAffineRawQuery.answer input ∧ used ≤ SourceAffineRawQuery.budget input.length := by
  obtain ⟨used,after,checked,output,budget⟩ := SourceAffineRawQuery.block_exec input
  exact ⟨used,Frame.join after (Store.empty 16),
    Frame.execution checked (Store.empty 16), (Frame.get_core after (Store.empty 16) 8).trans output,budget⟩

theorem plane_exec (input : BitString) :
    ∃ used after, Exec plane ((Store.empty 38).set 0 input) used after ∧
      after.get 8 = SourcePlaneInput.answer input ∧ used ≤ SourcePlaneRaw.sourceBudget input.length := by
  obtain ⟨used,after,checked,budget,output⟩ := SourcePlaneRaw.block_exec input
  exact ⟨used,Frame.join after (Store.empty 9),
    Frame.execution checked (Store.empty 9), (Frame.get_core after (Store.empty 9) 8).trans output,budget⟩

theorem line_exec (input : BitString) :
    ∃ used after, Exec line ((Store.empty 38).set 0 input) used after ∧
      after.get 8 = SourceLineInput.answer input ∧ used ≤ SourceLineRaw.sourceBudget input.length := by
  obtain ⟨used,after,checked,budget,output⟩ := SourceLineRaw.block_exec input
  exact ⟨used,after,checked,output,budget⟩

def affineCall {extra : Nat} (packet destination : Fin extra) : Block (extra + 38) :=
  SourceSelectionFrame.invoke affine 0 8 packet destination
def planeCall {extra : Nat} (packet destination : Fin extra) : Block (extra + 38) :=
  SourceSelectionFrame.invoke plane 0 8 packet destination
def lineCall {extra : Nat} (packet destination : Fin extra) : Block (extra + 38) :=
  SourceSelectionFrame.invoke line 0 8 packet destination

theorem affine_call_exec {extra : Nat} (r : Store 38) (data : Store extra)
    (packet destination : Fin extra) :
    ∃ used after, Exec (affineCall packet destination) (Frame.join r data) used
      (Frame.join after (data.set destination (SourceAffineRawQuery.answer (data.get packet)))) ∧
      used ≤ SourceAffineRawQuery.budget (data.get packet).length + 41 := by
  obtain ⟨used,after,checked,output,budget⟩ := affine_exec (data.get packet)
  have called := SourceSelectionFrame.invoke_exec affine 0 8 packet destination r data used after checked
  rw [output] at called
  exact ⟨40 + (used + 1),after,called,by omega⟩

theorem plane_call_exec {extra : Nat} (r : Store 38) (data : Store extra)
    (packet destination : Fin extra) :
    ∃ used after, Exec (planeCall packet destination) (Frame.join r data) used
      (Frame.join after (data.set destination (SourcePlaneInput.answer (data.get packet)))) ∧
      used ≤ SourcePlaneRaw.sourceBudget (data.get packet).length + 41 := by
  obtain ⟨used,after,checked,output,budget⟩ := plane_exec (data.get packet)
  have called := SourceSelectionFrame.invoke_exec plane 0 8 packet destination r data used after checked
  rw [output] at called
  exact ⟨40 + (used + 1),after,called,by omega⟩

theorem line_call_exec {extra : Nat} (r : Store 38) (data : Store extra)
    (packet destination : Fin extra) :
    ∃ used after, Exec (lineCall packet destination) (Frame.join r data) used
      (Frame.join after (data.set destination (SourceLineInput.answer (data.get packet)))) ∧
      used ≤ SourceLineRaw.sourceBudget (data.get packet).length + 41 := by
  obtain ⟨used,after,checked,output,budget⟩ := line_exec (data.get packet)
  have called := SourceSelectionFrame.invoke_exec line 0 8 packet destination r data used after checked
  rw [output] at called
  exact ⟨40 + (used + 1),after,called,by omega⟩

end PNP.Concrete.ResidualReduction.SourceSelectionQueryCall

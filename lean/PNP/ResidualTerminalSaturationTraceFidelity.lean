/-
Copyright (c) 2026 PNP Labs.

The actual saturation replay reaches the same ambient implementation and cost
coordinates as canonical saturation. Generated metadata events preserve those
costs structurally. This is not a supplied balance certificate, a physical
gate-transparency theorem, an obligation discharge, or a polynomial bound.
-/

import PNP.ResidualTerminalProfileLocality
import PNP.ResidualTerminalSaturationCostBalance

namespace PNP
namespace DirectWire

private theorem saturationSnapshot_eq_of_ambient_eq
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (ambientEqual : terminalAmbientSupportImplementation candidate left =
      terminalAmbientSupportImplementation candidate right) :
    terminalSaturationCostSnapshot candidate model left =
      { terminalSaturationCostSnapshot candidate model right with records := left } := by
  simp only [terminalSaturationCostSnapshot, ambientEqual]

/-- The actual replay endpoint, not merely its separately stored canonical
    field, has the ambient implementation of computed candidate saturation. -/
theorem terminalCandidateSaturateTrace_ambient_eq
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalAmbientSupportImplementation candidate
        (terminalSaturateTrace
          (terminalCandidateSaturationSystem candidate model) seed).replayRecords =
      terminalAmbientSupportImplementation candidate
        (terminalSaturateRecords
          (terminalCandidateSaturationSystem candidate model) seed) := by
  apply terminalAmbientSupportImplementation_eq_of_gateSelected_eq candidate
  funext gate
  simp only [terminalGateSelected, terminalSaturateTrace_replayRecords_iff]

/-- Every computed cost coordinate agrees at the replay and canonical
    endpoints. The deliberately order-sensitive stored record list stays explicit. -/
theorem terminalCandidateSaturateTrace_costSnapshot_eq
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalSaturationCostSnapshot candidate model
        (terminalSaturateTrace
          (terminalCandidateSaturationSystem candidate model) seed).replayRecords =
      { terminalSaturationCostSnapshot candidate model
          (terminalSaturateRecords
            (terminalCandidateSaturationSystem candidate model) seed) with
        records := (terminalSaturateTrace
          (terminalCandidateSaturationSystem candidate model) seed).replayRecords } := by
  exact saturationSnapshot_eq_of_ambient_eq candidate model _ _
    (terminalCandidateSaturateTrace_ambient_eq candidate model seed)

/-- Every non-gate event actually emitted by candidate saturation is cost
    transparent. This does not assert closure safety or obligation discharge. -/
theorem terminalCandidateSaturateTrace_metadata_transparent
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth)
    (member : event ∈
      (terminalSaturateTrace
        (terminalCandidateSaturationSystem candidate model) seed).events)
    (metadata : ∀ gate, event.required ≠ TerminalPrimitiveRecord.gate gate) :
    TerminalTransparentSaturationStep candidate model event := by
  obtain ⟨shape, kind, selected, _rule⟩ :=
    terminalSaturateTrace_event_valid
      (terminalCandidateSaturationSystem candidate model) seed event member
  have selectedEqual :
      terminalGateSelected event.afterRecords =
        terminalGateSelected event.beforeRecords := by
    funext gate
    have different :
        (TerminalPrimitiveRecord.gate gate :
          TerminalPrimitiveRecord inputs gates outputs profileWidth) ≠ event.required :=
      fun equal => metadata gate equal.symm
    simp only [terminalGateSelected, shape, List.mem_cons, different, false_or]
  have snapshots := saturationSnapshot_eq_of_ambient_eq candidate model
    event.afterRecords event.beforeRecords
    (terminalAmbientSupportImplementation_eq_of_gateSelected_eq candidate _ _
      selectedEqual)
  have supportEqual := congrArg TerminalSaturationCostSnapshot.supportSize snapshots
  have fullEqual := congrArg TerminalSaturationCostSnapshot.fullMinimum snapshots
  have quotientEqual := congrArg TerminalSaturationCostSnapshot.quotientMinimum snapshots
  have zeroCost : terminalSaturationEventCost event = 0 := by
    cases requiredEq : event.required <;>
      simp only [terminalSaturationEventCost, requiredEq]
    exact False.elim (metadata _ requiredEq)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro missing
    rw [selected] at missing
    cases missing
  · cases requiredEq : event.required <;> try exact True.intro
    exact False.elim (metadata _ requiredEq)
  · rw [zeroCost, Nat.add_zero]
    exact supportEqual
  · rw [zeroCost, Nat.add_zero]
    exact fullEqual
  · rw [zeroCost, Nat.add_zero]
    exact Nat.le_of_eq quotientEqual

end DirectWire
end PNP

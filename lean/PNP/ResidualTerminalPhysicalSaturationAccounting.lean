/-
Copyright (c) 2026 PNP Labs.

Actual saturation events carry an active dependency and insert a fresh record.
The physical extractor therefore charges exactly one unit for a new gate and
zero for metadata. Active ownership is not unique ownership, and physical
growth alone does not force full-minimum growth or global routing.
-/

import PNP.ResidualTerminalSaturationTraceFidelity

namespace PNP
namespace DirectWire

private theorem physicalSaturationListNoDuplicates_of_nodup {alpha : Type}
    {items : List alpha} (distinct : items.Nodup) : ListNoDuplicates items := by
  induction items with
  | nil => exact ListNoDuplicates.nil
  | cons head tail ih =>
      have parts := List.nodup_cons.mp distinct
      exact ListNoDuplicates.cons parts.1 (ih parts.2)

private theorem physicalSaturationSelectedGateCount_insert
    {inputs gates outputs profileWidth : Nat}
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (gate : Fin gates)
    (fresh : TerminalPrimitiveRecord.gate gate ∉ records) :
    (terminalSelectedGates (TerminalPrimitiveRecord.gate gate :: records)).length =
      (terminalSelectedGates records).length + 1 := by
  let after := terminalSelectedGates (TerminalPrimitiveRecord.gate gate :: records)
  let before := terminalSelectedGates records
  have gateAbsent : gate ∉ before := by
    intro member
    exact fresh ((terminalGateSelected_eq_true_iff records gate).mp
      ((mem_terminalSelectedGates_iff records gate).mp member))
  have insertedDistinct : (gate :: before).Nodup :=
    List.nodup_cons.mpr ⟨gateAbsent, terminalSelectedGates_nodup records⟩
  have memberEqual : ∀ found, found ∈ after ↔ found ∈ gate :: before := by
    intro found
    simp only [after, before, mem_terminalSelectedGates_iff,
      terminalGateSelected_eq_true_iff, List.mem_cons, TerminalPrimitiveRecord.gate.injEq]
  have forward := noDuplicatesSubset_length_le after (gate :: before)
    (physicalSaturationListNoDuplicates_of_nodup
      (terminalSelectedGates_nodup (TerminalPrimitiveRecord.gate gate :: records)))
    (fun found member => (memberEqual found).mp member)
  have backward := noDuplicatesSubset_length_le (gate :: before) after
    (physicalSaturationListNoDuplicates_of_nodup insertedDistinct)
    (fun found member => (memberEqual found).mpr member)
  have equal := Nat.le_antisymm forward backward
  simpa only [List.length_cons] using equal

private theorem physicalSaturationSnapshot_supportSize
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalSaturationCostSnapshot candidate model records).supportSize =
      (terminalSelectedGates records).length := by
  change (extractTerminalSupport candidate records).gateCount = _
  exact extractTerminalSupport_gateCount candidate records

/-- Every actual generated event has exactly its physical support charge.
    This does not assert that the full or quotient minimum has the same growth. -/
theorem terminalCandidateSaturateTrace_supportCostBalanced
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth)
    (member : event ∈ (terminalSaturateTrace
      (terminalCandidateSaturationSystem candidate model) seed).events) :
    (terminalSaturationCostSnapshot candidate model event.afterRecords).supportSize =
      (terminalSaturationCostSnapshot candidate model event.beforeRecords).supportSize +
        terminalSaturationEventCost event := by
  have metadataBalance
      (noGate : ∀ gate, event.required ≠ TerminalPrimitiveRecord.gate gate) :
      (terminalSaturationCostSnapshot candidate model event.afterRecords).supportSize =
        (terminalSaturationCostSnapshot candidate model event.beforeRecords).supportSize +
          terminalSaturationEventCost event :=
    (terminalCandidateSaturateTrace_metadata_transparent
      candidate model seed event member noGate).supportCostBalanced
  cases requiredEq : event.required with
  | gate gate =>
      have shape := (terminalSaturateTrace_event_valid
        (terminalCandidateSaturationSystem candidate model) seed event member).1
      have fresh := (terminalSaturateTrace_event_context
        (terminalCandidateSaturationSystem candidate model) seed event member).2
      rw [physicalSaturationSnapshot_supportSize, physicalSaturationSnapshot_supportSize,
        shape, requiredEq]
      simp only [terminalSaturationEventCost, requiredEq]
      exact physicalSaturationSelectedGateCount_insert event.beforeRecords gate
        (by simpa only [requiredEq] using fresh)
  | boundary _index | interface _index | profile _index =>
      apply metadataBalance
      intro gate same
      rw [requiredEq] at same
      cases same

/-- The recorded dependency is an active owner in the computed owner list.
    Other active owners may exist, so this is not a uniqueness theorem. -/
theorem terminalCandidateSaturateTrace_event_owner
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth)
    (member : event ∈ (terminalSaturateTrace
      (terminalCandidateSaturationSystem candidate model) seed).events) :
    ∃ kind, event.kind? = some kind ∧
      (kind, event.dependent) ∈ terminalSaturationEventOwners
        (terminalCandidateSaturationSystem candidate model) event := by
  obtain ⟨_shape, kind, selected, rule⟩ := terminalSaturateTrace_event_valid
    (terminalCandidateSaturationSystem candidate model) seed event member
  have active := (terminalSaturateTrace_event_context
    (terminalCandidateSaturationSystem candidate model) seed event member).1
  refine ⟨kind, selected, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨event.dependent, active, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨kind, mem_allTerminalSaturationRuleKinds kind, ?_⟩
  simp only [rule, if_true]

/-- A genuinely generated nontransparent step is a physical insertion with
    a real remaining ownership or minimum-cost obstruction. -/
theorem terminalCandidateSaturateTrace_physicalObstruction
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth)
    (member : event ∈ (terminalSaturateTrace
      (terminalCandidateSaturationSystem candidate model) seed).events)
    (failure : ¬TerminalTransparentSaturationStep candidate model event) :
    ∃ gate, event.required = TerminalPrimitiveRecord.gate gate ∧
      ((terminalSaturationEventOwners
          (terminalCandidateSaturationSystem candidate model) event).length ≠ 1 ∨
        (terminalSaturationCostSnapshot candidate model event.afterRecords).fullMinimum ≠
          (terminalSaturationCostSnapshot candidate model event.beforeRecords).fullMinimum + 1 ∨
        (terminalSaturationCostSnapshot candidate model event.beforeRecords).quotientMinimum + 1 <
          (terminalSaturationCostSnapshot candidate model event.afterRecords).quotientMinimum) := by
  cases requiredEq : event.required with
  | gate gate =>
      refine ⟨gate, rfl, ?_⟩
      obtain ⟨_shape, kind, selected, _rule⟩ := terminalSaturateTrace_event_valid
        (terminalCandidateSaturationSystem candidate model) seed event member
      have present : event.kind? ≠ none := by
        intro missing
        rw [selected] at missing
        cases missing
      have support := terminalCandidateSaturateTrace_supportCostBalanced
        candidate model seed event member
      by_cases owner :
          (terminalSaturationEventOwners
            (terminalCandidateSaturationSystem candidate model) event).length = 1
      · by_cases full :
            (terminalSaturationCostSnapshot candidate model event.afterRecords).fullMinimum =
              (terminalSaturationCostSnapshot candidate model event.beforeRecords).fullMinimum + 1
        · by_cases quotient :
              (terminalSaturationCostSnapshot candidate model event.afterRecords).quotientMinimum ≤
                (terminalSaturationCostSnapshot candidate model event.beforeRecords).quotientMinimum + 1
          · exfalso
            apply failure
            refine ⟨present, ?_, support, ?_, ?_⟩
            · simpa only [requiredEq] using owner
            · simpa only [terminalSaturationEventCost, requiredEq] using full
            · simpa only [terminalSaturationEventCost, requiredEq] using quotient
          · exact Or.inr (Or.inr (Nat.lt_of_not_ge quotient))
        · exact Or.inr (Or.inl full)
      · exact Or.inl owner
  | boundary _index | interface _index | profile _index =>
      exact False.elim (failure
        (terminalCandidateSaturateTrace_metadata_transparent
          candidate model seed event member (by
            intro gate same
            rw [requiredEq] at same
            cases same)))

/-- The existing total classifier either preserves full slack and projection
    positivity at canonical computed saturation, or identifies its exact first
    physical ownership/minimum obstruction. A local obstruction is not thereby
    a global named route, a gain, an obligation discharge or a strict descent. -/
theorem terminalCandidateSaturateTrace_balance_or_physicalObstruction
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    ((terminalSaturationCostSnapshot candidate model
        (terminalSaturateRecords
          (terminalCandidateSaturationSystem candidate model) seed)).fullSlack =
        (terminalSaturationCostSnapshot candidate model
          (terminalSaturateTrace
            (terminalCandidateSaturationSystem candidate model) seed).normalizedSeed.reverse).fullSlack ∧
      (terminalSaturationCostSnapshot candidate model
        (terminalSaturateTrace
          (terminalCandidateSaturationSystem candidate model) seed).normalizedSeed.reverse).projectionDefect ≤
        (terminalSaturationCostSnapshot candidate model
          (terminalSaturateRecords
            (terminalCandidateSaturationSystem candidate model) seed)).projectionDefect) ∨
    ∃ first : TerminalFirstNontransparentSaturationStep candidate model
        (terminalSaturateTrace
          (terminalCandidateSaturationSystem candidate model) seed).events,
      classifyTerminalSaturationBalance candidate model seed = .firstNontransparent first ∧
        ∃ gate, first.event.required = TerminalPrimitiveRecord.gate gate ∧
          ((terminalSaturationEventOwners
              (terminalCandidateSaturationSystem candidate model) first.event).length ≠ 1 ∨
            (terminalSaturationCostSnapshot candidate model first.event.afterRecords).fullMinimum ≠
              (terminalSaturationCostSnapshot candidate model first.event.beforeRecords).fullMinimum + 1 ∨
            (terminalSaturationCostSnapshot candidate model first.event.beforeRecords).quotientMinimum + 1 <
              (terminalSaturationCostSnapshot candidate model first.event.afterRecords).quotientMinimum) := by
  cases classified : classifyTerminalSaturationBalance candidate model seed with
  | balanced allTransparent =>
      apply Or.inl
      have snapshots := terminalCandidateSaturateTrace_costSnapshot_eq candidate model seed
      have fullEqual := congrArg TerminalSaturationCostSnapshot.fullSlack snapshots
      have defectEqual := congrArg TerminalSaturationCostSnapshot.projectionDefect snapshots
      have full := TerminalSaturationBalanceOutcome.balanced_fullSlack_preserved
        (allTransparent := allTransparent)
      have defect := TerminalSaturationBalanceOutcome.balanced_projectionDefect_mono
        (allTransparent := allTransparent)
      exact ⟨fullEqual.symm.trans full, Nat.le_trans defect (Nat.le_of_eq defectEqual)⟩
  | firstNontransparent first =>
      apply Or.inr
      refine ⟨first, ?_, ?_⟩
      · rfl
      · have member : first.event ∈ (terminalSaturateTrace
            (terminalCandidateSaturationSystem candidate model) seed).events := by
          have inSplit : first.event ∈ first.prior ++ first.event :: first.remaining :=
            List.mem_append_right _ (List.Mem.head _)
          exact (congrArg
            (fun events : List (TerminalSaturationTraceEvent inputs gates outputs profileWidth) =>
              first.event ∈ events) first.split).mpr inSplit
        exact terminalCandidateSaturateTrace_physicalObstruction
          candidate model seed first.event member first.failure

end DirectWire
end PNP

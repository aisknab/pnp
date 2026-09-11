/-
Copyright (c) 2026 PNP Labs.

Exact unit-charge partition of the physical gates in computed saturation.
Introduction provenance is not the manuscript-wide materializer ownership map.
The executor, profile observer, semantic minima and classifier remain unchanged.
-/

import PNP.ResidualTerminalPhysicalSaturationAccounting

namespace PNP
namespace DirectWire

/-- How a physical charge entered this particular computed support.
    This seed-dependent provenance is not the manuscript's global owner map. -/
inductive TerminalPhysicalChargeProvenance
    (inputs gates outputs profileWidth : Nat) where
  | seed
  | generated (kind : TerminalSaturationRuleKind)
      (dependent : TerminalPrimitiveRecord inputs gates outputs profileWidth)
  deriving Repr, DecidableEq

/-- One unit physical NAND charge, identified by the original gate. -/
structure TerminalPhysicalCharge (inputs gates outputs profileWidth : Nat) where
  gate : Fin gates
  provenance : TerminalPhysicalChargeProvenance inputs gates outputs profileWidth
  deriving Repr, DecidableEq

private def terminalInitialPhysicalCharges
    {inputs gates outputs profileWidth : Nat}
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    List (TerminalPhysicalCharge inputs gates outputs profileWidth) :=
  (terminalSelectedGates records).map fun gate => ⟨gate, .seed⟩

private def terminalEventPhysicalCharge?
    {inputs gates outputs profileWidth : Nat}
    (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth) :
    Option (TerminalPhysicalCharge inputs gates outputs profileWidth) :=
  match event.required, event.kind? with
  | .gate gate, some kind => some ⟨gate, .generated kind event.dependent⟩
  | _, _ => none

private def terminalPhysicalChargeLedger
    {inputs gates outputs profileWidth : Nat}
    (initial : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (events : List (TerminalSaturationTraceEvent inputs gates outputs profileWidth)) :
    List (TerminalPhysicalCharge inputs gates outputs profileWidth) :=
  terminalInitialPhysicalCharges initial ++ events.filterMap terminalEventPhysicalCharge?

/-- Compute inherited and generated physical charges from the actual trace.
    No charge list, coverage certificate or ownership table is supplied. -/
def terminalSaturatePhysicalCharges
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    List (TerminalPhysicalCharge inputs gates outputs profileWidth) :=
  let trace := terminalSaturateTrace system seed
  terminalPhysicalChargeLedger trace.normalizedSeed.reverse trace.events

private def terminalPhysicalChargeLookup
    {inputs gates outputs profileWidth : Nat}
    (gate : Fin gates) :
    List (TerminalPhysicalCharge inputs gates outputs profileWidth) →
    Option (TerminalPhysicalChargeProvenance inputs gates outputs profileWidth)
  | [] => none
  | charge :: remaining =>
      if charge.gate = gate then some charge.provenance
      else terminalPhysicalChargeLookup gate remaining

/-- Deterministic lookup of a physical charge's introduction provenance. -/
def terminalSaturatePhysicalChargeProvenance?
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (gate : Fin gates) :
    Option (TerminalPhysicalChargeProvenance inputs gates outputs profileWidth) :=
  terminalPhysicalChargeLookup gate (terminalSaturatePhysicalCharges system seed)

private theorem terminalInitialPhysicalCharges_gates
    {inputs gates outputs profileWidth : Nat}
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalInitialPhysicalCharges records).map TerminalPhysicalCharge.gate =
      terminalSelectedGates records := by
  simp only [terminalInitialPhysicalCharges, List.map_map, Function.comp_def,
    List.map_id_fun', id]

private theorem terminalPhysicalChargeLedger_snoc
    {inputs gates outputs profileWidth : Nat}
    (initial : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (events : List (TerminalSaturationTraceEvent inputs gates outputs profileWidth))
    (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth) :
    terminalPhysicalChargeLedger initial (events ++ [event]) =
      terminalPhysicalChargeLedger initial events ++
        (terminalEventPhysicalCharge? event).toList := by
  simp only [terminalPhysicalChargeLedger, List.filterMap_append, List.append_assoc]
  cases value : terminalEventPhysicalCharge? event <;>
    simp only [List.filterMap_cons, List.filterMap_nil, value, Option.toList]

private def terminalPhysicalChargeEventsValid
    {inputs gates outputs profileWidth : Nat}
    (events : List (TerminalSaturationTraceEvent inputs gates outputs profileWidth)) : Prop :=
  ∀ event, event ∈ events →
    event.afterRecords = event.required :: event.beforeRecords ∧
    event.required ∉ event.beforeRecords ∧ ∃ kind, event.kind? = some kind

private theorem terminalPhysicalChargeLedger_invariant
    {inputs gates outputs profileWidth : Nat}
    {initial final : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)}
    {events : List (TerminalSaturationTraceEvent inputs gates outputs profileWidth)}
    (linked : TerminalSaturationEventsLinked initial events final)
    (valid : terminalPhysicalChargeEventsValid events) :
    ((terminalPhysicalChargeLedger initial events).map TerminalPhysicalCharge.gate).Nodup ∧
    ∀ gate, gate ∈ (terminalPhysicalChargeLedger initial events).map
        TerminalPhysicalCharge.gate ↔ TerminalPrimitiveRecord.gate gate ∈ final := by
  revert valid
  induction linked with
  | nil =>
      intro _valid
      have gatesEqual :
          (terminalPhysicalChargeLedger initial []).map TerminalPhysicalCharge.gate =
            terminalSelectedGates initial := by
        simp only [terminalPhysicalChargeLedger, List.filterMap_nil, List.append_nil,
          terminalInitialPhysicalCharges_gates]
      rw [gatesEqual]
      refine ⟨terminalSelectedGates_nodup initial, ?_⟩
      intro gate
      exact (mem_terminalSelectedGates_iff initial gate).trans
        (terminalGateSelected_eq_true_iff initial gate)
  | @snoc events event linked ih =>
      intro valid
      have prefixValid : terminalPhysicalChargeEventsValid events := by
        intro earlier member
        exact valid earlier (List.mem_append_left _ member)
      have previous := ih prefixValid
      have lastMember : event ∈ events ++ [event] :=
        List.mem_append_right _ (List.Mem.head _)
      obtain ⟨shape, fresh, kind, selected⟩ := valid event lastMember
      rw [terminalPhysicalChargeLedger_snoc]
      cases required : event.required with
      | gate inserted =>
          simp only [terminalEventPhysicalCharge?, required, selected, Option.toList,
            List.map_append, List.map_cons, List.map_nil]
          constructor
          · apply List.nodup_append.mpr
            refine ⟨previous.1, List.nodup_cons.mpr ⟨?_, List.nodup_nil⟩, ?_⟩
            · exact List.not_mem_nil
            · intro old oldMember last lastMember same
              have lastEq : last = inserted := List.mem_singleton.mp lastMember
              have oldEq : old = inserted := same.trans lastEq
              apply fresh
              rw [required, ← oldEq]
              exact (previous.2 old).mp oldMember
          · intro gate
            rw [shape, required]
            constructor
            · intro member
              cases List.mem_append.mp member with
              | inl earlier =>
                  exact List.mem_cons.mpr (Or.inr ((previous.2 gate).mp earlier))
              | inr added =>
                  exact List.mem_cons.mpr
                    (Or.inl (congrArg TerminalPrimitiveRecord.gate
                      (List.mem_singleton.mp added)))
            · intro member
              cases List.mem_cons.mp member with
              | inl added =>
                  apply List.mem_append_right
                  exact List.mem_singleton.mpr (TerminalPrimitiveRecord.gate.inj added)
              | inr earlier =>
                  exact List.mem_append_left _ ((previous.2 gate).mpr earlier)
      | boundary index | interface index | profile index =>
          simp only [terminalEventPhysicalCharge?, required, Option.toList, List.append_nil]
          refine ⟨previous.1, ?_⟩
          intro gate
          rw [shape, required]
          simpa only [List.mem_cons, reduceCtorEq, false_or] using previous.2 gate

private theorem terminalSaturatePhysicalEvents_valid
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalPhysicalChargeEventsValid (terminalSaturateTrace system seed).events := by
  intro event member
  obtain ⟨shape, kind, selected, _rule⟩ :=
    terminalSaturateTrace_event_valid system seed event member
  exact ⟨shape, (terminalSaturateTrace_event_context system seed event member).2,
    kind, selected⟩

/-- Each physical gate appears at most once in the computed charge ledger,
    including inherited seed charges and every generated insertion. -/
theorem terminalSaturatePhysicalCharges_nodup
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    ((terminalSaturatePhysicalCharges system seed).map TerminalPhysicalCharge.gate).Nodup :=
  (terminalPhysicalChargeLedger_invariant (terminalSaturateTrace_eventsLinked system seed)
    (terminalSaturatePhysicalEvents_valid system seed)).1

/-- The computed charge ledger covers exactly the physical gates in actual
    executable saturation. It omits no seed or generated gate. -/
theorem terminalSaturatePhysicalCharges_complete
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (gate : Fin gates) :
    gate ∈ (terminalSaturatePhysicalCharges system seed).map TerminalPhysicalCharge.gate ↔
      TerminalPrimitiveRecord.gate gate ∈ terminalSaturateRecords system seed :=
  ((terminalPhysicalChargeLedger_invariant (terminalSaturateTrace_eventsLinked system seed)
    (terminalSaturatePhysicalEvents_valid system seed)).2 gate).trans
      (terminalSaturateTrace_replayRecords_iff system seed (TerminalPrimitiveRecord.gate gate))


/-- Every charge comes from the normalized seed or from its actual generated
    event, with the recorded rule, active dependent and fresh gate insertion.
    This introduction provenance is not a global materializer ownership map. -/
theorem terminalSaturatePhysicalCharges_provenance
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (charge : TerminalPhysicalCharge inputs gates outputs profileWidth)
    (member : charge ∈ terminalSaturatePhysicalCharges system seed) :
    (charge.provenance = .seed ∧
      TerminalPrimitiveRecord.gate charge.gate ∈
        (terminalSaturateTrace system seed).normalizedSeed.reverse) ∨
    ∃ event, event ∈ (terminalSaturateTrace system seed).events ∧
      ∃ kind, charge.provenance = .generated kind event.dependent ∧
        event.required = TerminalPrimitiveRecord.gate charge.gate ∧
        event.kind? = some kind ∧
        system.requires kind event.dependent (TerminalPrimitiveRecord.gate charge.gate) = true ∧
        event.dependent ∈ event.beforeRecords ∧
        TerminalPrimitiveRecord.gate charge.gate ∉ event.beforeRecords := by
  change charge ∈ terminalInitialPhysicalCharges
      (terminalSaturateTrace system seed).normalizedSeed.reverse ++
    (terminalSaturateTrace system seed).events.filterMap terminalEventPhysicalCharge? at member
  cases List.mem_append.mp member with
  | inl inherited =>
      obtain ⟨gate, gateMember, same⟩ := List.mem_map.mp inherited
      cases same
      apply Or.inl
      refine ⟨rfl, ?_⟩
      exact (terminalGateSelected_eq_true_iff _ gate).mp
        ((mem_terminalSelectedGates_iff _ gate).mp gateMember)
  | inr generated =>
      obtain ⟨event, eventMember, emitted⟩ := List.mem_filterMap.mp generated
      obtain ⟨_shape, kind, selected, rule⟩ :=
        terminalSaturateTrace_event_valid system seed event eventMember
      have context := terminalSaturateTrace_event_context system seed event eventMember
      cases required : event.required with
      | gate gate =>
          simp only [terminalEventPhysicalCharge?, required, selected, Option.some.injEq] at emitted
          cases emitted
          refine Or.inr ⟨event, eventMember, kind, rfl, required, selected, ?_,
            context.1, ?_⟩
          · simpa only [required] using rule
          · simpa only [required] using context.2
      | boundary index | interface index | profile index =>
          simp only [terminalEventPhysicalCharge?, required, reduceCtorEq] at emitted

private theorem terminalPhysicalChargeLookup_iff
    {inputs gates outputs profileWidth : Nat}
    (gate : Fin gates)
    (provenance : TerminalPhysicalChargeProvenance inputs gates outputs profileWidth)
    (charges : List (TerminalPhysicalCharge inputs gates outputs profileWidth))
    (distinct : (charges.map TerminalPhysicalCharge.gate).Nodup) :
    terminalPhysicalChargeLookup gate charges = some provenance ↔
      (⟨gate, provenance⟩ : TerminalPhysicalCharge inputs gates outputs profileWidth) ∈ charges := by
  induction charges with
  | nil =>
      simp only [terminalPhysicalChargeLookup, reduceCtorEq, List.mem_nil_iff]
  | cons charge remaining ih =>
      have parts := List.nodup_cons.mp (by simpa only [List.map_cons] using distinct)
      by_cases gateEqual : charge.gate = gate
      · have absent :
            (⟨gate, provenance⟩ : TerminalPhysicalCharge inputs gates outputs profileWidth) ∉ remaining := by
          intro member
          apply parts.1
          have gateMember : gate ∈ remaining.map TerminalPhysicalCharge.gate :=
            List.mem_map.mpr ⟨⟨gate, provenance⟩, member, rfl⟩
          simpa only [gateEqual] using gateMember
        simp only [terminalPhysicalChargeLookup, if_pos gateEqual, Option.some.injEq,
          List.mem_cons, absent, or_false]
        constructor
        · intro provenanceEqual
          cases charge with
          | mk originalGate originalProvenance =>
              dsimp only at gateEqual provenanceEqual
              cases gateEqual
              cases provenanceEqual
              rfl
        · intro same
          exact (congrArg TerminalPhysicalCharge.provenance same).symm
      · have different :
            (⟨gate, provenance⟩ : TerminalPhysicalCharge inputs gates outputs profileWidth) ≠ charge := by
          intro same
          exact gateEqual (congrArg TerminalPhysicalCharge.gate same).symm
        simp only [terminalPhysicalChargeLookup, if_neg gateEqual, List.mem_cons,
          different, false_or]
        exact ih parts.2

/-- Lookup returns exactly the provenance of the matching computed charge.
    Completeness and duplicate-freedom come from the actual saturation run,
    not a caller-supplied uniqueness or coverage certificate. -/
theorem terminalSaturatePhysicalChargeProvenance?_iff
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (gate : Fin gates)
    (provenance : TerminalPhysicalChargeProvenance inputs gates outputs profileWidth) :
    terminalSaturatePhysicalChargeProvenance? system seed gate = some provenance ↔
      (⟨gate, provenance⟩ : TerminalPhysicalCharge inputs gates outputs profileWidth) ∈
        terminalSaturatePhysicalCharges system seed :=
  terminalPhysicalChargeLookup_iff gate provenance (terminalSaturatePhysicalCharges system seed)
    (terminalSaturatePhysicalCharges_nodup system seed)

private theorem physicalChargeListNoDuplicates_of_nodup {alpha : Type}
    {items : List alpha} (distinct : items.Nodup) : ListNoDuplicates items := by
  induction items with
  | nil => exact ListNoDuplicates.nil
  | cons head tail ih =>
      have parts := List.nodup_cons.mp distinct
      exact ListNoDuplicates.cons parts.1 (ih parts.2)

/-- The entire computed support size equals its complete physical unit-charge
    ledger. This is not a full-minimum, materializer or polynomial-runtime claim. -/
theorem terminalCandidateSaturatePhysicalCharges_size
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalSaturationCostSnapshot candidate model
      (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)).supportSize =
      (terminalSaturatePhysicalCharges (terminalCandidateSaturationSystem candidate model) seed).length := by
  let system := terminalCandidateSaturationSystem candidate model
  let charges := terminalSaturatePhysicalCharges system seed
  let records := terminalSaturateRecords system seed
  let selected := terminalSelectedGates records
  have members : ∀ gate, gate ∈ charges.map TerminalPhysicalCharge.gate ↔ gate ∈ selected := by
    intro gate
    exact (terminalSaturatePhysicalCharges_complete system seed gate).trans
      ((terminalGateSelected_eq_true_iff records gate).symm.trans
        (mem_terminalSelectedGates_iff records gate).symm)
  have forward := noDuplicatesSubset_length_le
    (charges.map TerminalPhysicalCharge.gate) selected
    (physicalChargeListNoDuplicates_of_nodup
      (terminalSaturatePhysicalCharges_nodup system seed))
    (fun gate member => (members gate).mp member)
  have backward := noDuplicatesSubset_length_le
    selected (charges.map TerminalPhysicalCharge.gate)
    (physicalChargeListNoDuplicates_of_nodup (terminalSelectedGates_nodup records))
    (fun gate member => (members gate).mpr member)
  have sameLength : charges.length = selected.length := by
    simpa only [List.length_map] using Nat.le_antisymm forward backward
  change (extractTerminalSupport candidate records).gateCount = charges.length
  rw [extractTerminalSupport_gateCount]
  exact sameLength.symm

end DirectWire
end PNP

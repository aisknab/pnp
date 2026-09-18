/-
Copyright (c) 2026 PNP Labs.

Persistent physical identities for complete mixed programs. Every source gate
keeps its original coordinate. Each actual allocation carries the computed
outer execution position and its inner stage/event/local-gate coordinates.
Removed allocations remain in the historical charge ledger.

The public ledger is constructed from the compiler's actual execution and its
initial source. No owner map, namespace, charge total or invariant is supplied.
This does not prove global certificate discovery, full manuscript profiles,
unconditional ZeroSlack or polynomial execution.
-/

import PNP.NANDWireOpenPrimitiveOwnership
import PNP.NANDWireStructuralOwnership
import PNP.NANDWireRecodingOwnership

namespace PNP.DirectWire.WireOpenProgram

open WireObligationHistory (State)
open WireDescendantHistory (DescendantOrigin PersistentOwnership originalOrigins)

variable {inputs outputs fields initialGates physicalGates : Nat}
variable {source : WireCarrier inputs outputs fields}

namespace Transition

variable {before after : State source} {event : RawEvent}

/-- The local map comes from the actual primitive, nested, reordering or recoding receipt. -/
def localLedger (step : Transition source before event after) :
    PersistentOwnership before.current.implementation.gateCount after.current.implementation.gateCount :=
  match step with
  | .primitive _ _ _ _ _ _ inner => PrimitiveOwnership.labelled inner
  | .support _ _ _ _ receipt => receipt.ownership
  | .structural _ _ _ _ receipt => receipt.ownership
  | .recoding _ _ _ _ _ receipt => receipt.checked.ownership

theorem local_physical_ownership (step : Transition source before event after) :
    step.localLedger.live.length = after.current.implementation.gateCount ∧
      step.localLedger.charged.length = step.charged ∧
      step.localLedger.removed.length = step.removed ∧
      (step.localLedger.live ++ step.localLedger.removed).Nodup ∧
      (step.localLedger.live ++ step.localLedger.removed).Perm
        (originalOrigins before.current.implementation.gateCount ++ step.localLedger.charged) := by
  cases step with
  | primitive raw kind action decoded inner => exact PrimitiveOwnership.labelled_physical_ownership inner
  | support raw kind receipt => exact receipt.physical_ownership
  | structural raw kind receipt => exact receipt.physical_ownership
  | recoding rawEncoder rawDecoder kind receipt => exact receipt.checked.physical_ownership

theorem local_charged_origin (step : Transition source before event after)
    (origin : DescendantOrigin before.current.implementation.gateCount)
    (member : origin ∈ step.localLedger.charged) :
    ∃ stage identity localGate, origin = .allocated stage identity localGate := by
  cases origin with
  | original gate =>
      have checked := step.local_physical_ownership
      have separate := (List.nodup_append.mp (checked.2.2.2.2.nodup checked.2.2.2.1)).2.2
      exact False.elim (separate (.original gate) (List.mem_ofFn.mpr ⟨gate, rfl⟩)
        (.original gate) member rfl)
  | allocated stage identity localGate => exact ⟨stage, identity, localGate, rfl⟩

end Transition

/-- The computed outer position separates namespaces even when numeric event
identities coincide in independent nested programs or ambient operations. -/
inductive ProgramOrigin (initialGates : Nat) where
  | original (gate : Fin initialGates)
  | allocated (position stage event localGate : Nat)
  deriving Repr, DecidableEq

def programOriginals (initialGates : Nat) : List (ProgramOrigin initialGates) :=
  List.ofFn ProgramOrigin.original

def bornBefore (position : Nat) : ProgramOrigin initialGates → Prop
  | .original _ => True
  | .allocated created _ _ _ => created < position

theorem bornBefore_mono {left right : Nat} (origin : ProgramOrigin initialGates)
    (before : bornBefore left origin) (included : left ≤ right) : bornBefore right origin := by
  cases origin with
  | original _ => exact True.intro
  | allocated position stage event localGate => exact Nat.lt_of_lt_of_le before included

structure ProgramOwnership (initialGates physicalGates : Nat) where
  origin : Fin physicalGates → ProgramOrigin initialGates
  charged : List (ProgramOrigin initialGates)
  removed : List (ProgramOrigin initialGates)

private theorem ofFn_nodup {alpha : Type} {width : Nat}
    (value : Fin width → alpha) (injective : Function.Injective value) :
    (List.ofFn value).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro left right leftBound rightBound before same
  have leftValid : left < width := by simpa only [List.length_ofFn] using leftBound
  have rightValid : right < width := by simpa only [List.length_ofFn] using rightBound
  have sameValue : value ⟨left, leftValid⟩ = value ⟨right, rightValid⟩ := by
    simpa only [List.getElem_ofFn] using same
  have sameIndex : left = right := congrArg Fin.val (injective sameValue)
  omega

private theorem ofFn_injective {alpha : Type} {width : Nat}
    (value : Fin width → alpha) (distinct : (List.ofFn value).Nodup) :
    Function.Injective value := by
  intro left right same
  have leftBound : left.val < (List.ofFn value).length := by
    simpa only [List.length_ofFn] using left.isLt
  have rightBound : right.val < (List.ofFn value).length := by
    simpa only [List.length_ofFn] using right.isLt
  rcases Nat.lt_trichotomy left.val right.val with before | equal | after
  · have different := List.pairwise_iff_getElem.mp distinct
      left.val right.val leftBound rightBound before
    have differentValue : value left ≠ value right := by
      simpa only [List.getElem_ofFn] using different
    exact False.elim (differentValue same)
  · exact Fin.ext equal
  · have different := List.pairwise_iff_getElem.mp distinct
      right.val left.val rightBound leftBound after
    have differentValue : value right ≠ value left := by
      simpa only [List.getElem_ofFn] using different
    exact False.elim (differentValue same.symm)

private theorem swap_suffixes {alpha : Type} (first middle last : List alpha) :
    ((first ++ middle) ++ last).Perm ((first ++ last) ++ middle) := by
  simpa only [List.append_assoc] using
    (List.perm_append_comm (l₁ := middle) (l₂ := last)).append_left first

namespace ProgramOwnership

def live (ledger : ProgramOwnership initialGates physicalGates) : List (ProgramOrigin initialGates) :=
  List.ofFn ledger.origin

def initial (initialGates : Nat) : ProgramOwnership initialGates initialGates :=
  ⟨ProgramOrigin.original, [], []⟩

/-- This invariant is derived internally from the source and the actual run. -/
structure WellFormed (ledger : ProgramOwnership initialGates physicalGates) (position : Nat) : Prop where
  distinct : (ledger.live ++ ledger.removed).Nodup
  conserved : (ledger.live ++ ledger.removed).Perm (programOriginals initialGates ++ ledger.charged)
  chargedBefore : ∀ origin, origin ∈ ledger.charged → bornBefore position origin

theorem initial_wellFormed (initialGates : Nat) : WellFormed (initial initialGates) 0 := by
  refine ⟨?_, List.Perm.refl _, ?_⟩
  · change (List.ofFn ProgramOrigin.original ++ []).Nodup
    rw [List.append_nil]
    exact ofFn_nodup ProgramOrigin.original
      (fun _ _ same => ProgramOrigin.original.inj same)
  · intro origin member
    cases member

theorem accounted_before (ledger : ProgramOwnership initialGates physicalGates)
    (position : Nat) (checked : WellFormed ledger position) (origin : ProgramOrigin initialGates)
    (member : origin ∈ programOriginals initialGates ++ ledger.charged) :
    bornBefore position origin := by
  rcases List.mem_append.mp member with original | charged
  · obtain ⟨gate, originAt⟩ := List.mem_ofFn.mp original
    rw [← originAt]
    exact True.intro
  · exact checked.chargedBefore origin charged

theorem origin_before (ledger : ProgramOwnership initialGates physicalGates)
    (position : Nat) (checked : WellFormed ledger position) (gate : Fin physicalGates) :
    bornBefore position (ledger.origin gate) :=
  ledger.accounted_before position checked _ (checked.conserved.subset
    (List.mem_append_left _ (List.mem_ofFn.mpr ⟨gate, rfl⟩)))

theorem origin_injective (ledger : ProgramOwnership initialGates physicalGates)
    (position : Nat) (checked : WellFormed ledger position) : Function.Injective ledger.origin :=
  ofFn_injective ledger.origin (List.nodup_append.mp checked.distinct).1

/-- Old physical positions retain their established global identities. Only
actual fresh local allocations receive this computed outer execution position. -/
def liftOrigin (ledger : ProgramOwnership initialGates physicalGates) (position : Nat) :
    DescendantOrigin physicalGates → ProgramOrigin initialGates
  | .original gate => ledger.origin gate
  | .allocated stage event localGate => .allocated position stage event localGate

theorem liftOrigin_original (ledger : ProgramOwnership initialGates physicalGates)
    (position : Nat) (gate : Fin physicalGates) :
    ledger.liftOrigin position (.original gate) = ledger.origin gate := rfl

theorem liftOrigin_allocated (ledger : ProgramOwnership initialGates physicalGates)
    (position stage event localGate : Nat) :
    ledger.liftOrigin position (.allocated stage event localGate) =
      .allocated position stage event localGate := rfl

theorem liftOrigin_injective (ledger : ProgramOwnership initialGates physicalGates)
    (position : Nat) (checked : WellFormed ledger position) :
    Function.Injective (ledger.liftOrigin position) := by
  intro left right same
  cases left with
  | original left =>
      cases right with
      | original right =>
          exact congrArg DescendantOrigin.original (ledger.origin_injective position checked same)
      | allocated stage event localGate =>
          have before := ledger.origin_before position checked left
          change ledger.origin left = .allocated position stage event localGate at same
          rw [same] at before
          exact False.elim (Nat.lt_irrefl position before)
  | allocated stage event localGate =>
      cases right with
      | original right =>
          have before := ledger.origin_before position checked right
          change ProgramOrigin.allocated position stage event localGate = ledger.origin right at same
          rw [← same] at before
          exact False.elim (Nat.lt_irrefl position before)
      | allocated otherStage otherEvent otherGate =>
          obtain ⟨_, sameStage, sameEvent, sameGate⟩ := ProgramOrigin.allocated.inj same
          cases sameStage
          cases sameEvent
          cases sameGate
          rfl

theorem lift_originals (ledger : ProgramOwnership initialGates physicalGates) (position : Nat) :
    (originalOrigins physicalGates).map (ledger.liftOrigin position) = ledger.live := by
  rw [originalOrigins, List.map_ofFn]
  rfl

variable {before after : State source} {event : RawEvent}

def advance (ledger : ProgramOwnership initialGates before.current.implementation.gateCount)
    (position : Nat) (step : Transition source before event after) :
    ProgramOwnership initialGates after.current.implementation.gateCount :=
  ⟨fun gate => ledger.liftOrigin position (step.localLedger.origin gate),
    ledger.charged ++ step.localLedger.charged.map (ledger.liftOrigin position),
    ledger.removed ++ step.localLedger.removed.map (ledger.liftOrigin position)⟩

theorem advance_live (ledger : ProgramOwnership initialGates before.current.implementation.gateCount)
    (position : Nat) (step : Transition source before event after) :
    (ledger.advance position step).live = step.localLedger.live.map (ledger.liftOrigin position) := by
  rw [PersistentOwnership.live, List.map_ofFn]
  rfl

theorem advance_charged_length (ledger : ProgramOwnership initialGates before.current.implementation.gateCount)
    (position : Nat) (step : Transition source before event after) :
    (ledger.advance position step).charged.length = ledger.charged.length + step.charged := by
  change (ledger.charged ++ step.localLedger.charged.map (ledger.liftOrigin position)).length = _
  rw [List.length_append, List.length_map, step.local_physical_ownership.2.1]

theorem advance_removed_length (ledger : ProgramOwnership initialGates before.current.implementation.gateCount)
    (position : Nat) (step : Transition source before event after) :
    (ledger.advance position step).removed.length = ledger.removed.length + step.removed := by
  change (ledger.removed ++ step.localLedger.removed.map (ledger.liftOrigin position)).length = _
  rw [List.length_append, List.length_map, step.local_physical_ownership.2.2.1]

theorem advance_charge_origin (ledger : ProgramOwnership initialGates before.current.implementation.gateCount)
    (position : Nat) (step : Transition source before event after) (origin : ProgramOrigin initialGates)
    (member : origin ∈ step.localLedger.charged.map (ledger.liftOrigin position)) :
    ∃ stage identity localGate, origin = .allocated position stage identity localGate := by
  obtain ⟨inner, present, equation⟩ := List.mem_map.mp member
  obtain ⟨stage, identity, localGate, innerAt⟩ := step.local_charged_origin inner present
  refine ⟨stage, identity, localGate, ?_⟩
  rw [← equation, innerAt]
  rfl

theorem advance_physical_position
    (ledger : ProgramOwnership initialGates before.current.implementation.gateCount)
    (position : Nat) (step : Transition source before event after)
    (gate : Fin after.current.implementation.gateCount) :
    (ledger.advance position step).origin gate =
      ledger.liftOrigin position (step.localLedger.origin gate) := rfl

/-- The outer global identity uses the exact topological position map which
actually builds the nested support's returned circuit. -/
theorem advance_support_compiled_position
    (before : State source) (event : RawEvent) (raw : WireDescendantCertificate.RawCertificate)
    (kind : event.action = .support raw) (receipt : WireOpenSupportSplice.Receipt before raw)
    (ledger : ProgramOwnership initialGates before.current.implementation.gateCount) (position : Nat)
    (node : Fin ((ArbitrarySupportSplice.exterior receipt.records).length +
      receipt.executed.run.result.gateCount)) :
    (ledger.advance position (.support before event raw kind receipt)).origin
        (receipt.executed.compiled.position node) =
      ledger.liftOrigin position
        (WireOpenSupportSplice.ownershipRawNode before receipt.records receipt.executed node) :=
  congrArg (ledger.liftOrigin position)
    (WireOpenSupportSplice.ownership_compiled_position before receipt.records receipt.executed node)

theorem advance_partition (ledger : ProgramOwnership initialGates before.current.implementation.gateCount)
    (position : Nat) (step : Transition source before event after) (checked : WellFormed ledger position) :
    ((ledger.advance position step).live ++ (ledger.advance position step).removed).Perm
      (programOriginals initialGates ++ (ledger.advance position step).charged) := by
  have inside := step.local_physical_ownership.2.2.2.2.map (ledger.liftOrigin position)
  simp only [List.map_append] at inside
  rw [ledger.lift_originals position] at inside
  have first := swap_suffixes (step.localLedger.live.map (ledger.liftOrigin position))
    ledger.removed (step.localLedger.removed.map (ledger.liftOrigin position))
  have second := inside.append_right ledger.removed
  have third := swap_suffixes ledger.live
    (step.localLedger.charged.map (ledger.liftOrigin position)) ledger.removed
  have last := checked.conserved.append_right (step.localLedger.charged.map (ledger.liftOrigin position))
  rw [advance_live]
  change (step.localLedger.live.map (ledger.liftOrigin position) ++
    (ledger.removed ++ step.localLedger.removed.map (ledger.liftOrigin position))).Perm
      (programOriginals initialGates ++
        (ledger.charged ++ step.localLedger.charged.map (ledger.liftOrigin position)))
  have first' :
      (step.localLedger.live.map (ledger.liftOrigin position) ++
        (ledger.removed ++ step.localLedger.removed.map (ledger.liftOrigin position))).Perm
      ((step.localLedger.live.map (ledger.liftOrigin position) ++
        step.localLedger.removed.map (ledger.liftOrigin position)) ++ ledger.removed) := by
    simpa only [List.append_assoc] using first
  simpa only [List.append_assoc] using first'.trans (second.trans (third.trans last))

theorem advance_wellFormed (ledger : ProgramOwnership initialGates before.current.implementation.gateCount)
    (position : Nat) (step : Transition source before event after) (checked : WellFormed ledger position) :
    WellFormed (ledger.advance position step) (position + 1) := by
  have conserved := ledger.advance_partition position step checked
  have localChecked := step.local_physical_ownership
  have chargesDistinct := (List.nodup_append.mp
    (localChecked.2.2.2.2.nodup localChecked.2.2.2.1)).2.1
  have mappedDistinct :
      (step.localLedger.charged.map (ledger.liftOrigin position)).Nodup :=
    List.Pairwise.map (ledger.liftOrigin position)
      (fun _ _ different same => different (ledger.liftOrigin_injective position checked same))
      chargesDistinct
  have totalDistinct :
      (programOriginals initialGates ++
        (ledger.charged ++ step.localLedger.charged.map (ledger.liftOrigin position))).Nodup := by
    rw [← List.append_assoc]
    apply List.nodup_append.mpr
    refine ⟨checked.conserved.nodup checked.distinct, mappedDistinct, ?_⟩
    intro old oldMember fresh freshMember same
    have before := ledger.accounted_before position checked old oldMember
    obtain ⟨stage, identity, localGate, freshAt⟩ :=
      ledger.advance_charge_origin position step fresh freshMember
    rw [same, freshAt] at before
    exact Nat.lt_irrefl position before
  refine ⟨conserved.symm.nodup totalDistinct, conserved, ?_⟩
  intro origin member
  change origin ∈ ledger.charged ++ step.localLedger.charged.map (ledger.liftOrigin position) at member
  rcases List.mem_append.mp member with old | fresh
  · exact bornBefore_mono origin (checked.chargedBefore origin old) (Nat.le_succ position)
  · obtain ⟨stage, identity, localGate, originAt⟩ :=
      ledger.advance_charge_origin position step origin fresh
    rw [originAt]
    exact Nat.lt_succ_self position

end ProgramOwnership

namespace Execution

variable {before after : State source} {events : List RawEvent}

/-- Follow every actual transition, assigning namespace positions internally. -/
def carryOwnership {before after : State source} {events : List RawEvent}
    (trace : Execution source before events after) (position : Nat)
    (ledger : ProgramOwnership initialGates before.current.implementation.gateCount) :
    ProgramOwnership initialGates after.current.implementation.gateCount :=
  match trace with
  | .nil _ => ledger
  | .cons step tail => tail.carryOwnership (position + 1) (ledger.advance position step)

theorem carryOwnership_wellFormed (trace : Execution source before events after) :
    ∀ (position : Nat) (ledger : ProgramOwnership initialGates before.current.implementation.gateCount),
      ProgramOwnership.WellFormed ledger position →
      ProgramOwnership.WellFormed (trace.carryOwnership position ledger) (position + events.length) := by
  induction trace with
  | nil state =>
      intro position ledger checked
      simpa only [carryOwnership, List.length_nil, Nat.add_zero] using checked
  | @cons before middle after event remaining step tail ih =>
      intro position ledger checked
      have reached := ih (position + 1) (ledger.advance position step)
        (ledger.advance_wellFormed position step checked)
      have sameBound : position + 1 + remaining.length = position + (event :: remaining).length := by
        simp only [List.length_cons]
        omega
      rw [sameBound] at reached
      exact reached

theorem carryOwnership_charged_length (trace : Execution source before events after) :
    ∀ (position : Nat) (ledger : ProgramOwnership initialGates before.current.implementation.gateCount),
      (trace.carryOwnership position ledger).charged.length = ledger.charged.length + trace.charged := by
  induction trace with
  | nil state => intro position ledger; rfl
  | cons step tail ih =>
      intro position ledger
      change (tail.carryOwnership (position + 1) (ledger.advance position step)).charged.length =
        ledger.charged.length + (step.charged + tail.charged)
      rw [ih, ledger.advance_charged_length position step]
      exact Nat.add_assoc _ _ _

theorem carryOwnership_removed_length (trace : Execution source before events after) :
    ∀ (position : Nat) (ledger : ProgramOwnership initialGates before.current.implementation.gateCount),
      (trace.carryOwnership position ledger).removed.length = ledger.removed.length + trace.removed := by
  induction trace with
  | nil state => intro position ledger; rfl
  | cons step tail ih =>
      intro position ledger
      change (tail.carryOwnership (position + 1) (ledger.advance position step)).removed.length =
        ledger.removed.length + (step.removed + tail.removed)
      rw [ih, ledger.advance_removed_length position step]
      exact Nat.add_assoc _ _ _

/-- Even a later deletion cannot erase the historical record of an allocation. -/
theorem carryOwnership_charge_survives (trace : Execution source before events after) :
    ∀ (position : Nat) (ledger : ProgramOwnership initialGates before.current.implementation.gateCount)
      (origin : ProgramOrigin initialGates), origin ∈ ledger.charged →
        origin ∈ (trace.carryOwnership position ledger).charged := by
  induction trace with
  | nil state => intro position ledger origin member; exact member
  | cons step tail ih =>
      intro position ledger origin member
      exact ih (position + 1) (ledger.advance position step) origin
        (List.mem_append_left _ member)

end Execution

namespace CompiledProgram

variable {raw : List RawEvent}

/-- Public source-only ownership. Neither the initial map nor the namespace
position, allocation history, charges or removals are supplied by a caller. -/
def ownership (program : CompiledProgram source raw) :
    ProgramOwnership source.implementation.gateCount program.result.implementation.gateCount :=
  program.execution.carryOwnership 0 (ProgramOwnership.initial source.implementation.gateCount)

theorem ownership_wellFormed (program : CompiledProgram source raw) :
    ProgramOwnership.WellFormed program.ownership raw.length := by
  have checked := program.execution.carryOwnership_wellFormed 0
    (ProgramOwnership.initial source.implementation.gateCount)
    (ProgramOwnership.initial_wellFormed source.implementation.gateCount)
  simp only [Nat.zero_add, List.length_map, program.ordered.order_length] at checked
  exact checked

/-- All original and ever-allocated physical identities occur exactly once,
either live or removed. Counts are those of the independently defined actual
execution, including allocations which a later action removes. -/
theorem physical_ownership (program : CompiledProgram source raw) :
    program.ownership.live.length = program.result.implementation.gateCount ∧
      program.ownership.charged.length = program.execution.charged ∧
      program.ownership.removed.length = program.execution.removed ∧
      (program.ownership.live ++ program.ownership.removed).Nodup ∧
      (program.ownership.live ++ program.ownership.removed).Perm
        (programOriginals source.implementation.gateCount ++ program.ownership.charged) := by
  have checked := program.ownership_wellFormed
  refine ⟨List.length_ofFn, ?_, ?_, checked.distinct, checked.conserved⟩
  · change (program.execution.carryOwnership 0
      (ProgramOwnership.initial source.implementation.gateCount)).charged.length = _
    rw [program.execution.carryOwnership_charged_length]
    exact Nat.zero_add _
  · change (program.execution.carryOwnership 0
      (ProgramOwnership.initial source.implementation.gateCount)).removed.length = _
    rw [program.execution.carryOwnership_removed_length]
    exact Nat.zero_add _

theorem ownership_origin_injective (program : CompiledProgram source raw) :
    Function.Injective program.ownership.origin :=
  program.ownership.origin_injective raw.length program.ownership_wellFormed

theorem ownership_charge_origin (program : CompiledProgram source raw)
    (origin : ProgramOrigin source.implementation.gateCount) (member : origin ∈ program.ownership.charged) :
    ∃ position stage identity localGate,
      position < raw.length ∧ origin = .allocated position stage identity localGate := by
  cases origin with
  | original gate =>
      have checked := program.ownership_wellFormed
      have separate := (List.nodup_append.mp (checked.conserved.nodup checked.distinct)).2.2
      exact False.elim (separate (.original gate) (List.mem_ofFn.mpr ⟨gate, rfl⟩)
        (.original gate) member rfl)
  | allocated position stage identity localGate =>
      exact ⟨position, stage, identity, localGate,
        program.ownership_wellFormed.chargedBefore (.allocated position stage identity localGate) member, rfl⟩

end CompiledProgram

theorem allocation_namespaces_disjoint
    (left right leftStage rightStage leftEvent rightEvent leftGate rightGate : Nat)
    (different : left ≠ right) :
    (ProgramOrigin.allocated left leftStage leftEvent leftGate : ProgramOrigin initialGates) ≠
      .allocated right rightStage rightEvent rightGate :=
  fun same => different (ProgramOrigin.allocated.inj same).1

end PNP.DirectWire.WireOpenProgram

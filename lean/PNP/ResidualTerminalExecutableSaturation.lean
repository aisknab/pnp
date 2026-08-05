/-
Copyright (c) 2026 PNP Labs.

Executable finite saturation for the terminal primitive-record universe.  A
work-list traversal follows the ten manuscript-labelled dependency relations,
deduplicates every discovered record against the complete finite universe, and
stops after at most one visit per primitive record.

The exactness theorem below identifies list membership in the computed result
with the inductive saturation relation from `ResidualTerminalSaturation`.  No
caller closure certificate or host-side schedule is accepted.  This remains a
support-record closure theorem: it does not classify the manuscript frontier,
construct a proper positive support, or prove square/projection compatibility.
-/

import PNP.ResidualTerminalSaturation
import PNP.DirectWireBaseline

namespace PNP
namespace DirectWire

/-- The ten saturation rule tags in one deterministic order. -/
def allTerminalSaturationRuleKinds : List TerminalSaturationRuleKind :=
  [.gateSource, .interfaceConsumer, .origin, .kernel, .obligation,
    .prefixTail, .budget, .saturation, .direction, .charge]

/-- Every terminal saturation rule tag occurs in the deterministic list. -/
theorem mem_allTerminalSaturationRuleKinds
    (kind : TerminalSaturationRuleKind) :
    kind ∈ allTerminalSaturationRuleKinds := by
  cases kind <;> simp only [allTerminalSaturationRuleKinds, List.mem_cons,
    true_or, or_true]

private def terminalAny {alpha : Type} : List alpha → (alpha → Bool) → Bool
  | [], _predicate => false
  | item :: items, predicate => predicate item || terminalAny items predicate

private theorem terminalAny_true_iff {alpha : Type}
    (items : List alpha) (predicate : alpha → Bool) :
    terminalAny items predicate = true ↔
      ∃ item, item ∈ items ∧ predicate item = true := by
  induction items with
  | nil =>
      constructor
      · intro impossible
        exact Bool.noConfusion impossible
      · rintro ⟨item, member, _checked⟩
        cases member
  | cons head tail ih =>
      unfold terminalAny
      cases headCheck : predicate head with
      | false =>
          change terminalAny tail predicate = true ↔ _
          constructor
          · intro checked
            obtain ⟨item, member, itemCheck⟩ := ih.mp checked
            exact ⟨item, List.Mem.tail head member, itemCheck⟩
          · rintro ⟨item, member, itemCheck⟩
            cases List.mem_cons.mp member with
            | inl equal =>
                subst item
                rw [headCheck] at itemCheck
                exact Bool.noConfusion itemCheck
            | inr tailMember =>
                exact ih.mpr ⟨item, tailMember, itemCheck⟩
      | true =>
          change true = true ↔ _
          constructor
          · intro _checked
            exact ⟨head, List.Mem.head tail, headCheck⟩
          · intro _witness
            rfl

/-- Boolean union of the ten labelled direct dependency relations. -/
def terminalSaturationEdge
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (dependent required :
      TerminalPrimitiveRecord inputs gates outputs profileWidth) : Bool :=
  terminalAny allTerminalSaturationRuleKinds fun kind =>
    system.requires kind dependent required

/-- The executable edge test is true exactly for one of the ten governed
    dependency relations. -/
theorem terminalSaturationEdge_eq_true_iff
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (dependent required :
      TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    terminalSaturationEdge system dependent required = true ↔
      ∃ kind, system.requires kind dependent required = true := by
  unfold terminalSaturationEdge
  constructor
  · intro checked
    obtain ⟨kind, _member, edge⟩ := (terminalAny_true_iff _ _).1 checked
    exact ⟨kind, edge⟩
  · rintro ⟨kind, edge⟩
    exact (terminalAny_true_iff _ _).2
      ⟨kind, mem_allTerminalSaturationRuleKinds kind, edge⟩

private theorem nodup_of_listNoDuplicates {alpha : Type}
    {items : List alpha} (distinct : ListNoDuplicates items) :
    items.Nodup := by
  induction distinct with
  | nil => exact List.nodup_nil
  | cons headAbsent _tailDistinct ih =>
      exact List.nodup_cons.mpr ⟨headAbsent, ih⟩

private theorem allTerminalPrimitiveRecords_nodup
    (inputs gates outputs profileWidth : Nat) :
    (allTerminalPrimitiveRecords inputs gates outputs profileWidth).Nodup := by
  let gateRecords : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
    (allFin gates).map TerminalPrimitiveRecord.gate
  let inputRecords : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
    (allFin inputs).map TerminalPrimitiveRecord.boundary
  let outputRecords : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
    (allFin outputs).map TerminalPrimitiveRecord.interface
  let profileRecords : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
    (allFin profileWidth).map TerminalPrimitiveRecord.profile
  have gateDistinct : gateRecords.Nodup := by
    apply nodup_of_listNoDuplicates
    exact noDuplicates_map_of_injective TerminalPrimitiveRecord.gate
      (fun left right equal => by cases equal; rfl)
      (allFin gates) (allFin_noDuplicates gates)
  have inputDistinct : inputRecords.Nodup := by
    apply nodup_of_listNoDuplicates
    exact noDuplicates_map_of_injective TerminalPrimitiveRecord.boundary
      (fun left right equal => by cases equal; rfl)
      (allFin inputs) (allFin_noDuplicates inputs)
  have outputDistinct : outputRecords.Nodup := by
    apply nodup_of_listNoDuplicates
    exact noDuplicates_map_of_injective TerminalPrimitiveRecord.interface
      (fun left right equal => by cases equal; rfl)
      (allFin outputs) (allFin_noDuplicates outputs)
  have profileDistinct : profileRecords.Nodup := by
    apply nodup_of_listNoDuplicates
    exact noDuplicates_map_of_injective TerminalPrimitiveRecord.profile
      (fun left right equal => by cases equal; rfl)
      (allFin profileWidth) (allFin_noDuplicates profileWidth)
  have gateCross :
      ∀ gateRecord ∈ gateRecords,
        ∀ otherRecord ∈ inputRecords ++ (outputRecords ++ profileRecords),
          gateRecord ≠ otherRecord := by
    intro gateRecord gateMember otherRecord otherMember equal
    obtain ⟨gateIndex, _gateIndexMember, gateEqual⟩ :=
      mem_map_preimage TerminalPrimitiveRecord.gate (allFin gates) gateMember
    rw [← gateEqual] at equal
    cases List.mem_append.mp otherMember with
    | inl inputMember =>
        obtain ⟨inputIndex, _inputIndexMember, inputEqual⟩ :=
          mem_map_preimage TerminalPrimitiveRecord.boundary
            (allFin inputs) inputMember
        rw [← inputEqual] at equal
        cases equal
    | inr remainingMember =>
        cases List.mem_append.mp remainingMember with
        | inl outputMember =>
            obtain ⟨outputIndex, _outputIndexMember, outputEqual⟩ :=
              mem_map_preimage TerminalPrimitiveRecord.interface
                (allFin outputs) outputMember
            rw [← outputEqual] at equal
            cases equal
        | inr profileMember =>
            obtain ⟨profileIndex, _profileIndexMember, profileEqual⟩ :=
              mem_map_preimage TerminalPrimitiveRecord.profile
                (allFin profileWidth) profileMember
            rw [← profileEqual] at equal
            cases equal
  have inputCross :
      ∀ inputRecord ∈ inputRecords,
        ∀ otherRecord ∈ outputRecords ++ profileRecords,
          inputRecord ≠ otherRecord := by
    intro inputRecord inputMember otherRecord otherMember equal
    obtain ⟨inputIndex, _inputIndexMember, inputEqual⟩ :=
      mem_map_preimage TerminalPrimitiveRecord.boundary
        (allFin inputs) inputMember
    rw [← inputEqual] at equal
    cases List.mem_append.mp otherMember with
    | inl outputMember =>
        obtain ⟨outputIndex, _outputIndexMember, outputEqual⟩ :=
          mem_map_preimage TerminalPrimitiveRecord.interface
            (allFin outputs) outputMember
        rw [← outputEqual] at equal
        cases equal
    | inr profileMember =>
        obtain ⟨profileIndex, _profileIndexMember, profileEqual⟩ :=
          mem_map_preimage TerminalPrimitiveRecord.profile
            (allFin profileWidth) profileMember
        rw [← profileEqual] at equal
        cases equal
  have outputCross :
      ∀ outputRecord ∈ outputRecords,
        ∀ profileRecord ∈ profileRecords,
          outputRecord ≠ profileRecord := by
    intro outputRecord outputMember profileRecord profileMember equal
    obtain ⟨outputIndex, _outputIndexMember, outputEqual⟩ :=
      mem_map_preimage TerminalPrimitiveRecord.interface
        (allFin outputs) outputMember
    obtain ⟨profileIndex, _profileIndexMember, profileEqual⟩ :=
      mem_map_preimage TerminalPrimitiveRecord.profile
        (allFin profileWidth) profileMember
    rw [← outputEqual, ← profileEqual] at equal
    cases equal
  change (((gateRecords ++ inputRecords) ++ outputRecords) ++
    profileRecords).Nodup
  rw [List.append_assoc, List.append_assoc]
  apply List.nodup_append.mpr
  refine ⟨gateDistinct, ?_, gateCross⟩
  apply List.nodup_append.mpr
  refine ⟨inputDistinct, ?_, inputCross⟩
  exact List.nodup_append.mpr
    ⟨outputDistinct, profileDistinct, outputCross⟩

private structure TerminalSaturationWorkState
    (inputs gates outputs profileWidth : Nat) where
  processed : List
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  pending : List
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)

private def TerminalSaturationWorkState.known
    {inputs gates outputs profileWidth : Nat}
    (state : TerminalSaturationWorkState inputs gates outputs profileWidth) :=
  state.processed ++ state.pending

private def terminalNewRequiredRecords
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (known : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (dependent :
      TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  (allTerminalPrimitiveRecords inputs gates outputs profileWidth).filter
    (fun required =>
      terminalSaturationEdge system dependent required &&
        !(decide (required ∈ known)))

private theorem mem_terminalNewRequiredRecords_iff
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (known : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (dependent required :
      TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    required ∈ terminalNewRequiredRecords system known dependent ↔
      terminalSaturationEdge system dependent required = true ∧
        required ∉ known := by
  constructor
  · intro member
    have checked := (List.mem_filter.mp member).2
    simp only [Bool.and_eq_true] at checked
    have edge := checked.1
    have absentCheck := checked.2
    refine ⟨edge, ?_⟩
    intro present
    have presentCheck : decide (required ∈ known) = true :=
      decide_eq_true present
    rw [presentCheck] at absentCheck
    exact Bool.noConfusion absentCheck
  · rintro ⟨edge, absent⟩
    apply List.mem_filter.mpr
    refine ⟨mem_allTerminalPrimitiveRecords required, ?_⟩
    rw [edge, decide_eq_false absent]
    rfl

private theorem terminalNewRequiredRecords_nodup
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (known : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (dependent :
      TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    (terminalNewRequiredRecords system known dependent).Nodup := by
  exact (allTerminalPrimitiveRecords_nodup inputs gates outputs profileWidth).sublist
    List.filter_sublist

private def terminalSaturationStep
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth) :
    TerminalSaturationWorkState inputs gates outputs profileWidth →
      TerminalSaturationWorkState inputs gates outputs profileWidth
  | { processed, pending := [] } =>
      { processed, pending := [] }
  | { processed, pending := dependent :: remaining } =>
      let retained := dependent :: (processed ++ remaining)
      let newlyRequired :=
        terminalNewRequiredRecords system retained dependent
      { processed := dependent :: processed
        pending := remaining ++ newlyRequired }

private def terminalSaturationWork
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth) :
    Nat → TerminalSaturationWorkState inputs gates outputs profileWidth →
      TerminalSaturationWorkState inputs gates outputs profileWidth
  | 0, state => state
  | fuel + 1, state =>
      terminalSaturationWork system fuel (terminalSaturationStep system state)

private theorem mem_reordered_terminal_work_lists {alpha : Type}
    (item dependent : alpha) (processed remaining : List alpha) :
    item ∈ dependent :: (processed ++ remaining) ↔
      item ∈ processed ++ dependent :: remaining := by
  constructor
  · intro member
    cases List.mem_cons.mp member with
    | inl equal =>
        rw [equal]
        exact List.mem_append_right processed (List.Mem.head remaining)
    | inr tailMember =>
        cases List.mem_append.mp tailMember with
        | inl processedMember =>
            exact List.mem_append_left (dependent :: remaining) processedMember
        | inr remainingMember =>
            exact List.mem_append_right processed
              (List.Mem.tail dependent remainingMember)
  · intro member
    cases List.mem_append.mp member with
    | inl processedMember =>
        exact List.Mem.tail dependent
          (List.mem_append_left remaining processedMember)
    | inr pendingMember =>
        cases List.mem_cons.mp pendingMember with
        | inl equal =>
            rw [equal]
            exact List.Mem.head _
        | inr remainingMember =>
            exact List.Mem.tail dependent
              (List.mem_append_right processed remainingMember)

private theorem reordered_terminal_work_lists_nodup {alpha : Type}
    (dependent : alpha) (processed remaining : List alpha)
    (distinct : (processed ++ dependent :: remaining).Nodup) :
    (dependent :: (processed ++ remaining)).Nodup := by
  have parts := List.nodup_append.mp distinct
  have pendingParts := List.nodup_cons.mp parts.2.1
  have dependentAbsentProcessed : dependent ∉ processed := by
    intro member
    exact parts.2.2 dependent member dependent (List.Mem.head remaining) rfl
  have tailDistinct : (processed ++ remaining).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨parts.1, pendingParts.2, ?_⟩
    intro left leftMember right rightMember
    exact parts.2.2 left leftMember right
      (List.Mem.tail dependent rightMember)
  apply List.nodup_cons.mpr
  refine ⟨?_, tailDistinct⟩
  intro member
  cases List.mem_append.mp member with
  | inl processedMember => exact dependentAbsentProcessed processedMember
  | inr remainingMember => exact pendingParts.1 remainingMember

private theorem terminalSaturationStep_known_eq
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (processed remaining : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (dependent :
      TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    (terminalSaturationStep system
      { processed, pending := dependent :: remaining }).known =
        (dependent :: (processed ++ remaining)) ++
          terminalNewRequiredRecords system
            (dependent :: (processed ++ remaining)) dependent := by
  simp only [terminalSaturationStep, TerminalSaturationWorkState.known,
    List.cons_append, List.append_assoc]

private def TerminalSaturationWorkState.FinitelySupported
    {inputs gates outputs profileWidth : Nat}
    (state : TerminalSaturationWorkState inputs gates outputs profileWidth) : Prop :=
  state.known.Nodup ∧
    ∀ record, record ∈ state.known →
      record ∈ allTerminalPrimitiveRecords inputs gates outputs profileWidth

private theorem terminalSaturationStep_finitelySupported
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (state : TerminalSaturationWorkState inputs gates outputs profileWidth)
    (supported : state.FinitelySupported) :
    (terminalSaturationStep system state).FinitelySupported := by
  cases state with
  | mk processed pending =>
      cases pending with
      | nil => exact supported
      | cons dependent remaining =>
          let retained := dependent :: (processed ++ remaining)
          let newlyRequired :=
            terminalNewRequiredRecords system retained dependent
          have retainedDistinct : retained.Nodup :=
            reordered_terminal_work_lists_nodup dependent processed remaining
              supported.1
          have retainedSupported :
              ∀ record, record ∈ retained →
                record ∈ allTerminalPrimitiveRecords
                  inputs gates outputs profileWidth := by
            intro record member
            apply supported.2 record
            exact (mem_reordered_terminal_work_lists
              record dependent processed remaining).1 member
          have newDistinct : newlyRequired.Nodup :=
            terminalNewRequiredRecords_nodup system retained dependent
          have retainedNewDisjoint :
              ∀ retainedRecord ∈ retained,
                ∀ newRecord ∈ newlyRequired,
                  retainedRecord ≠ newRecord := by
            intro retainedRecord retainedMember newRecord newMember equal
            have newAbsent :=
              (mem_terminalNewRequiredRecords_iff
                system retained dependent newRecord).1 newMember |>.2
            apply newAbsent
            rw [← equal]
            exact retainedMember
          unfold TerminalSaturationWorkState.FinitelySupported
          rw [terminalSaturationStep_known_eq]
          constructor
          · exact List.nodup_append.mpr
              ⟨retainedDistinct, newDistinct, retainedNewDisjoint⟩
          · intro record member
            cases List.mem_append.mp member with
            | inl retainedMember =>
                exact retainedSupported record retainedMember
            | inr newMember =>
                exact (List.mem_filter.mp newMember).1

private theorem terminalSaturationWork_finitelySupported
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (fuel : Nat)
    (state : TerminalSaturationWorkState inputs gates outputs profileWidth)
    (supported : state.FinitelySupported) :
    (terminalSaturationWork system fuel state).FinitelySupported := by
  induction fuel generalizing state with
  | zero => exact supported
  | succ fuel ih =>
      exact ih (terminalSaturationStep system state)
        (terminalSaturationStep_finitelySupported system state supported)

private theorem listNoDuplicates_of_nodup {alpha : Type}
    {items : List alpha} (distinct : items.Nodup) :
    ListNoDuplicates items := by
  induction items with
  | nil => exact ListNoDuplicates.nil
  | cons head tail ih =>
      have parts := List.nodup_cons.mp distinct
      exact ListNoDuplicates.cons parts.1 (ih parts.2)

private theorem terminalSaturationWork_pending_empty
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (fuel : Nat)
    (processed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalSaturationWork system fuel
      { processed, pending := [] }).pending = [] := by
  induction fuel generalizing processed with
  | zero => rfl
  | succ fuel ih =>
      exact ih processed

private theorem terminalSaturationWork_processed_length_of_pending_ne
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (fuel : Nat)
    (state : TerminalSaturationWorkState inputs gates outputs profileWidth)
    (pending : (terminalSaturationWork system fuel state).pending ≠ []) :
    (terminalSaturationWork system fuel state).processed.length =
      state.processed.length + fuel := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases state with
      | mk processed statePending =>
          cases statePending with
          | nil =>
              have empty := terminalSaturationWork_pending_empty
                system (fuel + 1) processed
              exact False.elim (pending empty)
          | cons dependent remaining =>
              have prior := ih
                (terminalSaturationStep system
                  { processed, pending := dependent :: remaining }) pending
              calc
                (terminalSaturationWork system fuel
                    (terminalSaturationStep system
                      { processed,
                        pending := dependent :: remaining })).processed.length =
                    (dependent :: processed).length + fuel := prior
                _ = processed.length + (fuel + 1) := by
                    simp only [List.length_cons]
                    calc
                      Nat.succ processed.length + fuel =
                          Nat.succ (processed.length + fuel) :=
                        Nat.succ_add processed.length fuel
                      _ = (processed.length + fuel) + 1 := rfl
                      _ = processed.length + (fuel + 1) :=
                        Nat.add_assoc processed.length fuel 1

private theorem terminalSaturationStep_known_mono
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (state : TerminalSaturationWorkState inputs gates outputs profileWidth)
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (member : record ∈ state.known) :
    record ∈ (terminalSaturationStep system state).known := by
  cases state with
  | mk processed pending =>
      cases pending with
      | nil => exact member
      | cons dependent remaining =>
          rw [terminalSaturationStep_known_eq]
          apply List.mem_append_left
          exact (mem_reordered_terminal_work_lists
            record dependent processed remaining).2 member

private theorem terminalSaturationWork_known_mono
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (fuel : Nat)
    (state : TerminalSaturationWorkState inputs gates outputs profileWidth)
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (member : record ∈ state.known) :
    record ∈ (terminalSaturationWork system fuel state).known := by
  induction fuel generalizing state with
  | zero => exact member
  | succ fuel ih =>
      exact ih (terminalSaturationStep system state)
        (terminalSaturationStep_known_mono system state record member)

private def TerminalSaturationWorkState.SaturationSound
    {inputs gates outputs profileWidth : Nat}
    (state : TerminalSaturationWorkState inputs gates outputs profileWidth)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : Prop :=
  ∀ record, record ∈ state.known →
    terminalSaturate system (fun candidate => candidate ∈ seed) record

private theorem terminalSaturationStep_sound
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (state : TerminalSaturationWorkState inputs gates outputs profileWidth)
    (sound : state.SaturationSound system seed) :
    (terminalSaturationStep system state).SaturationSound system seed := by
  cases state with
  | mk processed pending =>
      cases pending with
      | nil => exact sound
      | cons dependent remaining =>
          intro record member
          rw [terminalSaturationStep_known_eq] at member
          cases List.mem_append.mp member with
          | inl retainedMember =>
              exact sound record
                ((mem_reordered_terminal_work_lists
                  record dependent processed remaining).1 retainedMember)
          | inr newMember =>
              have newFacts := (mem_terminalNewRequiredRecords_iff
                system (dependent :: (processed ++ remaining))
                  dependent record).1 newMember
              obtain ⟨kind, edge⟩ :=
                (terminalSaturationEdge_eq_true_iff
                  system dependent record).1 newFacts.1
              have dependentGenerated := sound dependent
                (List.mem_append_right processed (List.Mem.head remaining))
              exact TerminalSaturationGenerated.close dependentGenerated edge

private theorem terminalSaturationWork_sound
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (fuel : Nat)
    (state : TerminalSaturationWorkState inputs gates outputs profileWidth)
    (sound : state.SaturationSound system seed) :
    (terminalSaturationWork system fuel state).SaturationSound system seed := by
  induction fuel generalizing state with
  | zero => exact sound
  | succ fuel ih =>
      exact ih (terminalSaturationStep system state)
        (terminalSaturationStep_sound system seed state sound)

private def TerminalSaturationWorkState.FrontierClosed
    {inputs gates outputs profileWidth : Nat}
    (state : TerminalSaturationWorkState inputs gates outputs profileWidth)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth) : Prop :=
  ∀ dependent, dependent ∈ state.processed →
    ∀ required, terminalSaturationEdge system dependent required = true →
      required ∈ state.known

private theorem terminalSaturationStep_frontierClosed
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (state : TerminalSaturationWorkState inputs gates outputs profileWidth)
    (closed : state.FrontierClosed system) :
    (terminalSaturationStep system state).FrontierClosed system := by
  cases state with
  | mk processed pending =>
      cases pending with
      | nil => exact closed
      | cons current remaining =>
          intro dependent dependentMember required edge
          rw [terminalSaturationStep_known_eq]
          cases List.mem_cons.mp dependentMember with
          | inl equal =>
              rw [equal] at edge
              if present : required ∈ current :: (processed ++ remaining) then
                exact List.mem_append_left _ present
              else
                apply List.mem_append_right
                exact (mem_terminalNewRequiredRecords_iff
                  system (current :: (processed ++ remaining))
                    current required).2 ⟨edge, present⟩
          | inr processedMember =>
              apply List.mem_append_left
              exact (mem_reordered_terminal_work_lists
                required current processed remaining).2
                  (closed dependent processedMember required edge)

private theorem terminalSaturationWork_frontierClosed
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (fuel : Nat)
    (state : TerminalSaturationWorkState inputs gates outputs profileWidth)
    (closed : state.FrontierClosed system) :
    (terminalSaturationWork system fuel state).FrontierClosed system := by
  induction fuel generalizing state with
  | zero => exact closed
  | succ fuel ih =>
      exact ih (terminalSaturationStep system state)
        (terminalSaturationStep_frontierClosed system state closed)

private def terminalSaturationInitialState
    {inputs gates outputs profileWidth : Nat}
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalSaturationWorkState inputs gates outputs profileWidth :=
  { processed := []
    pending :=
      (allTerminalPrimitiveRecords inputs gates outputs profileWidth).filter
        (fun record => decide (record ∈ seed)) }

private theorem terminalSaturationInitialState_finitelySupported
    {inputs gates outputs profileWidth : Nat}
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalSaturationInitialState seed).FinitelySupported := by
  unfold TerminalSaturationWorkState.FinitelySupported
    TerminalSaturationWorkState.known terminalSaturationInitialState
  constructor
  · exact (allTerminalPrimitiveRecords_nodup
      inputs gates outputs profileWidth).sublist List.filter_sublist
  · intro record member
    exact (List.mem_filter.mp member).1

private theorem terminalSaturationInitialState_sound
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalSaturationInitialState seed).SaturationSound system seed := by
  intro record member
  unfold TerminalSaturationWorkState.known terminalSaturationInitialState at member
  have checked := (List.mem_filter.mp member).2
  exact TerminalSaturationGenerated.seed (of_decide_eq_true checked)

private theorem terminalSaturationInitialState_frontierClosed
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalSaturationInitialState seed).FrontierClosed system := by
  intro dependent member
  cases member

private theorem mem_terminalSaturationInitialState_known_of_mem
    {inputs gates outputs profileWidth : Nat}
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (member : record ∈ seed) :
    record ∈ (terminalSaturationInitialState seed).known := by
  unfold terminalSaturationInitialState TerminalSaturationWorkState.known
  apply List.mem_filter.mpr
  exact ⟨mem_allTerminalPrimitiveRecords record, decide_eq_true member⟩

private def terminalSaturationFinalState
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalSaturationWorkState inputs gates outputs profileWidth :=
  terminalSaturationWork system
    (allTerminalPrimitiveRecords inputs gates outputs profileWidth).length
    (terminalSaturationInitialState seed)

private theorem terminalSaturationFinalState_pending_empty
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalSaturationFinalState system seed).pending = [] := by
  let finiteUniverse :=
    allTerminalPrimitiveRecords inputs gates outputs profileWidth
  let initial := terminalSaturationInitialState seed
  let final := terminalSaturationFinalState system seed
  have initialSupported : initial.FinitelySupported :=
    terminalSaturationInitialState_finitelySupported seed
  have finalSupported : final.FinitelySupported := by
    exact terminalSaturationWork_finitelySupported system finiteUniverse.length
      initial initialSupported
  cases pendingShape : final.pending with
  | nil => rfl
  | cons head tail =>
      have pendingNonempty : final.pending ≠ [] := by
        rw [pendingShape]
        intro impossible
        cases impossible
      have processedLength :=
        terminalSaturationWork_processed_length_of_pending_ne
          system finiteUniverse.length initial pendingNonempty
      have lengthBound := noDuplicatesSubset_length_le final.known finiteUniverse
        (listNoDuplicates_of_nodup finalSupported.1) finalSupported.2
      unfold TerminalSaturationWorkState.known at lengthBound
      rw [List.length_append, pendingShape] at lengthBound
      change final.processed.length = [].length + finiteUniverse.length at processedLength
      have processedLengthExact :
          final.processed.length = finiteUniverse.length := by
        simpa only [List.length_nil, Nat.zero_add] using processedLength
      have pendingPositive : 0 < (head :: tail).length := by
        simp only [List.length_cons]
        exact Nat.zero_lt_succ tail.length
      rw [processedLengthExact] at lengthBound
      have cancelled : (head :: tail).length ≤ 0 := by
        apply (Nat.add_le_add_iff_left).1
        simpa only [Nat.add_zero] using lengthBound
      have pendingZero := Nat.eq_zero_of_le_zero cancelled
      rw [pendingZero] at pendingPositive
      exact False.elim (Nat.not_lt_zero 0 pendingPositive)

private theorem terminalSaturationFinalState_sound
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalSaturationFinalState system seed).SaturationSound system seed := by
  unfold terminalSaturationFinalState
  exact terminalSaturationWork_sound system seed _
    (terminalSaturationInitialState seed)
    (terminalSaturationInitialState_sound system seed)

private theorem terminalSaturationFinalState_frontierClosed
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalSaturationFinalState system seed).FrontierClosed system := by
  unfold terminalSaturationFinalState
  exact terminalSaturationWork_frontierClosed system _
    (terminalSaturationInitialState seed)
    (terminalSaturationInitialState_frontierClosed system seed)

/-- Compute the exact terminal saturation of a finite primitive-record seed.
    Output order is the deterministic work-list visitation order. -/
def terminalSaturateRecords
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  (terminalSaturationFinalState system seed).processed

/-- Every seed record occurs in the executable saturation. -/
theorem terminalSaturateRecords_extensive
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (member : record ∈ seed) :
    record ∈ terminalSaturateRecords system seed := by
  have initialMember :=
    mem_terminalSaturationInitialState_known_of_mem seed record member
  have finalMember := terminalSaturationWork_known_mono system
    (allTerminalPrimitiveRecords inputs gates outputs profileWidth).length
    (terminalSaturationInitialState seed) record initialMember
  change record ∈ (terminalSaturationFinalState system seed).known at finalMember
  unfold TerminalSaturationWorkState.known at finalMember
  rw [terminalSaturationFinalState_pending_empty system seed,
    List.append_nil] at finalMember
  exact finalMember

/-- Every executable output record has an inductive saturation derivation. -/
theorem terminalSaturateRecords_sound
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (member : record ∈ terminalSaturateRecords system seed) :
    terminalSaturate system (fun candidate => candidate ∈ seed) record := by
  apply terminalSaturationFinalState_sound system seed record
  exact List.mem_append_left _ member

/-- The executable result is closed under each labelled dependency rule. -/
theorem terminalSaturateRecords_closed
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalRawSupport.Closed
      (fun record => record ∈ terminalSaturateRecords system seed) system := by
  intro kind dependent required dependentMember edge
  have combinedEdge :
      terminalSaturationEdge system dependent required = true :=
    (terminalSaturationEdge_eq_true_iff system dependent required).2
      ⟨kind, edge⟩
  have requiredKnown :=
    terminalSaturationFinalState_frontierClosed system seed dependent
      dependentMember required combinedEdge
  unfold TerminalSaturationWorkState.known at requiredKnown
  rw [terminalSaturationFinalState_pending_empty system seed,
    List.append_nil] at requiredKnown
  exact requiredKnown

/-- Exact executable saturation: work-list membership is equivalent to the
    kernel-checked inductive reflexive-transitive closure. -/
theorem mem_terminalSaturateRecords_iff
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    record ∈ terminalSaturateRecords system seed ↔
      terminalSaturate system (fun candidate => candidate ∈ seed) record := by
  constructor
  · exact terminalSaturateRecords_sound system seed record
  · intro generated
    exact terminalSaturate_least system
      (fun candidate => candidate ∈ seed)
      (fun candidate => candidate ∈ terminalSaturateRecords system seed)
      (fun candidate candidateMember =>
        terminalSaturateRecords_extensive system seed candidate candidateMember)
      (terminalSaturateRecords_closed system seed)
      record generated

end DirectWire
end PNP

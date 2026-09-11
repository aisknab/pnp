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

private def firstTerminalSaturationRule?
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (dependent required :
      TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    List TerminalSaturationRuleKind → Option TerminalSaturationRuleKind
  | [] => none
  | kind :: kinds =>
      if system.requires kind dependent required = true then
        some kind
      else
        firstTerminalSaturationRule? system dependent required kinds

/-- The first rule witnessing an edge, in the same fixed order used by the
    executable saturation union.  `none` means that no rule witnesses the
    edge. -/
def terminalFirstSaturationRule?
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (dependent required :
      TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    Option TerminalSaturationRuleKind :=
  firstTerminalSaturationRule? system dependent required
    allTerminalSaturationRuleKinds

private theorem nodup_of_listNoDuplicates {alpha : Type}
    {items : List alpha} (distinct : ListNoDuplicates items) :
    items.Nodup := by
  induction distinct with
  | nil => exact List.nodup_nil
  | cons headAbsent _tailDistinct ih =>
      exact List.nodup_cons.mpr ⟨headAbsent, ih⟩

/-- The canonical terminal primitive-record universe contains no duplicates. -/
theorem allTerminalPrimitiveRecords_nodup
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

/-! ## Deterministic rule-labelled execution trace -/

/-- One generated record in the deterministic saturation execution.  The
    event stores the exact rule selected by the fixed rule order together with
    the support immediately before and after processing the generated record.
    A missing rule is retained as `none` and is handled fail-closed by the
    downstream balance classifier. -/
structure TerminalSaturationTraceEvent
    (inputs gates outputs profileWidth : Nat) where
  kind? : Option TerminalSaturationRuleKind
  dependent : TerminalPrimitiveRecord inputs gates outputs profileWidth
  required : TerminalPrimitiveRecord inputs gates outputs profileWidth
  beforeRecords : List
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  afterRecords : List
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  deriving Repr, DecidableEq

/-- Event lists produced by the trace form one continuous support history:
    every appended event starts at the preceding state and ends at its own
    recorded after-support. -/
inductive TerminalSaturationEventsLinked
    {inputs gates outputs profileWidth : Nat}
    (initial : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    List (TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) →
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) → Prop where
  | nil : TerminalSaturationEventsLinked initial [] initial
  | snoc
      {events : List (TerminalSaturationTraceEvent
        inputs gates outputs profileWidth)}
      {event : TerminalSaturationTraceEvent
        inputs gates outputs profileWidth}
      (linked : TerminalSaturationEventsLinked initial events
        event.beforeRecords) :
      TerminalSaturationEventsLinked initial (events ++ [event])
        event.afterRecords

private inductive TerminalSaturationPendingOrigin
    (inputs gates outputs profileWidth : Nat) where
  | seed
  | generated
      (kind? : Option TerminalSaturationRuleKind)
      (dependent :
        TerminalPrimitiveRecord inputs gates outputs profileWidth)

private structure TerminalSaturationTracePending
    (inputs gates outputs profileWidth : Nat) where
  record : TerminalPrimitiveRecord inputs gates outputs profileWidth
  origin : TerminalSaturationPendingOrigin inputs gates outputs profileWidth

private structure TerminalSaturationTraceWorkState
    (inputs gates outputs profileWidth : Nat) where
  processed : List
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  pending : List
    (TerminalSaturationTracePending inputs gates outputs profileWidth)
  costRecords : List
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  events : List
    (TerminalSaturationTraceEvent inputs gates outputs profileWidth)

private def terminalSaturationTraceKnown
    {inputs gates outputs profileWidth : Nat}
    (state : TerminalSaturationTraceWorkState
      inputs gates outputs profileWidth) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  state.processed ++ state.pending.map (fun item => item.record)

private def terminalSaturationTraceStep
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (state : TerminalSaturationTraceWorkState
      inputs gates outputs profileWidth) :
    TerminalSaturationTraceWorkState inputs gates outputs profileWidth :=
  match state.pending with
  | [] => state
  | current :: remaining =>
      let retained := current.record ::
        (state.processed ++ remaining.map (fun item => item.record))
      let newlyRequired :=
        terminalNewRequiredRecords system retained current.record
      let newlyPending := newlyRequired.map fun required =>
        { record := required
          origin := .generated
            (terminalFirstSaturationRule? system current.record required)
            current.record }
      match current.origin with
      | .seed =>
          { processed := current.record :: state.processed
            pending := remaining ++ newlyPending
            costRecords := state.costRecords
            events := state.events }
      | .generated kind? dependent =>
          let afterRecords := current.record :: state.costRecords
          let event : TerminalSaturationTraceEvent
              inputs gates outputs profileWidth :=
            { kind? := kind?
              dependent := dependent
              required := current.record
              beforeRecords := state.costRecords
              afterRecords := afterRecords }
          { processed := current.record :: state.processed
            pending := remaining ++ newlyPending
            costRecords := afterRecords
            events := state.events ++ [event] }

private def terminalSaturationTraceErase
    {inputs gates outputs profileWidth : Nat}
    (state : TerminalSaturationTraceWorkState
      inputs gates outputs profileWidth) :
    TerminalSaturationWorkState inputs gates outputs profileWidth :=
  { processed := state.processed
    pending := state.pending.map fun item => item.record }

private theorem terminalSaturationTraceStep_erase
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (state : TerminalSaturationTraceWorkState
      inputs gates outputs profileWidth) :
    terminalSaturationTraceErase (terminalSaturationTraceStep system state) =
      terminalSaturationStep system (terminalSaturationTraceErase state) := by
  cases pendingEq : state.pending with
  | nil =>
      simp only [terminalSaturationTraceStep, pendingEq,
        terminalSaturationTraceErase, List.map_nil, terminalSaturationStep]
  | cons current remaining =>
      cases originEq : current.origin <;>
        simp only [terminalSaturationTraceStep, pendingEq, originEq,
          terminalSaturationTraceErase, List.map_cons, List.map_append,
          List.map_map, Function.comp_def, List.map_id_fun', id, terminalSaturationStep]

private theorem terminalSaturationTraceStep_linked
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (initial : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (state : TerminalSaturationTraceWorkState
      inputs gates outputs profileWidth)
    (linked : TerminalSaturationEventsLinked initial state.events
      state.costRecords) :
    TerminalSaturationEventsLinked initial
      (terminalSaturationTraceStep system state).events
      (terminalSaturationTraceStep system state).costRecords := by
  unfold terminalSaturationTraceStep
  cases pendingEq : state.pending with
  | nil =>
      simpa [pendingEq] using linked
  | cons current remaining =>
      cases originEq : current.origin with
      | seed =>
          simpa [pendingEq, originEq] using linked
      | generated kind? dependent =>
          simpa [pendingEq, originEq] using
            (TerminalSaturationEventsLinked.snoc linked)

private def terminalSaturationTraceWork
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth) :
    Nat → TerminalSaturationTraceWorkState inputs gates outputs profileWidth →
      TerminalSaturationTraceWorkState inputs gates outputs profileWidth
  | 0, state => state
  | fuel + 1, state =>
      terminalSaturationTraceWork system fuel
        (terminalSaturationTraceStep system state)

private theorem terminalSaturationTraceWork_erase
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth) :
    ∀ fuel state,
      terminalSaturationTraceErase (terminalSaturationTraceWork system fuel state) =
        terminalSaturationWork system fuel (terminalSaturationTraceErase state) := by
  intro fuel
  induction fuel with
  | zero =>
      intro state
      rfl
  | succ fuel ih =>
      intro state
      simpa only [terminalSaturationTraceWork, terminalSaturationWork,
        terminalSaturationTraceStep_erase] using
        ih (terminalSaturationTraceStep system state)

private theorem terminalSaturationTraceWork_linked
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (initial : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    ∀ fuel state,
      TerminalSaturationEventsLinked initial state.events state.costRecords →
      TerminalSaturationEventsLinked initial
        (terminalSaturationTraceWork system fuel state).events
        (terminalSaturationTraceWork system fuel state).costRecords := by
  intro fuel
  induction fuel with
  | zero =>
      intro state linked
      exact linked
  | succ fuel ih =>
      intro state linked
      exact ih (terminalSaturationTraceStep system state)
        (terminalSaturationTraceStep_linked system initial state linked)

private def terminalSaturationTraceInitialState
    {inputs gates outputs profileWidth : Nat}
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalSaturationTraceWorkState inputs gates outputs profileWidth :=
  let normalized :=
    (allTerminalPrimitiveRecords inputs gates outputs profileWidth).filter
      (fun record => decide (record ∈ seed))
  { processed := []
    pending := normalized.map fun record =>
      { record := record, origin := .seed }
    costRecords := normalized.reverse
    events := [] }

private theorem terminalSaturationTraceInitialState_erase
    {inputs gates outputs profileWidth : Nat}
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalSaturationTraceErase (terminalSaturationTraceInitialState seed) =
      terminalSaturationInitialState seed := by
  simp only [terminalSaturationTraceErase, terminalSaturationTraceInitialState,
    terminalSaturationInitialState, List.map_map, Function.comp_def, List.map_id_fun', id]

private def terminalSaturationTraceFinalState
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalSaturationTraceWorkState inputs gates outputs profileWidth :=
  terminalSaturationTraceWork system
    (allTerminalPrimitiveRecords inputs gates outputs profileWidth).length
    (terminalSaturationTraceInitialState seed)

private theorem terminalSaturationTraceFinalState_erase
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalSaturationTraceErase (terminalSaturationTraceFinalState system seed) =
      terminalSaturationFinalState system seed := by
  unfold terminalSaturationTraceFinalState terminalSaturationFinalState
  rw [terminalSaturationTraceWork_erase, terminalSaturationTraceInitialState_erase]

private def terminalSaturationTraceSeedRecords
    {inputs gates outputs profileWidth : Nat} :
    List (TerminalSaturationTracePending inputs gates outputs profileWidth) →
      List (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  | [] => []
  | current :: remaining =>
      match current.origin with
      | .seed => current.record :: terminalSaturationTraceSeedRecords remaining
      | .generated _kind _dependent => terminalSaturationTraceSeedRecords remaining

private theorem terminalSaturationTraceSeedRecords_append
    {inputs gates outputs profileWidth : Nat}
    (left right : List
      (TerminalSaturationTracePending inputs gates outputs profileWidth)) :
    terminalSaturationTraceSeedRecords (left ++ right) =
      terminalSaturationTraceSeedRecords left ++
        terminalSaturationTraceSeedRecords right := by
  induction left with
  | nil => rfl
  | cons current remaining ih =>
      cases originEq : current.origin <;>
        simp only [List.cons_append, terminalSaturationTraceSeedRecords,
          originEq, ih]

private theorem terminalSaturationTraceSeedRecords_generated
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (dependent : TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (records : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalSaturationTraceSeedRecords
        (records.map fun required =>
          ({ record := required
             origin := .generated
               (terminalFirstSaturationRule? system dependent required) dependent } :
            TerminalSaturationTracePending inputs gates outputs profileWidth)) = [] := by
  induction records with
  | nil => rfl
  | cons current remaining ih =>
      simpa only [List.map_cons, terminalSaturationTraceSeedRecords] using ih

private theorem terminalSaturationTraceSeedRecords_seed
    {inputs gates outputs profileWidth : Nat}
    (records : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalSaturationTraceSeedRecords
        (records.map fun record =>
          ({ record := record, origin := .seed } :
            TerminalSaturationTracePending inputs gates outputs profileWidth)) =
      records := by
  induction records with
  | nil => rfl
  | cons current remaining ih =>
      simp only [List.map_cons, terminalSaturationTraceSeedRecords, ih]

private def TerminalSaturationTraceWorkState.CostRecordsAccounted
    {inputs gates outputs profileWidth : Nat}
    (state : TerminalSaturationTraceWorkState
      inputs gates outputs profileWidth) : Prop :=
  ∀ record, record ∈ state.costRecords ↔
    record ∈ state.processed ∨
      record ∈ terminalSaturationTraceSeedRecords state.pending

private theorem terminalSaturationTraceStep_costRecordsAccounted
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (state : TerminalSaturationTraceWorkState
      inputs gates outputs profileWidth)
    (accounted : state.CostRecordsAccounted) :
    (terminalSaturationTraceStep system state).CostRecordsAccounted := by
  intro record
  have old := accounted record
  cases pendingEq : state.pending with
  | nil =>
      simpa only [terminalSaturationTraceStep, pendingEq] using old
  | cons current remaining =>
      cases originEq : current.origin with
      | seed =>
          simpa only [terminalSaturationTraceStep, pendingEq, originEq,
            terminalSaturationTraceSeedRecords_append,
            terminalSaturationTraceSeedRecords_generated,
            terminalSaturationTraceSeedRecords, List.append_nil,
            List.mem_cons, or_assoc, or_comm, or_left_comm] using old
      | generated kind dependent =>
          have added :
              (record = current.record ∨ record ∈ state.costRecords) ↔
                (record = current.record ∨
                  (record ∈ state.processed ∨
                    record ∈ terminalSaturationTraceSeedRecords state.pending)) :=
            or_congr Iff.rfl old
          simpa only [terminalSaturationTraceStep, pendingEq, originEq,
            terminalSaturationTraceSeedRecords_append,
            terminalSaturationTraceSeedRecords_generated,
            terminalSaturationTraceSeedRecords, List.append_nil,
            List.mem_cons, or_assoc] using added

private theorem terminalSaturationTraceWork_costRecordsAccounted
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth) :
    ∀ fuel state, state.CostRecordsAccounted →
      (terminalSaturationTraceWork system fuel state).CostRecordsAccounted := by
  intro fuel
  induction fuel with
  | zero =>
      intro state accounted
      exact accounted
  | succ fuel ih =>
      intro state accounted
      exact ih (terminalSaturationTraceStep system state)
        (terminalSaturationTraceStep_costRecordsAccounted system state accounted)

private theorem terminalSaturationTraceInitialState_costRecordsAccounted
    {inputs gates outputs profileWidth : Nat}
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalSaturationTraceInitialState seed).CostRecordsAccounted := by
  intro record
  simp only [terminalSaturationTraceInitialState,
    terminalSaturationTraceSeedRecords_seed, List.mem_reverse,
    List.mem_nil_iff, false_or]

private theorem terminalSaturationTraceFinalState_costRecordsAccounted
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalSaturationTraceFinalState system seed).CostRecordsAccounted := by
  unfold terminalSaturationTraceFinalState
  exact terminalSaturationTraceWork_costRecordsAccounted system _
    (terminalSaturationTraceInitialState seed)
    (terminalSaturationTraceInitialState_costRecordsAccounted seed)

private theorem terminalSaturationTraceFinalState_pending_empty
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalSaturationTraceFinalState system seed).pending = [] := by
  have mapped :
      (terminalSaturationTraceFinalState system seed).pending.map
          (fun item => item.record) = [] := by
    change (terminalSaturationTraceErase
      (terminalSaturationTraceFinalState system seed)).pending = []
    rw [terminalSaturationTraceFinalState_erase,
      terminalSaturationFinalState_pending_empty]
  cases pendingEq : (terminalSaturationTraceFinalState system seed).pending with
  | nil => rfl
  | cons current remaining =>
      rw [pendingEq] at mapped
      cases mapped

private theorem firstTerminalSaturationRule?_valid
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (dependent required :
      TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (kinds : List TerminalSaturationRuleKind)
    (witness : ∃ kind, kind ∈ kinds ∧
      system.requires kind dependent required = true) :
    ∃ kind, firstTerminalSaturationRule? system dependent required kinds = some kind ∧
      system.requires kind dependent required = true := by
  induction kinds with
  | nil =>
      obtain ⟨kind, member, _edge⟩ := witness
      cases member
  | cons head tail ih =>
      by_cases headEdge : system.requires head dependent required = true
      · exact ⟨head, by simp only [firstTerminalSaturationRule?, headEdge, if_true],
          headEdge⟩
      · have tailWitness : ∃ kind, kind ∈ tail ∧
            system.requires kind dependent required = true := by
          obtain ⟨kind, member, edge⟩ := witness
          cases List.mem_cons.mp member with
          | inl equal =>
              subst kind
              exact False.elim (headEdge edge)
          | inr tailMember =>
              exact ⟨kind, tailMember, edge⟩
        obtain ⟨kind, selected, edge⟩ := ih tailWitness
        exact ⟨kind, by
          simpa only [firstTerminalSaturationRule?, if_neg headEdge] using selected,
          edge⟩

private theorem terminalFirstSaturationRule?_valid
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (dependent required :
      TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (edge : terminalSaturationEdge system dependent required = true) :
    ∃ kind, terminalFirstSaturationRule? system dependent required = some kind ∧
      system.requires kind dependent required = true := by
  obtain ⟨kind, rule⟩ :=
    (terminalSaturationEdge_eq_true_iff system dependent required).mp edge
  exact firstTerminalSaturationRule?_valid system dependent required _
    ⟨kind, mem_allTerminalSaturationRuleKinds kind, rule⟩

private def TerminalSaturationTracePending.RuleValid
    {inputs gates outputs profileWidth : Nat}
    (item : TerminalSaturationTracePending inputs gates outputs profileWidth)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth) : Prop :=
  match item.origin with
  | .seed => True
  | .generated selected dependent =>
      ∃ kind, selected = some kind ∧
        system.requires kind dependent item.record = true

private def TerminalSaturationTraceWorkState.RulesValid
    {inputs gates outputs profileWidth : Nat}
    (state : TerminalSaturationTraceWorkState inputs gates outputs profileWidth)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth) : Prop :=
  (∀ item, item ∈ state.pending → item.RuleValid system) ∧
    (∀ event, event ∈ state.events →
      event.afterRecords = event.required :: event.beforeRecords ∧
        ∃ kind, event.kind? = some kind ∧
          system.requires kind event.dependent event.required = true)

private theorem terminalSaturationTraceStep_rulesValid
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (state : TerminalSaturationTraceWorkState inputs gates outputs profileWidth)
    (valid : state.RulesValid system) :
    (terminalSaturationTraceStep system state).RulesValid system := by
  cases pendingEq : state.pending with
  | nil =>
      simpa only [terminalSaturationTraceStep, pendingEq] using valid
  | cons current remaining =>
      have currentValid : current.RuleValid system :=
        valid.1 current (by rw [pendingEq]; exact List.Mem.head _)
      let retained := current.record ::
        (state.processed ++ remaining.map (fun item => item.record))
      let newPending : List
          (TerminalSaturationTracePending inputs gates outputs profileWidth) :=
        (terminalNewRequiredRecords system retained current.record).map fun required =>
          { record := required
            origin := .generated
              (terminalFirstSaturationRule? system current.record required)
              current.record }
      have newValid : ∀ item, item ∈ newPending → item.RuleValid system := by
        intro item member
        obtain ⟨record, recordMember, equal⟩ := List.mem_map.mp member
        subst item
        have edge :=
          (mem_terminalNewRequiredRecords_iff system retained current.record record).mp
            recordMember
        exact terminalFirstSaturationRule?_valid system current.record record edge.1
      have pendingValid :
          ∀ item, item ∈ remaining ++ newPending → item.RuleValid system := by
        intro item member
        cases List.mem_append.mp member with
        | inl oldMember =>
            exact valid.1 item (by rw [pendingEq]; exact List.Mem.tail _ oldMember)
        | inr newMember =>
            exact newValid item newMember
      cases originEq : current.origin with
      | seed =>
          simpa only [TerminalSaturationTraceWorkState.RulesValid,
            terminalSaturationTraceStep, pendingEq, originEq] using
              And.intro pendingValid valid.2
      | generated selected dependent =>
          constructor
          · simpa only [terminalSaturationTraceStep, pendingEq, originEq] using
              pendingValid
          · intro event member
            simp only [terminalSaturationTraceStep, pendingEq, originEq] at member
            cases List.mem_append.mp member with
            | inl oldMember =>
                exact valid.2 event oldMember
            | inr newMember =>
                have equal := List.mem_singleton.mp newMember
                subst event
                exact ⟨rfl, by
                  simpa only [TerminalSaturationTracePending.RuleValid, originEq]
                    using currentValid⟩

private theorem terminalSaturationTraceWork_rulesValid
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth) :
    ∀ fuel state, state.RulesValid system →
      (terminalSaturationTraceWork system fuel state).RulesValid system := by
  intro fuel
  induction fuel with
  | zero =>
      intro state valid
      exact valid
  | succ fuel ih =>
      intro state valid
      exact ih (terminalSaturationTraceStep system state)
        (terminalSaturationTraceStep_rulesValid system state valid)

private theorem terminalSaturationTraceInitialState_rulesValid
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalSaturationTraceInitialState seed).RulesValid system := by
  constructor
  · intro item member
    obtain ⟨record, _recordMember, equal⟩ := List.mem_map.mp member
    subst item
    exact True.intro
  · intro event member
    cases member

private theorem terminalSaturationTraceFinalState_rulesValid
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalSaturationTraceFinalState system seed).RulesValid system := by
  unfold terminalSaturationTraceFinalState
  exact terminalSaturationTraceWork_rulesValid system _
    (terminalSaturationTraceInitialState seed)
    (terminalSaturationTraceInitialState_rulesValid system seed)

private theorem terminalSaturationTraceFinalState_linked
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    let normalized :=
      (allTerminalPrimitiveRecords inputs gates outputs profileWidth).filter
        (fun record => decide (record ∈ seed))
    TerminalSaturationEventsLinked normalized.reverse
      (terminalSaturationTraceFinalState system seed).events
      (terminalSaturationTraceFinalState system seed).costRecords := by
  dsimp only
  unfold terminalSaturationTraceFinalState
  apply terminalSaturationTraceWork_linked
  exact TerminalSaturationEventsLinked.nil

/-- Complete deterministic saturation trace.  `records` is definitionally the
    already audited executable saturation output; `replayRecords` is the same
    finite support accumulated in event order for stepwise cost accounting. -/
structure TerminalSaturationTrace
    (inputs gates outputs profileWidth : Nat) where
  normalizedSeed : List
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  events : List
    (TerminalSaturationTraceEvent inputs gates outputs profileWidth)
  replayRecords : List
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  records : List
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  deriving Repr, DecidableEq

/-- Execute saturation while retaining the first rule that generated every
    non-seed record. -/
def terminalSaturateTrace
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalSaturationTrace inputs gates outputs profileWidth :=
  let final := terminalSaturationTraceFinalState system seed
  { normalizedSeed :=
      (allTerminalPrimitiveRecords inputs gates outputs profileWidth).filter
        (fun record => decide (record ∈ seed))
    events := final.events
    replayRecords := final.costRecords
    records := terminalSaturateRecords system seed }

/-- The executable trace is a continuous history from the normalized seed to
    the replayed final record family. -/
theorem terminalSaturateTrace_eventsLinked
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalSaturationEventsLinked
      (terminalSaturateTrace system seed).normalizedSeed.reverse
      (terminalSaturateTrace system seed).events
      (terminalSaturateTrace system seed).replayRecords := by
  simpa only [terminalSaturateTrace] using
    terminalSaturationTraceFinalState_linked system seed

/-- Tracing never changes the existing executable saturation result. -/
@[simp] theorem terminalSaturateTrace_records
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalSaturateTrace system seed).records =
      terminalSaturateRecords system seed := rfl

/-- The trace seed is the canonical duplicate-free restriction of the caller
    seed to the finite primitive universe. -/
@[simp] theorem terminalSaturateTrace_normalizedSeed
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalSaturateTrace system seed).normalizedSeed =
      (allTerminalPrimitiveRecords inputs gates outputs profileWidth).filter
        (fun record => decide (record ∈ seed)) := rfl

/-- The actual cost-accounting replay has exactly the computed saturated
    records. Trace annotations do not change the finite terminal support. -/
theorem terminalSaturateTrace_replayRecords_iff
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    record ∈ (terminalSaturateTrace system seed).replayRecords ↔
      record ∈ terminalSaturateRecords system seed := by
  have accounted :=
    terminalSaturationTraceFinalState_costRecordsAccounted system seed record
  rw [terminalSaturationTraceFinalState_pending_empty] at accounted
  have processed :
      (terminalSaturationTraceFinalState system seed).processed =
        (terminalSaturationFinalState system seed).processed :=
    congrArg
      (fun state : TerminalSaturationWorkState inputs gates outputs profileWidth =>
        state.processed)
      (terminalSaturationTraceFinalState_erase system seed)
  simpa only [terminalSaturateTrace, terminalSaturateRecords,
    terminalSaturationTraceSeedRecords, List.mem_nil_iff, or_false, processed]
      using accounted

/-- Every event actually emitted by saturation adds its required record and
    carries a rule that really relates its dependent to that record. -/
theorem terminalSaturateTrace_event_valid
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth)
    (member : event ∈ (terminalSaturateTrace system seed).events) :
    event.afterRecords = event.required :: event.beforeRecords ∧
      ∃ kind, event.kind? = some kind ∧
        system.requires kind event.dependent event.required = true := by
  exact (terminalSaturationTraceFinalState_rulesValid system seed).2 event member

end DirectWire
end PNP

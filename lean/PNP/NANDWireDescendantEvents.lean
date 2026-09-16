/-
Copyright (c) 2026 PNP Labs.

Trace persistent descendant allocations to the raw input event family. Stage
positions come from traversal, and event IDs come from the unmodified input.
Uniqueness follows from actual accepted stage schedulers, not a supplied owner
map or a deduplicated list that could conceal conflicting raw events.

This is provenance for the existing closed history language, not global route
coverage, cross-support open obligations or polynomial runtime.
-/

import PNP.NANDWireDescendantOwnership

namespace PNP.DirectWire.WireDescendantHistory

/-- Full raw event family, computed before a final support is selected.
The position is advanced internally by traversal, not supplied by a stage. -/
def inputEventKeys : Nat → List RawStage → List (Nat × Nat)
  | _, [] => []
  | position, stage :: stages =>
      stage.events.map (fun event => (position, event.identity)) ++
        inputEventKeys (position + 1) stages

theorem inputEventKeys_nil (position : Nat) : inputEventKeys position [] = [] := rfl

theorem inputEventKeys_cons (position : Nat) (stage : RawStage) (stages : List RawStage) :
    inputEventKeys position (stage :: stages) =
      stage.events.map (fun event => (position, event.identity)) ++
        inputEventKeys (position + 1) stages := rfl

theorem inputEventKeys_bounds (position : Nat) (stages : List RawStage)
    (key : Nat × Nat) (member : key ∈ inputEventKeys position stages) :
    position ≤ key.1 ∧ key.1 < position + stages.length := by
  induction stages generalizing position with
  | nil => cases member
  | cons stage stages ih =>
      rw [inputEventKeys_cons] at member
      rcases List.mem_append.mp member with here | later
      · obtain ⟨event, _eventMember, keyAt⟩ := List.mem_map.mp here
        rw [← keyAt]
        simp only [List.length_cons]
        constructor <;> omega
      · have bounds := ih (position + 1) later
        simp only [List.length_cons]
        constructor <;> omega

/-- Decoding preserves IDs, and the existing accepted local scheduler proves
their uniqueness. This does not deduplicate malformed raw input. -/
theorem StageCompilation.rawEventIdentities_nodup
    {inputs outputs : Nat} {source : Implementation inputs outputs} {stage : RawStage}
    (compiled : StageCompilation source stage) :
    (stage.events.map EventInput.identity).Nodup := by
  rw [← compiled.events_source, List.map_map]
  change (compiled.events.map (fun event => event.identity)).Nodup
  apply List.pairwise_iff_getElem.mpr
  intro left right leftBound rightBound before same
  have leftValid : left < compiled.events.length := by
    simpa only [List.length_map] using leftBound
  have rightValid : right < compiled.events.length := by
    simpa only [List.length_map] using rightBound
  have sameIdentity :
      (compiled.events.get ⟨left, leftValid⟩).identity =
        (compiled.events.get ⟨right, rightValid⟩).identity := by
    simpa only [List.getElem_map, List.get_eq_getElem] using same
  have sameIndex : left = right :=
    congrArg Fin.val (compiled.event_identity_unique _ _ sameIdentity)
  omega

namespace CompiledRun

variable {inputs outputs initialGates : Nat}
variable {source : Implementation inputs outputs} {stages : List RawStage}

/-- Reused local IDs are distinct globally because stages have computed,
strictly increasing positions. -/
theorem inputEventKeys_nodup (run : CompiledRun source stages) :
    ∀ position, (inputEventKeys position stages).Nodup := by
  induction run with
  | nil source => intro position; exact List.nodup_nil
  | @cons source stage stages first rest ih =>
      intro position
      rw [inputEventKeys_cons]
      apply List.nodup_append.mpr
      refine ⟨?_, ih (position + 1), ?_⟩
      · have mapped :
            ((stage.events.map EventInput.identity).map (fun identity => (position, identity))).Nodup :=
          List.Pairwise.map (fun identity => (position, identity))
            (fun _ _ different same => different (congrArg Prod.snd same))
            first.rawEventIdentities_nodup
        simpa only [List.map_map, Function.comp_def] using mapped
      · intro left leftMember right rightMember same
        obtain ⟨event, _eventMember, leftAt⟩ := List.mem_map.mp leftMember
        have bounds := inputEventKeys_bounds (position + 1) stages right rightMember
        have samePosition : position = right.1 := congrArg Prod.fst (leftAt.trans same)
        omega

theorem inputEventKeys_unique (run : CompiledRun source stages) (position : Nat)
    (left right : Fin (inputEventKeys position stages).length)
    (same : (inputEventKeys position stages).get left =
      (inputEventKeys position stages).get right) : left = right := by
  apply Fin.ext
  exact (List.getElem_inj (run.inputEventKeys_nodup position)).mp same

/-- Every folded charge is either historical on entry or was allocated by an
actual raw event in this very stage sequence. No ownership premise is required. -/
theorem carry_charged_origin (run : CompiledRun source stages) :
    ∀ (position : Nat) (ledger : PersistentOwnership initialGates source.gateCount)
      (origin : DescendantOrigin initialGates),
      origin ∈ (run.carry position ledger).charged →
      origin ∈ ledger.charged ∨
        ∃ stagePosition identity localGate,
          origin = .allocated stagePosition identity localGate ∧
            (stagePosition, identity) ∈ inputEventKeys position stages := by
  induction run with
  | nil source =>
      intro position ledger origin member
      exact Or.inl member
  | @cons source stage stages first rest ih =>
      intro position ledger origin member
      have traced := ih (position + 1) (ledger.advance position first) origin member
      rcases traced with old | later
      · change origin ∈ ledger.charged ++
          first.ledger.charged.map (ledger.liftOrigin position) at old
        rcases List.mem_append.mp old with old | fresh
        · exact Or.inl old
        · obtain ⟨event, eventMember, localGate, originAt⟩ :=
            ledger.advance_charge_origin position first origin fresh
          refine Or.inr ⟨position, event.identity, localGate, originAt, ?_⟩
          exact List.mem_append_left _
            (List.mem_map.mpr ⟨event, eventMember, rfl⟩)
      · obtain ⟨stagePosition, identity, localGate, originAt, keyMember⟩ := later
        exact Or.inr ⟨stagePosition, identity, localGate, originAt,
          List.mem_append_right _ keyMember⟩

/-- The public fold begins without supplied historical charges, so every
charge comes from this program's own input event family. -/
theorem ledger_charged_origin (run : CompiledRun source stages)
    (origin : DescendantOrigin source.gateCount) (member : origin ∈ run.ledger.charged) :
    ∃ stagePosition identity localGate,
      origin = .allocated stagePosition identity localGate ∧
        (stagePosition, identity) ∈ inputEventKeys 0 stages := by
  have traced := run.carry_charged_origin 0
    (PersistentOwnership.initial source.gateCount) origin member
  rcases traced with impossible | actual
  · cases impossible
  · exact actual

/-- Identity conservation links every live allocation to its actual raw event.
Surviving original gates cannot be mistaken for charged allocations. -/
theorem ledger_live_allocated_event (run : CompiledRun source stages)
    (gate : Fin run.result.gateCount) (stagePosition identity localGate : Nat)
    (originAt : run.ledger.origin gate = .allocated stagePosition identity localGate) :
    (stagePosition, identity) ∈ inputEventKeys 0 stages := by
  have live : DescendantOrigin.allocated stagePosition identity localGate ∈ run.ledger.live :=
    List.mem_ofFn.mpr ⟨gate, originAt⟩
  have present := run.physical_ownership.2.2.2.2.subset (List.mem_append_left _ live)
  rcases List.mem_append.mp present with original | charged
  · obtain ⟨originalGate, impossible⟩ := List.mem_ofFn.mp original
    cases impossible
  · obtain ⟨otherPosition, otherIdentity, otherGate, allocatedAt, keyMember⟩ :=
      run.ledger_charged_origin _ charged
    obtain ⟨samePosition, sameIdentity, _sameGate⟩ := DescendantOrigin.allocated.inj allocatedAt
    cases samePosition
    cases sameIdentity
    exact keyMember

end CompiledRun
end PNP.DirectWire.WireDescendantHistory

/-
Copyright (c) 2026 PNP Labs.

Source-derived syntactic dependency bounds through every actual R5/R6/R7/R8
wire-obligation history. The invariant includes each immutable pending snapshot,
not only the current carrier. All final caps come from the original source.
These bounds do not replace source identity with Boolean equivalence and do not
supply a complete manuscript calculus, global ZeroSlack or polynomial PCCMin.
-/

import PNP.NANDWireCausalBounds
import PNP.NANDWireObligationHistoryExecution

namespace PNP.DirectWire.WireObligationHistory

open WireObligationRestoration

variable {inputs outputs fields : Nat}

/-- Fixed bounds computed from the original carrier's literal source graph. -/
def SourceCausalBounds (source current : WireCarrier inputs outputs fields)
    (labels : Fin inputs → Nat) : Prop :=
  current.CausalBounds labels
    (CausalBound.outputLevel source.implementation.candidate labels)
    (source.fieldLevel labels)

/-- Each pending snapshot keeps the bounds of every original observation. -/
def PendingCausalBounds (source : WireCarrier inputs outputs fields)
    (pending : (field : Fin fields) → Option (Snapshot source field))
    (labels : Fin inputs → Nat) : Prop :=
  ∀ field snapshot, pending field = some snapshot →
    SourceCausalBounds source snapshot.carrier labels

def State.CausalInvariant {source : WireCarrier inputs outputs fields}
    (state : State source) (labels : Fin inputs → Nat) : Prop :=
  SourceCausalBounds source state.current labels ∧
    PendingCausalBounds source state.pending labels

private theorem pendingCausalBounds_set
    (source : WireCarrier inputs outputs fields)
    (pending : (field : Fin fields) → Option (Snapshot source field))
    (field : Fin fields) (next : Option (Snapshot source field))
    (labels : Fin inputs → Nat)
    (bounded : PendingCausalBounds source pending labels)
    (nextBounded : ∀ snapshot, next = some snapshot →
      SourceCausalBounds source snapshot.carrier labels) :
    PendingCausalBounds source (setPending pending field next) labels := by
  intro other snapshot found
  by_cases same : other = field
  · subst other
    rw [setPending_self] at found
    exact nextBounded snapshot found
  · exact bounded other snapshot
      ((setPending_other pending field next other same).symm.trans found)

namespace State

variable {source : WireCarrier inputs outputs fields}

theorem initial_causalInvariant (source : WireCarrier inputs outputs fields)
    (labels : Fin inputs → Nat) : (initial source).CausalInvariant labels := by
  constructor
  · exact source.causalBounds_self labels
  · intro field snapshot found
    change (none : Option (Snapshot source field)) = some snapshot at found
    cases found

theorem create_causalInvariant (state : State source) (identity : Nat)
    (field : Fin fields) (available : state.pending field = none)
    (labels : Fin inputs → Nat) (bounded : state.CausalInvariant labels) :
    (state.create identity field available).CausalInvariant labels := by
  constructor
  · exact masked_causalBounds state.current (keepExcept field) labels _ _ bounded.1
  · apply pendingCausalBounds_set source state.pending field
      (some (state.capture identity field available)) labels bounded.2
    intro snapshot found
    have same := Option.some.inj found
    cases same
    exact bounded.1

theorem normalize_causalInvariant (state : State source)
    (labels : Fin inputs → Nat) (bounded : state.CausalInvariant labels) :
    state.normalize.CausalInvariant labels :=
  ⟨state.current.normalize_causalBounds labels _ _ bounded.1, bounded.2⟩

theorem restore_causalInvariant (state : State source) (field : Fin fields)
    (snapshot : Snapshot source field) (found : state.pending field = some snapshot)
    (labels : Fin inputs → Nat) (bounded : state.CausalInvariant labels) :
    (state.restore field snapshot found).CausalInvariant labels := by
  have snapshotBound := bounded.2 field snapshot found
  constructor
  · exact join_causalBounds state.current
      (materializer snapshot.carrier (keepExcept field)) (keepExcept field)
      labels _ _ bounded.1
      (materializer_causalBounds snapshot.carrier (keepExcept field) labels _
        snapshotBound.2)
  · apply pendingCausalBounds_set source state.pending field none labels bounded.2
    intro missing impossible
    cases impossible

theorem restoreR7_causalInvariant (state : State source) (field : Fin fields)
    (snapshot : Snapshot source field) (found : state.pending field = some snapshot)
    (raw : List RawSupportRecord) (realization : R7Realization snapshot.carrier raw)
    (labels : Fin inputs → Nat) (bounded : state.CausalInvariant labels) :
    (state.restoreR7 field snapshot found raw realization).CausalInvariant labels := by
  have snapshotBound := bounded.2 field snapshot found
  have realizedBound := realization.causalBounds labels
  constructor
  · exact join_causalBounds state.current
      (materializer realization.carrier (keepExcept field)) (keepExcept field)
      labels _ _ bounded.1
      (materializer_causalBounds realization.carrier (keepExcept field) labels _
        (fun other => Nat.le_trans (realizedBound.2 other) (snapshotBound.2 other)))
  · apply pendingCausalBounds_set source state.pending field none labels bounded.2
    intro missing impossible
    cases impossible

theorem cancel_causalInvariant (state : State source) (field : Fin fields)
    (snapshot : Snapshot source field) (found : state.pending field = some snapshot)
    (alias : WireMatchedCancellation.Representative source state.keep field)
    (labels : Fin inputs → Nat) (bounded : state.CausalInvariant labels) :
    (state.cancel field snapshot found alias).CausalInvariant labels := by
  have observationBound :
      CausalBound.source
          (state.current.exposed.candidate.directWireWord.source alias.observation) labels
          (CausalBound.levels state.current.implementation.candidate.program labels) ≤
        source.fieldLevel labels field := by
    calc
      _ ≤ splitFin (CausalBound.outputLevel source.implementation.candidate labels)
            (source.fieldLevel labels) alias.observation :=
        state.current.causalBounds_exposed_le labels _ _ bounded.1 alias.observation
      _ = CausalBound.outputLevel source.exposed.candidate labels alias.observation :=
        (source.exposed_level labels alias.observation).symm
      _ = source.fieldLevel labels field := by
        change CausalBound.source
          (source.exposed.candidate.directWireWord.source alias.observation) labels
          (CausalBound.levels source.implementation.candidate.program labels) = _
        rw [alias.sourceExact]
        rfl
  constructor
  · constructor
    · exact bounded.1.1
    · intro other
      change CausalBound.source
        (if other = field then state.current.exposed.candidate.directWireWord.source alias.observation
          else state.current.source other) labels
        (CausalBound.levels state.current.implementation.candidate.program labels) ≤
          source.fieldLevel labels other
      by_cases same : other = field
      · subst other
        rw [if_pos rfl]
        exact observationBound
      · rw [if_neg same]
        exact bounded.1.2 other
  · apply pendingCausalBounds_set source state.pending field none labels bounded.2
    intro missing impossible
    cases impossible

end State

theorem Transition.causalInvariant
    {source : WireCarrier inputs outputs fields}
    {before after : State source} {event : RawEvent fields}
    (step : Transition source before event after) (labels : Fin inputs → Nat) :
    before.CausalInvariant labels → after.CausalInvariant labels := by
  intro bounded
  cases step with
  | create field kind available =>
      exact before.create_causalInvariant event.identity field available labels bounded
  | restore identity kind entry =>
      exact before.restore_causalInvariant entry.field entry.snapshot entry.found labels bounded
  | realize identity raw kind entry realization computed =>
      exact before.restoreR7_causalInvariant entry.field entry.snapshot entry.found raw realization labels bounded
  | cancel identity kind entry alias computed =>
      exact before.cancel_causalInvariant entry.field entry.snapshot entry.found alias labels bounded
  | normalize kind => exact before.normalize_causalInvariant labels bounded
  | read field kind available => exact bounded

theorem Execution.causalInvariant
    {source : WireCarrier inputs outputs fields}
    {before after : State source} {events : List (RawEvent fields)}
    (trace : Execution source before events after) (labels : Fin inputs → Nat) :
    before.CausalInvariant labels → after.CausalInvariant labels := by
  induction trace with
  | nil state => exact fun bounded => bounded
  | cons step tail ih =>
      intro bounded
      exact ih (step.causalInvariant labels bounded)

namespace ClosedHistory

variable {source : WireCarrier inputs outputs fields} {raw : List (RawEvent fields)}

/-- The complete executed history derives its own invariant from the source. -/
theorem causalInvariant (history : ClosedHistory source raw) (labels : Fin inputs → Nat) :
    history.state.CausalInvariant labels :=
  history.execution.causalInvariant labels (State.initial_causalInvariant source labels)

theorem output_causal_bound (history : ClosedHistory source raw)
    (labels : Fin inputs → Nat) (output : Fin outputs) :
    CausalBound.outputLevel history.state.current.implementation.candidate labels output ≤
      CausalBound.outputLevel source.implementation.candidate labels output :=
  (history.causalInvariant labels).1.1 output

theorem field_causal_bound (history : ClosedHistory source raw)
    (labels : Fin inputs → Nat) (field : Fin fields) :
    history.state.current.fieldLevel labels field ≤ source.fieldLevel labels field :=
  (history.causalInvariant labels).1.2 field

end ClosedHistory

/-- Every successful raw-input compilation carries source-derived wiring bounds.
No additional rank, coverage or correctness certificate is supplied. -/
theorem compileHistory_causal_bounds (source : WireCarrier inputs outputs fields)
    (raw : List (RawEvent fields)) (labels : Fin inputs → Nat) :
    match compileHistory source raw with
    | none => True
    | some history => SourceCausalBounds source history.state.current labels := by
  cases compileHistory source raw with
  | none => trivial
  | some history => exact (history.causalInvariant labels).1

end PNP.DirectWire.WireObligationHistory

/-
Copyright (c) 2026 PNP Labs.

The internal physical state of a computed wire-obligation history. A creation
captures its actual pre-drop carrier. Normalization transports available full
values without changing those snapshots. R6 uses a genuinely visible original
source representative; R8 appends and pays its actual captured materializer.

These transition constructors are not the raw-input history compiler, complete
Package E, unconditional ZeroSlack, or a polynomial execution theorem.
-/

import PNP.NANDWireMatchedCancellation

namespace PNP.DirectWire.WireObligationHistory

open WireObligationRestoration

variable {inputs outputs fields : Nat}

/-- An immutable actual carrier and its full-value connection to one field. -/
structure Snapshot (source : WireCarrier inputs outputs fields) (field : Fin fields) where
  identity : Nat
  carrier : WireCarrier inputs outputs fields
  fullValue : ∀ valuation, carrier.fieldValue valuation field = source.fieldValue valuation field

def keepExcept (field : Fin fields) (other : Fin fields) : Bool :=
  decide (other ≠ field)

theorem keepExcept_self (field : Fin fields) : keepExcept field field = false := by
  simp [keepExcept]

theorem keepExcept_other (field other : Fin fields) (different : other ≠ field) :
    keepExcept field other = true := by
  simp [keepExcept, different]

/-- Replace just one coordinate of the dependent open ledger. -/
def setPending {source : WireCarrier inputs outputs fields}
    (pending : (field : Fin fields) → Option (Snapshot source field))
    (field : Fin fields) (next : Option (Snapshot source field)) :
    (other : Fin fields) → Option (Snapshot source other) :=
  fun other => if same : field = other then same ▸ next else pending other

theorem setPending_self {source : WireCarrier inputs outputs fields}
    (pending : (field : Fin fields) → Option (Snapshot source field))
    (field : Fin fields) (next : Option (Snapshot source field)) :
    setPending pending field next field = next := by
  unfold setPending
  exact dif_pos rfl

theorem setPending_other {source : WireCarrier inputs outputs fields}
    (pending : (field : Fin fields) → Option (Snapshot source field))
    (field : Fin fields) (next : Option (Snapshot source field))
    (other : Fin fields) (different : other ≠ field) :
    setPending pending field next other = pending other := by
  simp only [setPending, dif_neg (Ne.symm different)]

private theorem masked_other (carrier : WireCarrier inputs outputs fields)
    (field other : Fin fields) (different : other ≠ field) (valuation : Valuation inputs) :
    (masked carrier (keepExcept field)).fieldValue valuation other =
      carrier.fieldValue valuation other := by
  change (if keepExcept field other then carrier.source other else .constant false).eval
    valuation (carrier.implementation.candidate.program.eval valuation) = _
  rw [keepExcept_other field other different]
  rfl

/-- Invariants are constructed by execution, never supplied with the raw events. -/
structure State (source : WireCarrier inputs outputs fields) where
  current : WireCarrier inputs outputs fields
  pending : (field : Fin fields) → Option (Snapshot source field)
  charged : Nat
  removed : Nat
  output : ∀ valuation output, current.implementation.candidate.semantics valuation output =
    source.implementation.candidate.semantics valuation output
  available : ∀ valuation field, pending field = none →
    current.fieldValue valuation field = source.fieldValue valuation field
  balance : current.implementation.gateCount + removed =
    source.implementation.gateCount + charged

namespace State

variable {source : WireCarrier inputs outputs fields}

def initial (source : WireCarrier inputs outputs fields) : State source where
  current := source
  pending := fun _ => none
  charged := 0
  removed := 0
  output := fun _ _ => rfl
  available := fun _ _ _ => rfl
  balance := rfl

/-- Only an available coordinate can supply its actual pre-drop snapshot. -/
def capture (state : State source) (identity : Nat) (field : Fin fields)
    (available : state.pending field = none) : Snapshot source field where
  identity := identity
  carrier := state.current
  fullValue := fun valuation => state.available valuation field available

/-- R5 changes a quotient binding only; it does not physically prune a gate. -/
def create (state : State source) (identity : Nat) (field : Fin fields)
    (available : state.pending field = none) : State source where
  current := masked state.current (keepExcept field)
  pending := setPending state.pending field (some (state.capture identity field available))
  charged := state.charged
  removed := state.removed
  output := state.output
  available := by
    intro valuation other closed
    by_cases same : other = field
    · subst other
      simp only [setPending_self] at closed
      cases closed
    · apply (masked_other state.current field other same valuation).trans
      apply state.available valuation other
      exact (setPending_other state.pending field _ other same).symm.trans closed
  balance := state.balance

theorem create_source_snapshot (state : State source) (identity : Nat) (field : Fin fields)
    (available : state.pending field = none) :
    (state.create identity field available).pending field =
      some (state.capture identity field available) :=
  setPending_self state.pending field _

theorem create_gateCount (state : State source) (identity : Nat) (field : Fin fields)
    (available : state.pending field = none) :
    (state.create identity field available).current.implementation.gateCount =
      state.current.implementation.gateCount := rfl

/-- Physical normalization preserves available fields and immutable open snapshots. -/
def normalize (state : State source) : State source where
  current := state.current.normalize
  pending := state.pending
  charged := state.charged
  removed := state.removed + (runPhysicalNormalization state.current.exposed).trace.savedGates
  output := fun valuation output =>
    (state.current.normalize_output valuation output).trans (state.output valuation output)
  available := fun valuation field closed =>
    (state.current.normalize_field valuation field).trans (state.available valuation field closed)
  balance := by
    have physical := state.current.normalize_exact_accounting
    have prior := state.balance
    omega

theorem normalize_gate_balance (state : State source) :
    state.normalize.current.implementation.gateCount + state.normalize.removed =
      source.implementation.gateCount + state.charged := state.normalize.balance

/-- R8 appends the real materializer of this creation, paying the entire suffix. -/
def restore (state : State source) (field : Fin fields) (snapshot : Snapshot source field)
    (_found : state.pending field = some snapshot) : State source where
  current := join state.current (materializer snapshot.carrier (keepExcept field)) (keepExcept field)
  pending := setPending state.pending field none
  charged := state.charged + (materializer snapshot.carrier (keepExcept field)).implementation.gateCount
  removed := state.removed
  output := fun valuation output =>
    (join_output state.current _ (keepExcept field) valuation output).trans (state.output valuation output)
  available := by
    intro valuation other closed
    by_cases same : other = field
    · subst other
      exact (join_forgotten_field state.current _ (keepExcept field) valuation field
        (keepExcept_self field)).trans
          ((materializer_forgotten_field snapshot.carrier (keepExcept field) valuation field
            (keepExcept_self field)).trans (snapshot.fullValue valuation))
    · apply (join_kept_field state.current _ (keepExcept field) valuation other
        (keepExcept_other field other same)).trans
      apply state.available valuation other
      exact (setPending_other state.pending field none other same).symm.trans closed
  balance := by
    have prior := state.balance
    change (state.current.implementation.gateCount +
      (materializer snapshot.carrier (keepExcept field)).implementation.gateCount) + state.removed =
        source.implementation.gateCount + (state.charged +
          (materializer snapshot.carrier (keepExcept field)).implementation.gateCount)
    omega

theorem restore_gate_charge (state : State source) (field : Fin fields)
    (snapshot : Snapshot source field) (found : state.pending field = some snapshot) :
    (state.restore field snapshot found).current.implementation.gateCount =
      state.current.implementation.gateCount +
        (materializer snapshot.carrier (keepExcept field)).implementation.gateCount := rfl

theorem restore_full_value (state : State source) (field : Fin fields)
    (snapshot : Snapshot source field) (found : state.pending field = some snapshot)
    (valuation : Valuation inputs) :
    (state.restore field snapshot found).current.fieldValue valuation field =
      snapshot.carrier.fieldValue valuation field :=
  ((state.restore field snapshot found).available valuation field
    (setPending_self state.pending field none)).trans (snapshot.fullValue valuation).symm

/-- The mask is derived from the current open ledger, not supplied by a caller. -/
def keep (state : State source) (field : Fin fields) : Bool :=
  (state.pending field).isNone

theorem keep_iff (state : State source) (field : Fin fields) :
    state.keep field = true ↔ state.pending field = none := by
  cases found : state.pending field <;> simp [keep, found]

theorem currentAgreement (state : State source) :
    WireQuotientLift.QuotientAgreement source state.keep state.current where
  output := fun valuation output => (state.output valuation output).trans
    (projected_output source state.keep valuation output).symm
  keptField := fun valuation field kept =>
    (state.available valuation field ((state.keep_iff field).1 kept)).trans
      (projected_kept_field source state.keep valuation field kept).symm

/-- Rebind one coordinate to an actual source in the current program. -/
def rebind (carrier : WireCarrier inputs outputs fields) (field : Fin fields)
    (wire : Source inputs carrier.implementation.gateCount) : WireCarrier inputs outputs fields where
  implementation := carrier.implementation
  source := fun other => if other = field then wire else carrier.source other

private theorem rebind_self (carrier : WireCarrier inputs outputs fields) (field : Fin fields)
    (wire : Source inputs carrier.implementation.gateCount) (valuation : Valuation inputs) :
    (rebind carrier field wire).fieldValue valuation field =
      wire.eval valuation (carrier.implementation.candidate.program.eval valuation) := by
  change (if field = field then wire else carrier.source field).eval valuation
    (carrier.implementation.candidate.program.eval valuation) = _
  rw [if_pos rfl]

private theorem rebind_other (carrier : WireCarrier inputs outputs fields) (field other : Fin fields)
    (wire : Source inputs carrier.implementation.gateCount) (different : other ≠ field)
    (valuation : Valuation inputs) :
    (rebind carrier field wire).fieldValue valuation other = carrier.fieldValue valuation other := by
  simp only [rebind, WireCarrier.fieldValue, if_neg different]

/-- The source-identity R6 case uses full values of a genuinely visible observation. -/
def cancel (state : State source) (field : Fin fields) (snapshot : Snapshot source field)
    (_found : state.pending field = some snapshot)
    (alias : WireMatchedCancellation.Representative source state.keep field) : State source where
  current := rebind state.current field
    (state.current.exposed.candidate.directWireWord.source alias.observation)
  pending := setPending state.pending field none
  charged := state.charged
  removed := state.removed
  output := state.output
  available := by
    intro valuation other closed
    by_cases same : other = field
    · subst other
      apply (rebind_self state.current field _ valuation).trans
      exact alias.full_value state.current state.currentAgreement valuation
    · apply (rebind_other state.current field other _ same valuation).trans
      apply state.available valuation other
      exact (setPending_other state.pending field none other same).symm.trans closed
  balance := state.balance

theorem cancel_gateCount (state : State source) (field : Fin fields)
    (snapshot : Snapshot source field) (found : state.pending field = some snapshot)
    (alias : WireMatchedCancellation.Representative source state.keep field) :
    (state.cancel field snapshot found alias).current.implementation.gateCount =
      state.current.implementation.gateCount := rfl

theorem cancel_full_value (state : State source) (field : Fin fields)
    (snapshot : Snapshot source field) (found : state.pending field = some snapshot)
    (alias : WireMatchedCancellation.Representative source state.keep field)
    (valuation : Valuation inputs) :
    (state.cancel field snapshot found alias).current.fieldValue valuation field =
      snapshot.carrier.fieldValue valuation field :=
  ((state.cancel field snapshot found alias).available valuation field
    (setPending_self state.pending field none)).trans (snapshot.fullValue valuation).symm

/-- Empty means every coordinate is available, not just a caller's closed bit. -/
theorem closed_field (state : State source) (closed : ∀ field, state.pending field = none)
    (valuation : Valuation inputs) (field : Fin fields) :
    state.current.fieldValue valuation field = source.fieldValue valuation field :=
  state.available valuation field (closed field)

end State
end PNP.DirectWire.WireObligationHistory

/-
Copyright (c) 2026 PNP Labs.

Decode raw computational support coordinates against the immutable carrier of
one open creation. Derive its zero/unary replacement from the actual open
function, then restore the requested full field using that result's physical
materializer. Every appended gate is charged; no replacement or correctness
certificate is a raw input.

This R7 transition is not a global support-selection strategy, complete Package E,
unconditional ZeroSlack, strict gain, or polynomial-time PCCMin.
-/

import PNP.NANDWireObligationHistoryState
import PNP.NANDWireUnaryCausalBounds

namespace PNP.DirectWire.WireObligationHistory

open WireObligationRestoration

variable {inputs outputs fields : Nat}

/-- Untyped coordinates carry no implementation, order, rank, or proof data. -/
inductive RawSupportRecord where
  | gate (index : Nat)
  | boundary (index : Nat)
  | interface (index : Nat)
  deriving Repr, DecidableEq

def decodeRecord (inputs gates observations : Nat) : RawSupportRecord →
    Option (TerminalPrimitiveRecord inputs gates observations 0)
  | .gate index => if valid : index < gates then some (.gate ⟨index, valid⟩) else none
  | .boundary index => if valid : index < inputs then some (.boundary ⟨index, valid⟩) else none
  | .interface index =>
      if valid : index < observations then some (.interface ⟨index, valid⟩) else none

def encodeRecord {inputs gates observations : Nat} :
    TerminalPrimitiveRecord inputs gates observations 0 → RawSupportRecord
  | .gate index => .gate index.val
  | .boundary index => .boundary index.val
  | .interface index => .interface index.val
  | .profile index => Fin.elim0 index

/-- Every well-typed computational record is accepted without changing its index. -/
theorem decodeRecord_encode {inputs gates observations : Nat}
    (record : TerminalPrimitiveRecord inputs gates observations 0) :
    decodeRecord inputs gates observations (encodeRecord record) = some record := by
  cases record with
  | gate index => simp only [encodeRecord, decodeRecord, dif_pos index.isLt]
  | boundary index => simp only [encodeRecord, decodeRecord, dif_pos index.isLt]
  | interface index => simp only [encodeRecord, decodeRecord, dif_pos index.isLt]
  | profile index => exact Fin.elim0 index

/-- A successful decoder cannot silently substitute a different raw coordinate. -/
theorem decodeRecord_source {inputs gates observations : Nat} (raw : RawSupportRecord)
    (record : TerminalPrimitiveRecord inputs gates observations 0)
    (accepted : decodeRecord inputs gates observations raw = some record) :
    encodeRecord record = raw := by
  cases raw with
  | gate index =>
      change (if valid : index < gates then some (.gate ⟨index, valid⟩) else none) =
        some record at accepted
      by_cases valid : index < gates
      · rw [dif_pos valid] at accepted
        rw [← Option.some.inj accepted]
        rfl
      · rw [dif_neg valid] at accepted
        cases accepted
  | boundary index =>
      change (if valid : index < inputs then some (.boundary ⟨index, valid⟩) else none) =
        some record at accepted
      by_cases valid : index < inputs
      · rw [dif_pos valid] at accepted
        rw [← Option.some.inj accepted]
        rfl
      · rw [dif_neg valid] at accepted
        cases accepted
  | interface index =>
      change (if valid : index < observations then some (.interface ⟨index, valid⟩) else none) =
        some record at accepted
      by_cases valid : index < observations
      · rw [dif_pos valid] at accepted
        rw [← Option.some.inj accepted]
        rfl
      · rw [dif_neg valid] at accepted
        cases accepted

def decodeRecords (inputs gates observations : Nat) (raw : List RawSupportRecord) :
    Option (List (TerminalPrimitiveRecord inputs gates observations 0)) :=
  raw.mapM (decodeRecord inputs gates observations)

/-- Every finite well-typed record list round-trips through the raw decoder. -/
theorem decodeRecords_encode {inputs gates observations : Nat}
    (records : List (TerminalPrimitiveRecord inputs gates observations 0)) :
    decodeRecords inputs gates observations (records.map encodeRecord) = some records := by
  induction records with
  | nil => rfl
  | cons head tail ih =>
      change (encodeRecord head :: tail.map encodeRecord).mapM
        (decodeRecord inputs gates observations) = some (head :: tail)
      rw [List.mapM_cons, decodeRecord_encode]
      change (decodeRecords inputs gates observations (tail.map encodeRecord)).bind
        (fun rest => some (head :: rest)) = some (head :: tail)
      rw [ih]
      rfl

/-- Success preserves every raw coordinate and its position, not only the head. -/
theorem decodeRecords_source {inputs gates observations : Nat} (raw : List RawSupportRecord)
    (records : List (TerminalPrimitiveRecord inputs gates observations 0))
    (accepted : decodeRecords inputs gates observations raw = some records) :
    records.map encodeRecord = raw := by
  induction raw generalizing records with
  | nil =>
      change some [] = some records at accepted
      cases accepted
      rfl
  | cons head tail ih =>
      change (head :: tail).mapM (decodeRecord inputs gates observations) = some records at accepted
      rw [List.mapM_cons] at accepted
      change (decodeRecord inputs gates observations head).bind
        (fun item => (decodeRecords inputs gates observations tail).bind
          (fun items => some (item :: items))) = some records at accepted
      cases first : decodeRecord inputs gates observations head with
      | none =>
          rw [first] at accepted
          cases accepted
      | some item =>
          cases rest : decodeRecords inputs gates observations tail with
          | none =>
              rw [first, rest] at accepted
              cases accepted
          | some items =>
              rw [first, rest] at accepted
              have same := Option.some.inj accepted
              subst records
              rw [List.map_cons, decodeRecord_source head item first, ih items rest]


/-- Internal output of decoding and recognition, never a public raw-action premise. -/
structure R7Realization (original : WireCarrier inputs outputs fields)
    (raw : List RawSupportRecord) where
  records : List (TerminalPrimitiveRecord inputs original.implementation.gateCount
    (outputs + fields) 0)
  decoded : decodeRecords inputs original.implementation.gateCount (outputs + fields) raw =
    some records
  small : (WireUnaryArbitrarySupport.pulled original records).boundary.length ≤ 1

/-- Both the coordinate check and the completed-boundary check are executable. -/
def computeR7 (original : WireCarrier inputs outputs fields) (raw : List RawSupportRecord) :
    Option (R7Realization original raw) :=
  match decoded : decodeRecords inputs original.implementation.gateCount (outputs + fields) raw with
  | none => none
  | some records =>
      if small : (WireUnaryArbitrarySupport.pulled original records).boundary.length ≤ 1 then
        some ⟨records, decoded, small⟩
      else none

/-- Recognition succeeds exactly for valid coordinates with a completed zero/unary boundary. -/
theorem computeR7_isSome_iff (original : WireCarrier inputs outputs fields)
    (raw : List RawSupportRecord) :
    (computeR7 original raw).isSome = true ↔
      ∃ records, decodeRecords inputs original.implementation.gateCount (outputs + fields) raw =
        some records ∧ (WireUnaryArbitrarySupport.pulled original records).boundary.length ≤ 1 := by
  unfold computeR7
  split
  next missing =>
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨records, accepted, _small⟩
      rw [missing] at accepted
      cases accepted
  next records decoded =>
    split
    next small => exact ⟨fun _ => ⟨records, decoded, small⟩, fun _ => rfl⟩
    next notSmall =>
      constructor
      · intro impossible
        cases impossible
      · rintro ⟨other, accepted, small⟩
        have same := Option.some.inj (decoded.symm.trans accepted)
        subst other
        exact (notSmall small).elim


namespace R7Realization

variable {original : WireCarrier inputs outputs fields} {raw : List RawSupportRecord}

/-- The physical result is the actual computed R7 splice, not an arbitrary witness. -/
def carrier (realization : R7Realization original raw) : WireCarrier inputs outputs fields :=
  WireUnaryArbitrarySupport.expanded original realization.records realization.small

theorem full_field (realization : R7Realization original raw) (valuation : Valuation inputs)
    (field : Fin fields) : realization.carrier.fieldValue valuation field =
      original.fieldValue valuation field :=
  WireUnaryArbitrarySupport.expanded_field original realization.records realization.small
    valuation field

theorem exact_charge (realization : R7Realization original raw) :
    realization.carrier.implementation.gateCount =
      (WireUnaryArbitrarySupport.replacement original realization.records realization.small).gateCount +
        WireUnaryArbitrarySupport.exteriorCharge original realization.records :=
  WireUnaryArbitrarySupport.expanded_charge original realization.records realization.small

theorem causalBounds (realization : R7Realization original raw) (labels : Fin inputs → Nat) :
    realization.carrier.CausalBounds labels
      (CausalBound.outputLevel original.implementation.candidate labels)
      (original.fieldLevel labels) :=
  WireUnaryCausalBound.expanded_causalBounds original realization.records realization.small labels

end R7Realization

namespace State

variable {source : WireCarrier inputs outputs fields}

/-- R7 materializes its own computed realization of this exact captured creation. -/
def restoreR7 (state : State source) (field : Fin fields) (snapshot : Snapshot source field)
    (_found : state.pending field = some snapshot) (raw : List RawSupportRecord)
    (realization : R7Realization snapshot.carrier raw) : State source where
  current := join state.current (materializer realization.carrier (keepExcept field)) (keepExcept field)
  pending := setPending state.pending field none
  charged := state.charged + (materializer realization.carrier (keepExcept field)).implementation.gateCount
  removed := state.removed
  output := fun valuation output =>
    (join_output state.current _ (keepExcept field) valuation output).trans (state.output valuation output)
  available := by
    intro valuation other closed
    by_cases same : other = field
    · subst other
      exact (join_forgotten_field state.current _ (keepExcept field) valuation field
        (keepExcept_self field)).trans
          ((materializer_forgotten_field realization.carrier (keepExcept field) valuation field
            (keepExcept_self field)).trans
              ((realization.full_field valuation field).trans (snapshot.fullValue valuation)))
    · apply (join_kept_field state.current _ (keepExcept field) valuation other
        (keepExcept_other field other same)).trans
      apply state.available valuation other
      exact (setPending_other state.pending field none other same).symm.trans closed
  balance := by
    have prior := state.balance
    change (state.current.implementation.gateCount +
      (materializer realization.carrier (keepExcept field)).implementation.gateCount) + state.removed =
        source.implementation.gateCount + (state.charged +
          (materializer realization.carrier (keepExcept field)).implementation.gateCount)
    omega

theorem restoreR7_gate_charge (state : State source) (field : Fin fields)
    (snapshot : Snapshot source field) (found : state.pending field = some snapshot)
    (raw : List RawSupportRecord) (realization : R7Realization snapshot.carrier raw) :
    (state.restoreR7 field snapshot found raw realization).current.implementation.gateCount =
      state.current.implementation.gateCount +
        (materializer realization.carrier (keepExcept field)).implementation.gateCount := rfl

theorem restoreR7_full_value (state : State source) (field : Fin fields)
    (snapshot : Snapshot source field) (found : state.pending field = some snapshot)
    (raw : List RawSupportRecord) (realization : R7Realization snapshot.carrier raw)
    (valuation : Valuation inputs) :
    (state.restoreR7 field snapshot found raw realization).current.fieldValue valuation field =
      snapshot.carrier.fieldValue valuation field :=
  ((state.restoreR7 field snapshot found raw realization).available valuation field
    (setPending_self state.pending field none)).trans (snapshot.fullValue valuation).symm

theorem restoreR7_other_pending (state : State source) (field : Fin fields)
    (snapshot : Snapshot source field) (found : state.pending field = some snapshot)
    (raw : List RawSupportRecord) (realization : R7Realization snapshot.carrier raw)
    (other : Fin fields) (different : other ≠ field) :
    (state.restoreR7 field snapshot found raw realization).pending other = state.pending other :=
  setPending_other state.pending field none other different

end State
end PNP.DirectWire.WireObligationHistory

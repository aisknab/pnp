/-
Copyright (c) 2026 PNP Labs.

Raw inputs for successive computational-history compilations. Coordinates are
decoded against the current finite shape; event identities, predecessor lists,
actions and captured R7 support data are preserved exactly. No implementation,
owner map, charge amount or correctness certificate is an input.

This is input decoding, not full-profile compatibility, a complete manuscript
calculus, a successful global strategy or a polynomial-runtime theorem.
-/

import PNP.NANDWireObligationHistory

namespace PNP.DirectWire.WireDescendantHistory

open WireObligationHistory

inductive RawRecord where
  | gate (index : Nat)
  | boundary (index : Nat)
  | interface (index : Nat)
  | profile (index : Nat)
  deriving Repr, DecidableEq

def decodeRecord (inputs gates outputs profileWidth : Nat) : RawRecord →
    Option (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  | .gate index => if valid : index < gates then some (.gate ⟨index, valid⟩) else none
  | .boundary index => if valid : index < inputs then some (.boundary ⟨index, valid⟩) else none
  | .interface index => if valid : index < outputs then some (.interface ⟨index, valid⟩) else none
  | .profile index =>
      if valid : index < profileWidth then some (.profile ⟨index, valid⟩) else none

def encodeRecord {inputs gates outputs profileWidth : Nat} :
    TerminalPrimitiveRecord inputs gates outputs profileWidth → RawRecord
  | .gate index => .gate index.val
  | .boundary index => .boundary index.val
  | .interface index => .interface index.val
  | .profile index => .profile index.val

theorem decodeRecord_encode {inputs gates outputs profileWidth : Nat}
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    decodeRecord inputs gates outputs profileWidth (encodeRecord record) = some record := by
  cases record with
  | gate index => simp only [encodeRecord, decodeRecord, dif_pos index.isLt]
  | boundary index => simp only [encodeRecord, decodeRecord, dif_pos index.isLt]
  | interface index => simp only [encodeRecord, decodeRecord, dif_pos index.isLt]
  | profile index => simp only [encodeRecord, decodeRecord, dif_pos index.isLt]

theorem decodeRecord_source (inputs gates outputs profileWidth : Nat)
    (raw : RawRecord) (record : TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (accepted : decodeRecord inputs gates outputs profileWidth raw = some record) :
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
      change (if valid : index < outputs then some (.interface ⟨index, valid⟩) else none) =
        some record at accepted
      by_cases valid : index < outputs
      · rw [dif_pos valid] at accepted
        rw [← Option.some.inj accepted]
        rfl
      · rw [dif_neg valid] at accepted
        cases accepted
  | profile index =>
      change (if valid : index < profileWidth then some (.profile ⟨index, valid⟩) else none) =
        some record at accepted
      by_cases valid : index < profileWidth
      · rw [dif_pos valid] at accepted
        rw [← Option.some.inj accepted]
        rfl
      · rw [dif_neg valid] at accepted
        cases accepted

private theorem mapM_encode {alpha beta : Type}
    (encode : alpha → beta) (decode : beta → Option alpha)
    (roundtrip : ∀ item, decode (encode item) = some item) (items : List alpha) :
    (items.map encode).mapM decode = some items := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      change (encode head :: tail.map encode).mapM decode = some (head :: tail)
      rw [List.mapM_cons, roundtrip]
      change ((tail.map encode).mapM decode).bind
        (fun rest => some (head :: rest)) = some (head :: tail)
      rw [ih]
      rfl

private theorem mapM_source {alpha beta : Type}
    (encode : alpha → beta) (decode : beta → Option alpha)
    (source : ∀ raw item, decode raw = some item → encode item = raw)
    (raw : List beta) (items : List alpha)
    (accepted : raw.mapM decode = some items) : items.map encode = raw := by
  induction raw generalizing items with
  | nil =>
      change some [] = some items at accepted
      cases accepted
      rfl
  | cons head tail ih =>
      rw [List.mapM_cons] at accepted
      change (decode head).bind
        (fun item => (tail.mapM decode).bind
          (fun rest => some (item :: rest))) = some items at accepted
      cases first : decode head with
      | none =>
          rw [first] at accepted
          cases accepted
      | some item =>
          cases remaining : tail.mapM decode with
          | none =>
              rw [first, remaining] at accepted
              cases accepted
          | some rest =>
              rw [first, remaining] at accepted
              cases accepted
              change encode item :: rest.map encode = head :: tail
              rw [source head item first, ih rest remaining]

def decodeRecords (inputs gates outputs profileWidth : Nat) (raw : List RawRecord) :
    Option (List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :=
  raw.mapM (decodeRecord inputs gates outputs profileWidth)

theorem decodeRecords_encode {inputs gates outputs profileWidth : Nat}
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    decodeRecords inputs gates outputs profileWidth (records.map encodeRecord) = some records :=
  mapM_encode encodeRecord (decodeRecord inputs gates outputs profileWidth)
    decodeRecord_encode records

theorem decodeRecords_source (inputs gates outputs profileWidth : Nat)
    (raw : List RawRecord) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (accepted : decodeRecords inputs gates outputs profileWidth raw = some records) :
    records.map encodeRecord = raw :=
  mapM_source encodeRecord (decodeRecord inputs gates outputs profileWidth)
    (decodeRecord_source inputs gates outputs profileWidth) raw records accepted

inductive RawAction where
  | createR5 (field : Nat)
  | cancelR6 (creationID : Nat)
  | restoreR8 (creationID : Nat)
  | realizeR7 (creationID : Nat) (records : List RawSupportRecord)
  | normalize
  | readFull (field : Nat)
  deriving Repr, DecidableEq

def decodeAction (fields : Nat) : RawAction → Option (Action fields)
  | .createR5 field =>
      if valid : field < fields then some (.createR5 ⟨field, valid⟩) else none
  | .cancelR6 identity => some (.cancelR6 identity)
  | .restoreR8 identity => some (.restoreR8 identity)
  | .realizeR7 identity records => some (.realizeR7 identity records)
  | .normalize => some .normalize
  | .readFull field =>
      if valid : field < fields then some (.readFull ⟨field, valid⟩) else none

def encodeAction {fields : Nat} : Action fields → RawAction
  | .createR5 field => .createR5 field.val
  | .cancelR6 identity => .cancelR6 identity
  | .restoreR8 identity => .restoreR8 identity
  | .realizeR7 identity records => .realizeR7 identity records
  | .normalize => .normalize
  | .readFull field => .readFull field.val

theorem decodeAction_encode {fields : Nat} (action : Action fields) :
    decodeAction fields (encodeAction action) = some action := by
  cases action with
  | createR5 field => simp only [encodeAction, decodeAction, dif_pos field.isLt]
  | cancelR6 identity => rfl
  | restoreR8 identity => rfl
  | realizeR7 identity records => rfl
  | normalize => rfl
  | readFull field => simp only [encodeAction, decodeAction, dif_pos field.isLt]

theorem decodeAction_source (fields : Nat) (raw : RawAction) (action : Action fields)
    (accepted : decodeAction fields raw = some action) : encodeAction action = raw := by
  cases raw with
  | createR5 field =>
      change (if valid : field < fields then some (.createR5 ⟨field, valid⟩) else none) =
        some action at accepted
      by_cases valid : field < fields
      · rw [dif_pos valid] at accepted
        rw [← Option.some.inj accepted]
        rfl
      · rw [dif_neg valid] at accepted
        cases accepted
  | cancelR6 identity => cases accepted; rfl
  | restoreR8 identity => cases accepted; rfl
  | realizeR7 identity records => cases accepted; rfl
  | normalize => cases accepted; rfl
  | readFull field =>
      change (if valid : field < fields then some (.readFull ⟨field, valid⟩) else none) =
        some action at accepted
      by_cases valid : field < fields
      · rw [dif_pos valid] at accepted
        rw [← Option.some.inj accepted]
        rfl
      · rw [dif_neg valid] at accepted
        cases accepted

structure EventInput where
  identity : Nat
  predecessorIDs : List Nat
  action : RawAction
  deriving Repr, DecidableEq

def decodeEvent (fields : Nat) (raw : EventInput) : Option (RawEvent fields) :=
  (decodeAction fields raw.action).map fun action =>
    { identity := raw.identity, predecessorIDs := raw.predecessorIDs, action := action }

def encodeEvent {fields : Nat} (event : RawEvent fields) : EventInput :=
  { identity := event.identity, predecessorIDs := event.predecessorIDs,
    action := encodeAction event.action }

theorem decodeEvent_encode {fields : Nat} (event : RawEvent fields) :
    decodeEvent fields (encodeEvent event) = some event := by
  unfold decodeEvent encodeEvent
  rw [decodeAction_encode]
  rfl

theorem decodeEvent_source (fields : Nat) (raw : EventInput) (event : RawEvent fields)
    (accepted : decodeEvent fields raw = some event) : encodeEvent event = raw := by
  unfold decodeEvent at accepted
  cases decoded : decodeAction fields raw.action with
  | none =>
      rw [decoded] at accepted
      cases accepted
  | some action =>
      rw [decoded] at accepted
      cases accepted
      have same := decodeAction_source fields raw.action action decoded
      cases raw with
      | mk identity predecessors rawAction =>
          exact congrArg (EventInput.mk identity predecessors) same

def decodeEvents (fields : Nat) (raw : List EventInput) : Option (List (RawEvent fields)) :=
  raw.mapM (decodeEvent fields)

theorem decodeEvents_encode {fields : Nat} (events : List (RawEvent fields)) :
    decodeEvents fields (events.map encodeEvent) = some events :=
  mapM_encode encodeEvent (decodeEvent fields) decodeEvent_encode events

theorem decodeEvents_source (fields : Nat) (raw : List EventInput)
    (events : List (RawEvent fields)) (accepted : decodeEvents fields raw = some events) :
    events.map encodeEvent = raw :=
  mapM_source encodeEvent (decodeEvent fields) (decodeEvent_source fields) raw events accepted

/-- All stage dimensions and coordinates are finite data, not supplied proof authority. -/
structure RawStage where
  profileWidth : Nat
  records : List RawRecord
  events : List EventInput
  deriving Repr, DecidableEq

end PNP.DirectWire.WireDescendantHistory

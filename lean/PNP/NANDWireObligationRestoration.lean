/-
Copyright (c) 2026 PNP Labs.

Construct the values forgotten by a wire-backed quotient from actual NAND
materializers. Projection padding is not a full-value witness. Restoration
pays the whole shared materializer once, even for repeated field references.

This is a computational lost-wire component, not the complete manuscript
carrier, R6/R7 calculus, Package E, global ZeroSlack or polynomial PCCMin.
-/

import PNP.NANDWireCarrier

namespace PNP.DirectWire.WireObligationRestoration

variable {inputs outputs fields : Nat}

/-- A quotient-only mask. Forgotten padding is not agreement on that field. -/
def masked (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : WireCarrier inputs outputs fields :=
  { implementation := carrier.implementation
    source := fun field =>
      if keep field then carrier.source field else .constant false }

/-- Normalize the actual ordinary outputs and retained computational fields. -/
def projected (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : WireCarrier inputs outputs fields :=
  (masked carrier keep).normalize

/-- One real program for all forgotten wires; records do not supply outputs. -/
def hidden (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : WireCarrier inputs 0 fields :=
  { implementation :=
      (Candidate.ofDirectWireWord carrier.implementation.candidate.program
        ⟨Fin.elim0⟩).toImplementation
    source := fun field =>
      if keep field then .constant false else carrier.source field }

/-- Sharing and pruning apply to the actual common materializer program. -/
def materializer (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : WireCarrier inputs 0 fields :=
  (hidden carrier keep).normalize

theorem projected_output (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (projected carrier keep).implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output :=
  (masked carrier keep).normalize_output valuation output

theorem projected_kept_field (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (valuation : Valuation inputs) (field : Fin fields)
    (kept : keep field = true) :
    (projected carrier keep).fieldValue valuation field =
      carrier.fieldValue valuation field := by
  apply ((masked carrier keep).normalize_field valuation field).trans
  change (if keep field then carrier.source field else .constant false).eval
      valuation (carrier.implementation.candidate.program.eval valuation) = _
  rw [kept]
  rfl

theorem materializer_forgotten_field (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (valuation : Valuation inputs) (field : Fin fields)
    (forgotten : keep field = false) :
    (materializer carrier keep).fieldValue valuation field =
      carrier.fieldValue valuation field := by
  apply ((hidden carrier keep).normalize_field valuation field).trans
  change (if keep field then .constant false else carrier.source field).eval
      valuation (carrier.implementation.candidate.program.eval valuation) = _
  rw [forgotten]
  rfl

private theorem prefix_value {leftGates rightGates : Nat}
    (left : Program inputs leftGates) (right : Program inputs rightGates)
    (source : Source inputs leftGates) (valuation : Valuation inputs) :
    (source.weakenGates rightGates).eval valuation
        ((left.appendSubstituted (fun input => .input input) right).eval valuation) =
      source.eval valuation (left.eval valuation) := by
  rw [Source.eval_weakenGates]
  exact source.eval_congr (fun _ => rfl)
    (fun gate => Program.eval_appendSubstituted_prefix left
      (fun input => .input input) right valuation gate)

private theorem suffix_value {leftGates rightGates : Nat}
    (left : Program inputs leftGates) (right : Program inputs rightGates)
    (source : Source inputs rightGates) (valuation : Valuation inputs) :
    (source.substituteInputs (fun input => Source.input (gates := leftGates) input)).eval
        valuation
        ((left.appendSubstituted (fun input => .input input) right).eval valuation) =
      source.eval valuation (right.eval valuation) := by
  rw [Source.eval_substituteInputs]
  exact source.eval_congr (fun _ => rfl)
    (fun gate => Program.eval_appendSubstituted_suffix left
      (fun input => .input input) right valuation gate)

/-- Literal common-input concatenation. The suffix is charged once, not per
field, and its values can only come from physical input/constant/gate sources. -/
def join (visible : WireCarrier inputs outputs fields)
    (missing : WireCarrier inputs 0 fields) (keep : Fin fields → Bool) :
    WireCarrier inputs outputs fields :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (visible.implementation.candidate.program.appendSubstituted
          (fun input => .input input) missing.implementation.candidate.program)
        ⟨fun output =>
          (visible.implementation.candidate.directWireWord.source output).weakenGates
            missing.implementation.gateCount⟩).toImplementation
    source := fun field =>
      if keep field then
        (visible.source field).weakenGates missing.implementation.gateCount
      else
        (missing.source field).substituteInputs (fun input => .input input) }

theorem join_output (visible : WireCarrier inputs outputs fields)
    (missing : WireCarrier inputs 0 fields) (keep : Fin fields → Bool)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (join visible missing keep).implementation.candidate.semantics valuation output =
      visible.implementation.candidate.semantics valuation output := by
  unfold join
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_semantics]
  exact prefix_value visible.implementation.candidate.program
    missing.implementation.candidate.program
    (visible.implementation.candidate.directWireWord.source output) valuation

theorem join_kept_field (visible : WireCarrier inputs outputs fields)
    (missing : WireCarrier inputs 0 fields) (keep : Fin fields → Bool)
    (valuation : Valuation inputs) (field : Fin fields) (kept : keep field = true) :
    (join visible missing keep).fieldValue valuation field =
      visible.fieldValue valuation field := by
  unfold join WireCarrier.fieldValue
  dsimp only [Candidate.toImplementation]
  rw [kept]
  exact prefix_value visible.implementation.candidate.program
    missing.implementation.candidate.program (visible.source field) valuation

theorem join_forgotten_field (visible : WireCarrier inputs outputs fields)
    (missing : WireCarrier inputs 0 fields) (keep : Fin fields → Bool)
    (valuation : Valuation inputs) (field : Fin fields)
    (forgotten : keep field = false) :
    (join visible missing keep).fieldValue valuation field =
      missing.fieldValue valuation field := by
  unfold join WireCarrier.fieldValue
  dsimp only [Candidate.toImplementation]
  rw [forgotten]
  exact suffix_value visible.implementation.candidate.program
    missing.implementation.candidate.program (missing.source field) valuation

/-- Compute both actual programs and reconstruct the complete field word. -/
def restored (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : WireCarrier inputs outputs fields :=
  join (projected carrier keep) (materializer carrier keep) keep

theorem restored_output (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (restored carrier keep).implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output :=
  (join_output (projected carrier keep) (materializer carrier keep) keep
    valuation output).trans (projected_output carrier keep valuation output)

theorem restored_field (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (valuation : Valuation inputs) (field : Fin fields) :
    (restored carrier keep).fieldValue valuation field =
      carrier.fieldValue valuation field := by
  cases kept : keep field with
  | true =>
      exact (join_kept_field (projected carrier keep) (materializer carrier keep)
        keep valuation field kept).trans
          (projected_kept_field carrier keep valuation field kept)
  | false =>
      exact (join_forgotten_field (projected carrier keep) (materializer carrier keep)
        keep valuation field kept).trans
          (materializer_forgotten_field carrier keep valuation field kept)

theorem restored_exact_gate_charge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (restored carrier keep).implementation.gateCount =
      (projected carrier keep).implementation.gateCount +
      (materializer carrier keep).implementation.gateCount := rfl

/-- An output gate-count bound, not an encoded execution-time theorem. -/
theorem restored_gate_bound (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (restored carrier keep).implementation.gateCount ≤
      carrier.implementation.gateCount + carrier.implementation.gateCount := by
  rw [restored_exact_gate_charge]
  exact Nat.add_le_add
    (Nat.le.intro ((masked carrier keep).normalize_exact_accounting))
    (Nat.le.intro ((hidden carrier keep).normalize_exact_accounting))


/-- A lost coordinate, bound to its literal original source and projection. -/
structure R5Creation (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) where
  coordinate : Fin fields
  forgotten : keep coordinate = false
  originalSource : Source inputs carrier.implementation.gateCount
  sourceExact : originalSource = carrier.source coordinate

/-- Derive the creation binding from a coordinate actually omitted by the mask. -/
def createR5 (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (field : Fin fields) (forgotten : keep field = false) :
    R5Creation carrier keep :=
  { coordinate := field, forgotten := forgotten
    originalSource := carrier.source field, sourceExact := rfl }

/-- A full-value discharge names the actual restored wire. Its record cannot
supply a new Boolean source or replace the witness by a quotient agreement. -/
structure R8Discharge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (creation : R5Creation carrier keep) where
  restoredSource : Source inputs (restored carrier keep).implementation.gateCount
  sourceExact : restoredSource = (restored carrier keep).source creation.coordinate
  fullWitness : ∀ valuation,
    restoredSource.eval valuation
        ((restored carrier keep).implementation.candidate.program.eval valuation) =
      creation.originalSource.eval valuation
        (carrier.implementation.candidate.program.eval valuation)

/-- Construct the full witness from the actual paid materializer, not an input
proof, closed bit, observer, or supplied discharge record. -/
def dischargeR8 (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (creation : R5Creation carrier keep) :
    R8Discharge carrier keep creation :=
  { restoredSource := (restored carrier keep).source creation.coordinate
    sourceExact := rfl
    fullWitness := by
      intro valuation
      rw [creation.sourceExact]
      exact restored_field carrier keep valuation creation.coordinate }

/-- This concrete slice creates with R5 and discharges with a full R8 witness.
It does not define other rewrite families or arbitrary dependency DAGs. -/
inductive Event (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) where
  | createR5 (creation : R5Creation carrier keep)
  | dischargeR8 (creation : R5Creation carrier keep)
      (witness : R8Discharge carrier keep creation)

/-- Deterministic independent lost-wire events: creation precedes discharge. -/
def eventsFor (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    List (Fin fields) → List (Event carrier keep)
  | [] => []
  | field :: remaining =>
      if forgotten : keep field = false then
        let creation := createR5 carrier keep field forgotten
        .createR5 creation :: .dischargeR8 creation (dischargeR8 carrier keep creation) ::
          eventsFor carrier keep remaining
      else eventsFor carrier keep remaining

def events (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : List (Event carrier keep) :=
  eventsFor carrier keep (List.finRange fields)

def forgottenCoordinates (keep : Fin fields → Bool) : List (Fin fields) :=
  (List.finRange fields).filter (fun field => !(keep field))

def createdCoordinates {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} : List (Event carrier keep) → List (Fin fields)
  | [] => []
  | .createR5 creation :: remaining =>
      creation.coordinate :: createdCoordinates remaining
  | .dischargeR8 _ _ :: remaining => createdCoordinates remaining

def dischargedCoordinates {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} : List (Event carrier keep) → List (Fin fields)
  | [] => []
  | .createR5 _ :: remaining => dischargedCoordinates remaining
  | .dischargeR8 creation _ :: remaining =>
      creation.coordinate :: dischargedCoordinates remaining

/-- Replay the pending stack after whole-trace identity validation. -/
private def replayPending {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} (pending : List (Fin fields)) :
    List (Event carrier keep) → Option (List (Fin fields))
  | [] => some pending
  | .createR5 creation :: remaining =>
      if creation.coordinate ∈ pending then none
      else replayPending (creation.coordinate :: pending) remaining
  | .dischargeR8 creation _ :: remaining =>
      match pending with
      | [] => none
      | first :: rest =>
          if first = creation.coordinate then replayPending rest remaining else none

/-- Validate identities across the entire trace, including already pending
coordinates. A discharged identity cannot be created again later. Every R8
event must also carry its actual full-value witness. -/
def replay {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} (pending : List (Fin fields))
    (transcript : List (Event carrier keep)) : Option (List (Fin fields)) :=
  if (pending ++ createdCoordinates transcript).Nodup then
    replayPending pending transcript
  else none


private theorem createdCoordinates_eventsFor
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (coordinates : List (Fin fields)) :
    createdCoordinates (eventsFor carrier keep coordinates) =
      coordinates.filter (fun field => !(keep field)) := by
  induction coordinates with
  | nil => rfl
  | cons field remaining ih =>
      cases kept : keep field <;>
        simp [eventsFor, kept, createdCoordinates, createR5, ih]

private theorem dischargedCoordinates_eventsFor
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (coordinates : List (Fin fields)) :
    dischargedCoordinates (eventsFor carrier keep coordinates) =
      coordinates.filter (fun field => !(keep field)) := by
  induction coordinates with
  | nil => rfl
  | cons field remaining ih =>
      cases kept : keep field <;>
        simp [eventsFor, kept, dischargedCoordinates, createR5, ih]

theorem created_exact (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    createdCoordinates (events carrier keep) = forgottenCoordinates keep :=
  createdCoordinates_eventsFor carrier keep (List.finRange fields)

theorem discharged_exact (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    dischargedCoordinates (events carrier keep) = forgottenCoordinates keep :=
  dischargedCoordinates_eventsFor carrier keep (List.finRange fields)

theorem mem_forgottenCoordinates_iff (keep : Fin fields → Bool) (field : Fin fields) :
    field ∈ forgottenCoordinates keep ↔ keep field = false := by
  simp [forgottenCoordinates]

theorem creation_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (field : Fin fields) :
    field ∈ createdCoordinates (events carrier keep) ↔ keep field = false := by
  rw [created_exact]
  exact mem_forgottenCoordinates_iff keep field

theorem discharge_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (field : Fin fields) :
    field ∈ dischargedCoordinates (events carrier keep) ↔ keep field = false := by
  rw [discharged_exact]
  exact mem_forgottenCoordinates_iff keep field

private theorem replayPending_eventsFor (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (coordinates : List (Fin fields)) :
    replayPending [] (eventsFor carrier keep coordinates) = some [] := by
  induction coordinates with
  | nil => rfl
  | cons field remaining ih =>
      cases kept : keep field <;>
        simp [eventsFor, kept, replayPending, createR5, ih]

private theorem replayPending_events (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    replayPending [] (events carrier keep) = some [] :=
  replayPending_eventsFor carrier keep (List.finRange fields)

theorem dischargeR8_full_value (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (creation : R5Creation carrier keep)
    (valuation : Valuation inputs) :
    (dischargeR8 carrier keep creation).restoredSource.eval valuation
        ((restored carrier keep).implementation.candidate.program.eval valuation) =
      carrier.fieldValue valuation creation.coordinate :=
  restored_field carrier keep valuation creation.coordinate

/-- A gain witness refers only to the actual constructed and fully charged word. -/
structure RestoredGain (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : Type where
  smaller : (restored carrier keep).implementation.gateCount <
    carrier.implementation.gateCount

def gain? (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : Option (RestoredGain carrier keep) :=
  if smaller : (restored carrier keep).implementation.gateCount <
      carrier.implementation.gateCount then some ⟨smaller⟩ else none

theorem gain?_isSome_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (gain? carrier keep).isSome = true ↔
      (projected carrier keep).implementation.gateCount +
        (materializer carrier keep).implementation.gateCount <
          carrier.implementation.gateCount := by
  unfold gain?
  split
  next smaller =>
    constructor
    · intro _accepted
      rw [← restored_exact_gate_charge]
      exact smaller
    · intro _charged
      rfl
  next notSmaller =>
    constructor
    · intro impossible
      cases impossible
    · intro charged
      exact (notSmaller (by
        rw [restored_exact_gate_charge]
        exact charged)).elim

theorem gain_checked (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (gain : RestoredGain carrier keep) :
    (∀ valuation output,
      (restored carrier keep).implementation.candidate.semantics valuation output =
        carrier.implementation.candidate.semantics valuation output) ∧
    (∀ valuation field,
      (restored carrier keep).fieldValue valuation field =
        carrier.fieldValue valuation field) ∧
    (restored carrier keep).implementation.gateCount <
      carrier.implementation.gateCount ∧
    (restored carrier keep).implementation.gateCount =
      (projected carrier keep).implementation.gateCount +
        (materializer carrier keep).implementation.gateCount :=
  ⟨restored_output carrier keep, restored_field carrier keep, gain.smaller,
    restored_exact_gate_charge carrier keep⟩


/-- Constructive uniqueness of the actual finite coordinate enumeration. -/
private theorem wireFieldRange_nodup (width : Nat) :
    (List.finRange width).Nodup := by
  induction width with
  | zero =>
      rw [List.finRange_zero]
      exact List.nodup_nil
  | succ width ih =>
      rw [List.finRange_succ, List.nodup_cons]
      constructor
      · intro member
        obtain ⟨index, _present, same⟩ := List.mem_map.mp member
        have impossible := congrArg Fin.val same
        change index.val + 1 = 0 at impossible
        omega
      · exact List.Pairwise.map Fin.succ
          (fun left right different same =>
            different (Fin.ext (Nat.succ.inj (congrArg Fin.val same)))) ih

theorem created_nodup (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (createdCoordinates (events carrier keep)).Nodup := by
  rw [created_exact]
  exact List.Pairwise.filter (fun field => !(keep field)) (wireFieldRange_nodup fields)

theorem discharged_nodup (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (dischargedCoordinates (events carrier keep)).Nodup := by
  rw [discharged_exact]
  exact List.Pairwise.filter (fun field => !(keep field)) (wireFieldRange_nodup fields)


/-- The computed lifecycle closes every generated lost-wire obligation after
validating identity uniqueness across the entire event sequence. -/
theorem replay_closed (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    replay [] (events carrier keep) = some [] := by
  unfold replay
  have unique : ([] ++ createdCoordinates (events carrier keep)).Nodup :=
    created_nodup carrier keep
  rw [if_pos unique]
  exact replayPending_events carrier keep

theorem replay_rejects_duplicate_ids {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} (pending : List (Fin fields))
    (transcript : List (Event carrier keep))
    (duplicate : ¬(pending ++ createdCoordinates transcript).Nodup) :
    replay pending transcript = none := by
  unfold replay
  rw [if_neg duplicate]

end PNP.DirectWire.WireObligationRestoration

/-
Copyright (c) 2026 PNP Labs.

Computed structural reordering of the current open-obligation state. The exact
pending snapshot function is retained: reordering cannot create, discharge or
replace an obligation. No physical gate is allocated or removed.

This is a state operation and raw decoder, not yet its complete mixed-program
integration, full manuscript profiles, global ZeroSlack or polynomial PCCMin.
-/

import PNP.NANDWireStructuralReindexing
import PNP.NANDWireHistoryCausalBounds

namespace PNP.DirectWire

open StructuralReindexing

namespace WireObligationHistory.State

variable {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}

def reindex (state : State source)
    (relabeling : GateRenaming state.current.implementation.gateCount) : State source where
  current := state.current.reindex relabeling
  pending := state.pending
  charged := state.charged
  removed := state.removed
  output := fun valuation output =>
    (state.current.reindex_output relabeling valuation output).trans
      (state.output valuation output)
  available := fun valuation field closed =>
    (state.current.reindex_field relabeling valuation field).trans
      (state.available valuation field closed)
  balance := by
    rw [WireCarrier.reindex_gateCount]
    exact state.balance

theorem reindex_pending (state : State source)
    (relabeling : GateRenaming state.current.implementation.gateCount) :
    (state.reindex relabeling).pending = state.pending := rfl

theorem reindex_charged (state : State source)
    (relabeling : GateRenaming state.current.implementation.gateCount) :
    (state.reindex relabeling).charged = state.charged := rfl

theorem reindex_removed (state : State source)
    (relabeling : GateRenaming state.current.implementation.gateCount) :
    (state.reindex relabeling).removed = state.removed := rfl

theorem reindex_gateCount (state : State source)
    (relabeling : GateRenaming state.current.implementation.gateCount) :
    (state.reindex relabeling).current.implementation.gateCount =
      state.current.implementation.gateCount :=
  state.current.reindex_gateCount relabeling

theorem reindex_causalInvariant (state : State source)
    (relabeling : GateRenaming state.current.implementation.gateCount)
    (labels : Fin inputs → Nat) (bounded : state.CausalInvariant labels) :
    (state.reindex relabeling).CausalInvariant labels :=
  ⟨state.current.reindex_causalBounds relabeling labels _ _ bounded.1, bounded.2⟩

end WireObligationHistory.State

namespace WireStructuralState

open WireObligationHistory (State)

variable {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}

/-- The decoder constructs this binding; callers provide only raw swap pairs. -/
structure Receipt (before : State source) (code : List (Nat × Nat)) where
  relabeling : GateRenaming before.current.implementation.gateCount
  decoded : GateRenaming.decode before.current.implementation.gateCount code = some relabeling

def Receipt.next {before : State source} {code : List (Nat × Nat)}
    (receipt : Receipt before code) : State source :=
  before.reindex receipt.relabeling

def execute (before : State source) (code : List (Nat × Nat)) :
    Option (Receipt before code) :=
  match decoded : GateRenaming.decode before.current.implementation.gateCount code with
  | none => none
  | some relabeling => some ⟨relabeling, decoded⟩

theorem execute_isSome (before : State source) (code : List (Nat × Nat)) :
    (execute before code).isSome =
      GateRenaming.validCode before.current.implementation.gateCount code := by
  have same : (execute before code).isSome =
      (GateRenaming.decode before.current.implementation.gateCount code).isSome := by
    unfold execute
    split
    · rename_i decoded
      exact (congrArg Option.isSome decoded).symm
    · rename_i relabeling decoded
      exact (congrArg Option.isSome decoded).symm
  exact same.trans (GateRenaming.decode_isSome _ code)

theorem execute_failure_iff (before : State source) (code : List (Nat × Nat)) :
    execute before code = none ↔
      GateRenaming.validCode before.current.implementation.gateCount code = false := by
  constructor
  · intro rejected
    have checked := execute_isSome before code
    rw [rejected] at checked
    exact checked.symm
  · intro invalid
    cases found : execute before code with
    | none => rfl
    | some receipt =>
        have checked := execute_isSome before code
        rw [found, invalid] at checked
        cases checked

end WireStructuralState
end PNP.DirectWire

/-
Copyright (c) 2026 PNP Labs.

Checked finite recoding of an actual open-obligation state. Inverse equations
come from literal NAND programs, and an independent finite guard checks the
actual result's syntactic dependencies. The complete pending snapshot function
is unchanged. Gate additions and deletions are computed, not supplied.

This state operation does not yet provide its physical ownership map, complete
mixed-program integration, full manuscript profiles or polynomial execution.
-/

import PNP.NANDCausalGuard
import PNP.NANDWireCarrierRecoding
import PNP.NANDWireHistoryCausalBounds

namespace PNP.DirectWire
namespace WireObligationHistory.State

variable {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}

def recode (state : State source) (encoder decoder : Implementation fields fields)
    (checked : WireCarrierRecoding.Checked encoder decoder) : State source where
  current := WireCarrierRecoding.result state.current encoder decoder
  pending := state.pending
  charged := state.charged + encoder.gateCount + decoder.gateCount
  removed := state.removed + WireCarrierRecoding.removed state.current encoder decoder
  output := fun valuation output =>
    (WireCarrierRecoding.result_output state.current encoder decoder valuation output).trans
      (state.output valuation output)
  available := fun valuation field closed =>
    (WireCarrierRecoding.result_field state.current encoder decoder checked valuation field).trans
      (state.available valuation field closed)
  balance := by
    have currentBalance := WireCarrierRecoding.result_gate_balance state.current encoder decoder
    have previousBalance := state.balance
    change (WireCarrierRecoding.result state.current encoder decoder).implementation.gateCount +
        (state.removed + WireCarrierRecoding.removed state.current encoder decoder) =
      source.implementation.gateCount + (state.charged + encoder.gateCount + decoder.gateCount)
    omega

/-- Preserve identities, captured carriers and full-value proofs, not only open bits. -/
theorem recode_pending (state : State source) (encoder decoder : Implementation fields fields)
    (checked : WireCarrierRecoding.Checked encoder decoder) :
    (state.recode encoder decoder checked).pending = state.pending := rfl

theorem recode_charged (state : State source) (encoder decoder : Implementation fields fields)
    (checked : WireCarrierRecoding.Checked encoder decoder) :
    (state.recode encoder decoder checked).charged =
      state.charged + encoder.gateCount + decoder.gateCount := rfl

theorem recode_removed (state : State source) (encoder decoder : Implementation fields fields)
    (checked : WireCarrierRecoding.Checked encoder decoder) :
    (state.recode encoder decoder checked).removed =
      state.removed + WireCarrierRecoding.removed state.current encoder decoder := rfl

theorem recode_causalInvariant (state : State source)
    (encoder decoder : Implementation fields fields)
    (checked : WireCarrierRecoding.Checked encoder decoder)
    (safe : state.current.dependencyGuard
      (WireCarrierRecoding.result state.current encoder decoder) = true)
    (labels : Fin inputs → Nat) (bounded : state.CausalInvariant labels) :
    (state.recode encoder decoder checked).CausalInvariant labels := by
  have actual := (WireCarrier.dependencyGuard_iff _ _).1 safe labels
  refine ⟨?_, bounded.2⟩
  exact ⟨fun output => Nat.le_trans (actual.1 output) (bounded.1.1 output),
    fun field => Nat.le_trans (actual.2 field) (bounded.1.2 field)⟩

end WireObligationHistory.State

namespace WireRecodingState

open WireObligationHistory (State)

variable {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}

/-- The executor derives both facts; the input contains only actual programs. -/
structure Receipt (before : State source) (encoder decoder : Implementation fields fields) : Type where
  inverse : WireCarrierRecoding.Checked encoder decoder
  causal : before.current.dependencyGuard
    (WireCarrierRecoding.result before.current encoder decoder) = true

def Receipt.next {before : State source} {encoder decoder : Implementation fields fields}
    (receipt : Receipt before encoder decoder) : State source :=
  before.recode encoder decoder receipt.inverse

def execute (before : State source) (encoder decoder : Implementation fields fields) :
    Option (Receipt before encoder decoder) :=
  match WireCarrierRecoding.compile encoder decoder with
  | none => none
  | some inverse =>
      if safe : before.current.dependencyGuard
          (WireCarrierRecoding.result before.current encoder decoder) = true then
        some ⟨inverse, safe⟩
      else none

theorem execute_success_iff (before : State source)
    (encoder decoder : Implementation fields fields) :
    (∃ receipt, execute before encoder decoder = some receipt) ↔
      WireCarrierRecoding.check encoder decoder = true ∧
        before.current.dependencyGuard
          (WireCarrierRecoding.result before.current encoder decoder) = true := by
  constructor
  · rintro ⟨receipt, _found⟩
    exact ⟨(WireCarrierRecoding.check_iff encoder decoder).2
      ⟨receipt.inverse.decode_encode, receipt.inverse.encode_decode⟩, receipt.causal⟩
  · rintro ⟨inverse, safe⟩
    obtain ⟨checked, compiled⟩ :=
      (WireCarrierRecoding.compile_success_iff encoder decoder).2 inverse
    refine ⟨⟨checked, safe⟩, ?_⟩
    unfold execute
    rw [compiled]
    simp only [dif_pos safe]

theorem execute_failure_iff (before : State source)
    (encoder decoder : Implementation fields fields) :
    execute before encoder decoder = none ↔
      ¬(WireCarrierRecoding.check encoder decoder = true ∧
        before.current.dependencyGuard
          (WireCarrierRecoding.result before.current encoder decoder) = true) := by
  constructor
  · intro rejected valid
    obtain ⟨receipt, accepted⟩ := (execute_success_iff before encoder decoder).2 valid
    rw [rejected] at accepted
    cases accepted
  · intro invalid
    cases found : execute before encoder decoder with
    | none => rfl
    | some receipt =>
        exact False.elim (invalid ((execute_success_iff before encoder decoder).1
          ⟨receipt, found⟩))

theorem Receipt.pending {before : State source} {encoder decoder : Implementation fields fields}
    (receipt : Receipt before encoder decoder) :
    receipt.next.pending = before.pending := rfl

theorem Receipt.causalInvariant
    {before : State source} {encoder decoder : Implementation fields fields}
    (receipt : Receipt before encoder decoder) (labels : Fin inputs → Nat)
    (bounded : before.CausalInvariant labels) : receipt.next.CausalInvariant labels :=
  before.recode_causalInvariant encoder decoder receipt.inverse receipt.causal labels bounded

theorem Receipt.gate_balance
    {before : State source} {encoder decoder : Implementation fields fields}
    (receipt : Receipt before encoder decoder) :
    receipt.next.current.implementation.gateCount + receipt.next.removed =
      source.implementation.gateCount + receipt.next.charged :=
  receipt.next.balance

end WireRecodingState
end PNP.DirectWire

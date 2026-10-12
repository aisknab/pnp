/-
Copyright (c) 2026 PNP Labs.

A fixed row-list assembly frame keeps the growing output outside the
coefficient scratch prefix. Per-row work is charged against preserved data
and the runtime ordinal, not against previous output growth.
-/
import PNP.Concrete.NormalizerCoefficientEligibility

namespace PNP.Concrete.NormalizerBlocks.SystemRows
open BitRegister Occurrence

structure State where
  core : Coefficient.State
  rows : BitString
  remaining : BitString
  counter : BitString
  count : BitString
  buffer : BitString
def State.frame (r : State) : Store 5 :=
  .cons r.rows (.cons r.remaining (.cons r.counter (.cons r.count (.cons r.buffer .nil))))
def State.store (r : State) : Store 29 := Frame.join r.core.store r.frame
def State.registers (r : State) : Registers := r.core.registers
def State.withCore (r : State) (core : Coefficient.State) : State := {r with core := core}
def State.shared (r : State) : Coefficient.Data := {r.core.data with row := []}
def liftCore (body : Block 24) : Block 29 := Frame.block 5 body
theorem liftCore_exec (body : Block 24) (r : State) (fuel : Nat) (after : Coefficient.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (liftCore body) r.store fuel (r.withCore after).store := Frame.execution checked r.frame

def loadRow : Block 29 := .action (.copy 22 26)
def loaded (r : State) : State := r.withCore {r.core with row := r.counter}
theorem loadRow_exec (r : State) : Exec loadRow r.store 1 (loaded r).store := .action _ _
theorem loaded_shared (r : State) : (loaded r).shared = r.shared := rfl
theorem loaded_data_bounded (r : State) (n : Nat)
    (fixed : r.shared.Bounded n) (index : r.counter.length ≤ n) :
    (loaded r).core.data.Bounded n := by
  obtain ⟨literals,owners,slots,modes,assignment,failed,_⟩ := fixed
  exact ⟨literals,owners,slots,modes,assignment,failed,index⟩

def run (routine : Coefficient.Routine) : Block 29 :=
  .seq loadRow (liftCore (Coefficient.fresh routine).block)
def result (routine : Coefficient.Routine) (r : State) : State :=
  (loaded r).withCore ((Coefficient.fresh routine).result (loaded r).core)
def fuel (routine : Coefficient.Routine) (r : State) : Nat :=
  1 + (Coefficient.fresh routine).fuel (loaded r).core
theorem run_exec (routine : Coefficient.Routine) (r : State) :
    Exec (run routine) r.store (fuel routine r) (result routine r).store :=
  Exec.seq (loadRow_exec r) (liftCore_exec _ (loaded r) _ _ ((Coefficient.fresh routine).exec _))
theorem result_data (routine : Coefficient.Routine)
    (kept : ∀ r, (routine.result r).data = r.data) (r : State) :
    (result routine r).core.data = (loaded r).core.data :=
  Coefficient.fresh_data routine kept (loaded r).core
theorem result_shared (routine : Coefficient.Routine)
    (kept : ∀ r, (routine.result r).data = r.data) (r : State) :
    (result routine r).shared = r.shared :=
  congrArg (fun d : Coefficient.Data => {d with row := []}) (result_data routine kept r)
theorem result_row (routine : Coefficient.Routine)
    (kept : ∀ r, (routine.result r).data = r.data) (r : State) :
    (result routine r).core.row = r.counter :=
  congrArg Coefficient.Data.row (result_data routine kept r)
theorem result_frame (routine : Coefficient.Routine) (r : State) :
    (result routine r).rows = r.rows ∧ (result routine r).remaining = r.remaining ∧
    (result routine r).counter = r.counter ∧ (result routine r).count = r.count ∧
    (result routine r).buffer = r.buffer := ⟨rfl,rfl,rfl,rfl,rfl⟩
theorem fuel_bound (routine : Coefficient.Routine) (r : State) (n : Nat)
    (fixed : r.shared.Bounded n) (index : r.counter.length ≤ n) :
    fuel routine r ≤ 19 + routine.bound.eval n := by
  have cost := Coefficient.fresh_fuel_bound routine (loaded r).core n (loaded_data_bounded r n fixed index)
  unfold fuel
  omega
theorem result_core_bounded (routine : Coefficient.Routine) (r : State) (n : Nat)
    (fixed : r.shared.Bounded n) (index : r.counter.length ≤ n) :
    (result routine r).core.store.Bounded (n + routine.bound.eval n) :=
  Coefficient.fresh_result_bounded routine (loaded r).core n (loaded_data_bounded r n fixed index)
theorem result_output_bound (routine : Coefficient.Routine) (r : State) (n : Nat)
    (fixed : r.shared.Bounded n) (index : r.counter.length ≤ n) :
    (result routine r).registers.output.length ≤ n + routine.bound.eval n :=
  Store.get_length_le (result routine r).core.store (8 : Fin 24)
    (result_core_bounded routine r n fixed index)

theorem shared_bounded (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    r.shared.Bounded n :=
  ⟨Store.get_length_le r.store (13 : Fin 29) bounded,
   Store.get_length_le r.store (16 : Fin 29) bounded,
   Store.get_length_le r.store (17 : Fin 29) bounded,
   Store.get_length_le r.store (18 : Fin 29) bounded,
   Store.get_length_le r.store (19 : Fin 29) bounded,
   Store.get_length_le r.store (20 : Fin 29) bounded,
   Nat.zero_le n⟩

theorem encoded_transport (ctx : Coefficient.Context) (before after : State)
    (encoded : ctx.Encoded before.core) (same : after.shared = before.shared) :
    ctx.Encoded after.core :=
  ⟨(congrArg Coefficient.Data.literals same).trans encoded.formula,
   (congrArg Coefficient.Data.owners same).trans encoded.owners,
   (congrArg Coefficient.Data.slots same).trans encoded.slots,
   (congrArg Coefficient.Data.modes same).trans encoded.modes,
   (congrArg Coefficient.Data.assignment same).trans encoded.assignment,
   (congrArg Coefficient.Data.failed same).trans encoded.failed⟩
theorem loaded_encoded (ctx : Coefficient.Context) (r : State) (encoded : ctx.Encoded r.core) :
    ctx.Encoded (loaded r).core := encoded_transport ctx r (loaded r) encoded rfl

end PNP.Concrete.NormalizerBlocks.SystemRows

/-
Copyright (c) 2026 PNP Labs.

Reset all coefficient scratch before each source-row iteration. Its next
runtime bound depends on fixed cached data and the current row, not on
scratch or output accumulated by earlier iterations.
-/
import PNP.Concrete.NormalizerCoefficientPacket

namespace PNP.Concrete.NormalizerBlocks.Coefficient
open BitRegister Occurrence

def Data.Bounded (d : Data) (n : Nat) : Prop :=
  d.literals.length ≤ n ∧ d.owners.length ≤ n ∧ d.slots.length ≤ n ∧
  d.modes.length ≤ n ∧ d.assignment.length ≤ n ∧ d.failed.length ≤ n ∧ d.row.length ≤ n
def cleared (r : State) : State :=
  {core := ⟨⟨⟨⟨[],[],[],[],[],[],[],[],[]⟩,[],[],[],[]⟩,r.core.core.formula,[],[]⟩,
    r.core.matching,r.core.counter,r.core.target⟩,
   assignment := r.assignment, failed := r.failed, variableIndex := [], row := r.row, auxiliary := []}
def wipe {count : Nat} : List (Fin count) → Block count
  | [] => .skip
  | index::rest => .seq (.action (.clear index)) (wipe rest)
def wiped {count : Nat} : List (Fin count) → Store count → Store count
  | [],r => r
  | index::rest,r => wiped rest (r.set index [])
theorem wipe_exec {count : Nat} (indices : List (Fin count)) (r : Store count) :
    Exec (wipe indices) r (indices.length+1) (wiped indices r) := by
  induction indices generalizing r with
  | nil => exact .skip _
  | cons index rest ih =>
      have checked := Exec.seq (Exec.action (.clear index) r) (ih (r.set index []))
      have cost : 1 + (rest.length+1) = (index::rest).length+1 := by simp only [List.length_cons]; omega
      rw [cost] at checked
      exact checked
def scratchIndices : List (Fin 24) := [0,1,2,3,4,5,6,7,8,9,10,11,12,14,15,21,23]
theorem wiped_store (r : State) : wiped scratchIndices r.store = (cleared r).store := by
  dsimp only [scratchIndices,wiped,cleared,State.store,State.frame,CacheMode.State.store,
    CacheMode.State.frame,DenseClauses.State.store,DenseClauses.State.frame,
    CompactClause.State.store,CompactClause.State.frame,Registers.store,Frame.join,
    Store.set,Store.indexCases]
def resetScratch : Routine where
  block := wipe scratchIndices
  result := cleared
  fuel _ := 18
  bound := .constant 18
  exec r := by
    have checked := wipe_exec scratchIndices r.store
    rw [wiped_store] at checked
    exact checked
  cost _ _ _ := Nat.le_refl 18
theorem cleared_data (r : State) : (cleared r).data = r.data := rfl
theorem cleared_buffers (r : State) : (cleared r).count = [] ∧ (cleared r).buffer = [] := ⟨rfl,rfl⟩
theorem data_bounded (r : State) (n : Nat) (bounded : r.store.Bounded n) : r.data.Bounded n :=
  ⟨Store.get_length_le r.store (13 : Fin 24) bounded,
   Store.get_length_le r.store (16 : Fin 24) bounded,
   Store.get_length_le r.store (17 : Fin 24) bounded,
   Store.get_length_le r.store (18 : Fin 24) bounded,
   Store.get_length_le r.store (19 : Fin 24) bounded,
   Store.get_length_le r.store (20 : Fin 24) bounded,
   Store.get_length_le r.store (22 : Fin 24) bounded⟩
theorem cleared_bounded (r : State) (n : Nat) (bounded : r.data.Bounded n) :
    (cleared r).store.Bounded n := by
  obtain ⟨literals,owners,slots,modes,assignment,failed,row⟩ := bounded
  exact ⟨Nat.zero_le n,⟨Nat.zero_le n,⟨Nat.zero_le n,⟨Nat.zero_le n,⟨Nat.zero_le n,⟨Nat.zero_le n,⟨Nat.zero_le n,⟨Nat.zero_le n,⟨Nat.zero_le n,⟨Nat.zero_le n,⟨Nat.zero_le n,⟨Nat.zero_le n,⟨Nat.zero_le n,⟨literals,⟨Nat.zero_le n,⟨Nat.zero_le n,⟨owners,⟨slots,⟨modes,⟨assignment,⟨failed,⟨Nat.zero_le n,⟨row,⟨Nat.zero_le n,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def fresh (routine : Routine) : Routine := Routine.seq resetScratch routine
theorem fresh_result (routine : Routine) (r : State) :
    (fresh routine).result r = routine.result (cleared r) := rfl
theorem fresh_exec (routine : Routine) (r : State) :
    Exec (fresh routine).block r.store (18 + routine.fuel (cleared r)) (routine.result (cleared r)).store :=
  (fresh routine).exec r
theorem fresh_data (routine : Routine) (kept : ∀ r, (routine.result r).data = r.data) (r : State) :
    ((fresh routine).result r).data = r.data :=
  Routine.seq_data _ _ cleared_data kept r
theorem fresh_fuel (routine : Routine) (r : State) :
    (fresh routine).fuel r = 18 + routine.fuel (cleared r) := rfl
theorem fresh_fuel_bound (routine : Routine) (r : State) (n : Nat)
    (bounded : r.data.Bounded n) :
    (fresh routine).fuel r ≤ 18 + routine.bound.eval n :=
  Nat.add_le_add_left (routine.cost (cleared r) n (cleared_bounded r n bounded)) 18
theorem fresh_result_bounded (routine : Routine) (r : State) (n : Nat)
    (bounded : r.data.Bounded n) :
    ((fresh routine).result r).store.Bounded (n + routine.bound.eval n) :=
  routine.result_bounded (cleared r) n (cleared_bounded r n bounded)

end PNP.Concrete.NormalizerBlocks.Coefficient

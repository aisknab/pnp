/-
Copyright (c) 2026 PNP Labs.

The complete system serializer has two saved packets outside the row-loop
scratch and seven untouched recovery registers. All composition is finite
code; polynomial bounds are composed a fixed number of times.
-/
import PNP.Concrete.NormalizerSystemRowsWholeSemantics

namespace PNP.Concrete.NormalizerBlocks.SystemAssembly
open BitRegister Occurrence

structure State where
  core : SystemRows.State
  recovery : Store 7
  b : BitString
  a : BitString
def State.frame (r : State) : Store 9 := Frame.join r.recovery (.cons r.b (.cons r.a .nil))
def State.store (r : State) : Store 38 := Frame.join r.core.store r.frame
def State.withRows (r : State) (core : SystemRows.State) : State := {r with core := core}
def State.registers (r : State) : Registers := r.core.registers
def State.withRegisters (r : State) (registers : Registers) : State :=
  r.withRows (r.core.withCore (r.core.core.withRegisters registers))
def liftRows (block : Block 29) : Block 38 := Frame.block 9 block
theorem liftRows_exec (body : Block 29) (r : State) (fuel : Nat) (after : SystemRows.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (liftRows body) r.store fuel (r.withRows after).store := Frame.execution checked r.frame
theorem frame_core_bounded {extra count n : Nat} (core : Store count) (frame : Store extra)
    (bounded : (Frame.join core frame).Bounded n) : core.Bounded n := by
  induction core with
  | nil => exact True.intro
  | cons first rest ih => exact ⟨bounded.1,ih bounded.2⟩
theorem rows_bounded (r : State) (n : Nat) (bounded : r.store.Bounded n) : r.core.store.Bounded n :=
  frame_core_bounded r.core.store r.frame bounded

theorem frame_set {extra count : Nat} (core : Store count) (frame : Store extra)
    (index : Fin extra) (value : BitString) :
    (Frame.join core frame).set (Frame.frameIndex count index) value =
      Frame.join core (frame.set index value) := by
  induction core with
  | nil =>
      have zero : Frame.frameIndex 0 index = index := by apply Fin.ext; simp only [Frame.frameIndex,Nat.zero_add]
      rw [zero]
      rfl
  | @cons count first rest ih =>
      have next : Frame.frameIndex (count+1) index = (Frame.frameIndex count index).succ := by
        apply Fin.ext
        change count+1+index.val = count+index.val+1
        omega
      rw [next]
      exact congrArg (Store.cons first) ih
theorem saved_b_store (r : State) :
    r.store.set 36 r.registers.output = ({r with b := r.registers.output}).store := by
  have outer := frame_set r.core.store r.frame (7 : Fin 9) r.registers.output
  have inner := frame_set r.recovery (.cons r.b (.cons r.a .nil)) (0 : Fin 2) r.registers.output
  change (Frame.join r.recovery (.cons r.b (.cons r.a .nil))).set (7 : Fin 9) r.registers.output = _ at inner
  dsimp only [State.frame] at outer
  rw [inner] at outer
  exact outer
theorem saved_a_store (r : State) :
    r.store.set 37 r.registers.output = ({r with a := r.registers.output}).store := by
  have outer := frame_set r.core.store r.frame (8 : Fin 9) r.registers.output
  have inner := frame_set r.recovery (.cons r.b (.cons r.a .nil)) (1 : Fin 2) r.registers.output
  change (Frame.join r.recovery (.cons r.b (.cons r.a .nil))).set (8 : Fin 9) r.registers.output = _ at inner
  dsimp only [State.frame] at outer
  rw [inner] at outer
  exact outer

structure Routine where
  block : Block 38
  result : State → State
  fuel : State → Nat
  bound : NatPolynomial
  exec : ∀ r, Exec block r.store (fuel r) (result r).store
  cost : ∀ r n, r.store.Bounded n → fuel r ≤ bound.eval n
namespace Routine
theorem result_bounded (routine : Routine) (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    (routine.result r).store.Bounded (n+routine.bound.eval n) :=
  Store.bounded_mono ((routine.exec r).bounded n bounded)
    (Nat.add_le_add_left (routine.cost r n bounded) n)
def seq (first second : Routine) : Routine where
  block := .seq first.block second.block
  result r := second.result (first.result r)
  fuel r := first.fuel r + second.fuel (first.result r)
  bound := .add first.bound (second.bound.substitute (.add .variable first.bound))
  exec r := Exec.seq (first.exec r) (second.exec (first.result r))
  cost r n bounded := by
    have a := first.cost r n bounded
    have b := second.cost (first.result r) (n+first.bound.eval n) (result_bounded first r n bounded)
    change first.fuel r + second.fuel (first.result r) ≤
      first.bound.eval n+(second.bound.substitute (.add .variable first.bound)).eval n
    rw [NatPolynomial.eval_substitute]
    exact Nat.add_le_add a b
end Routine

def bRoutine : Routine where
  block := liftRows (SystemRows.run (Coefficient.packet Coefficient.bTerms))
  result r := r.withRows (SystemRows.result (Coefficient.packet Coefficient.bTerms) r.core)
  fuel r := SystemRows.fuel (Coefficient.packet Coefficient.bTerms) r.core
  bound := .add (.constant 19) (Coefficient.packet Coefficient.bTerms).bound
  exec r := liftRows_exec _ r _ _ (SystemRows.run_exec _ _)
  cost r n bounded := by
    have raw := rows_bounded r n bounded
    exact SystemRows.fuel_bound _ r.core n (SystemRows.shared_bounded r.core n raw)
      (Store.get_length_le r.core.store (26 : Fin 29) raw)
def listRoutine (iteration : SystemRows.Iteration) : Routine where
  block := liftRows (SystemRows.listBlock iteration)
  result r := r.withRows (SystemRows.listResult iteration r.core)
  fuel r := SystemRows.listFuel iteration r.core
  bound := SystemRows.listBound iteration
  exec r := liftRows_exec _ r _ _ (SystemRows.list_exec iteration r.core)
  cost r n bounded := SystemRows.list_fuel_bound iteration r.core n (rows_bounded r n bounded)
def saveB : Routine where
  block := .action (.copy 36 8)
  result r := {r with b := r.registers.output}
  fuel _ := 1
  bound := .constant 1
  exec r := by
    have checked := Exec.action (.copy 36 8) r.store
    change Exec (.action (.copy 36 8)) r.store 1 (r.store.set 36 r.registers.output) at checked
    rw [saved_b_store] at checked
    exact checked
  cost _ _ _ := Nat.le_refl 1
def saveA : Routine where
  block := .action (.copy 37 8)
  result r := {r with a := r.registers.output}
  fuel _ := 1
  bound := .constant 1
  exec r := by
    have checked := Exec.action (.copy 37 8) r.store
    change Exec (.action (.copy 37 8)) r.store 1 (r.store.set 37 r.registers.output) at checked
    rw [saved_a_store] at checked
    exact checked
  cost _ _ _ := Nat.le_refl 1

theorem b_shared (r : State) : (bRoutine.result r).core.shared = r.core.shared :=
  SystemRows.result_shared _ (Coefficient.packet_data _ Coefficient.bTerms_data) r.core
theorem b_rows (r : State) : (bRoutine.result r).core.rows = r.core.rows := rfl
theorem list_shared (iteration : SystemRows.Iteration) (r : State) :
    ((listRoutine iteration).result r).core.shared = r.core.shared :=
  SystemRows.list_shared iteration r.core
theorem list_rows (iteration : SystemRows.Iteration) (r : State) :
    ((listRoutine iteration).result r).core.rows = r.core.rows :=
  SystemRows.list_rows iteration r.core
theorem phase_recovery (iteration : SystemRows.Iteration) (r : State) :
    (bRoutine.result r).recovery = r.recovery ∧
    ((listRoutine iteration).result r).recovery = r.recovery ∧
    (saveB.result r).recovery = r.recovery ∧ (saveA.result r).recovery = r.recovery :=
  ⟨rfl,rfl,rfl,rfl⟩

end PNP.Concrete.NormalizerBlocks.SystemAssembly

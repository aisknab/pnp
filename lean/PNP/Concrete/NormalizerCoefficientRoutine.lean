/-
Copyright (c) 2026 PNP Labs.

Composition of concrete coefficient routines, including an encoded-size
polynomial for each finite block. Routine fields are proof infrastructure;
execution uses only the composed finite instructions, never a callback.
-/
import PNP.Concrete.NormalizerCoefficientRow
import PNP.Concrete.NormalizerOrdinalTest

namespace PNP.Concrete.NormalizerBlocks.Coefficient
open BitRegister Occurrence

structure Routine where
  block : Block 24
  result : State → State
  fuel : State → Nat
  bound : NatPolynomial
  exec : ∀ r, Exec block r.store (fuel r) (result r).store
  cost : ∀ r n, r.store.Bounded n → fuel r ≤ bound.eval n

namespace Routine
theorem result_bounded (routine : Routine) (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    (routine.result r).store.Bounded (n + routine.bound.eval n) :=
  Store.bounded_mono ((routine.exec r).bounded n bounded)
    (Nat.add_le_add_left (routine.cost r n bounded) n)
def seq (first second : Routine) : Routine where
  block := .seq first.block second.block
  result r := second.result (first.result r)
  fuel r := first.fuel r + second.fuel (first.result r)
  bound := .add first.bound (second.bound.substitute (.add (.linear 1 0) first.bound))
  exec r := Exec.seq (first.exec r) (second.exec (first.result r))
  cost r n bounded := by
    have a := first.cost r n bounded
    have b := second.cost (first.result r) (n + first.bound.eval n)
      (result_bounded first r n bounded)
    change first.fuel r + second.fuel (first.result r) ≤
      first.bound.eval n + (second.bound.substitute (.add (.linear 1 0) first.bound)).eval n
    rw [NatPolynomial.eval_substitute]
    change first.fuel r + second.fuel (first.result r) ≤
      first.bound.eval n + second.bound.eval ((1 * n + 0) + first.bound.eval n)
    simp only [Nat.one_mul,Nat.add_zero]
    omega
def choose (source : Fin 24) (onFalse onTrue : Routine) : Routine where
  block := .branch source onFalse.block onFalse.block onTrue.block
  result r := if (r.store.get source).headD false then onTrue.result r else onFalse.result r
  fuel r := 1 + if (r.store.get source).headD false then onTrue.fuel r else onFalse.fuel r
  bound := .add (.add onFalse.bound onTrue.bound) (.constant 1)
  exec r := by
    have checked := EdgeKinds.branch_head source r.store onFalse.block onTrue.block
      (onFalse.fuel r) (onTrue.fuel r) (onFalse.result r).store (onTrue.result r).store
      (onFalse.exec r) (onTrue.exec r)
    cases h : (r.store.get source).headD false <;>
      simpa only [h,Bool.false_eq_true,ite_false,ite_true] using checked
  cost r n bounded := by
    have a := onFalse.cost r n bounded
    have b := onTrue.cost r n bounded
    change 1 + (if (r.store.get source).headD false then onTrue.fuel r else onFalse.fuel r) ≤
      onFalse.bound.eval n + onTrue.bound.eval n + 1
    cases (r.store.get source).headD false <;>
      simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem seq_result (first second : Routine) (r : State) :
    (seq first second).result r = second.result (first.result r) := rfl
theorem choose_result (source : Fin 24) (onFalse onTrue : Routine) (r : State) :
    (choose source onFalse onTrue).result r =
      if (r.store.get source).headD false then onTrue.result r else onFalse.result r := rfl
theorem seq_data (first second : Routine)
    (hf : ∀ r, (first.result r).data = r.data) (hs : ∀ r, (second.result r).data = r.data) (r : State) :
    ((seq first second).result r).data = r.data := (hs (first.result r)).trans (hf r)
theorem choose_data (source : Fin 24) (onFalse onTrue : Routine)
    (hf : ∀ r, (onFalse.result r).data = r.data) (ht : ∀ r, (onTrue.result r).data = r.data) (r : State) :
    ((choose source onFalse onTrue).result r).data = r.data := by
  rw [choose_result]
  split
  · exact ht r
  · exact hf r
end Routine

theorem index_length_le (index : Index) (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    (indexWord index r).length ≤ n := by
  have size := Store.get_length_le r.store (indexRegister index) bounded
  cases index <;> exact size
theorem table_length_le (kind : CoefficientCache.Kind) (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    (CoefficientCache.table kind r.core).length ≤ n := by
  cases kind with
  | owner => exact Store.get_length_le r.store (16 : Fin 24) bounded
  | slot => exact Store.get_length_le r.store (17 : Fin 24) bounded
  | mode => exact Store.get_length_le r.store (18 : Fin 24) bounded
def queryRoutine (kind : CoefficientCache.Kind) (index : Index) : Routine where
  block := query kind index
  result := queried kind index
  fuel := queryFuel kind index
  bound := .linear 838 1172
  exec := query_exec kind index
  cost r n bounded := by
    have a := queryFuel_bound kind index r
    have b := table_length_le kind r n bounded
    have c := index_length_le index r n bounded
    change queryFuel kind index r ≤ 838 * n + 1172
    omega
def ordinalRoutine (value : Nat) : Routine where
  block := liftCore (OrdinalTest.read value)
  result r := r.withRegisters (OrdinalTest.result value r.registers)
  fuel r := OrdinalTest.fuel value r.registers
  bound := .linear 4 (value+10)
  exec r := liftCore_exec _ r _ _ (OrdinalTest.read_exec value _)
  cost r n bounded := by
    have a := OrdinalTest.fuel_bound value r.registers
    have b := Store.get_length_le r.store (8 : Fin 24) bounded
    change r.registers.output.length ≤ n at b
    change OrdinalTest.fuel value r.registers ≤ 4 * n + (value+10)
    omega
def emitIndexRoutine (index : Index) (tag : Bool) : Routine where
  block := emitIndex index tag
  result := indexEmitted index tag
  fuel := emitIndexFuel index
  bound := .linear 3 5
  exec := emitIndex_exec index tag
  cost r n bounded := by
    have size := index_length_le index r n bounded
    rw [emitIndexFuel_eq]
    change 3 * (indexWord index r).length + 5 ≤ 3 * n + 5
    omega
def emitAnswerRoutine (tag : Bool) : Routine where
  block := emitAnswer tag
  result := answerEmitted tag
  fuel := emitAnswerFuel
  bound := .linear 3 6
  exec := emitAnswer_exec tag
  cost r n bounded := by
    have size := Store.get_length_le r.store (8 : Fin 24) bounded
    change r.registers.output.length ≤ n at size
    have cost := emitAnswerFuel_bound r
    change emitAnswerFuel r ≤ 3 * n + 6
    omega

end PNP.Concrete.NormalizerBlocks.Coefficient

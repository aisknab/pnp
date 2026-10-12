/-
Copyright (c) 2026 PNP Labs.

Whole encoded-size budgets for path-derived table augmentation. Pair
generation is charged before the batch writer, including the generated
update bytes and table-growth bound.
-/
import PNP.Concrete.NormalizerAugmentationPhase

namespace PNP.Concrete.NormalizerBlocks.Augmentation
open BitRegister

def pairBudget : NatPolynomial :=
  .add (.linear 4 13) (.mul (.constant 5) (.mul (.linear 64 129) (.linear 1 1)))
def prepareBudget : NatPolynomial := .add (.constant 3) pairBudget
def preparedBudget : NatPolynomial := .add .variable prepareBudget
def phaseBudget : NatPolynomial :=
  .add prepareBudget (.add (BatchPacket.wholePolynomial.substitute preparedBudget) (.constant 1))
theorem pairBudget_eval (size : Nat) :
    pairBudget.eval size = 4 * size + 13 + 5 * ((64 * size + 129) * (size + 1)) := by
  change 4 * size + 13 + 5 * ((64 * size + 129) * (1 * size + 1)) = _
  rw [Nat.one_mul]
theorem prepareBudget_eval (size : Nat) : prepareBudget.eval size = 3 + pairBudget.eval size := rfl
theorem preparedBudget_eval (size : Nat) : preparedBudget.eval size = size + prepareBudget.eval size := rfl
theorem phaseBudget_eval (size : Nat) :
    phaseBudget.eval size = prepareBudget.eval size + (BatchPacket.wholePolynomial.eval (preparedBudget.eval size) + 1) := by
  change prepareBudget.eval size + ((BatchPacket.wholePolynomial.substitute preparedBudget).eval size + 1) = _
  rw [NatPolynomial.eval_substitute]

theorem pairsFuel_bound (r : State) (bound : Nat) (checked : r.store.Bounded bound) :
    pairsFuel r ≤ pairBudget.eval bound := by
  have viewed := Frame.core_bounded r.pairs.store r.frame checked
  have pending : r.pairs.pending.length ≤ bound := r.pairs.store.get_length_le 9 viewed
  have phase := PathPairs.phaseFuel_bound r.pairs bound viewed
  have first : 64 * r.pairs.pending.length + 129 ≤ 64 * bound + 129 := by omega
  have product := Nat.mul_le_mul first (Nat.add_le_add_right pending 1)
  rw [pairBudget_eval]
  calc
    pairsFuel r ≤ 4 * bound + 5 * ((64 * r.pairs.pending.length + 129) * (r.pairs.pending.length + 1)) + 13 := phase
    _ ≤ 4 * bound + 5 * ((64 * bound + 129) * (bound + 1)) + 13 :=
      Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 5 product) (4 * bound)) 13
    _ = 4 * bound + 13 + 5 * ((64 * bound + 129) * (bound + 1)) := Nat.add_right_comm _ _ _
theorem prepareFuel_bound (r : State) (bound : Nat) (checked : r.store.Bounded bound) :
    prepareFuel r ≤ prepareBudget.eval bound := by
  have pairs := pairsFuel_bound r bound checked
  have same : pairsFuel (tableSaved r) = pairsFuel r := rfl
  rw [prepareBudget_eval]
  unfold prepareFuel
  rw [same]
  omega
theorem prepared_bounded (r : State) (bound : Nat) (checked : r.store.Bounded bound) :
    (prepared r).store.Bounded (preparedBudget.eval bound) := by
  have after := (prepare_exec r).bounded bound checked
  apply Store.bounded_mono after
  rw [preparedBudget_eval]
  exact Nat.add_le_add_left (prepareFuel_bound r bound checked) bound

theorem updatesFuel_bound (r : State) (bound : Nat) (checked : r.store.Bounded bound) :
    updatesFuel r ≤ BatchPacket.wholePolynomial.eval bound := by
  rw [State.batch_store] at checked
  have viewed := Frame.core_bounded r.batch.store r.batchFrame checked
  have pending : r.batch.pending.length ≤ bound := r.batch.store.get_length_le 9 viewed
  have table : r.batch.table.length ≤ bound := r.batch.store.get_length_le 10 viewed
  have batch := (TableBatch.whole_bounds r.batch).2
  have growth := BatchPacket.totalCostBound_mono pending table
  change (TableBatch.whole r.batch).fuel ≤ TableBatch.totalCostBound bound bound
  exact Nat.le_trans batch growth

theorem phaseFuel_bound (r : State) (bound : Nat) (checked : r.store.Bounded bound) :
    phaseFuel r ≤ phaseBudget.eval bound := by
  have prepare := prepareFuel_bound r bound checked
  have batch := updatesFuel_bound (prepared r) (preparedBudget.eval bound) (prepared_bounded r bound checked)
  rw [phaseBudget_eval]
  unfold phaseFuel
  omega

end PNP.Concrete.NormalizerBlocks.Augmentation

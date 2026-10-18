import PNP.Concrete.ResidualReduction.MatrixSweepStep

/-! Complete forward elimination by a fixed finite-register program. The bound
is in the original matrix dimensions, including every failed pivot search and
the construction of the actual pivot history. This is source-register execution
from a prepared encoded matrix, not yet the all-input loader, solution-map
reconstruction, or final raw-machine polynomial runtime theorem. -/

namespace PNP.Concrete.ResidualReduction.MatrixSweep
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions

def residue : (n : Nat) → System n → System 0
  | 0, rows => rows
  | n + 1, rows => residue n (reducedRows rows)

def historyBits : (n : Nat) → System n → BitString → BitString
  | 0, _, acc => acc
  | n + 1, rows, acc =>
    historyBits n (reducedRows rows) (recordBits (choosePivot rows) ++ acc)

def fuel : (n : Nat) → System n → Nat
  | 0, _ => 1
  | n + 1, rows => 1 + (bodyFuel rows + fuel n (reducedRows rows))

def loop : Block 11 := .loop 9 body

theorem loop_exec (n : Nat) (rows : System n) (history : BitString) :
    Exec loop (start n rows history).store (fuel n rows)
      (start 0 (residue n rows) (historyBits n rows history)).store := by
  induction n generalizing history with
  | zero => exact Exec.loopStop rfl
  | succ n ih =>
    have first := body_exec rows history
    have rest := ih (reducedRows rows) (recordBits (choosePivot rows) ++ history)
    exact Exec.loopStep (source := (9 : Fin 11)) rfl first rest

theorem residue_length (n : Nat) (rows : System n) :
    (residue n rows).length = rows.length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [residue, ih, reducedRows_length]

theorem historyBits_suffix (n : Nat) (rows : System n) (acc : BitString) :
    historyBits n rows acc = historyBits n rows [] ++ acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    change historyBits n (reducedRows rows) (recordBits (choosePivot rows) ++ acc) =
      historyBits n (reducedRows rows) (recordBits (choosePivot rows) ++ []) ++ acc
    rw [ih (reducedRows rows) (recordBits (choosePivot rows) ++ acc),
      ih (reducedRows rows) (recordBits (choosePivot rows) ++ [])]
    simp only [List.append_nil, List.append_assoc]

theorem historyBits_bound (n : Nat) (rows : System n) (acc : BitString) :
    (historyBits n rows acc).length ≤ acc.length + n * (n + 1) := by
  induction n generalizing acc with
  | zero => simp only [historyBits, Nat.zero_mul, Nat.add_zero, Nat.le_refl]
  | succ n ih =>
    have previous := ih (reducedRows rows) (recordBits (choosePivot rows) ++ acc)
    have added := recordBits_length_bound (choosePivot rows)
    rw [List.length_append] at previous
    change (historyBits n (reducedRows rows) (recordBits (choosePivot rows) ++ acc)).length ≤
      acc.length + (n + 1) * ((n + 1) + 1)
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at *
    omega

/-- Whole-loop work is bounded by the original dimension and original row count.
The finite-register instruction model's copy operations are compiled separately;
this does not identify unit-cost register steps with raw-machine steps. -/
theorem fuel_bound (n : Nat) (rows : System n) :
    fuel n rows ≤ 80 * n * n * (rows.length + 1) + 1 := by
  induction n with
  | zero => simp only [fuel, Nat.mul_zero, Nat.zero_mul, Nat.zero_add, Nat.le_refl]
  | succ n ih =>
    have previous := ih (reducedRows rows)
    rw [reducedRows_length] at previous
    have stepBound := bodyFuel_bound rows
    change 1 + (bodyFuel rows + fuel n (reducedRows rows)) ≤
      80 * (n + 1) * (n + 1) * (rows.length + 1) + 1
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc] at *
    omega

/-- The zero-dimensional residue has precisely the existing solver's feasibility
answer. A complete Space still requires actual affine-map reconstruction. -/
theorem solve_isSome_residue (n : Nat) (rows : System n) :
    (solve n rows).isSome = satisfies (residue n rows) () := by
  induction n with
  | zero =>
    cases h : satisfies rows () <;> simp only [solve, residue, h] <;> rfl
  | succ n ih =>
    cases hp : choosePivot rows with
    | none =>
      simpa only [solve, hp, Option.isSome_map, residue, reducedRows, hp] using ih (tails rows)
    | some p =>
      simpa only [solve, hp, Option.isSome_map, residue, reducedRows, hp] using ih (substituteRows p rows)

def sweepProgram : Program 11 := loop.program 0 0

theorem program_run (n : Nat) (rows : System n) (history : BitString) :
    BitRegister.run sweepProgram (fuel n rows + 1) ⟨.running 0, (start n rows history).store⟩ =
      ⟨.accepted, (start 0 (residue n rows) (historyBits n rows history)).store⟩ :=
  (loop_exec n rows history).program_run 0 0

end PNP.Concrete.ResidualReduction.MatrixSweep

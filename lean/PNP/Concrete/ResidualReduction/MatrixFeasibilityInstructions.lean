import PNP.Concrete.ResidualReduction.MatrixSweepLoop

/-! Literal feasibility checking for every finite Boolean linear system after
the complete source-derived elimination sweep. The program also retains its
discovered pivot history. It does not yet reconstruct the full affine solution
map or establish the all-bitstring loader and raw-machine runtime bound. -/

namespace PNP.Concrete.ResidualReduction.MatrixFeasibility
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSweep

theorem matrixBits_zero (rows : System 0) : matrixBits rows = rows := by
  induction rows with
  | nil => rfl
  | cons b rows ih =>
    change b :: matrixBits rows = b :: rows
    rw [ih]

def constantResult : BitString → Bool → Bool
  | [], flag => flag
  | false :: bits, flag => constantResult bits flag
  | true :: bits, _ => constantResult bits false
def constantFuel : BitString → Nat
  | [] => 1
  | false :: bits => 3 + constantFuel bits
  | true :: bits => 5 + constantFuel bits

def checkBody : Block 9 :=
  .branch 0 .skip (.action (.pop 0))
    (.seq (.action (.clear 8)) (.seq (.action (.push 8 false)) (.action (.pop 0))))
def checkLoop : Block 9 := .loop 0 checkBody

theorem checkLoop_exec (bits : BitString) (r : Registers) (flag : Bool) :
    Exec checkLoop ({r with input := bits, output := [flag]}).store (constantFuel bits)
      ({r with input := [], output := [constantResult bits flag]}).store := by
  induction bits generalizing flag with
  | nil => exact Exec.loopStop rfl
  | cons b bits ih =>
    cases b with
    | false =>
      have first : Exec checkBody ({r with input := false :: bits, output := [flag]}).store 2
          ({r with input := bits, output := [flag]}).store := Exec.zero rfl (.action _ _)
      have checked := Exec.loopStep (source := (0 : Fin 9)) rfl first (ih flag)
      have cost : constantFuel (false :: bits) = 1 + (2 + constantFuel bits) := by
        simp only [constantFuel]; omega
      rw [cost]
      exact checked
    | true =>
      have first : Exec checkBody ({r with input := true :: bits, output := [flag]}).store 4
          ({r with input := bits, output := [false]}).store :=
        Exec.one rfl (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
      have checked := Exec.loopStep (source := (0 : Fin 9)) rfl first (ih false)
      have cost : constantFuel (true :: bits) = 1 + (4 + constantFuel bits) := by
        simp only [constantFuel]; omega
      rw [cost]
      exact checked

theorem constantResult_eq (bits : BitString) (flag : Bool) :
    constantResult bits flag = (flag && satisfies (n := 0) bits ()) := by
  induction bits generalizing flag with
  | nil => cases flag <;> rfl
  | cons b bits ih =>
    cases b with
    | false => exact ih flag
    | true =>
      change constantResult bits false = (flag && false)
      simpa only [Bool.false_and, Bool.and_false] using ih false

theorem constantFuel_bound (bits : BitString) : constantFuel bits ≤ 5 * bits.length + 1 := by
  induction bits with
  | nil => exact Nat.le_refl 1
  | cons b bits ih =>
    cases b <;> simp only [constantFuel, List.length_cons] <;> omega

def finish : Block 9 :=
  .seq (.action (.clear 8)) (.seq (.action (.push 8 true)) checkLoop)

theorem finish_exec (r : Registers) (bits : BitString) :
    Exec finish ({r with input := bits}).store (2 + constantFuel bits)
      ({r with input := [], output := [satisfies (n := 0) bits ()]}).store := by
  have scan := checkLoop_exec bits r true
  rw [constantResult_eq, Bool.true_and] at scan
  have first := Exec.action (.clear (8 : Fin 9)) ({r with input := bits}).store
  have second : Exec (.action (.push (8 : Fin 9) true))
      ({r with input := bits, output := []}).store 1
      ({r with input := bits, output := [true]}).store := .action _ _
  have checked := Exec.seq first (Exec.seq second scan)
  have cost : 2 + constantFuel bits = 1 + (1 + constantFuel bits) := by omega
  rw [cost]
  exact checked

def result (n : Nat) (rows : System n) (history : BitString) : MatrixSweep.State :=
  let r := start 0 (residue n rows) (historyBits n rows history)
  {r with core := {r.core with input := [], output := [(solve n rows).isSome]}}

def phase : Block 11 := .seq MatrixSweep.loop (MatrixSweep.lift finish)
def phaseFuel (n : Nat) (rows : System n) : Nat :=
  MatrixSweep.fuel n rows + (2 + constantFuel (residue n rows))

/-- The answer is computed from the encoded rows; it is not an input flag. -/
theorem phase_exec (n : Nat) (rows : System n) (history : BitString) :
    Exec phase (start n rows history).store (phaseFuel n rows) (result n rows history).store := by
  let r := start 0 (residue n rows) (historyBits n rows history)
  have checked : Exec finish r.core.store (2 + constantFuel (residue n rows))
      ({r.core with input := [], output := [(solve n rows).isSome]}).store := by
    simpa only [r, start, matrixBits_zero, solve_isSome_residue] using
      finish_exec r.core (residue n rows)
  have lifted := MatrixSweep.lift_exec finish r _ _ checked
  exact Exec.seq (loop_exec n rows history) lifted

theorem phaseFuel_bound (n : Nat) (rows : System n) :
    phaseFuel n rows ≤ 80 * n * n * (rows.length + 1) + 5 * rows.length + 4 := by
  have sweep := fuel_bound n rows
  have sameLength : (residue n rows : BitString).length = rows.length :=
    residue_length n rows
  have check : constantFuel (residue n rows) ≤ 5 * rows.length + 1 := by
    calc
      constantFuel (residue n rows) ≤ 5 * (residue n rows : BitString).length + 1 :=
        constantFuel_bound (residue n rows)
      _ = 5 * rows.length + 1 := congrArg (fun length => 5 * length + 1) sameLength
  unfold phaseFuel
  omega

def program : Program 11 := phase.program 0 8
theorem program_run (n : Nat) (rows : System n) (history : BitString) :
    BitRegister.run program (phaseFuel n rows + 1) ⟨.running 0, (start n rows history).store⟩ =
      ⟨.accepted, (result n rows history).store⟩ :=
  (phase_exec n rows history).program_run 0 8

end PNP.Concrete.ResidualReduction.MatrixFeasibility

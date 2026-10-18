import PNP.Concrete.ResidualReduction.MatrixSolutionSerialization
import PNP.Concrete.ResidualReduction.MatrixFeasibilityInstructions

/-! Complete literal linear solving on a prepared finite coefficient matrix:
forward elimination, contradiction check, full solution-map reconstruction, and
canonical Option/Space output. Every phase contributes to the polynomial source
instruction bound. Parsing arbitrary original input and composing the literal
raw-machine compiler remain separate obligations, not inferred from this result. -/

namespace PNP.Concrete.ResidualReduction.MatrixSolutionInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.MatrixSolutionHistory
open PNP.Concrete.ResidualReduction.MatrixReconstruction

def fromSweep (r : MatrixSweep.State) (pending : BitString) : State :=
  ⟨r.core, r.pending, r.history, pending⟩
def forwardLift (block : Block 11) : Block 12 := Frame.block 1 block

theorem forwardLift_exec (block : Block 11) (before after : MatrixSweep.State)
    (pending : BitString) (fuel : Nat) (checked : Exec block before.store fuel after.store) :
    Exec (forwardLift block) (fromSweep before pending).store fuel (fromSweep after pending).store :=
  Frame.execution checked (.cons pending .nil)

def start (n : Nat) (rows : System n) : State := fromSweep (MatrixSweep.start n rows []) []
def checked (n : Nat) (rows : System n) : State :=
  fromSweep (MatrixFeasibility.result n rows []) (List.replicate n true)

def prepareCore : Block 9 :=
  .seq (.action (.clear 7)) (.seq (.action (.clear 8)) (.action (.push 1 true)))
def preparePositive : Block 12 :=
  .seq (lift prepareCore) (.action (.push 9 true))

theorem preparePositive_exec (n : Nat) (rows : System n) :
    Exec preparePositive (checked n rows).store 4
      (ready zeroSpace (MatrixSweep.historyBits n rows []) (List.replicate n true)).store := by
  let before := checked n rows
  let afterCore := {before with core := (ready zeroSpace [] []).core}
  have core : Exec prepareCore before.core.store 3 afterCore.core.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have first : Exec (lift prepareCore) before.store 3 afterCore.store :=
    lift_exec prepareCore before 3 afterCore.core core
  have second : Exec (.action (.push (9 : Fin 12) true)) afterCore.store 1
      (ready zeroSpace (MatrixSweep.historyBits n rows []) (List.replicate n true)).store := .action _ _
  exact Exec.seq first second

def positive : Block 12 :=
  .seq preparePositive (.seq MatrixReconstruction.loop (lift MatrixSolutionSerialization.block))
def positiveFuel (n : Nat) (rows : System n) : Nat :=
  4 + (actualFuel n rows + (3 * (computedSpace n rows).parameters + 6))

theorem positive_exec (n : Nat) (rows : System n) :
    Exec positive (checked n rows).store (positiveFuel n rows)
      (MatrixSolutionSerialization.result (computedSpace n rows)).store :=
  Exec.seq (preparePositive_exec n rows)
    (Exec.seq (actual_history_exec n rows) (MatrixSolutionSerialization.lifted_exec (computedSpace n rows)))

def selection : Block 12 := .branch 8 .skip .skip positive
def selectionFuel (n : Nat) (rows : System n) : Nat :=
  if (solve n rows).isSome then 1 + positiveFuel n rows else 2
def result (n : Nat) (rows : System n) : State :=
  if (solve n rows).isSome then MatrixSolutionSerialization.result (computedSpace n rows)
  else checked n rows

theorem selection_exec (n : Nat) (rows : System n) :
    Exec selection (checked n rows).store (selectionFuel n rows) (result n rows).store := by
  cases h : (solve n rows).isSome with
  | false =>
    have read : (checked n rows).store.get 8 = [false] := by
      change [(solve n rows).isSome] = [false]
      rw [h]
    have selected : Exec selection (checked n rows).store 2 (checked n rows).store :=
      Exec.zero read (.skip _)
    simpa only [selectionFuel, result, h, Bool.false_eq_true, if_false] using selected
  | true =>
    have read : (checked n rows).store.get 8 = [true] := by
      change [(solve n rows).isSome] = [true]
      rw [h]
    have selected : Exec selection (checked n rows).store (1 + positiveFuel n rows)
        (MatrixSolutionSerialization.result (computedSpace n rows)).store :=
      Exec.one read (positive_exec n rows)
    simpa only [selectionFuel, result, h, if_true] using selected

def phase : Block 12 :=
  .seq (.action (.copy 11 9)) (.seq (forwardLift MatrixFeasibility.phase) selection)
def phaseFuel (n : Nat) (rows : System n) : Nat :=
  1 + (MatrixFeasibility.phaseFuel n rows + selectionFuel n rows)

theorem phase_exec (n : Nat) (rows : System n) :
    Exec phase (start n rows).store (phaseFuel n rows) (result n rows).store := by
  have saved : Exec (.action (.copy (11 : Fin 12) 9)) (start n rows).store 1
      (fromSweep (MatrixSweep.start n rows []) (List.replicate n true)).store := .action _ _
  have forward := forwardLift_exec MatrixFeasibility.phase
    (MatrixSweep.start n rows []) (MatrixFeasibility.result n rows [])
    (List.replicate n true) (MatrixFeasibility.phaseFuel n rows)
    (MatrixFeasibility.phase_exec n rows [])
  exact Exec.seq saved (Exec.seq forward (selection_exec n rows))

theorem result_output (n : Nat) (rows : System n) :
    (result n rows).core.output = (solutionCodec n).encode (solve n rows) := by
  have answer : solve n rows =
      if (solve n rows).isSome then some (computedSpace n rows) else none := by
    rw [MatrixSweep.solve_isSome_residue]
    exact computedSpace_exact n rows
  rw [answer]
  cases h : (solve n rows).isSome with
  | false =>
    simp only [result, h, Bool.false_eq_true, if_false]
    change [(solve n rows).isSome] = [false]
    rw [h]
  | true =>
    simp only [result, h, if_true]
    rfl

theorem selectionFuel_bound (n : Nat) (rows : System n) :
    selectionFuel n rows ≤ actualFuel n rows + 3 * n + 11 := by
  have parameters := computedSpace_parameters n rows
  cases h : (solve n rows).isSome <;>
    simp only [selectionFuel, positiveFuel, h, Bool.false_eq_true, if_false, if_true] <;> omega

theorem phaseFuel_bound (n : Nat) (rows : System n) :
    phaseFuel n rows ≤ 80 * n * n * (rows.length + 1) + 5 * rows.length +
      (50 * (n + 2) * (n + 1) + 1) * n + 3 * n + 20 := by
  have forward := MatrixFeasibility.phaseFuel_bound n rows
  have reconstructed := actualFuel_bound n rows
  have selected := selectionFuel_bound n rows
  unfold phaseFuel
  omega

def program : Program 12 := phase.program 0 8

theorem program_run (n : Nat) (rows : System n) :
    BitRegister.run program (phaseFuel n rows + 1) ⟨.running 0, (start n rows).store⟩ =
      ⟨.accepted, (result n rows).store⟩ :=
  (phase_exec n rows).program_run 0 8

theorem program_output (n : Nat) (rows : System n) :
    (BitRegister.run program (phaseFuel n rows + 1)
      ⟨.running 0, (start n rows).store⟩).store.get 8 = (solutionCodec n).encode (solve n rows) := by
  rw [program_run]
  exact result_output n rows

end PNP.Concrete.ResidualReduction.MatrixSolutionInstructions

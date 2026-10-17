import PNP.Concrete.ResidualReduction.MatrixSweepLoop
import PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

/-! The reconstruction order of the history actually produced by elimination.
The indexed history is a proof-side description of finite bytes, not a machine
primitive or a supplied solution certificate. Its reconstruction is exactly the
existing solver's complete Space, including the same parameter ordering. -/

namespace PNP.Concrete.ResidualReduction.MatrixSolutionHistory
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions

def applyPivot {n : Nat} (pivot : Option (Affine n)) (s : Space n) : Space (n + 1) :=
  match pivot with
  | none => freeSpace s
  | some p => pivotSpace p s

theorem applyPivot_parameters {n : Nat} (pivot : Option (Affine n)) (s : Space n)
    (bound : s.parameters ≤ n) : (applyPivot pivot s).parameters ≤ n + 1 := by
  cases pivot <;> simp only [applyPivot, freeSpace, pivotSpace] <;> omega

inductive History : Nat → Nat → Type where
  | nil (n : Nat) : History n n
  | step {n final : Nat} (pivot : Option (Affine n))
      (rest : History (n + 1) final) : History n final

def History.length : {n final : Nat} → History n final → Nat
  | _, _, .nil _ => 0
  | _, _, .step _ rest => 1 + rest.length

def History.encode : {n final : Nat} → History n final → BitString
  | _, _, .nil _ => []
  | _, _, .step pivot rest => MatrixSweep.recordBits pivot ++ rest.encode

def History.append : {a b c : Nat} → History a b → History b c → History a c
  | _, _, _, .nil _, right => right
  | _, _, _, .step pivot rest, right => .step pivot (rest.append right)

def History.reconstruct : {n final : Nat} → History n final → Space n → Space final
  | _, _, .nil _, s => s
  | _, _, .step pivot rest, s => rest.reconstruct (applyPivot pivot s)

theorem History.length_coordinate {n final : Nat} (h : History n final) :
    n + h.length = final := by
  induction h with
  | nil => rfl
  | step pivot rest ih => simp only [History.length]; omega

theorem History.encode_append {a b c : Nat} (left : History a b) (right : History b c) :
    (left.append right).encode = left.encode ++ right.encode := by
  induction left with
  | nil => rfl
  | step pivot rest ih => simp only [append, encode, ih, List.append_assoc]

theorem History.reconstruct_append {a b c : Nat} (left : History a b)
    (right : History b c) (s : Space a) :
    (left.append right).reconstruct s = right.reconstruct (left.reconstruct s) := by
  induction left with
  | nil => rfl
  | step pivot rest ih => exact ih right (applyPivot pivot s)

theorem History.parameters_bound {n final : Nat} (h : History n final)
    (s : Space n) (bound : s.parameters ≤ n) : (h.reconstruct s).parameters ≤ final := by
  induction h with
  | nil => exact bound
  | step pivot rest ih => exact ih (applyPivot pivot s) (applyPivot_parameters pivot s bound)

def fromRows : (n : Nat) → System n → History 0 n
  | 0, _ => .nil 0
  | n + 1, rows =>
    (fromRows n (reducedRows rows)).append (.step (choosePivot rows) (.nil (n + 1)))

theorem fromRows_history (n : Nat) (rows : System n) (suffix : BitString) :
    MatrixSweep.historyBits n rows suffix = (fromRows n rows).encode ++ suffix := by
  induction n generalizing suffix with
  | zero => rfl
  | succ n ih =>
    rw [MatrixSweep.historyBits, ih]
    simp only [fromRows, History.encode_append, History.encode,
      List.append_nil, List.append_assoc]

theorem solve_step {n : Nat} (rows : System (n + 1)) :
    solve (n + 1) rows = (solve n (reducedRows rows)).map (applyPivot (choosePivot rows)) := by
  cases hp : choosePivot rows <;> simp only [solve, reducedRows, hp] <;> rfl

theorem solve_history (n : Nat) (rows : System n) :
    solve n rows = (solve 0 (MatrixSweep.residue n rows)).map (fromRows n rows).reconstruct := by
  induction n with
  | zero =>
    change solve 0 rows = (solve 0 rows).map (fun s => s)
    cases h : solve 0 rows <;> rfl
  | succ n ih =>
    rw [solve_step, ih]
    cases h : solve 0 (MatrixSweep.residue n (reducedRows rows)) with
    | none => simp only [MatrixSweep.residue, h, Option.map_none]
    | some s =>
      simp only [MatrixSweep.residue, h, Option.map_some, fromRows,
        History.reconstruct_append, History.reconstruct]

def zeroSpace : Space 0 := ⟨0, ()⟩

theorem solve_exact (n : Nat) (rows : System n) :
    solve n rows =
      if satisfies (MatrixSweep.residue n rows) () then
        some ((fromRows n rows).reconstruct zeroSpace) else none := by
  rw [solve_history]
  cases h : satisfies (MatrixSweep.residue n rows) () <;>
    simp only [solve, h, Bool.false_eq_true, if_false, if_true,
      Option.map_none, Option.map_some, zeroSpace]

end PNP.Concrete.ResidualReduction.MatrixSolutionHistory

import PNP.Concrete.ResidualReduction.MatrixReconstructionStep

/-! Complete unbounded reconstruction from the finite history. The fixed
instruction loop consumes every record produced by the forward sweep and
returns the existing solver's exact affine solution map. The uniform cubic
bound counts history decoding and both reconstruction branches. -/

namespace PNP.Concrete.ResidualReduction.MatrixReconstruction
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixSolutionHistory

def loop : Block 12 := .loop 11 body

def fuel : {n final : Nat} → (h : History n final) → Space n → Nat
  | _, _, .nil _, _ => 1
  | _, _, .step pivot rest, s =>
    1 + (bodyFuel pivot s + fuel rest (applyPivot pivot s))

theorem loop_exec {n final : Nat} (h : History n final) (s : Space n) (suffix : BitString) :
    Exec loop (ready s (h.encode ++ suffix) (List.replicate h.length true)).store
      (fuel h s) (ready (h.reconstruct s) suffix []).store := by
  induction h with
  | nil => exact Exec.loopStop rfl
  | step pivot rest ih =>
    have step := body_exec pivot s (rest.encode ++ suffix) (List.replicate rest.length true) true
    have checked := Exec.loopStep (source := (11 : Fin 12)) rfl step (ih (applyPivot pivot s))
    simpa only [loop, fuel, History.length, History.encode, History.reconstruct,
      Nat.one_add, List.replicate_succ, List.append_assoc] using checked

theorem fuel_bound {n final : Nat} (h : History n final) (s : Space n)
    (parameters : s.parameters ≤ n) :
    fuel h s ≤ (50 * (final + 2) * (final + 1) + 1) * h.length + 1 := by
  induction h with
  | nil => exact Nat.le_refl 1
  | @step n final pivot rest ih =>
    have coordinate := rest.length_coordinate
    have dimension : n ≤ final := by omega
    have tailBound := ih (applyPivot pivot s) (applyPivot_parameters pivot s parameters)
    have stepBound := bodyFuel_bound pivot s
    have paramBound : s.parameters + 2 ≤ final + 2 := by omega
    have dimBound : n + 1 ≤ final + 1 := by omega
    have common : 50 * (s.parameters + 2) * (n + 1) ≤
        50 * (final + 2) * (final + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 50 paramBound) dimBound
    have current := Nat.le_trans stepBound common
    simp only [fuel, History.length, Nat.mul_add, Nat.mul_one] at current tailBound ⊢
    omega

def computedSpace (n : Nat) (rows : System n) : Space n :=
  (fromRows n rows).reconstruct zeroSpace
def actualFuel (n : Nat) (rows : System n) : Nat := fuel (fromRows n rows) zeroSpace

theorem actual_history_exec (n : Nat) (rows : System n) :
    Exec loop (ready zeroSpace (MatrixSweep.historyBits n rows []) (List.replicate n true)).store
      (actualFuel n rows) (ready (computedSpace n rows) [] []).store := by
  have length : (fromRows n rows).length = n := by
    have coordinate := (fromRows n rows).length_coordinate
    omega
  simpa only [fromRows_history, length, computedSpace, actualFuel] using
    loop_exec (fromRows n rows) zeroSpace []

theorem actualFuel_bound (n : Nat) (rows : System n) :
    actualFuel n rows ≤ (50 * (n + 2) * (n + 1) + 1) * n + 1 := by
  have length : (fromRows n rows).length = n := by
    have coordinate := (fromRows n rows).length_coordinate
    omega
  simpa only [actualFuel, length] using
    fuel_bound (fromRows n rows) zeroSpace (Nat.le_refl 0)

theorem computedSpace_parameters (n : Nat) (rows : System n) :
    (computedSpace n rows).parameters ≤ n :=
  (fromRows n rows).parameters_bound zeroSpace (Nat.le_refl 0)

/-- No completeness premise is supplied: feasibility comes from the generated
residue, while the full Space is constructed from the generated history. -/
theorem computedSpace_exact (n : Nat) (rows : System n) :
    solve n rows =
      if satisfies (MatrixSweep.residue n rows) () then some (computedSpace n rows) else none :=
  solve_exact n rows

def program : Program 12 := loop.program 10 0

theorem program_run (n : Nat) (rows : System n) :
    BitRegister.run program (actualFuel n rows + 1)
      ⟨.running 0, (ready zeroSpace (MatrixSweep.historyBits n rows []) (List.replicate n true)).store⟩ =
      ⟨.accepted, (ready (computedSpace n rows) [] []).store⟩ :=
  (actual_history_exec n rows).program_run 10 0

end PNP.Concrete.ResidualReduction.MatrixReconstruction

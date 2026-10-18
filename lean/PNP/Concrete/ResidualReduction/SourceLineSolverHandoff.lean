import PNP.Concrete.ResidualReduction.SourceLineMatrixConstruction
import PNP.Concrete.ResidualReduction.SourcePlaneSolver

/-! Prepare the exact rank-one constraint system for the existing solver.
Its unknowns are all source weights followed by all covector coordinates.
The combined unary dimension is computed by a literal counted loop while
the original dimension, source count and input normal remain protected. -/

namespace PNP.Concrete.ResidualReduction.SourceLineSolver
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourcePlaneMatrixAugmentation (State)
open PNP.Concrete.ResidualReduction.SourcePlaneSolver (solver setSolver)

def saved {n : Nat} (F : Family n) (alpha : Affine n) : State :=
  let r := SourceLineMatrixConstruction.result F alpha
  {r with core := {r.core with core := {r.core.core with outer := List.replicate n true}}}
def counterReady {n : Nat} (F : Family n) (alpha : Affine n) (width remaining : Nat) : State :=
  setSolver (saved F alpha)
    ⟨{base 0 [] with target := List.replicate width true, output := matrixBits (SourceLine.rankOneRows F alpha)},
      List.replicate n true, List.replicate remaining true, []⟩
def ready {n : Nat} (F : Family n) (alpha : Affine n) : State :=
  setSolver (saved F alpha)
    (MatrixSolutionInstructions.start (n + F.length) (SourceLine.rankOneRows F alpha))

def countStep : Block 17 := .seq (.action (.push 1 true)) (.action (.pop 10))
def countLoop : Block 17 := .loop 10 countStep
theorem countStep_exec {n : Nat} (F : Family n) (alpha : Affine n) (width remaining : Nat) :
    Exec countStep (counterReady F alpha width (remaining + 1)).store 2
      (counterReady F alpha (width + 1) remaining).store :=
  Exec.seq (.action _ _) (.action _ _)
theorem countLoop_exec {n : Nat} (F : Family n) (alpha : Affine n) (width remaining : Nat) :
    Exec countLoop (counterReady F alpha width remaining).store (3 * remaining + 1)
      (counterReady F alpha (width + remaining) 0).store := by
  induction remaining generalizing width with
  | zero => exact Exec.loopStop rfl
  | succ remaining ih =>
    have checked := Exec.loopStep (source := (10 : Fin 17)) rfl
      (countStep_exec F alpha width remaining) (ih (width + 1))
    have index : width + 1 + remaining = width + (remaining + 1) := by omega
    have cost : 3 * (remaining + 1) + 1 = 1 + (2 + (3 * remaining + 1)) := by omega
    simpa only [countLoop, cost, index] using checked

def finish : Block 17 := .seq (.action (.copy 9 1)) SourcePlaneSolver.copyData
theorem finish_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec finish (counterReady F alpha (n + F.length) 0).store 4 (ready F alpha).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
def prepare : Block 17 := .seq (.action (.copy 13 9)) <|
  .seq (.action (.copy 1 15)) (.seq countLoop finish)
def prepareFuel (n : Nat) : Nat := 3 * n + 7
theorem prepare_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec prepare (SourceLineMatrixConstruction.result F alpha).store (prepareFuel n)
      (ready F alpha).store := by
  have dimension : Exec (.action (.copy (13 : Fin 17) 9))
      (SourceLineMatrixConstruction.result F alpha).store 1 (saved F alpha).store := .action _ _
  have count : Exec (.action (.copy (1 : Fin 17) 15)) (saved F alpha).store 1
      (counterReady F alpha F.length n).store := .action _ _
  have combined : Exec countLoop (counterReady F alpha F.length n).store (3 * n + 1)
      (counterReady F alpha (n + F.length) 0).store := by
    simpa only [Nat.add_comm F.length n] using countLoop_exec F alpha F.length n
  have cost : prepareFuel n = 1 + (1 + ((3 * n + 1) + 4)) := by
    unfold prepareFuel
    omega
  simpa only [prepare, cost] using Exec.seq dimension (Exec.seq count (Exec.seq combined (finish_exec F alpha)))
theorem ready_width {n : Nat} (F : Family n) (alpha : Affine n) :
    (ready F alpha).store.get 1 = List.replicate (n + F.length) true := rfl
theorem ready_matrix {n : Nat} (F : Family n) (alpha : Affine n) :
    (ready F alpha).store.get 0 = matrixBits (SourceLine.rankOneRows F alpha) := rfl
theorem ready_dimension {n : Nat} (F : Family n) (alpha : Affine n) :
    (ready F alpha).store.get 13 = List.replicate n true := rfl
theorem ready_source_count {n : Nat} (F : Family n) (alpha : Affine n) :
    (ready F alpha).store.get 15 = List.replicate F.length true := rfl

end PNP.Concrete.ResidualReduction.SourceLineSolver

import PNP.Concrete.ResidualReduction.SourceDirectionEncoding

/-! The complete two-kernel direction construction on prepared original
source data. The first map is computed, transferred into the complete polar
constructor, and followed by a second actual kernel computation. Every data
transfer is literal code. Raw input parsing remains a separate entry boundary. -/

namespace PNP.Concrete.ResidualReduction.SourceDirectionInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (familyBits)
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding (matrixBits_append)

structure State where
  family : SourcePolarFamilyInstructions.State
  dimension : BitString
  normals : BitString
def State.frame (r : State) : Store 2 := .cons r.dimension (.cons r.normals .nil)
def State.store (r : State) : Store 20 := Frame.join r.family.store r.frame
def core (r : State) : MatrixReconstruction.State :=
  ⟨r.family.core.core, r.family.core.width, r.family.core.left, r.family.core.right⟩
def setCore (r : State) (c : MatrixReconstruction.State) : State :=
  {r with family := {r.family with core := {r.family.core with core := c.core, width := c.width, left := c.history, right := c.pending}}}
def State.solverFrame (r : State) : Store 8 :=
  .cons r.family.core.leftCoefficients <| .cons r.family.core.rightCoefficients <|
    .cons r.family.core.pending <| .cons r.family.core.map <| .cons r.family.core.savedOutput <|
      .cons r.family.source <| .cons r.dimension (.cons r.normals .nil)
theorem store_core (r : State) : r.store = Frame.join (core r).store r.solverFrame := rfl

def solver (body : Block 12) : Block 20 := Frame.block 8 body
theorem solver_exec (body : Block 12) (r : State) (fuel : Nat) (after : MatrixReconstruction.State)
    (checked : Exec body (core r).store fuel after.store) :
    Exec (solver body) r.store fuel (setCore r after).store := Frame.execution checked r.solverFrame
def family (body : Block 18) : Block 20 := Frame.block 2 body
theorem family_exec (body : Block 18) (r : State) (fuel : Nat) (after : SourcePolarFamilyInstructions.State)
    (checked : Exec body r.family.store fuel after.store) :
    Exec (family body) r.store fuel ({r with family := after}).store := Frame.execution checked r.frame
def small (body : Block 9) : Block 20 := family (SourcePolarFamilyInstructions.small body)
theorem small_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.family.core.core.store fuel after.store) :
    Exec (small body) r.store fuel ({r with family := {r.family with core := {r.family.core with core := after}}}).store :=
  Frame.execution (SourcePolarFamilyInstructions.small_exec body r.family fuel after checked) r.frame

def framed {n : Nat} (F : Family n) (U : System n) : State :=
  ⟨SourcePolarFamilyInstructions.ready n 0 [] (familyBits F) [], List.replicate n true, (matrixBits U).reverse⟩
def start {n : Nat} (F : Family n) (U : System n) : State :=
  setCore (framed F U) (MatrixSolutionInstructions.start n U)
def fromKernel {n : Nat} (F : Family n) (U : System n) (s : Space n) : State :=
  setCore (framed F U) (MatrixSolutionSerialization.result s)
def familyReady {n : Nat} (F : Family n) (U : System n) (s : Space n) : State :=
  ⟨SourcePolarFamilyInstructions.ready n s.parameters (mapBits s.forms) (familyBits F) [],
    List.replicate n true, (matrixBits U).reverse⟩
def familyDone {n : Nat} (F : Family n) (U : System n) (s : Space n) : State :=
  ⟨SourcePolarFamilyInstructions.ready n s.parameters (mapBits s.forms) [] (matrixBits (polarRows F s)),
    List.replicate n true, (matrixBits U).reverse⟩

def kernelFuel (n : Nat) (U : System n) : Nat :=
  MatrixHomogeneous.fuel n U + MatrixSolutionInstructions.phaseFuel n (homogeneous U)
theorem firstKernel_exec {n : Nat} (F : Family n) (U : System n) :
    Exec (solver MatrixKernelSolver.consumer) (start F U).store (kernelFuel n U)
      (fromKernel F U (kernelSpace U)).store :=
  solver_exec _ (start F U) _ _ (MatrixKernelSolver.consumer_exec n U)

/-- Copy the actual retained map and restore the original source dimension.
The solver's parameter-width counter remains intact, including width one. -/
def prepareFamily : Block 20 := .seq (.action (.copy 15 7)) <|
  .seq (.action (.copy 9 18)) <| .seq (.action (.clear 0)) <|
    .seq (.action (.clear 7)) (.action (.clear 8))
theorem prepareFamily_exec {n : Nat} (F : Family n) (U : System n) (s : Space n) :
    Exec prepareFamily (fromKernel F U s).store 5 (familyReady F U s).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _)
    (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))))
theorem polar_exec {n : Nat} (F : Family n) (U : System n) (s : Space n) :
    Exec (family SourcePolarFamilyInstructions.block) (familyReady F U s).store
      (SourcePolarFamilyInstructions.fuel F s) (familyDone F U s).store :=
  family_exec _ (familyReady F U s) _ _ (SourcePolarFamilyInstructions.block_exec F s)

def secondStart {n : Nat} (F : Family n) (U : System n) (s : Space n) : State :=
  setCore (framed ([] : Family n) U) (MatrixSolutionInstructions.start n (U ++ polarRows F s))
def resetSecond : Block 20 := .seq (.action (.copy 0 8)) <|
  .seq (.action (.copy 7 8)) <| .seq (.action (.clear 8)) <|
    .seq (.action (.copy 1 18)) <| .seq (.action (.copy 9 18)) (.action (.clear 15))
def prepareSecond : Block 20 := .seq (.action (.copy 3 19)) <|
  .seq (small ClauseQuery.reverseLoop) resetSecond

theorem prepareSecond_exec {n : Nat} (F : Family n) (U : System n) (s : Space n) :
    Exec prepareSecond (familyDone F U s).store (4 * (matrixBits U).length + 8)
      (secondStart F U s).store := by
  let before := familyDone F U s
  let seeded := {before with family := {before.family with core := {before.family.core with core := {before.family.core.core with excess := (matrixBits U).reverse}}}}
  let joined := {before with family := {before.family with core := {before.family.core with core := {before.family.core.core with output := matrixBits U ++ matrixBits (polarRows F s)}}}}
  have seed : Exec (.action (.copy (3 : Fin 20) 19)) before.store 1 seeded.store := .action _ _
  have reversedCore : Exec ClauseQuery.reverseLoop seeded.family.core.core.store
      (4 * (matrixBits U).length + 1) joined.family.core.core.store := by
    simpa only [seeded, joined, before, familyDone, SourcePolarFamilyInstructions.ready,
      SourcePolarRowInstructions.idle, base, List.length_reverse, List.reverse_reverse] using
      ClauseQuery.reverse_exec {base (s.parameters + 1) [] with output := matrixBits (polarRows F s)}
        (matrixBits U).reverse
  have reversed := small_exec ClauseQuery.reverseLoop seeded _ joined.family.core.core reversedCore
  have reset : Exec resetSecond joined.store 6 (secondStart F U s).store := by
    simp only [secondStart, MatrixSolutionInstructions.start, MatrixSolutionInstructions.fromSweep,
      MatrixSweep.start, matrixBits_append]
    exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
      (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))))
  have cost : 4 * (matrixBits U).length + 8 = 1 + ((4 * (matrixBits U).length + 1) + 6) := by omega
  simpa only [prepareSecond, cost] using Exec.seq seed (Exec.seq reversed reset)

def result {n : Nat} (F : Family n) (U : System n) : State :=
  setCore (framed ([] : Family n) U) (MatrixSolutionSerialization.result (directionSpace F U))
theorem secondKernel_exec {n : Nat} (F : Family n) (U : System n) :
    Exec (solver MatrixKernelSolver.consumer) (secondStart F U (kernelSpace U)).store
      (kernelFuel n (directionSystem F U)) (result F U).store :=
  solver_exec _ (secondStart F U (kernelSpace U)) _ _
    (MatrixKernelSolver.consumer_exec n (directionSystem F U))

def block : Block 20 := .seq (solver MatrixKernelSolver.consumer) <|
  .seq prepareFamily <| .seq (family SourcePolarFamilyInstructions.block) <|
    .seq prepareSecond (solver MatrixKernelSolver.consumer)
def fuel {n : Nat} (F : Family n) (U : System n) : Nat :=
  kernelFuel n U + (5 + (SourcePolarFamilyInstructions.fuel F (kernelSpace U) +
    ((4 * (matrixBits U).length + 8) + kernelFuel n (directionSystem F U))))

theorem block_exec {n : Nat} (F : Family n) (U : System n) :
    Exec block (start F U).store (fuel F U) (result F U).store :=
  Exec.seq (firstKernel_exec F U) (Exec.seq (prepareFamily_exec F U (kernelSpace U))
    (Exec.seq (polar_exec F U (kernelSpace U))
      (Exec.seq (prepareSecond_exec F U (kernelSpace U)) (secondKernel_exec F U))))
theorem result_output {n : Nat} (F : Family n) (U : System n) :
    (result F U).store.get 8 = (solutionCodec n).encode (some (directionSpace F U)) := rfl

def program : Program 20 := block.program 0 8
theorem program_run {n : Nat} (F : Family n) (U : System n) :
    BitRegister.run program (fuel F U + 1) ⟨.running 0, (start F U).store⟩ =
      ⟨.accepted, (result F U).store⟩ := (block_exec F U).program_run 0 8

end PNP.Concrete.ResidualReduction.SourceDirectionInstructions

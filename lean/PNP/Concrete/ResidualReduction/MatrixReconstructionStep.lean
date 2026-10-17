import PNP.Concrete.ResidualReduction.MatrixSolutionHistory
import PNP.Concrete.ResidualReduction.MatrixPivotMapInstructions

/-! One literal reconstruction step consumes the next saved history record.
Three protected registers hold the increasing pivot width, unread history, and
remaining step count. Pivot coefficients are copied from the encoded history;
the solution map is computed by the previously checked finite routines. -/

namespace PNP.Concrete.ResidualReduction.MatrixReconstruction
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.MatrixSolutionHistory

structure State where
  core : Registers
  width : BitString
  history : BitString
  pending : BitString

def State.frame (r : State) : Store 3 := .cons r.width (.cons r.history (.cons r.pending .nil))
def State.store (r : State) : Store 12 := Frame.join r.core.store r.frame
def lift (body : Block 9) : Block 12 := Frame.block 3 body

theorem lift_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (lift body) r.store fuel ({r with core := after}).store :=
  Frame.execution checked r.frame

def ready {n : Nat} (s : Space n) (history pending : BitString) : State :=
  ⟨{base (s.parameters + 1) (mapBits s.forms) with input := mapBits s.forms},
    List.replicate (n + 1) true, history, pending⟩

def afterMap {n : Nat} (s : Space (n + 1)) (oldMap history pending : BitString) : State :=
  ⟨{base (s.parameters + 1) oldMap with output := mapBits s.forms},
    List.replicate (n + 1) true, history, pending⟩

def resetMap : Block 9 :=
  .seq (.action (.copy 0 8)) (.seq (.action (.copy 7 8)) (.action (.clear 8)))
def advance : Block 12 := .seq (.action (.push 9 true)) (.action (.pop 11))
def reset : Block 12 := .seq (lift resetMap) advance

theorem reset_exec {n : Nat} (s : Space (n + 1)) (oldMap history pending : BitString)
    (tick : Bool) :
    Exec reset (afterMap s oldMap history (tick :: pending)).store 5
      (ready s history pending).store := by
  let before := afterMap s oldMap history (tick :: pending)
  let copied := {before with core := (ready s history pending).core}
  have core : Exec resetMap before.core.store 3 copied.core.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have first : Exec (lift resetMap) before.store 3 copied.store :=
    lift_exec resetMap before 3 copied.core core
  have second : Exec advance copied.store 2 (ready s history pending).store :=
    Exec.seq (.action _ _) (.action _ _)
  exact Exec.seq first second

def freeStep : Block 12 :=
  .seq (.action (.pop 10)) (.seq (lift MatrixFreeInstructions.block) reset)

theorem freeStep_exec {n : Nat} (s : Space n) (history pending : BitString) (tick : Bool) :
    Exec freeStep (ready s (false :: history) (tick :: pending)).store
      (1 + (MatrixFreeInstructions.fuel n s.parameters + 5))
      (ready (freeSpace s) history pending).store := by
  have popped : Exec (.action (.pop (10 : Fin 12)))
      (ready s (false :: history) (tick :: pending)).store 1
      (ready s history (tick :: pending)).store := .action _ _
  have constructed : Exec (lift MatrixFreeInstructions.block)
      (ready s history (tick :: pending)).store (MatrixFreeInstructions.fuel n s.parameters)
      (afterMap (freeSpace s) (mapBits s.forms) history (tick :: pending)).store :=
    lift_exec _ (ready s history (tick :: pending)) _
      (afterMap (freeSpace s) (mapBits s.forms) history (tick :: pending)).core
      (MatrixFreeInstructions.block_exec s.forms (mapBits s.forms))
  exact Exec.seq popped (Exec.seq constructed (reset_exec (freeSpace s) (mapBits s.forms) history pending tick))

def readPivotHeader : Block 12 :=
  .seq (.action (.pop 10)) (.seq (.action (.copy 0 10)) (.action (.copy 2 9)))

def restoreMap : Block 12 :=
  .seq (.action (.copy 10 0)) <| .seq (.action (.copy 6 3)) <|
    .seq (.action (.clear 3)) (.action (.copy 0 7))

def preparePivot : Block 12 := .seq readPivotHeader (.seq (lift copyLoop) restoreMap)

def pivotReady {n : Nat} (p : Affine n) (s : Space n) (history pending : BitString) : State :=
  ⟨MatrixPivotMapInstructions.start p s.forms (mapBits s.forms),
    List.replicate (n + 1) true, history, pending⟩

theorem preparePivot_exec {n : Nat} (p : Affine n) (s : Space n) (history pending : BitString) :
    Exec preparePivot (ready s (MatrixSweep.recordBits (some p) ++ history) pending).store
      (5 * (n + 1) + 8) (pivotReady p s history pending).store := by
  let loaded : State :=
    ⟨{base (s.parameters + 1) (mapBits s.forms) with input := (affineWord p).reverse ++ history, remaining := List.replicate (n + 1) true},
      List.replicate (n + 1) true, (affineWord p).reverse ++ history, pending⟩
  let copied : State :=
    ⟨{base (s.parameters + 1) (mapBits s.forms) with input := history, excess := affineWord p},
      List.replicate (n + 1) true, (affineWord p).reverse ++ history, pending⟩
  have header : Exec readPivotHeader
      (ready s (MatrixSweep.recordBits (some p) ++ history) pending).store 3 loaded.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have coreCopy : Exec copyLoop loaded.core.store (5 * (n + 1) + 1) copied.core.store := by
    simpa only [loaded, copied, base, List.length_reverse, affineWord_length,
      List.reverse_reverse, List.append_nil] using
      copy_exec (base (s.parameters + 1) (mapBits s.forms)) (affineWord p).reverse history
  have copy : Exec (lift copyLoop) loaded.store (5 * (n + 1) + 1) copied.store :=
    lift_exec copyLoop loaded _ copied.core coreCopy
  have restored : Exec restoreMap copied.store 4 (pivotReady p s history pending).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have checked := Exec.seq header (Exec.seq copy restored)
  have cost : 5 * (n + 1) + 8 = 3 + ((5 * (n + 1) + 1) + 4) := by omega
  simpa only [preparePivot, cost] using checked

def pivotStep : Block 12 := .seq preparePivot (.seq (lift MatrixPivotMapInstructions.block) reset)

theorem pivotStep_exec {n : Nat} (p : Affine n) (s : Space n)
    (history pending : BitString) (tick : Bool) :
    Exec pivotStep (ready s (MatrixSweep.recordBits (some p) ++ history) (tick :: pending)).store
      ((5 * (n + 1) + 8) + (MatrixPivotMapInstructions.fuel s.parameters p + 5))
      (ready (pivotSpace p s) history pending).store := by
  have prepared := preparePivot_exec p s history (tick :: pending)
  have constructed : Exec (lift MatrixPivotMapInstructions.block)
      (pivotReady p s history (tick :: pending)).store (MatrixPivotMapInstructions.fuel s.parameters p)
      (afterMap (pivotSpace p s) (mapBits s.forms) history (tick :: pending)).store :=
    lift_exec _ (pivotReady p s history (tick :: pending)) _
      (afterMap (pivotSpace p s) (mapBits s.forms) history (tick :: pending)).core
      (MatrixPivotMapInstructions.block_exec p s.forms)
  exact Exec.seq prepared (Exec.seq constructed (reset_exec (pivotSpace p s) (mapBits s.forms) history pending tick))

def body : Block 12 := .branch 10 .skip freeStep pivotStep

def bodyFuel {n : Nat} (pivot : Option (Affine n)) (s : Space n) : Nat :=
  match pivot with
  | none => 1 + (1 + (MatrixFreeInstructions.fuel n s.parameters + 5))
  | some p => 1 + ((5 * (n + 1) + 8) + (MatrixPivotMapInstructions.fuel s.parameters p + 5))

theorem body_exec {n : Nat} (pivot : Option (Affine n)) (s : Space n)
    (history pending : BitString) (tick : Bool) :
    Exec body (ready s (MatrixSweep.recordBits pivot ++ history) (tick :: pending)).store
      (bodyFuel pivot s) (ready (applyPivot pivot s) history pending).store := by
  cases pivot with
  | none => exact Exec.zero rfl (freeStep_exec s history pending tick)
  | some p => exact Exec.one rfl (pivotStep_exec p s history pending tick)

theorem bodyFuel_bound {n : Nat} (pivot : Option (Affine n)) (s : Space n) :
    bodyFuel pivot s ≤ 50 * (s.parameters + 2) * (n + 1) := by
  cases pivot with
  | none =>
    have bound := MatrixFreeInstructions.fuel_bound n s.parameters
    simp only [bodyFuel, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc] at *
    omega
  | some p =>
    have bound := MatrixPivotMapInstructions.fuel_bound s.parameters p
    simp only [bodyFuel, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc] at *
    omega

end PNP.Concrete.ResidualReduction.MatrixReconstruction

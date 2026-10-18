import PNP.Concrete.ResidualReduction.SourceMapUnitInstructions

/-! Compute one exact pulled-back coefficient, constructing both unit
directions internally and reading the encoded source matrix literally.
Protected maps and cursors survive for the complete row-major sweep. -/

namespace PNP.Concrete.ResidualReduction.SourceBilinearPullbackEntry
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra

structure State where
  core : SourceMapUnit.State
  matrix : BitString
  leftMap : BitString
  rightMap : BitString
  leftWidth : BitString
  rightWidth : BitString
  leftIndex : BitString
  rightIndex : BitString
  leftVector : BitString
def State.frame (r : State) : Store 8 :=
  .cons r.matrix <| .cons r.leftMap <| .cons r.rightMap <| .cons r.leftWidth <|
    .cons r.rightWidth <| .cons r.leftIndex <| .cons r.rightIndex (.cons r.leftVector .nil)
def State.store (r : State) : Store 18 := Frame.join r.core.store r.frame
def lifted (body : Block 10) : Block 18 := Frame.block 8 body
theorem lifted_exec (body : Block 10) (r : State) (fuel : Nat) (after : SourceMapUnit.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (lifted body) r.store fuel ({r with core := after}).store := Frame.execution checked r.frame
def small (body : Block 9) : Block 18 := lifted (SourceMapUnit.lift body)
theorem small_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.core.core.store fuel after.store) :
    Exec (small body) r.store fuel ({r with core := {r.core with core := after}}).store :=
  lifted_exec _ r _ _ (SourceMapUnit.lift_exec body r.core fuel after checked)

def stage {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) (core : SourceMapUnit.State) (leftVector : BitString) : State :=
  ⟨core, coefficientMatrixBits M, mapBits s.forms, mapBits t.forms,
    List.replicate s.parameters true, List.replicate t.parameters true,
    List.replicate i.val true, List.replicate j.val true, leftVector⟩
def start {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) : State :=
  stage M s t i j ⟨base 0 [], []⟩ []
def leftReady {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) : State :=
  stage M s t i j (SourceMapUnit.start s.forms i) []
def leftDone {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) : State :=
  stage M s t i j (SourceMapUnit.result s.forms i) []
def rightReady {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) : State :=
  stage M s t i j (SourceMapUnit.start t.forms j) ((SourceEncoding.pointCodec m).encode (s.direction (unitPoint _ i)))
def rightDone {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) : State :=
  stage M s t i j (SourceMapUnit.result t.forms j) ((SourceEncoding.pointCodec m).encode (s.direction (unitPoint _ i)))
def evalReady {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) : State :=
  stage M s t i j
    ⟨{base 0 [] with input := coefficientMatrixBits M, target := (SourceEncoding.pointCodec m).encode (s.direction (unitPoint _ i)), reserved := (SourceEncoding.pointCodec n).encode (t.direction (unitPoint _ j))}, List.replicate t.parameters true⟩
    ((SourceEncoding.pointCodec m).encode (s.direction (unitPoint _ i)))
def evalDone {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) : State :=
  stage M s t i j
    ⟨{base 0 [] with reserved := (SourceEncoding.pointCodec n).encode (t.direction (unitPoint _ j)), output := [pullMatrix M s t i j]}, List.replicate t.parameters true⟩
    ((SourceEncoding.pointCodec m).encode (s.direction (unitPoint _ i)))
def result {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) : State :=
  stage M s t i j ⟨{base 0 [] with output := [pullMatrix M s t i j]}, []⟩ []

def prepareLeft : Block 18 := .seq (.action (.copy 0 11)) <|
  .seq (.action (.copy 1 15)) <| .seq (.action (.copy 2 13)) (.action (.copy 9 13))
def prepareRight : Block 18 := .seq (.action (.copy 17 8)) <|
  .seq (.action (.clear 8)) <| .seq (.action (.clear 7)) <| .seq (.action (.copy 0 12)) <|
    .seq (.action (.copy 1 16)) <| .seq (.action (.copy 2 14)) (.action (.copy 9 14))
def prepareEval : Block 18 := .seq (.action (.copy 7 8)) <|
  .seq (.action (.copy 1 17)) <| .seq (.action (.copy 0 10)) (.action (.clear 8))
def finish : Block 18 := .seq (.action (.clear 7)) <|
  .seq (.action (.clear 17)) (.action (.clear 9))

theorem prepareLeft_exec {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) :
    Exec prepareLeft (start M s t i j).store 4 (leftReady M s t i j).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
theorem left_exec {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) :
    Exec (lifted SourceMapUnit.block) (leftReady M s t i j).store
      (SourceMapUnit.fuel m s.parameters i.val) (leftDone M s t i j).store :=
  lifted_exec _ (leftReady M s t i j) _ _ (SourceMapUnit.block_exec s.forms i)
theorem prepareRight_exec {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) :
    Exec prepareRight (leftDone M s t i j).store 7 (rightReady M s t i j).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
    (Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))))))
theorem right_exec {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) :
    Exec (lifted SourceMapUnit.block) (rightReady M s t i j).store
      (SourceMapUnit.fuel n t.parameters j.val) (rightDone M s t i j).store :=
  lifted_exec _ (rightReady M s t i j) _ _ (SourceMapUnit.block_exec t.forms j)
theorem prepareEval_exec {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) :
    Exec prepareEval (rightDone M s t i j).store 4 (evalReady M s t i j).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
theorem eval_exec {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) :
    Exec (small SourceBilinearEvaluation.block) (evalReady M s t i j).store
      (SourceBilinearEvaluation.fuel m n) (evalDone M s t i j).store :=
  small_exec _ (evalReady M s t i j) _ _
    (SourceBilinearEvaluation.block_exec (base 0 []) M (s.direction (unitPoint _ i)) (t.direction (unitPoint _ j)))
theorem finish_exec {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) :
    Exec finish (evalDone M s t i j).store 3 (result M s t i j).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def block : Block 18 := .seq prepareLeft <| .seq (lifted SourceMapUnit.block) <|
  .seq prepareRight <| .seq (lifted SourceMapUnit.block) <| .seq prepareEval <|
    .seq (small SourceBilinearEvaluation.block) finish
def fuel (m n p q i j : Nat) : Nat :=
  4 + (SourceMapUnit.fuel m p i + (7 + (SourceMapUnit.fuel n q j +
    (4 + (SourceBilinearEvaluation.fuel m n + 3)))))
theorem block_exec {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) :
    Exec block (start M s t i j).store (fuel m n s.parameters t.parameters i.val j.val) (result M s t i j).store :=
  Exec.seq (prepareLeft_exec M s t i j) (Exec.seq (left_exec M s t i j)
    (Exec.seq (prepareRight_exec M s t i j) (Exec.seq (right_exec M s t i j)
      (Exec.seq (prepareEval_exec M s t i j) (Exec.seq (eval_exec M s t i j) (finish_exec M s t i j))))))

theorem result_output {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) :
    (result M s t i j).store.get 8 = [pullMatrix M s t i j] := rfl
def budget (m n p q : Nat) : Nat :=
  4 + (SourceMapUnit.budget m p + (7 + (SourceMapUnit.budget n q +
    (4 + (SourceBilinearEvaluation.fuel m n + 3)))))
theorem fuel_bound {m n p q : Nat} (i : Fin p) (j : Fin q) :
    fuel m n p q i.val j.val ≤ budget m n p q := by
  have left := SourceMapUnit.fuel_bound (m := m) i
  have right := SourceMapUnit.fuel_bound (m := n) j
  unfold fuel budget
  omega
theorem budget_mono (m n p q M N P Q : Nat)
    (hm : m ≤ M) (hn : n ≤ N) (hp : p ≤ P) (hq : q ≤ Q) :
    budget m n p q ≤ budget M N P Q := by
  have left := SourceMapUnit.budget_mono m p M P hm hp
  have right := SourceMapUnit.budget_mono n q N Q hn hq
  have matrix := SourceBilinearEvaluation.fuel_mono m n M N hm hn
  unfold budget
  omega

end PNP.Concrete.ResidualReduction.SourceBilinearPullbackEntry

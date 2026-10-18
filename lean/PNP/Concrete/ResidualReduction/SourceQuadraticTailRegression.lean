import PNP.Concrete.ResidualReduction.SourcePlaneRemainderInstructions
import Lean

/-! Exact extraction/remainder contracts, including genuine mixed quadratic
terms, Boolean diagonals, constants, suffixes and arbitrary surrounding registers.
Runtime fixtures supplement the all-dimension proofs and do not imply a global
contraction or raw-machine complexity claim. -/

namespace PNP.Concrete.ResidualReduction.SourceQuadraticTailRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceScalarState

private def x : Affine 2 := (true,(false,false))
private def y : Affine 2 := (false,(true,false))
private def one : Affine 2 := (false,(false,true))
private def q2 : Quadratic 2 := ((true,true),(false,true))
private def q3 : Quadratic 3 := ((true,(false,true)),((true,false),(true,true)))
private def f : Affine 3 := (true,(false,(true,true)))
private def g : Affine 3 := (false,(true,(true,false)))

example : affinePart (n := 0) true = true := rfl
example : affineWord (affinePart q2) = [true,false,true] := rfl
example : affineWord (affinePart q3) = [true,false,true,true] := rfl
example : affineWord (affinePart (qProduct x x)) = [true,false,false] := rfl
example : affineWord (planeRemainder (qProduct x y) x y) = [false,false,false] := rfl
example : affineWord (planeRemainder (qProduct (aAdd x one) (aAdd y one)) x y) =
    [true,true,true] := rfl
example : affineWord (planeRemainder (zero 2) x y) = [false,false,false] := rfl
example : aEval (affinePart (qProduct x y)) (true,(true,())) = false ∧
    qEval (qProduct x y) (true,(true,())) = true := by constructor <;> rfl
example : qEq (zero 2) (qAdd (qProduct x y)
    (qOfAffine (planeRemainder (zero 2) x y))) = false := rfl
example : SourceQuadraticDiagonal.fuel 0 = 4 := rfl
example : SourceQuadraticDiagonal.forwardFuel 0 = 11 := rfl
example : SourceQuadraticDiagonal.forwardFuel 2 = 36 := rfl
example : SourcePlaneRemainderInstructions.fuel 2 = 310 := rfl

example {n : Nat} (a : Affine n) (q : Quadratic n) :
    affinePart (n := n + 1) (a,q) = (aConstant a,affinePart q) :=
  SourceQuadraticDiagonalAlgebra.affinePart_cons a q
example (r : Registers) {n : Nat} (q : Quadratic n) (suffix : BitString) :
    Exec SourceQuadraticDiagonal.block (SourceQuadraticDiagonal.ready r q suffix).store
      (SourceQuadraticDiagonal.fuel n)
      ({r with input := suffix,target := [],remaining := [],output := (affineWord (affinePart q)).reverse ++ r.output}).store :=
  SourceQuadraticDiagonal.block_exec r q suffix
example (r : Registers) {n : Nat} (q : Quadratic n) (suffix : BitString) :
    Exec SourceQuadraticDiagonal.forwardBlock
      (SourceQuadraticDiagonal.ready {r with output := []} q suffix).store (SourceQuadraticDiagonal.forwardFuel n)
      ({r with input := suffix,target := [],remaining := [],excess := [],output := affineWord (affinePart q)}).store :=
  SourceQuadraticDiagonal.forward_exec r q suffix
example {n : Nat} (q : Quadratic n) (a b : Affine n) :
    Exec SourcePlaneRemainderInstructions.block
      (initial n (SourcePlaneRemainderInstructions.packet q a b))
      (SourcePlaneRemainderInstructions.fuel n) (SourcePlaneRemainderInstructions.finished q a b) :=
  SourcePlaneRemainderInstructions.block_exec q a b
example {n : Nat} (q : Quadratic n) (a b : Affine n) :
    SourcePlaneRemainderInstructions.fuel n ≤ 40 * (SourcePlaneRemainderInstructions.packet q a b).length :=
  SourcePlaneRemainderInstructions.fuel_source_bound q a b

private def surrounding : Registers :=
  ⟨[true,false],[false,false],[true,false],[true,false,true],[false,true],
    [true,true],[true,false,true],[false,false,true],[true,false,false]⟩
private def suffix : BitString := [false,true,false,true,true]

private def expectStore {k : Nat} (final : BitRegister.Configuration k) (expected : Store k) (label : String) : IO Unit := do
  if final.control != .accepted then
    throw (IO.userError (label ++ ": instruction bound exhausted"))
  for index in List.finRange k do
    if final.store.get index != expected.get index then
      throw (IO.userError (label ++ ": exact register-state mismatch"))

private def checkDiagonal {n : Nat} (q : Quadratic n) : IO Unit := do
  let reverseRun := BitRegister.run (SourceQuadraticDiagonal.block.program 0 8)
    (SourceQuadraticDiagonal.fuel n + 1)
    ⟨.running 0,(SourceQuadraticDiagonal.ready surrounding q suffix).store⟩
  let reverseExpected := {surrounding with input := suffix,target := [],remaining := [],output := (affineWord (affinePart q)).reverse ++ surrounding.output}
  expectStore reverseRun reverseExpected.store "Reversed affine extraction"
  let forwardRun := BitRegister.run (SourceQuadraticDiagonal.forwardBlock.program 0 8)
    (SourceQuadraticDiagonal.forwardFuel n + 1)
    ⟨.running 0,(SourceQuadraticDiagonal.ready {surrounding with output := []} q suffix).store⟩
  let forwardExpected := {surrounding with input := suffix,target := [],remaining := [],excess := [],output := affineWord (affinePart q)}
  expectStore forwardRun forwardExpected.store "Canonical affine extraction"

private def checkRemainder {n : Nat} (q : Quadratic n) (a b : Affine n) : IO Unit := do
  let final := BitRegister.run (SourcePlaneRemainderInstructions.block.program 0 8)
    (SourcePlaneRemainderInstructions.fuel n + 1)
    ⟨.running 0,initial n (SourcePlaneRemainderInstructions.packet q a b)⟩
  expectStore final (SourcePlaneRemainderInstructions.finished q a b) "Complete plane remainder"

private def checkLoad {n : Nat} (q : Quadratic n) : IO Unit := do
  let acc := qAdd q (qOfAffine (aConst n true))
  let before := full (work (SourceQuadraticEncoding.word q ++ suffix)) emptySaved (data [true,false,true] acc)
  let final := BitRegister.run (SourcePlaneRemainderInstructions.loadPolynomial.program 0 8)
    (SourcePlaneRemainderInstructions.loadFuel n + 1) ⟨.running 0,before⟩
  expectStore final (state suffix q) "Quadratic loading and suffix preservation"

#eval (show IO Unit from do
  for c in [false,true] do
    checkDiagonal (n := 0) c
    for a in [false,true] do
      for b in [false,true] do checkRemainder (n := 0) c a b
    for a in [false,true] do
      checkDiagonal (n := 1) (a,c)
      for f in [(true,false),(true,true)] do
        for g in [(true,false),(true,true)] do checkRemainder (n := 1) (a,c) f g
      for b in [false,true] do
        for d in [false,true] do checkDiagonal (n := 2) ((a,b),(d,c))
  checkDiagonal q3
  checkDiagonal (qProduct f g)
  checkDiagonal (qAdd q3 (qProduct f g))
  checkDiagonal (qOfAffine (aConst 5 true))
  for q in [q2,qProduct x y,qProduct (aAdd x one) (aAdd y one)] do
    checkRemainder q x y
    checkRemainder q (aAdd x one) (aAdd y one)
    checkRemainder q x x
  checkRemainder q3 f g
  checkRemainder (qProduct f g) f g
  checkRemainder (qAdd q3 (qProduct f g)) (aAdd f g) (aConst 3 true)
  checkRemainder (qOfAffine (aConst 5 true)) (aConst 5 false) (aConst 5 true)
  checkLoad (n := 0) true
  checkLoad q2
  checkLoad q3
  checkLoad (qProduct f g)
  IO.println "QUADRATIC_TAIL_RUNTIME_REGRESSIONS_GREEN: 93 executions")

run_cmd do
  for name in [
    ``SourceQuadraticDiagonalAlgebra.affinePart_zero,
    ``SourceQuadraticDiagonalAlgebra.affinePart_cons,
    ``SourceQuadraticDiagonalAlgebra.diagonal_eq,
    ``SourceQuadraticDiagonalAlgebra.diagonal_constant,
    ``SourceQuadraticDiagonalAlgebra.constant_eval,
    ``SourceQuadraticDiagonalAlgebra.output_split,
    ``SourceQuadraticDiagonalAlgebra.normal_cons,
    ``SourceQuadraticDiagonalAlgebra.dimension_bound,
    ``SourceQuadraticDiagonal.take_exec,
    ``SourceQuadraticDiagonal.body_exec,
    ``SourceQuadraticDiagonal.loop_exec,
    ``SourceQuadraticDiagonal.block_exec,
    ``SourceQuadraticDiagonal.loopFuel_exact,
    ``SourceQuadraticDiagonal.fuel_exact,
    ``SourceQuadraticDiagonal.forward_exec,
    ``SourceQuadraticDiagonal.forwardFuel_exact,
    ``SourceQuadraticDiagonal.forwardFuel_source_bound,
    ``SourcePlaneRemainderInstructions.packet_length,
    ``SourcePlaneRemainderInstructions.load_exec,
    ``SourcePlaneRemainderInstructions.extract_exec,
    ``SourcePlaneRemainderInstructions.block_exec,
    ``SourcePlaneRemainderInstructions.productLoopFuel_exact,
    ``SourcePlaneRemainderInstructions.productFuel_exact,
    ``SourcePlaneRemainderInstructions.fuel_exact,
    ``SourcePlaneRemainderInstructions.fuel_source_bound,
    ``SourcePlaneRemainderInstructions.output_get,
    ``SourcePlaneRemainderInstructions.output_decode,
    ``SourcePlaneRemainderInstructions.output_length,
    ``SourcePlaneRemainderInstructions.output_source_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceQuadraticDiagonalAlgebra.affinePart_cons
#print axioms PNP.Concrete.ResidualReduction.SourceQuadraticDiagonal.forward_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePlaneRemainderInstructions.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePlaneRemainderInstructions.fuel_source_bound

end PNP.Concrete.ResidualReduction.SourceQuadraticTailRegression

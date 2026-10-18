import PNP.Concrete.ResidualReduction.SourceQuadraticProduct
import Lean

/-! Exact product contracts, constant/diagonal boundary fixtures, arbitrary
surrounding state, executable output checks and strict axiom-closure guards.
Finite fixtures supplement the arbitrary-dimension proofs, not replace them. -/

namespace PNP.Concrete.ResidualReduction.SourceQuadraticProduct.Regression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions

private def x : Affine 2 := (true,(false,false))
private def y : Affine 2 := (false,(true,false))
private def one : Affine 2 := (false,(false,true))
private def f : Affine 3 := (true,(false,(true,true)))
private def g : Affine 3 := (false,(true,(true,false)))

example : SourceQuadraticEncoding.word (qProduct (n := 0) false true) = [false] := rfl
example : SourceQuadraticEncoding.word (qProduct (n := 0) true true) = [true] := rfl
example : SourceQuadraticEncoding.word (qProduct x x) = [false,true,false,false] := rfl
example : SourceQuadraticEncoding.word (qProduct x y) = [true,false,false,false] := rfl
example : SourceQuadraticEncoding.word (qProduct x one) = [false,true,false,false] := rfl
example : SourceQuadraticEncoding.word (qProduct one one) = [false,false,false,true] := rfl
example : SourceQuadraticEncoding.word (qProduct (aAdd x one) (aAdd x one)) =
    [false,true,false,true] := rfl
example : (SourceQuadraticEncoding.word (qProduct f g)).length = 7 := rfl
example : fuel 0 = 6 := rfl
example : fuel 3 = 78 := rfl
example : forwardFuel 0 = 13 := rfl
example : forwardFuel 3 = 109 := rfl

example {n : Nat} (p q : Quadratic n) :
    SourceQuadraticEncoding.word (qAdd p q) =
      List.zipWith Bool.xor (SourceQuadraticEncoding.word p) (SourceQuadraticEncoding.word q) :=
  SourceQuadraticEncoding.word_add p q
example {n : Nat} (r : Registers) (s : Saved) (a b : Affine n) :
    ∃ after : Saved, Exec block (full (ready r a b) s) (fuel n)
      (full {r with input := [],mode := [],target := [],remaining := [],output := (SourceQuadraticEncoding.word (qProduct a b)).reverse ++ r.output} after) :=
  block_exec r s a b
example {n : Nat} (r : Registers) (s : Saved) (a b : Affine n) :
    ∃ after : Saved, Exec forwardBlock (full (ready {r with output := []} a b) s) (forwardFuel n)
      (full {r with input := [],mode := [],target := [],remaining := [],excess := [],output := SourceQuadraticEncoding.word (qProduct a b)} after) :=
  forward_exec r s a b
example {n : Nat} (a b : Affine n) :
    let L := (affineWord a ++ affineWord b).length
    forwardFuel n ≤ (7 * L + 17) * L + 4 * ((L + 1) * (L + 1)) + 9 :=
  sourceFuel_bound a b

private def surrounding : Registers :=
  ⟨[false,true],[false],[true,false],[true,false,true],[true,false],
    [false,false],[true,true],[false,true,false],[true,false,false,true]⟩
private def saved : Saved := ⟨[true,false,true],[false,true,false]⟩

private def checkProduct {n : Nat} (a b : Affine n) : IO Unit := do
  let expected := SourceQuadraticEncoding.word (qProduct a b)
  let reverseRun := BitRegister.run (block.program 0 8) (fuel n + 1)
    ⟨.running 0,full (ready surrounding a b) saved⟩
  if reverseRun.control != .accepted || reverseRun.store.get 8 != expected.reverse ++ surrounding.output ||
      reverseRun.store.get 0 != [] || reverseRun.store.get 1 != [] ||
      reverseRun.store.get 2 != [] || reverseRun.store.get 5 != [] ||
      reverseRun.store.get 3 != surrounding.excess || reverseRun.store.get 4 != surrounding.sign ||
      reverseRun.store.get 6 != surrounding.active || reverseRun.store.get 7 != surrounding.reserved then
    throw (IO.userError "Reversed literal product regression failed")
  let forwardRun := BitRegister.run (forwardBlock.program 0 8) (forwardFuel n + 1)
    ⟨.running 0,full (ready {surrounding with output := []} a b) saved⟩
  if forwardRun.control != .accepted || forwardRun.store.get 8 != expected ||
      forwardRun.store.get 0 != [] || forwardRun.store.get 1 != [] || forwardRun.store.get 2 != [] ||
      forwardRun.store.get 3 != [] || forwardRun.store.get 5 != [] ||
      forwardRun.store.get 4 != surrounding.sign || forwardRun.store.get 6 != surrounding.active ||
      forwardRun.store.get 7 != surrounding.reserved then
    throw (IO.userError "Canonical literal product regression failed")
  let lastLeft := if n == 0 then saved.left else [aConstant a]
  let lastRight := if n == 0 then saved.right else [aConstant b]
  if reverseRun.store.get 9 != lastLeft || reverseRun.store.get 10 != lastRight ||
      forwardRun.store.get 9 != lastLeft || forwardRun.store.get 10 != lastRight then
    throw (IO.userError "Product saved-tail preservation regression failed")
  if expected.length != quadraticBits n then
    throw (IO.userError "Product output width regression failed")

private def checkHead {n : Nat} (d e : Bool) (a b : Affine n) : IO Unit := do
  let leftSuffix := [true,false,true]
  let rightSuffix := [false,false,true]
  let before := {surrounding with input := affineWord a ++ leftSuffix,mode := affineWord b ++ rightSuffix,remaining := List.replicate n true}
  let final := BitRegister.run ((SourceQuadraticHead.block d e).program 0 8)
    (SourceQuadraticHead.fuel n + 1) ⟨.running 0,before.store⟩
  if final.control != .accepted || final.store.get 0 != leftSuffix ||
      final.store.get 5 != rightSuffix || final.store.get 2 != [] ||
      final.store.get 8 != (affineWord (SourceQuadraticHead.head d e a b)).reverse ++ surrounding.output ||
      final.store.get 1 != surrounding.target || final.store.get 3 != surrounding.excess ||
      final.store.get 4 != surrounding.sign || final.store.get 6 != surrounding.active ||
      final.store.get 7 != surrounding.reserved then
    throw (IO.userError "Product head constant or surrounding-state regression failed")

#eval (show IO Unit from do
  for a in [false,true] do
    for b in [false,true] do
      checkProduct (n := 0) a b
      checkHead (n := 0) a b true false
      checkHead a b f g
  checkProduct (n := 1) (false,false) (true,true)
  checkProduct (n := 1) (true,false) (true,false)
  checkProduct (n := 1) (true,true) (true,false)
  checkProduct (n := 1) (false,true) (false,true)
  checkProduct x x
  checkProduct x y
  checkProduct x one
  checkProduct (aAdd x one) (aAdd x one)
  checkProduct f g
  checkProduct (aAdd f (aConst 3 true)) (aAdd g (aConst 3 true))
  IO.println "QUADRATIC_PRODUCT_RUNTIME_REGRESSIONS_GREEN: 36 executions")

run_cmd do
  for name in [
    ``SourceQuadraticEncoding.word_zero_dimension,
    ``SourceQuadraticEncoding.word_cons,
    ``SourceQuadraticEncoding.roundtrip,
    ``SourceQuadraticEncoding.word_length,
    ``SourceQuadraticEncoding.word_add,
    ``SourceQuadraticEncoding.affine_zero_word,
    ``SourceQuadraticEncoding.word_zero,
    ``SourceQuadraticEncoding.word_bound,
    ``SourceQuadraticHead.head_normal,
    ``SourceQuadraticHead.head_constant,
    ``SourceQuadraticHead.head_word,
    ``SourceQuadraticHead.product_word,
    ``SourceQuadraticHead.finish_exec,
    ``SourceQuadraticHead.block_exec,
    ``SourceQuadraticProduct.word_split,
    ``SourceQuadraticProduct.readLeft_exec,
    ``SourceQuadraticProduct.readRight_exec,
    ``SourceQuadraticProduct.body_exec,
    ``SourceQuadraticProduct.loop_exec,
    ``SourceQuadraticProduct.finish_exec,
    ``SourceQuadraticProduct.block_exec,
    ``SourceQuadraticProduct.loopFuel_bound,
    ``SourceQuadraticProduct.fuel_bound,
    ``SourceQuadraticProduct.forward_exec,
    ``SourceQuadraticProduct.forwardFuel_bound,
    ``SourceQuadraticProduct.sourceFuel_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceQuadraticProduct.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceQuadraticProduct.forward_exec
#print axioms PNP.Concrete.ResidualReduction.SourceQuadraticProduct.sourceFuel_bound

end PNP.Concrete.ResidualReduction.SourceQuadraticProduct.Regression

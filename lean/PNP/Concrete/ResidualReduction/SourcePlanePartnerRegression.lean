import PNP.Concrete.ResidualReduction.SourcePlanePartnerInstructions
import Lean

/-! Exact row-coefficient and ordered-partner regressions. Small exhaustive
fixtures are tests only; the program itself constructs seven prescribed
candidates and does not enumerate affine functions. General theorems cover
all dimensions, constants, degenerate normals, duplicates and failed lookups. -/

namespace PNP.Concrete.ResidualReduction.SourcePlanePartnerRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourcePlanePartnerSpecification

private def x : Affine 2 := (true,(false,false))
private def y : Affine 2 := (false,(true,false))
private def z : Affine 2 := aConst 2 false
private def one : Affine 2 := aConst 2 true
private def a5 : Affine 5 := (true,(false,(true,(false,(true,true)))))
private def b5 : Affine 5 := (false,(true,(true,(false,(false,true)))))

example : aEq x (aAdd x one) = false := rfl
example : affineWord (aAdd x one) = [true,false,true] := rfl
example : planePartner x y z = some z := rfl
example : planePartner x y x = some y := rfl
example : planePartner x y (aAdd x one) = some z := rfl
example : planePartner x y y = some x := rfl
example : planePartner x y (aAdd y one) = some z := rfl
example : planePartner x y (aAdd x y) = some z := rfl
example : planePartner x y (aAdd (aAdd x y) one) = some x := rfl
example : planePartner x y one = none := rfl
example : planePartner z y z = some z := rfl
example : planePartner x x x = some x := rfl
example : planePartner (n := 0) false true false = some false := rfl
example : planePartner (n := 0) false true true = some false := rfl
example : (SourcePlanePartnerInstructions.codec 2).encode none = [false] := rfl
example : (SourcePlanePartnerInstructions.codec 2).encode (some x) = [true,true,false,false] := rfl
example : (SourcePlanePartnerInstructions.codec 2).decode [true] = none := rfl
example {n : Nat} (a b f : Affine n) :
    SourcePlanePartnerSpecification.lookup a b f entries = planePartner a b f :=
  lookup_existing a b f
example {n : Nat} (a b f : Affine n) :
    Exec SourcePlanePartnerInstructions.block (SourcePlanePartnerBuilder.initial a b f)
      (SourcePlanePartnerInstructions.fuel a b f) (SourcePlanePartnerInstructions.finished a b f) :=
  SourcePlanePartnerInstructions.block_exec a b f
example {n : Nat} (a b f : Affine n) :
    SourcePlanePartnerInstructions.fuel a b f ≤
      121 * (SourcePlanePartnerInstructions.operandBytes a b f).length :=
  SourcePlanePartnerInstructions.fuel_operand_bound a b f
example {n : Nat} (a b f : Affine n) :
    (SourcePlanePartnerInstructions.codec n).decode ((SourcePlanePartnerInstructions.finished a b f).get 8) =
      some (planePartner a b f) := SourcePlanePartnerInstructions.output_decode a b f

private def surrounding : Registers :=
  ⟨[true,false],[false,true],[true,true],[false,true,false],[true,false,true],
    [false,false,true],[true,false],[false,true,true],[true,false,false]⟩

private def expectStore {k : Nat} (count : IO.Ref Nat)
    (final : BitRegister.Configuration k) (expected : Store k) (label : String) : IO Unit := do
  if final.control != .accepted then throw (IO.userError (label ++ ": instruction bound exhausted"))
  for i in List.finRange k do
    if final.store.get i != expected.get i then throw (IO.userError (label ++ ": exact state mismatch"))
  count.modify (· + 1)

private def checkBinary {n : Nat} (count : IO.Ref Nat) (a b : Affine n) : IO Unit := do
  let start := (SourceRowCoefficientInstructions.binaryReady surrounding a b).store
  let add := BitRegister.run (SourceRowCoefficientInstructions.add.program 0 8)
    (11 * (n + 1) + 4) ⟨.running 0,start⟩
  expectStore count add (SourceRowCoefficientInstructions.added surrounding a b).store "Coefficient addition"
  let equal := BitRegister.run (SourceRowCoefficientInstructions.equal.program 0 6)
    (12 * (n + 1) + 6) ⟨.running 0,start⟩
  expectStore count equal (SourceRowCoefficientInstructions.compared surrounding a b).store "Full coefficient equality"

private def checkToggle {n : Nat} (count : IO.Ref Nat) (a : Affine n) : IO Unit := do
  let final := BitRegister.run (SourceRowCoefficientInstructions.toggle.program 0 8)
    (9 * (n + 1) + 3) ⟨.running 0,(SourceRowCoefficientInstructions.unaryReady surrounding a).store⟩
  expectStore count final (SourceRowCoefficientInstructions.toggled surrounding a).store "Constant-only toggle"

private def checkZero (count : IO.Ref Nat) (n : Nat) : IO Unit := do
  let before := {surrounding with target := List.replicate (n + 1) true,remaining := [],output := []}
  let expected := {surrounding with target := List.replicate (n + 1) true,remaining := [],output := affineWord (aConst n false)}
  let final := BitRegister.run (SourceRowCoefficientInstructions.zero.program 0 8)
    (3 * (n + 1) + 3) ⟨.running 0,before.store⟩
  expectStore count final expected.store "Constructed zero coefficients"

private def checkPartner {n : Nat} (count : IO.Ref Nat) (a b f : Affine n) : IO Unit := do
  let ticks := SourcePlanePartnerInstructions.fuel a b f
  if ticks > 121 * (SourcePlanePartnerInstructions.operandBytes a b f).length then
    throw (IO.userError "Partner lookup: encoded operand bound")
  let final := BitRegister.run (SourcePlanePartnerInstructions.block.program 0 8)
    (ticks + 1) ⟨.running 0,SourcePlanePartnerBuilder.initial a b f⟩
  expectStore count final (SourcePlanePartnerInstructions.finished a b f) "Complete ordered partner lookup"
  if final.store.get 8 != (SourcePlanePartnerInstructions.codec n).encode (planePartner a b f) then
    throw (IO.userError "Partner lookup: original semantic result mismatch")

private def checkCandidate (count : IO.Ref Nat) (flag : Bool) (c : Candidate) : IO Unit := do
  let final := BitRegister.run ((SourcePlanePartnerBuilder.generate c).program 0 8)
    (SourcePlanePartnerBuilder.generateFuel 2 c + 1)
    ⟨.running 0,SourcePlanePartnerBuilder.state x y one flag []⟩
  expectStore count final (SourcePlanePartnerBuilder.state x y one flag (affineWord (value x y c)))
    "Candidate construction and flag preservation"

private def fixtures : (n : Nat) → List (Affine n)
  | 0 => [false,true]
  | n + 1 => (fixtures n).flatMap fun rest => [(false,rest),(true,rest)]

#eval (show IO Unit from do
  let count ← IO.mkRef 0
  for n in [0,1,2] do
    for a in fixtures n do
      checkToggle count a
      for b in fixtures n do
        checkBinary count a b
        for f in fixtures n do checkPartner count a b f
  for n in List.range 6 do checkZero count n
  for c in [Candidate.zero,.left,.right,.leftOne,.rightOne,.sum,.sumOne] do
    for flag in [false,true] do checkCandidate count flag c
    checkPartner count a5 b5 (value a5 b5 c)
  checkPartner count a5 b5 (aConst 5 true)
  checkPartner count (aConst 16 true) (aConst 16 false) (aConst 16 true)
  checkPartner count (aConst 16 true) (aConst 16 false) (aConst 16 false)
  IO.println s!"PLANE_PARTNER_RUNTIME_REGRESSIONS_GREEN: {← count.get} executions")

run_cmd do
  for name in [
    ``SourceRowCoefficientAlgebra.nonzero_append,
    ``SourceRowCoefficientAlgebra.nonzero_reverse,
    ``SourceRowCoefficientAlgebra.equal_word,
    ``SourceRowCoefficientAlgebra.zero_word,
    ``SourceRowCoefficientAlgebra.toggle_word,
    ``SourceRowCoefficientInstructions.zero_exec,
    ``SourceRowCoefficientInstructions.add_exec,
    ``SourceRowCoefficientInstructions.toggle_exec,
    ``SourceRowCoefficientInstructions.zeroBody_exec,
    ``SourceRowCoefficientInstructions.zeroLoop_exec,
    ``SourceRowCoefficientInstructions.equal_exec,
    ``SourcePlanePartnerSpecification.lookup_eq,
    ``SourcePlanePartnerSpecification.entries_eq,
    ``SourcePlanePartnerSpecification.lookup_existing,
    ``SourcePlanePartnerBuilder.core_exec,
    ``SourcePlanePartnerBuilder.initialize_exec,
    ``SourcePlanePartnerBuilder.sum_exec,
    ``SourcePlanePartnerBuilder.flip_exec,
    ``SourcePlanePartnerBuilder.generate_exec,
    ``SourcePlanePartnerBuilder.generateFuel_bound,
    ``SourcePlanePartnerBuilder.compare_exec,
    ``SourcePlanePartnerBuilder.choose_exec,
    ``SourcePlanePartnerInstructions.search_exec,
    ``SourcePlanePartnerInstructions.searchFuel_bound,
    ``SourcePlanePartnerInstructions.serialize_exec,
    ``SourcePlanePartnerInstructions.block_exec,
    ``SourcePlanePartnerInstructions.fuel_bound,
    ``SourcePlanePartnerInstructions.fuel_operand_bound,
    ``SourcePlanePartnerInstructions.output_get,
    ``SourcePlanePartnerInstructions.output_decode,
    ``SourcePlanePartnerInstructions.result_flag,
    ``SourcePlanePartnerInstructions.output_bound,
    ``SourcePlanePartnerInstructions.program_run] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceRowCoefficientInstructions.equal_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePlanePartnerInstructions.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePlanePartnerInstructions.fuel_operand_bound
#print axioms PNP.Concrete.ResidualReduction.SourcePlanePartnerInstructions.program_run

end PNP.Concrete.ResidualReduction.SourcePlanePartnerRegression

import PNP.Concrete.ResidualReduction.SourceComputedTailInstructions
import Lean

/-! The all-dimension constructor is checked against exact byte and state
contracts. Fixtures exercise constants, every pivot in several dimensions,
mixed quadratics, both branches, preserved suffixes and rejection boundaries.
These executions supplement the general proofs; they are not milestone credit. -/

namespace PNP.Concrete.ResidualReduction.SourceComputedTailRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceScalarState (work data emptySaved zero)
open PNP.Concrete.ResidualReduction.SourceComputedTailState
open PNP.Concrete.ResidualReduction.SourceComputedTailEncoding

private def x : Affine 2 := (true,(false,false))
private def y : Affine 2 := (false,(true,false))
private def a : Affine 3 := (true,(false,(true,true)))
private def b : Affine 3 := (false,(true,(false,true)))
private def q2 : Quadratic 2 := ((true,true),(false,true))

example : affineWord (tailNormal (n := 0) 0 (true,true)) = [false] := rfl
example : affineWord (tailNormal (n := 2) 0 a) = [false,true,false] := rfl
example : affineWord (tailNormal (n := 2) 1 a) = [true,true,false] := rfl
example : affineWord (tailNormal (n := 2) 2 a) = [true,false,false] := rfl
example : tailNormal (n := 2) 1 (aConst 3 true) = aConst 2 false := rfl
example : (codec 0).encode (.affine true) = [false,true] := rfl
example : (codec 0).encode (.plane false true true) = [true,false,true,true] := rfl
example : packet (n := 0) true none = [false,true] := rfl
example : packet (n := 0) false (some ((true,true),(false,true))) =
    [true,true,true,false,true,false] := rfl
example : (codec 2).decode [] = none := rfl
example : (codec 0).decode [true,false] = none := rfl
example : (codec 0).decode [false,true,false] = none := rfl
example : (codec 0).encode (computed (n := 0) true 0 (some ((true,true),(false,true)))) =
    [true,false,false,true] := rfl
example : qEq (qProduct x y) (computed (qProduct x y) 2 (some (a,b))).polynomial = true := rfl
example : qEq (zero 2) (computed (zero 2) 2 (some (a,b))).polynomial = false := rfl
example : qEq (qProduct x y) (computed (qProduct x y) 2 none).polynomial = false := rfl
example : SourceComputedTailInstructions.fuel 0 0 false = 46 := rfl
example : SourceComputedTailInstructions.fuel 0 0 true = 206 := rfl
example : SourceComputedTailInstructions.fuel 2 2 true = 510 := rfl
example {n : Nat} (q : Quadratic n) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    Exec SourceComputedTailInstructions.block (SourceComputedTailState.initial (packet q normals) k)
      (SourceComputedTailInstructions.fuel n k.val normals.isSome)
      (SourceComputedTailInstructions.finished q k normals) :=
  SourceComputedTailInstructions.block_exec q k normals
example {n : Nat} (q : Quadratic n) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    SourceComputedTailInstructions.fuel n k.val normals.isSome ≤ 46 * (packet q normals).length :=
  SourceComputedTailInstructions.fuel_source_bound q k normals
example {n : Nat} (q : Quadratic n) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    (codec n).decode ((SourceComputedTailInstructions.finished q k normals).get 8) =
      some (computed q k normals) := SourceComputedTailInstructions.output_decode q k normals

private def expectStore {k : Nat} (count : IO.Ref Nat)
    (final : BitRegister.Configuration k) (expected : Store k) (label : String) : IO Unit := do
  if final.control != .accepted then
    throw (IO.userError (label ++ ": instruction bound exhausted"))
  for index in List.finRange k do
    if final.store.get index != expected.get index then
      throw (IO.userError (label ++ ": exact register-state mismatch"))
  count.modify (· + 1)

private def checkComplete {n : Nat} (count : IO.Ref Nat) (q : Quadratic n) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : IO Unit := do
  let ticks := SourceComputedTailInstructions.fuel n k.val normals.isSome
  let input := packet q normals
  if ticks > 46 * input.length then throw (IO.userError "Computed tail: source-size bound")
  let final := BitRegister.run (SourceComputedTailInstructions.block.program 0 8) (ticks + 1)
    ⟨.running 0,SourceComputedTailState.initial input k⟩
  expectStore count final (SourceComputedTailInstructions.finished q k normals) "Computed tail"
  if ((codec n).decode (final.store.get 8)).map (codec n).encode !=
      some ((codec n).encode (computed q k normals)) then
    throw (IO.userError "Computed tail: encoded output round trip")

private def checkNormal {n : Nat} (count : IO.Ref Nat) (f : Affine (n + 1)) (k : Fin (n + 1)) : IO Unit := do
  let final := BitRegister.run (SourceTailNormal.block.program 0 8) (SourceTailNormal.fuel n k.val + 1)
    ⟨.running 0,(SourceTailNormal.ready f k).store⟩
  expectStore count final (SourceTailNormal.finished f k).store "Original-to-tail normal"

private def checkPair {n : Nat} (count : IO.Ref Nat) (f g : Affine (n + 1))
    (q : Quadratic n) (k : Fin (n + 1)) : IO Unit := do
  let suffix := [false,true,false,false,true]
  let input := affineWord f ++ (affineWord g ++ suffix)
  let before := full (work input) emptySaved (data [true,false,true] q)
    (extras k [true,false] [false,true,true])
  let expected := full (work suffix) emptySaved (data suffix q)
    (extras k (affineWord (tailNormal k f)) (affineWord (tailNormal k g)))
  let final := BitRegister.run (SourceComputedTailNormals.pair.program 0 8)
    (SourceComputedTailNormals.pairFuel n k.val + 1) ⟨.running 0,before⟩
  expectStore count final expected "Paired normals and suffix preservation"

private def checkPrepend (count : IO.Ref Nat) (word : BitString) (right : Bool) : IO Unit := do
  let out := [false,true,false,true]
  let extra : Extra := ⟨[true,false,true],word,word.reverse⟩
  let metadata := data [true,false,true] q2
  let chosen := SourceComputedTailInstructions.selected extra right
  let before := full {work [] with output := out} emptySaved metadata extra
  let expected := full {work [] with output := chosen ++ out} emptySaved metadata extra
  let final := BitRegister.run ((SourceComputedTailInstructions.prepend right).program 0 8)
    (8 * chosen.length + 9) ⟨.running 0,before⟩
  expectStore count final expected "Serialization and frame preservation"

#eval (show IO Unit from do
  let count ← IO.mkRef 0
  for c in [false,true] do
    checkComplete count (n := 0) c 0 none
    for f in [(false,false),(false,true),(true,false),(true,true)] do
      for g in [(false,false),(false,true),(true,false),(true,true)] do
        checkComplete count (n := 0) c 0 (some (f,g))
    for d in [false,true] do
      for k in List.finRange 2 do
        checkComplete count (n := 1) (d,c) k none
        for f in [(true,(false,false)),(false,(true,true)),(false,(false,true))] do
          for g in [(true,(false,false)),(false,(true,true)),(false,(false,true))] do
            checkComplete count (n := 1) (d,c) k (some (f,g))
  for k in List.finRange 3 do
    for q in [qProduct x y,q2,zero 2] do
      checkComplete count q k none
      for pair in [(a,b),(a,a),(b,a)] do checkComplete count q k (some pair)
    checkNormal count a k
    checkNormal count b k
    checkNormal count (aConst 3 true) k
    checkPair count a b q2 k
  for k in List.finRange 6 do
    checkComplete count (zero 5) k none
    checkComplete count (zero 5) k (some (aConst 6 true,aConst 6 false))
    checkNormal count (aConst 6 true) k
  for word in [[],[true],[false,true],[true,false,false,true]] do
    for right in [false,true] do checkPrepend count word right
  IO.println s!"COMPUTED_TAIL_RUNTIME_REGRESSIONS_GREEN: {← count.get} executions")

run_cmd do
  for name in [
    ``SourceTailNormalAlgebra.cut_homogeneous,
    ``SourceTailNormalAlgebra.tailNormal_eq,
    ``SourceTailNormalAlgebra.homogeneous_word,
    ``SourceTailNormalAlgebra.tailNormal_word,
    ``SourceTailNormal.block_exec,
    ``SourceTailNormal.fuel_bound,
    ``SourceTailNormal.fuel_source_bound,
    ``SourceComputedTailEncoding.affine_bytes,
    ``SourceComputedTailEncoding.plane_bytes,
    ``SourceComputedTailEncoding.roundtrip,
    ``SourceComputedTailEncoding.bytes_bound,
    ``SourceComputedTailEncoding.packet_none,
    ``SourceComputedTailEncoding.packet_some,
    ``SourceComputedTailEncoding.packet_none_length,
    ``SourceComputedTailEncoding.packet_some_length,
    ``SourceComputedTailEncoding.packet_roundtrip,
    ``SourceComputedTailEncoding.computed_eq,
    ``SourceComputedTailState.core_exec,
    ``SourceComputedTailState.scalar_exec,
    ``SourceComputedTailState.product_exec,
    ``SourceComputedTailState.output_get,
    ``SourceComputedTailState.pivot_get,
    ``SourceComputedTailState.left_get,
    ``SourceComputedTailState.right_get,
    ``SourceComputedTailNormals.block_exec,
    ``SourceComputedTailNormals.pair_exec,
    ``SourceComputedTailNormals.pairFuel_bound,
    ``SourceComputedTailInstructions.prepend_exec,
    ``SourceComputedTailInstructions.serialize_exec,
    ``SourceComputedTailInstructions.affine_exec,
    ``SourceComputedTailInstructions.plane_exec,
    ``SourceComputedTailInstructions.block_exec,
    ``SourceComputedTailInstructions.affineFuel_exact,
    ``SourceComputedTailInstructions.planeFuel_exact,
    ``SourceComputedTailInstructions.fuel_source_bound,
    ``SourceComputedTailInstructions.output_get,
    ``SourceComputedTailInstructions.output_decode,
    ``SourceComputedTailInstructions.output_bound,
    ``SourceComputedTailInstructions.output_existing] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceComputedTailInstructions.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceComputedTailInstructions.fuel_source_bound
#print axioms PNP.Concrete.ResidualReduction.SourceComputedTailInstructions.output_existing

end PNP.Concrete.ResidualReduction.SourceComputedTailRegression

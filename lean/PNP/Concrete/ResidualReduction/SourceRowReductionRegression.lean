import PNP.Concrete.ResidualReduction.SourceRowReductionInstructions
import Lean

/-! Whole-row transformation regressions. Finite fixtures are tests, not the
program's definition or proof boundary. The general execution theorems cover
all dimensions, both tail kinds, all leading-bit cases and arbitrary suffixes.
The audit rejects project axioms and classical choice in every new theorem. -/

namespace PNP.Concrete.ResidualReduction.SourceRowReductionRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceRowReductionState

private def x : Affine 2 := (true,(false,false))
private def y : Affine 2 := (false,(true,false))
private def z : Affine 2 := aConst 2 false
private def one : Affine 2 := aConst 2 true
private def a5 : Affine 5 := (true,(false,(true,(false,(true,true)))))
private def b5 : Affine 5 := (false,(true,(true,(false,(false,true)))))
private def suffix : BitString := [true,false,true,true,false]

example : reduceRow (.affine x) ⟨true,(false,x),(false,y)⟩ = some ⟨true,x,y⟩ := rfl
example : reduceRow (.affine x) ⟨true,(true,x),(false,y)⟩ = some ⟨true,z,y⟩ := rfl
example : reduceRow (.affine y) ⟨true,(false,x),(true,y)⟩ = some ⟨true,x,z⟩ := rfl
example : reduceRow (.affine one) ⟨false,(true,x),(true,y)⟩ =
    some ⟨false,aAdd one x,aAdd one y⟩ := rfl
example : reduceRow (.plane x y z) ⟨true,(false,one),(false,one)⟩ = some ⟨true,one,one⟩ := rfl
example : reduceRow (.plane x y z) ⟨true,(false,x),(true,y)⟩ = some ⟨true,x,z⟩ := rfl
example : reduceRow (.plane x y z) ⟨true,(true,x),(false,y)⟩ = some ⟨true,y,z⟩ := rfl
example : reduceRow (.plane x y z) ⟨true,(true,x),(true,y)⟩ =
    some ⟨true,aAdd (aAdd x y) one,z⟩ := rfl
example : reduceRow (.plane x y z) ⟨true,(false,one),(true,y)⟩ = none := rfl
example : reduceRow (.plane x y z) ⟨true,(true,x),(false,one)⟩ = none := rfl
example : reduceRow (.plane x y z) ⟨true,(true,z),(true,z)⟩ = none := rfl
example : reduceRow (.plane (n := 0) false true true) ⟨false,(true,false),(false,true)⟩ =
    some ⟨false,true,true⟩ := rfl
example : reduceRow (.plane x y z) ⟨false,(false,x),(true,y)⟩ = some ⟨false,x,z⟩ := rfl
example : (codec 2).encode none = [false] := rfl
example : (codec 2).encode (some ⟨false,x,y⟩) = [true,false,true,false,false,false,true,false] := rfl
example : (codec 2).decode [false] = some none := rfl
example : (codec 2).decode [true] = none := rfl
example {n : Nat} (t : TailForm n) (r : Row (n + 1)) (rest : BitString) :
    Exec SourceRowReductionInstructions.block (SourceRowReductionState.initial t r rest)
      (SourceRowReductionInstructions.fuel t r) (finished t rest (reduceRow t r)) :=
  SourceRowReductionInstructions.block_exec t r rest
example {n : Nat} (t : TailForm n) (r : Row (n + 1)) (rest : BitString) :
    BitRegister.run (SourceRowReductionInstructions.block.program 0 8)
      (SourceRowReductionInstructions.fuel t r + 1) ⟨.running 0,SourceRowReductionState.initial t r rest⟩ =
      ⟨.accepted,finished t rest (reduceRow t r)⟩ :=
  SourceRowReductionInstructions.program_run t r rest
example {n : Nat} (t : TailForm n) (r : Row (n + 1)) :
    SourceRowReductionInstructions.fuel t r + 1 ≤ 153 * (rowWord r).length :=
  SourceRowReductionInstructions.fuel_row_bound t r
example {n : Nat} (t : TailForm n) (r : Row (n + 1)) (rest : BitString) :
    (codec n).decode ((finished t rest (reduceRow t r)).get 8) = some (reduceRow t r) :=
  SourceRowReductionInstructions.output_decode t r rest
example {n : Nat} (t : TailForm n) (r : Row (n + 1)) (rest : BitString) :
    (finished t rest (reduceRow t r)).get 0 = rest :=
  SourceRowReductionInstructions.suffix_get t r rest

private def expectStore {k : Nat} (count : IO.Ref Nat)
    (final : BitRegister.Configuration k) (expected : Store k) (label : String) : IO Unit := do
  if final.control != .accepted then throw (IO.userError (label ++ ": instruction bound exhausted"))
  for i in List.finRange k do
    if final.store.get i != expected.get i then throw (IO.userError (label ++ ": exact state mismatch"))
  count.modify (· + 1)

private def checkRow {n : Nat} (count : IO.Ref Nat) (t : TailForm n)
    (r : Row (n + 1)) (rest : BitString) : IO Unit := do
  let ticks := SourceRowReductionInstructions.fuel t r
  if ticks + 1 > 153 * (rowWord r).length then throw (IO.userError "Row: encoded source instruction bound")
  let final := BitRegister.run (SourceRowReductionInstructions.block.program 0 8)
    (ticks + 1) ⟨.running 0,SourceRowReductionState.initial t r rest⟩
  expectStore count final (finished t rest (reduceRow t r)) "Complete row reduction"
  if final.store.get 8 != (codec n).encode (reduceRow t r) then throw (IO.userError "Row: semantic encoding")
  if (final.store.get 8).length > 2 * n + 4 then throw (IO.userError "Row: output size")
  if final.store.get 0 != rest then throw (IO.userError "Row: source suffix changed")

private def checkLoader {n : Nat} (count : IO.Ref Nat) (t : TailForm n)
    (r : Row (n + 1)) (rest : BitString) : IO Unit := do
  let final := BitRegister.run (SourceRowReductionLoad.block.program 0 8)
    (SourceRowReductionLoad.fuel n + 1) ⟨.running 0,SourceRowReductionState.initial t r rest⟩
  expectStore count final (loaded t r rest) "Exact row consumption"

private def checkShort {n : Nat} (count : IO.Ref Nat) (t : TailForm n) (r : Row (n + 1)) : IO Unit := do
  let final := BitRegister.run (SourceRowReductionInstructions.block.program 0 8)
    (SourceRowReductionInstructions.fuel t r) ⟨.running 0,SourceRowReductionState.initial t r suffix⟩
  if final.control == .accepted then throw (IO.userError "Row: unexpectedly accepted with one instruction missing")
  count.modify (· + 1)

private def exercise {n : Nat} (count : IO.Ref Nat) (t : TailForm n) (f g : Affine n) : IO Unit := do
  for selected in [false,true] do
    for lh in [false,true] do
      for rh in [false,true] do checkRow count t ⟨selected,(lh,f),(rh,g)⟩ suffix

private def fixtures : (n : Nat) → List (Affine n)
  | 0 => [false,true]
  | n + 1 => (fixtures n).flatMap fun rest => [(false,rest),(true,rest)]

#eval (show IO Unit from do
  let count ← IO.mkRef 0
  for n in [0,1] do
    for u in fixtures n do
      for f in fixtures n do
        for g in fixtures n do
          exercise count (.affine u) f g
          exercise count (.plane (aConst n false) (aConst n true) u) f g
  for u in [z,aAdd x y] do
    for f in fixtures 2 do
      for g in [x,y,one] do exercise count (.plane x y u) f g
  for c in [SourcePlanePartnerSpecification.Candidate.zero,.left,.right,.leftOne,.rightOne,.sum,.sumOne] do
    exercise count (.plane a5 b5 b5) (SourcePlanePartnerSpecification.value a5 b5 c) a5
  exercise count (.plane a5 b5 b5) (aConst 5 true) a5
  exercise count (.affine a5) a5 b5
  exercise count (.affine b5) b5 a5
  exercise count (.affine (aConst 16 true)) (aConst 16 true) (aConst 16 false)
  exercise count (.plane (aConst 16 true) (aConst 16 false) (aConst 16 true))
    (aConst 16 true) (aConst 16 false)
  for t in [TailForm.affine one,.plane x y one] do
    for selected in [false,true] do
      for lh in [false,true] do
        for rh in [false,true] do
          for rest in [[],suffix] do checkLoader count t ⟨selected,(lh,x),(rh,y)⟩ rest
          checkShort count t ⟨selected,(lh,x),(rh,y)⟩
  IO.println s!"FULL_ROW_RUNTIME_REGRESSIONS_GREEN: {← count.get} executions")

run_cmd do
  for name in [
    ``SourceRowReductionState.core_exec,
    ``SourceRowReductionState.partner_exec,
    ``SourceRowReductionState.none_bytes,
    ``SourceRowReductionState.some_bytes,
    ``SourceRowReductionState.roundtrip,
    ``SourceRowReductionState.bytes_bound,
    ``SourceRowReductionState.cleanup_exec,
    ``SourceRowReductionState.output_get,
    ``SourceRowReductionState.suffix_get,
    ``SourceRowReductionState.output_decode,
    ``SourceRowReductionLoad.takeFlag_exec,
    ``SourceRowReductionLoad.factor_exec,
    ``SourceRowReductionLoad.block_exec,
    ``SourceRowReductionOutput.serialize_exec,
    ``SourceRowReductionOutput.cleanup_buffered,
    ``SourceRowReductionOutput.finish_exec,
    ``SourceRowReductionAffine.addLeft_exec,
    ``SourceRowReductionAffine.addRight_exec,
    ``SourceRowReductionAffine.left_exec,
    ``SourceRowReductionAffine.right_exec,
    ``SourceRowReductionAffine.block_exec,
    ``SourceRowReductionAffine.fuel_bound,
    ``SourceRowReductionAssemble.add_exec,
    ``SourceRowReductionAssemble.storePartner_exec,
    ``SourceRowReductionAssemble.success_exec,
    ``SourceRowReductionAssemble.complete_exec,
    ``SourceRowReductionAssemble.clearFlags_exec,
    ``SourceRowReductionAssemble.block_exec,
    ``SourceRowReductionAssemble.completeFuel_bound,
    ``SourceRowReductionAssemble.fuel_bound,
    ``SourceRowReductionPlane.swap_exec,
    ``SourceRowReductionPlane.both_exec,
    ``SourceRowReductionPlane.block_exec,
    ``SourceRowReductionPlane.fuel_bound,
    ``SourceRowReductionInstructions.dispatch_exec,
    ``SourceRowReductionInstructions.block_exec,
    ``SourceRowReductionInstructions.program_run,
    ``SourceRowReductionInstructions.output_get,
    ``SourceRowReductionInstructions.suffix_get,
    ``SourceRowReductionInstructions.output_decode,
    ``SourceRowReductionInstructions.output_bound,
    ``SourceRowReductionInstructions.transformFuel_bound,
    ``SourceRowReductionInstructions.fuel_bound,
    ``SourceRowReductionInstructions.fuel_row_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceRowReductionLoad.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceRowReductionPlane.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceRowReductionInstructions.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceRowReductionInstructions.program_run
#print axioms PNP.Concrete.ResidualReduction.SourceRowReductionInstructions.fuel_row_bound

end PNP.Concrete.ResidualReduction.SourceRowReductionRegression

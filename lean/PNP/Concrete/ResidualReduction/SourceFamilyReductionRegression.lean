import PNP.Concrete.ResidualReduction.SourceFamilyReductionRaw
import Lean

/-! Full-family input-boundary regressions. Earlier exhaustive row tests are
not repeated. These fixtures exercise collection order, sticky failure,
source-derived headers, exact suffix consumption and input-only startup.
Malformed examples concern the codec only: the canonical source-program
theorem does not claim a complete all-bitstring validation wrapper. -/

namespace PNP.Concrete.ResidualReduction.SourceFamilyReductionRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (familyBits rowWord)
open PNP.Concrete.ResidualReduction.SourceRowReductionState (reduceRow)
open PNP.Concrete.ResidualReduction.SourceFamilyReductionEncoding
open PNP.Concrete.ResidualReduction.SourceFamilyReductionState (finished)

private def x : Affine 2 := (true,(false,false))
private def y : Affine 2 := (false,(true,false))
private def z : Affine 2 := aConst 2 false
private def one : Affine 2 := aConst 2 true
private def a5 : Affine 5 := (true,(false,(true,(false,(true,true)))))
private def b5 : Affine 5 := (false,(true,(true,(false,(false,true)))))
private def r0 : Row 3 := ⟨false,(false,x),(false,y)⟩
private def r1 : Row 3 := ⟨true,(false,x),(true,y)⟩
private def r2 : Row 3 := ⟨false,(true,x),(false,y)⟩
private def r3 : Row 3 := ⟨true,(true,x),(true,y)⟩
private def bad : Row 3 := ⟨true,(false,one),(true,y)⟩
private def suffix : BitString := [true,false,true,true,false]

example : (TailForm.affine x).reduce [] = some [] := rfl
example : (TailForm.plane x y z).reduce [] = some [] := rfl
example : (TailForm.plane x y z).reduce [r0,r1,r2,r3] =
    some [⟨false,x,y⟩,⟨true,x,z⟩,⟨false,y,z⟩,⟨true,aAdd (aAdd x y) one,z⟩] := rfl
example : (TailForm.plane x y z).reduce [bad] = none := rfl
example : (TailForm.plane x y z).reduce [bad,r1,r2] = none := rfl
example : (TailForm.plane x y z).reduce [r1,bad,r2] = none := rfl
example : (TailForm.plane x y z).reduce [r1,r2,bad] = none := rfl
example : valid (.plane x y z) [bad,r1,r2] = false := rfl
example : retained (.plane x y z) [bad,r1] = [⟨true,x,z⟩] := rfl
example : output (.plane x y z) [bad,r1] = [false] := rfl
example : packet (.affine (n := 0) false) [] = [false,false,false,false] := rfl
example : packet (.plane (n := 0) false true false) [] = [false,true,false,true,false,false] := rfl
example : (codec 2).encode none = [false] := rfl
example : (codec 2).encode (some []) = [true,false] := rfl
example : (codec 2).decode [] = none := rfl
example : (codec 2).decode [true] = none := rfl
example : inputCodec.decode [] = none := rfl
example : inputCodec.decode [true] = none := rfl
example {n : Nat} (t : TailForm n) (F : Family (n + 1)) :
    result t F = t.reduce F := result_eq_reduce t F
example {n : Nat} (t : TailForm n) (F : Family (n + 1)) (rest : BitString) :
    Exec SourceFamilyReductionRaw.block (SourceFamilyReductionLoad.initial (packet t F ++ rest))
      (SourceFamilyReductionRaw.fuel t F) (finished t rest ((codec n).encode (t.reduce F))) :=
  SourceFamilyReductionRaw.block_exec t F rest
example {n : Nat} (t : TailForm n) (F : Family (n + 1)) (rest : BitString) :
    BitRegister.run (SourceFamilyReductionRaw.block.program 0 8) (SourceFamilyReductionRaw.fuel t F + 1)
      ⟨.running 0,SourceFamilyReductionLoad.initial (packet t F ++ rest)⟩ =
      ⟨.accepted,finished t rest ((codec n).encode (t.reduce F))⟩ :=
  SourceFamilyReductionRaw.program_run t F rest
example {n : Nat} (t : TailForm n) (F : Family (n + 1)) :
    SourceFamilyReductionRaw.fuel t F + 1 ≤ 165 * (packet t F).length + 43 :=
  SourceFamilyReductionRaw.fuel_encoded_bound t F
example {n : Nat} (t : TailForm n) (F : Family (n + 1)) (rest : BitString) :
    (codec n).decode ((finished t rest ((codec n).encode (t.reduce F))).get 8) = some (t.reduce F) :=
  SourceFamilyReductionRaw.output_decode t F rest
example {n : Nat} (t : TailForm n) (F : Family (n + 1)) (rest : BitString) :
    (finished t rest ((codec n).encode (t.reduce F))).get 0 = rest :=
  SourceFamilyReductionRaw.suffix_get t F rest
example {n : Nat} (t : TailForm n) (F : Family (n + 1)) (rest : BitString) :
    Exec SourceFamilyReductionLoad.block (SourceFamilyReductionLoad.initial (packet t F ++ rest))
      (SourceFamilyReductionLoad.fuel t F) (SourceFamilyReductionState.initial t F rest) :=
  SourceFamilyReductionLoad.block_exec t F rest

private def expectStore {k : Nat} (count : IO.Ref Nat)
    (final : BitRegister.Configuration k) (expected : Store k) (label : String) : IO Unit := do
  if final.control != .accepted then throw (IO.userError (label ++ ": instruction bound exhausted"))
  for i in List.finRange k do
    if final.store.get i != expected.get i then throw (IO.userError (label ++ ": exact state mismatch"))
  count.modify (· + 1)

private def checkRaw {n : Nat} (count : IO.Ref Nat) (t : TailForm n)
    (F : Family (n + 1)) (rest : BitString) : IO Unit := do
  let input := packet t F ++ rest
  let start := SourceFamilyReductionLoad.initial input
  if start.get 0 != input then throw (IO.userError "Family: original input missing")
  for i in List.finRange 23 do
    if i.val != 0 then
      if start.get i != [] then throw (IO.userError "Family: hidden prepared input register")
  let ticks := SourceFamilyReductionRaw.fuel t F
  if ticks + 1 > 165 * (packet t F).length + 43 then throw (IO.userError "Family: encoded instruction bound")
  let final := BitRegister.run (SourceFamilyReductionRaw.block.program 0 8) (ticks + 1) ⟨.running 0,start⟩
  expectStore count final (finished t rest ((codec n).encode (t.reduce F))) "Input-only family pass"
  if (final.store.get 8).length > (2 * n + 4) * F.length + 2 then throw (IO.userError "Family: output size")

private def checkLoad {n : Nat} (count : IO.Ref Nat) (t : TailForm n)
    (F : Family (n + 1)) : IO Unit := do
  let final := BitRegister.run (SourceFamilyReductionLoad.block.program 0 8)
    (SourceFamilyReductionLoad.fuel t F + 1) ⟨.running 0,SourceFamilyReductionLoad.initial (packet t F ++ suffix)⟩
  expectStore count final (SourceFamilyReductionState.initial t F suffix) "Actual packet register loading"

private def checkSticky (count : IO.Ref Nat) (r : Row 3) (flag : Bool) : IO Unit := do
  let t := TailForm.plane x y z
  let rest := [true,false]
  let acc := [false,true,true]
  let total := [true,true,true]
  let start := SourceFamilyReductionState.state t (rowWord r ++ suffix) (true :: rest) acc flag total
  let expected := SourceFamilyReductionState.state t suffix rest ((emitted (reduceRow t r)).reverse ++ acc)
    (flag && (reduceRow t r).isSome) total
  let final := BitRegister.run (SourceFamilyReductionRow.block.program 0 8)
    (SourceFamilyReductionRow.fuel t r + 1) ⟨.running 0,start⟩
  expectStore count final expected "Sticky row failure"

private def checkLoop (count : IO.Ref Nat) (F : Family 3) : IO Unit := do
  let t := TailForm.plane x y z
  let acc := [false,true,false]
  let total := [true,true,true,true]
  let start := SourceFamilyReductionState.loopState t F suffix acc false total
  let expected := SourceFamilyReductionState.done t suffix ((familyBits (retained t F)).reverse ++ acc) false total
  let final := BitRegister.run (SourceFamilyReductionLoop.block.program 0 8)
    (SourceFamilyReductionLoop.fuel t F + 1) ⟨.running 0,start⟩
  expectStore count final expected "Previously failed family remains failed"

private def checkShort {n : Nat} (count : IO.Ref Nat) (t : TailForm n) (F : Family (n + 1)) : IO Unit := do
  let final := BitRegister.run (SourceFamilyReductionRaw.block.program 0 8)
    (SourceFamilyReductionRaw.fuel t F) ⟨.running 0,SourceFamilyReductionLoad.initial (packet t F ++ suffix)⟩
  if final.control == .accepted then throw (IO.userError "Family: accepted with one instruction missing")
  count.modify (· + 1)

private def flagRows {n : Nat} (f g : Affine n) : Family (n + 1) :=
  [⟨false,(false,f),(false,g)⟩,⟨true,(false,f),(false,g)⟩,
   ⟨false,(false,f),(true,g)⟩,⟨true,(false,f),(true,g)⟩,
   ⟨false,(true,f),(false,g)⟩,⟨true,(true,f),(false,g)⟩,
   ⟨false,(true,f),(true,g)⟩,⟨true,(true,f),(true,g)⟩]
private def fixtures : (n : Nat) → List (Affine n)
  | 0 => [false,true]
  | n + 1 => (fixtures n).flatMap fun rest => [(false,rest),(true,rest)]

#eval (show IO Unit from do
  let count ← IO.mkRef 0
  let tails := [TailForm.affine x,.affine one,.plane x y z,.plane x y one,.plane z z one,.plane x x one]
  let families : List (Family 3) :=
    [[],[r0],[r1],[r2],[r3],[bad],[r0,r1,r2,r3],[bad,r1,r2],
     [r1,bad,r2],[r1,r2,bad],[bad,bad,r1],[r0,r0,r1],List.replicate 8 r3]
  for t in tails do
    for F in families do
      for rest in [[],suffix,[false,false]] do checkRaw count t F rest
    for F in [[],[r1],[r0,bad,r3]] do checkLoad count t F
  for n in [0,1] do
    for f in fixtures n do
      for g in fixtures n do
        checkRaw count (.affine (aConst n true)) (flagRows f g) suffix
        checkRaw count (.plane (aConst n false) (aConst n true) (aConst n true)) (flagRows f g) suffix
  for t in [TailForm.affine b5,.plane a5 b5 (aConst 5 true)] do
    for rest in [[],suffix] do checkRaw count t (flagRows a5 b5) rest
  checkRaw count (.affine (aConst 16 true)) (flagRows (aConst 16 true) (aConst 16 false)) suffix
  checkRaw count (.plane (aConst 16 true) (aConst 16 false) (aConst 16 true))
    (flagRows (aConst 16 true) (aConst 16 false)) suffix
  checkRaw count (.plane x y z) (List.replicate 24 r3) suffix
  checkRaw count (.plane x y z) (List.replicate 12 r1 ++ bad :: List.replicate 12 r2) suffix
  for r in [r1,bad] do
    for flag in [false,true] do checkSticky count r flag
  checkLoop count [r1,r2,r3]
  checkLoop count [r1,bad,r2]
  for t in [TailForm.affine x,.plane x y z] do
    for F in [[],[r1,bad,r2]] do checkShort count t F
  IO.println s!"FULL_FAMILY_RUNTIME_REGRESSIONS_GREEN: {← count.get} executions")

run_cmd do
  for name in [
    ``SourceFamilyReductionEncoding.reduce_nil,
    ``SourceFamilyReductionEncoding.reduce_cons,
    ``SourceFamilyReductionEncoding.result_eq_reduce,
    ``SourceFamilyReductionEncoding.retained_length_le,
    ``SourceFamilyReductionEncoding.valid_length,
    ``SourceFamilyReductionEncoding.retained_bits_cons,
    ``SourceFamilyReductionEncoding.family_bytes,
    ``SourceFamilyReductionEncoding.family_length,
    ``SourceFamilyReductionEncoding.none_bytes,
    ``SourceFamilyReductionEncoding.some_bytes,
    ``SourceFamilyReductionEncoding.output_eq,
    ``SourceFamilyReductionEncoding.output_decode,
    ``SourceFamilyReductionEncoding.output_length,
    ``SourceFamilyReductionEncoding.packet_bytes,
    ``SourceFamilyReductionEncoding.packet_roundtrip,
    ``SourceFamilyReductionState.row_exec,
    ``SourceFamilyReductionState.core_exec,
    ``SourceFamilyReductionState.cleanup_exec,
    ``SourceFamilyReductionState.output_get,
    ``SourceFamilyReductionState.suffix_get,
    ``SourceFamilyReductionRow.failure_exec,
    ``SourceFamilyReductionRow.success_exec,
    ``SourceFamilyReductionRow.collect_exec,
    ``SourceFamilyReductionRow.block_exec,
    ``SourceFamilyReductionRow.collectFuel_bound,
    ``SourceFamilyReductionRow.fuel_bound,
    ``SourceFamilyReductionLoop.block_exec,
    ``SourceFamilyReductionLoop.fuel_bound,
    ``SourceFamilyReductionLoop.header_exec,
    ``SourceFamilyReductionOutput.success_exec,
    ``SourceFamilyReductionOutput.emit_exec,
    ``SourceFamilyReductionOutput.block_exec,
    ``SourceFamilyReductionOutput.fuel_bound,
    ``SourceFamilyReductionInstructions.accumulator_reverse,
    ``SourceFamilyReductionInstructions.accumulator_length,
    ``SourceFamilyReductionInstructions.accumulator_output,
    ``SourceFamilyReductionInstructions.block_exec,
    ``SourceFamilyReductionInstructions.program_run,
    ``SourceFamilyReductionInstructions.fuel_bound,
    ``SourceFamilyReductionInstructions.fuel_encoded_bound,
    ``SourceFamilyReductionInstructions.output_decode,
    ``SourceFamilyReductionInstructions.suffix_get,
    ``SourceFamilyTailLoad.readField_exec,
    ``SourceFamilyTailLoad.takeKind_exec,
    ``SourceFamilyTailLoad.block_exec,
    ``SourceFamilyTailLoad.fuel_bound,
    ``SourceFamilyReductionLoad.headerFuel,
    ``SourceFamilyReductionLoad.dimension_exec,
    ``SourceFamilyReductionLoad.count_exec,
    ``SourceFamilyReductionLoad.block_exec,
    ``SourceFamilyReductionLoad.fuel_bound,
    ``SourceFamilyReductionRaw.block_exec,
    ``SourceFamilyReductionRaw.program_run,
    ``SourceFamilyReductionRaw.packet_length,
    ``SourceFamilyReductionRaw.family_count_bound,
    ``SourceFamilyReductionRaw.fuel_encoded_bound,
    ``SourceFamilyReductionRaw.output_decode,
    ``SourceFamilyReductionRaw.output_bound,
    ``SourceFamilyReductionRaw.suffix_get] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceFamilyReductionEncoding.result_eq_reduce
#print axioms PNP.Concrete.ResidualReduction.SourceFamilyReductionLoop.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceFamilyReductionLoad.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceFamilyReductionRaw.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceFamilyReductionRaw.program_run
#print axioms PNP.Concrete.ResidualReduction.SourceFamilyReductionRaw.fuel_encoded_bound

end PNP.Concrete.ResidualReduction.SourceFamilyReductionRegression

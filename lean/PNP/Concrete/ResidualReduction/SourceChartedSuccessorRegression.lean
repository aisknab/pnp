import PNP.Concrete.ResidualReduction.SourceChartedSuccessorBounds
import Lean

/-! Connected-path regressions, without rerunning earlier component suites.
Inputs contain only the dimension, pivot, original normals and actual family.
Hostile fixtures distinguish head rejection, off-diagonal rejection, accepted
gates followed by row failure, and successful reductions. Physical runtime and
the upstream selected-source/chart composition are not claimed here. -/

namespace PNP.Concrete.ResidualReduction.SourceChartedSuccessorRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChartedSuccessorState
open PNP.Concrete.ResidualReduction.SourceChartedSuccessorInput (packet)
open PNP.Concrete.ResidualReduction.SourceChartedSuccessorGate (decision)

private def x : Affine 2 := (true,(false,false))
private def y : Affine 2 := (false,(true,false))
private def z : Affine 2 := aConst 2 false
private def one : Affine 2 := aConst 2 true
private def rA : Row 3 := ⟨true,(false,x),(true,y)⟩
private def rB : Row 3 := ⟨true,(false,aAdd x one),(true,z)⟩
private def bad : Row 3 := ⟨false,(false,one),(true,y)⟩
private def planeFamily : Family 3 := [rA,rB]
private def planeNormals : Option (Affine 3 × Affine 3) := some ((false,x),(false,y))
private def unitRow (n : Nat) : Row (n + 1) := ⟨true,(true,aConst n false),(false,aConst n true)⟩

example : scalar planeFamily = (one,qProduct x y) := rfl
example : decision planeFamily (0 : Fin 3) none = false := rfl
example : decision planeFamily (0 : Fin 3) planeNormals = true := rfl
example : decision (planeFamily ++ [bad]) (0 : Fin 3) planeNormals = true := rfl
example : (candidate (planeFamily ++ [bad]) (0 : Fin 3) planeNormals).reduce (planeFamily ++ [bad]) = none := rfl
example : result (planeFamily ++ [bad]) (0 : Fin 3) planeNormals = none := rfl
example : (result planeFamily (0 : Fin 3) planeNormals).isSome = true := rfl
example : result planeFamily (0 : Fin 3) none = none := rfl
example : result ([] : Family 3) (0 : Fin 3) none = none := rfl
example : decision (planeFamily ++ planeFamily) (0 : Fin 3) planeNormals = false := rfl
example : result [unitRow 0] (0 : Fin 1) none = some [⟨true,false,true⟩] := rfl
example : (result [unitRow 2] (0 : Fin 3) none).isSome = true := rfl
example {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    Exec SourceChartedSuccessorRaw.block (SourceChartedSuccessorState.initial (packet F k normals))
      (SourceChartedSuccessorRaw.fuel F k normals) (SourceChartedSuccessorFinish.finished F k normals) :=
  SourceChartedSuccessorRaw.block_exec F k normals
example {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    (SourceFamilyReductionEncoding.codec n).decode
      ((BitRegister.run (SourceChartedSuccessorRaw.block.program 0 8) (SourceChartedSuccessorRaw.fuel F k normals + 1)
        ⟨.running 0,SourceChartedSuccessorState.initial (packet F k normals)⟩).store.get 8) =
      some (result F k normals) := SourceChartedSuccessorRaw.output_decode F k normals
example {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    SourceChartedSuccessorRaw.fuel F k normals + 1 ≤ SourceChartedSuccessorBounds.bound (packet F k normals).length :=
  SourceChartedSuccessorBounds.source_bound F k normals
example (L : Nat) : SourceChartedSuccessorBounds.bound L =
    22 * (L * L * L) + 191 * (L * L) + 1426 * L + 1737 := SourceChartedSuccessorBounds.bound_cubic L
example {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (c : Fin (n + 1) × Point n) (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    result (chartRows (SourceBalance.markSource F w) c.1 c.2) c.1 normals =
      contract (SourceBalance.markSource F w) c.1 c.2 (SourceClosure.computedTail F w c normals) :=
  result_chart F w c normals

private def expectStore {k : Nat} (count : IO.Ref Nat)
    (actual : BitRegister.Configuration k) (expected : Store k) (label : String) : IO Unit := do
  if actual.control != .accepted then throw (IO.userError (label ++ ": instruction budget exhausted"))
  for i in List.finRange k do
    if actual.store.get i != expected.get i then throw (IO.userError (label ++ ": exact state differs"))
  count.modify (· + 1)

private def checkRaw {n : Nat} (count : IO.Ref Nat) (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : IO Unit := do
  let input := packet F k normals
  let start := SourceChartedSuccessorState.initial input
  if start.get 0 != input then throw (IO.userError "Successor: input stream missing")
  for i in List.finRange 29 do
    if i.val != 0 then
      if start.get i != [] then throw (IO.userError "Successor: hidden initial result or metadata")
  let ticks := SourceChartedSuccessorRaw.fuel F k normals
  if ticks + 1 > SourceChartedSuccessorBounds.bound input.length then
    throw (IO.userError "Successor: cubic encoded-source instruction bound")
  let actual := BitRegister.run (SourceChartedSuccessorRaw.block.program 0 8) (ticks + 1) ⟨.running 0,start⟩
  if actual.store.get 8 != (SourceFamilyReductionEncoding.codec n).encode (result F k normals) then
    throw (IO.userError "Successor: wrong optional reduction")
  expectStore count actual (SourceChartedSuccessorFinish.finished F k normals) "Input-only charted successor"

private def checkShort (count : IO.Ref Nat) (F : Family 3) (normals : Option (Affine 3 × Affine 3)) : IO Unit := do
  let actual := BitRegister.run (SourceChartedSuccessorRaw.block.program 0 8)
    (SourceChartedSuccessorRaw.fuel F (0 : Fin 3) normals)
    ⟨.running 0,SourceChartedSuccessorState.initial (packet F (0 : Fin 3) normals)⟩
  if actual.control == .accepted then throw (IO.userError "Successor: accepted one instruction too early")
  count.modify (· + 1)

private def dirty : (n : Nat) → Store n
  | 0 => .nil
  | n + 1 => .cons [true,false,true] (dirty n)
private def checkClear (count : IO.Ref Nat) (n : Nat) : IO Unit := do
  let actual := BitRegister.run ((SourceChartedSuccessorWords.clearAll (n + 1)).program 0 0)
    (n + 3) ⟨.running 0,dirty (n + 1)⟩
  expectStore count actual (Store.empty (n + 1)) "Workspace reset"

private def checkPrepend (count : IO.Ref Nat) (front back : BitString) : IO Unit := do
  let r : NormalizerBlocks.Occurrence.Registers :=
    ⟨[true],[false,true],[true],[false],[true],[false],[true],[true,false],[false]⟩
  let actual := BitRegister.run (SourceChartedSuccessorWords.prepend.program 0 8) (8 * front.length + 10)
    ⟨.running 0,(SourceChartedSuccessorWords.prependReady r front back).store⟩
  expectStore count actual (SourceChartedSuccessorWords.prepended r front back).store "Exact packet concatenation"

private def affineOne : List (Affine 1) := [(false,false),(false,true),(true,false),(true,true)]

#eval (show IO Unit from do
  let count ← IO.mkRef 0
  for n in [0,6,22] do checkClear count n
  let words : List BitString := [[],[false],[true],[true,false,true],List.replicate 7 false]
  for front in words do
    for back in words do checkPrepend count front back
  for a in affineOne do
    for b in affineOne do
      for flag in [false,true] do
        let F : Family 1 := [⟨flag,a,b⟩]
        checkRaw count F (0 : Fin 1) none
        checkRaw count F (0 : Fin 1) (some (a,b))
  let families : List (Family 3) :=
    [[],[unitRow 2],planeFamily,planeFamily ++ [bad],bad :: planeFamily,
      planeFamily ++ [unitRow 2],planeFamily ++ planeFamily,[bad]]
  let choices : List (Option (Affine 3 × Affine 3)) :=
    [none,planeNormals,some ((false,y),(false,x)),some ((false,x),(false,x)),
      some (aConst 3 false,aConst 3 false)]
  for F in families do
    for k in List.finRange 3 do
      for normals in choices do checkRaw count F k normals
  for n in [3,5] do
    let k : Fin (n + 1) := ⟨0,Nat.zero_lt_succ n⟩
    for F in [[unitRow n],List.replicate 3 (unitRow n)] do
      checkRaw count F k none
      checkRaw count F k (some (aConst (n + 1) false,aConst (n + 1) true))
  let longer := List.replicate 9 rA ++ List.replicate 9 rB
  checkRaw count longer (0 : Fin 3) none
  checkRaw count longer (0 : Fin 3) planeNormals
  checkShort count [] none
  checkShort count planeFamily planeNormals
  IO.println s!"CHARTED_SUCCESSOR_REGRESSIONS_GREEN: {← count.get} executions")

run_cmd do
  for name in [
    ``SourceChartedSuccessorWords.clear_exec,
    ``SourceChartedSuccessorWords.cleared_get,
    ``SourceChartedSuccessorWords.empty_get,
    ``SourceChartedSuccessorWords.cleared_all,
    ``SourceChartedSuccessorWords.clearAll_exec,
    ``SourceChartedSuccessorWords.prepend_exec,
    ``SourceChartedSuccessorState.core_exec,
    ``SourceChartedSuccessorState.use16_exec,
    ``SourceChartedSuccessorState.use18_exec,
    ``SourceChartedSuccessorState.use19_exec,
    ``SourceChartedSuccessorState.use23_exec,
    ``SourceChartedSuccessorState.reset_exec,
    ``SourceChartedSuccessorState.prepend_exec,
    ``SourceChartedSuccessorState.dimensionHeader_exec,
    ``SourceChartedSuccessorState.toInput_exec,
    ``SourceChartedSuccessorState.result_chart,
    ``SourceChartedSuccessorInput.header_exec,
    ``SourceChartedSuccessorInput.headers_exec,
    ``SourceChartedSuccessorInput.packet_length,
    ``SourceChartedSuccessorNormals.none_bytes,
    ``SourceChartedSuccessorNormals.some_bytes,
    ``SourceChartedSuccessorNormals.read_exec,
    ``SourceChartedSuccessorNormals.pair_exec,
    ``SourceChartedSuccessorNormals.emit_exec,
    ``SourceChartedSuccessorNormals.block_exec,
    ``SourceChartedSuccessorNormals.fuel_bound,
    ``SourceChartedSuccessorScalar.load_exec,
    ``SourceChartedSuccessorScalar.save_exec,
    ``SourceChartedSuccessorScalar.block_exec,
    ``SourceChartedSuccessorTail.load_exec,
    ``SourceChartedSuccessorTail.constructor_packet,
    ``SourceChartedSuccessorTail.prepareCall_exec,
    ``SourceChartedSuccessorTail.save_exec,
    ``SourceChartedSuccessorTail.block_exec,
    ``SourceChartedSuccessorGate.initial_eq,
    ``SourceChartedSuccessorGate.prepare_exec,
    ``SourceChartedSuccessorGate.block_exec,
    ``SourceChartedSuccessorGate.output_get,
    ``SourceChartedSuccessorFinish.initial_eq,
    ``SourceChartedSuccessorFinish.prepare_exec,
    ``SourceChartedSuccessorFinish.success_exec,
    ``SourceChartedSuccessorFinish.failure_exec,
    ``SourceChartedSuccessorFinish.block_exec,
    ``SourceChartedSuccessorFinish.output_eq,
    ``SourceChartedSuccessorFinish.output_decode,
    ``SourceChartedSuccessorRaw.block_exec,
    ``SourceChartedSuccessorRaw.program_run,
    ``SourceChartedSuccessorRaw.program_output,
    ``SourceChartedSuccessorRaw.output_decode,
    ``SourceChartedSuccessorRaw.charted_contract,
    ``SourceChartedSuccessorBounds.normals_length,
    ``SourceChartedSuccessorBounds.candidate_fuel,
    ``SourceChartedSuccessorBounds.tail_fuel,
    ``SourceChartedSuccessorBounds.gate_fuel,
    ``SourceChartedSuccessorBounds.finish_fuel,
    ``SourceChartedSuccessorBounds.combined_fuel,
    ``SourceChartedSuccessorBounds.scalar_bound_mono,
    ``SourceChartedSuccessorBounds.source_bound,
    ``SourceChartedSuccessorBounds.bound_cubic] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo "CHARTED_SUCCESSOR_AXIOMS_GREEN: 59 theorems"

#print axioms PNP.Concrete.ResidualReduction.SourceChartedSuccessorWords.clearAll_exec
#print axioms PNP.Concrete.ResidualReduction.SourceChartedSuccessorScalar.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceChartedSuccessorTail.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceChartedSuccessorRaw.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceChartedSuccessorRaw.charted_contract
#print axioms PNP.Concrete.ResidualReduction.SourceChartedSuccessorBounds.source_bound

end PNP.Concrete.ResidualReduction.SourceChartedSuccessorRegression

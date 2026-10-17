import PNP.Concrete.ResidualReduction.SourceOriginalSuccessorPolynomial
import Lean

/-! New connection-boundary regressions only: protected outer state, actual
Choice parsing through construction, complete step bytes, hostile original
packets, and the all-input polynomial machine contracts. Earlier unchanged
component suites are deliberately not imported or re-executed. -/

namespace PNP.Concrete.ResidualReduction.SourceOriginalSuccessorRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceWitnessSelection
open PNP.Concrete.ResidualReduction.SourceOriginalSuccessorState
open PNP.Concrete.ResidualReduction.SourceOriginalSuccessorPolynomial

private def x : Affine 2 := (true,(false,false))
private def y : Affine 2 := (false,(true,false))
private def rA : Row 3 := ⟨true,(false,x),(true,y)⟩
private def rB : Row 3 := ⟨true,(false,aAdd x (aConst 2 true)),(true,aConst 2 false)⟩
private def bad : Row 3 := ⟨false,(false,aConst 2 true),(true,y)⟩
private def nonlinear : Family 3 := [rA,rB]
private def unit : Family 1 := [⟨false,(true,false),(false,true)⟩]
private def expectedUnit : SourceClosure.ConstructedStep 0 1 := ⟨(true,()),0,(),[⟨true,false,true⟩]⟩

example : (stepCodec 0 1).encode (some expectedUnit) = [true,true,false,true,false,true,false,true] := rfl
example : SourceOriginalSuccessorRaw.answer [] = [false] := rfl
example : SourceOriginalSuccessorRaw.answer [true] = [false] := rfl
example : SourceOriginalSuccessorRaw.answer [false] = [false] := rfl
example : SourceOriginalSuccessorRaw.answer [false,false] = [false] := rfl
example (input : BitString) :
    ∃ used after, Exec SourceOriginalSuccessorRaw.block (SourceOriginalSuccessorState.initial input) used after ∧
      used ≤ SourceOriginalSuccessorRaw.budget input.length ∧ after.get 8 = SourceOriginalSuccessorRaw.answer input :=
  SourceOriginalSuccessorRaw.block_exec input
example : CompilerIO.AcceptsWithin program SourceOriginalSuccessorBounds.sourceFuel := acceptsWithin
example : polynomial.program = .machine (CompilerIO.rawMachine program)
    (CompilerIO.runtimePolynomial 56 SourceOriginalSuccessorBounds.sourceFuel) := polynomial_program
example (input : BitString) : polynomial.output input = SourceOriginalSuccessorRaw.answer input := polynomial_output input
example {n : Nat} (F : Family (n + 1)) :
    (stepCodec n F.length).decode (polynomial.output (SourceMatrixEncoding.codec.encode ⟨n + 1,F⟩)) =
      some (SourceChain.globalStep F) := exact_decoded_step F
example {n : Nat} (F : Family (n + 1)) (s : SourceClosure.ConstructedStep n F.length)
    (h : (stepCodec n F.length).decode (polynomial.output (SourceMatrixEncoding.codec.encode ⟨n + 1,F⟩)) = some (some s)) :
    SourceClosure.StepSound F s := polynomial_step_sound F s h
example {n : Nat} (F : Family (n + 1)) :
    (stepCodec n F.length).decode (polynomial.output (SourceMatrixEncoding.codec.encode ⟨n + 1,F⟩)) = some none ↔
      SourceChain.globalStep F = none := exact_absence F
example (input : BitString) (h : SourceMatrixEncoding.codec.decode input = none) :
    polynomial.output input = [false] := polynomial_malformed input h
example (F : Family 0) : polynomial.output (SourceMatrixEncoding.codec.encode ⟨0,F⟩) = [false] := polynomial_zero F
example (input : BitString) :
    (polynomial.output input).length ≤ 2 * (input.length * input.length) + 8 * input.length + 5 :=
  polynomial_output_bound input
example (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 56 SourceOriginalSuccessorBounds.sourceFuel).eval input.length) input = .accept :=
  polynomial_machine_accepts input

private def sameStore (count : IO.Ref Nat) (actual : BitRegister.Configuration 56) (expected : Store 56)
    (label : String) : IO Unit := do
  if actual.control != .accepted then throw (IO.userError (label ++ ": did not halt"))
  for i in List.finRange 56 do
    if actual.store.get i != expected.get i then throw (IO.userError (label ++ ": state mismatch"))
  count.modify (· + 1)

private def runBounded (p : Program 56) (start : Store 56) (limit : Nat) : IO (Nat × BitRegister.Configuration 56) := do
  let mut state : BitRegister.Configuration 56 := ⟨.running 0,start⟩
  let mut used := 0
  for _ in [0:limit] do
    if state.control == .accepted then break
    state := BitRegister.run p 1 state
    used := used + 1
  if state.control != .accepted then throw (IO.userError "Successor regression instruction cap reached")
  return (used,state)

private def checkInput (count : IO.Ref Nat) (p : Program 56) (input expected : BitString) : IO Nat := do
  let start := SourceOriginalSuccessorState.initial input
  for i in List.finRange 56 do
    if start.get i != (if i.val == 0 then input else []) then
      throw (IO.userError "Original successor has hidden startup data")
  let (used,actual) ← runBounded p start 500000
  if used > SourceOriginalSuccessorBounds.sourceFuel.eval input.length ||
      actual.store.get 8 != expected ||
      actual.store.get 8 != SourceOriginalSuccessorRaw.answer input then
    throw (IO.userError "Original successor output or input-size bound differs")
  for i in List.finRange 48 do
    if i.val != 8 then
      if actual.store.get (Frame.index 8 i) != [] then
        throw (IO.userError "Original successor left unexpected workspace data")
  count.modify (· + 1)
  return used

private def checkConstruction (count : IO.Ref Nat) (p : Program 56)
    (w : Choice 3 nonlinear.length) : IO Unit := do
  let (used,actual) ← runBounded p (work [] [] (SourceOriginalSuccessorChoice.before nonlinear w)) 100000
  if actual.store.get 8 != (stepCodec 2 nonlinear.length).encode (build nonlinear w) ||
      actual.store.get 48 != SourceMatrixEncoding.familyBits nonlinear ||
      actual.store.get 52 != SourceOriginalSuccessorChoice.normalBytes nonlinear w ||
      actual.store.get 53 != SourceOriginalSuccessorChoice.weightBytes nonlinear w ||
      used > SourceOriginalSuccessorBounds.postBudget (SourceMatrixEncoding.codec.encode ⟨3,nonlinear⟩).length then
    throw (IO.userError "Parsed choice construction or protected reconstruction fields differ")
  count.modify (· + 1)

private def dirty : (n : Nat) → Store n
  | 0 => .nil
  | n + 1 => .cons [true,false,true] (dirty n)

#eval (show IO Unit from do
  let count ← IO.mkRef 0
  let saved : Saved := ⟨[true],[false],[true,false],[false,true],[true,true],[false,false],[true,false,true],[false,true,false]⟩
  let cleared := BitRegister.run (reset.program 0 8) 50 ⟨.running 0,full (dirty 48) saved⟩
  sameStore count cleared (work [] [] saved) "Protected workspace reset"
  for field in [Field.source,.choice,.dimension,.rows,.normals,.weights,.pivot,.tail] do
    let actual := BitRegister.run ((prepend field).program 0 8) (8 * (field.word saved).length + 11)
      ⟨.running 0,work [] [false,true,true] saved⟩
    sameStore count actual (work [] (field.word saved ++ [false,true,true]) saved) "Outer field packet assembly"
  let cp := SourceOriginalSuccessorRaw.construct.program 0 8
  let directions : List (Point 3) := [(true,(false,(false,()))),(false,(true,(false,()))),(false,(false,(false,())))]
  let normals : List (Option (Affine 3 × Affine 3)) :=
    [none,some ((false,x),(false,y)),some (aConst 3 false,aConst 3 true)]
  for direction in directions do
    for normal in normals do
      checkConstruction count cp ⟨(true,(true,())),direction,normal⟩
  IO.println "ORIGINAL_SUCCESSOR_PHASE: protected state and construction connections passed"
  let p := program
  let unitBytes := (stepCodec 0 1).encode (some expectedUnit)
  if SourceOriginalSuccessorRaw.canonicalAnswer 1 unit != unitBytes then
    throw (IO.userError "Independent one-variable construction fixture differs")
  let unitTicks ← checkInput count p (SourceMatrixEncoding.codec.encode ⟨1,unit⟩) unitBytes
  let short := BitRegister.run p (unitTicks - 1) (BitRegister.initial p (SourceMatrixEncoding.codec.encode ⟨1,unit⟩))
  if short.control == .accepted then throw (IO.userError "Complete successor accepted one instruction early")
  count.modify (· + 1)
  for F in [([] : Family 0),[⟨true,false,true⟩,⟨false,true,true⟩]] do
    let _ ← checkInput count p (SourceMatrixEncoding.codec.encode ⟨0,F⟩) [false]
  let _ ← checkInput count p (SourceMatrixEncoding.codec.encode ⟨1,([] : Family 1)⟩) [false]
  for selected in [false,true] do
    for a in [false,true] do
      for b in [false,true] do
        for c in [false,true] do
          for d in [false,true] do
            if !selected && a && !b && !c && d then continue
            let F : Family 1 := [⟨selected,(a,b),(c,d)⟩]
            let _ ← checkInput count p (SourceMatrixEncoding.codec.encode ⟨1,F⟩)
              (SourceOriginalSuccessorRaw.canonicalAnswer 1 F)
  let xy : Row 2 := ⟨true,x,y⟩
  let late : Row 2 := ⟨false,(false,(true,false)),aConst 2 true⟩
  for F in [([] : Family 2),[xy],[xy,xy],[late],[xy,late],[late,xy]] do
    let _ ← checkInput count p (SourceMatrixEncoding.codec.encode ⟨2,F⟩)
      (SourceOriginalSuccessorRaw.canonicalAnswer 2 F)
  if !((choose nonlinear).map (fun w => w.normals.isSome)).getD false then
    throw (IO.userError "Nonlinear fixture did not exercise the normal-pair handoff")
  for F in [nonlinear,nonlinear.reverse,nonlinear.map (fun r => {r with selected := false}),nonlinear ++ [bad]] do
    let _ ← checkInput count p (SourceMatrixEncoding.codec.encode ⟨3,F⟩)
      (SourceOriginalSuccessorRaw.canonicalAnswer 3 F)
  let lateFour : Family 4 := [⟨false,(false,(false,(false,(true,false)))),aConst 4 true⟩]
  let _ ← checkInput count p (SourceMatrixEncoding.codec.encode ⟨4,lateFour⟩)
    (SourceOriginalSuccessorRaw.canonicalAnswer 4 lateFour)
  IO.println "ORIGINAL_SUCCESSOR_PHASE: complete original-source cases passed"
  let original := SourceMatrixEncoding.codec.encode ⟨3,nonlinear⟩
  let malformed : List BitString := [[],[true],[false],[true,false],[false,true,false],
    [false,false,true],[true,false,false,true],List.replicate 7 true,
    original.take (original.length - 1),original ++ [false],original ++ [true]]
  for input in malformed do
    if (SourceMatrixEncoding.codec.decode input).isSome then throw (IO.userError "Invalid-input fixture became canonical")
    let _ ← checkInput count p input [false]
  IO.println s!"ORIGINAL_SUCCESSOR_REGRESSIONS_GREEN: {← count.get} executions")

run_cmd do
  let names := [
    ``SourceOriginalSuccessorApply.block_exec,
    ``SourceOriginalSuccessorApply.dimensionPrefix_exec,
    ``SourceOriginalSuccessorApply.output_eq,
    ``SourceOriginalSuccessorApply.prepare_exec,
    ``SourceOriginalSuccessorApply.state29_initial_eq,
    ``SourceOriginalSuccessorApply.unaryPrefix_exec,
    ``SourceOriginalSuccessorBounds.absent_chart_bound,
    ``SourceOriginalSuccessorBounds.apply_bound,
    ``SourceOriginalSuccessorBounds.charted_bound_mono,
    ``SourceOriginalSuccessorBounds.failure_bound,
    ``SourceOriginalSuccessorBounds.packet_bound,
    ``SourceOriginalSuccessorBounds.positive_bound,
    ``SourceOriginalSuccessorBounds.postPolynomial_eval,
    ``SourceOriginalSuccessorBounds.prepare_bound,
    ``SourceOriginalSuccessorBounds.sourceFuel_eval,
    ``SourceOriginalSuccessorBounds.zero_bound,
    ``SourceOriginalSuccessorChart.absent_exec,
    ``SourceOriginalSuccessorChart.absent_output,
    ``SourceOriginalSuccessorChart.capture_exec,
    ``SourceOriginalSuccessorChart.chosenFuel_bound,
    ``SourceOriginalSuccessorChart.chosen_exec,
    ``SourceOriginalSuccessorChart.prepare_exec,
    ``SourceOriginalSuccessorChart.success_output,
    ``SourceOriginalSuccessorChoice.block_exec,
    ``SourceOriginalSuccessorChoice.bytes_eq,
    ``SourceOriginalSuccessorChoice.fuel_bound,
    ``SourceOriginalSuccessorChoice.normals_exec,
    ``SourceOriginalSuccessorChoice.weights_exec,
    ``SourceOriginalSuccessorInput.header_exec,
    ``SourceOriginalSuccessorInput.headers_exec,
    ``SourceOriginalSuccessorInput.retain_exec,
    ``SourceOriginalSuccessorInput.select_exec,
    ``SourceOriginalSuccessorOutput.block_exec,
    ``SourceOriginalSuccessorOutput.capture_exec,
    ``SourceOriginalSuccessorOutput.emit_exec,
    ``SourceOriginalSuccessorOutput.fuel_bound,
    ``SourceOriginalSuccessorOutput.output_eq,
    ``SourceOriginalSuccessorOutput.stepResult_build,
    ``SourceOriginalSuccessorPolynomial.acceptsWithin,
    ``SourceOriginalSuccessorPolynomial.canonical_output_bound,
    ``SourceOriginalSuccessorPolynomial.exact_absence,
    ``SourceOriginalSuccessorPolynomial.exact_decoded_step,
    ``SourceOriginalSuccessorPolynomial.polynomial_canonical,
    ``SourceOriginalSuccessorPolynomial.polynomial_machine_accepts,
    ``SourceOriginalSuccessorPolynomial.polynomial_malformed,
    ``SourceOriginalSuccessorPolynomial.polynomial_output,
    ``SourceOriginalSuccessorPolynomial.polynomial_output_bound,
    ``SourceOriginalSuccessorPolynomial.polynomial_program,
    ``SourceOriginalSuccessorPolynomial.polynomial_step_sound,
    ``SourceOriginalSuccessorPolynomial.polynomial_zero,
    ``SourceOriginalSuccessorPolynomial.source_output,
    ``SourceOriginalSuccessorPolynomial.source_result,
    ``SourceOriginalSuccessorRaw.answer_canonical,
    ``SourceOriginalSuccessorRaw.answer_malformed,
    ``SourceOriginalSuccessorRaw.block_exec,
    ``SourceOriginalSuccessorRaw.canonical_none,
    ``SourceOriginalSuccessorRaw.construct_absent,
    ``SourceOriginalSuccessorRaw.construct_chosen,
    ``SourceOriginalSuccessorRaw.construct_exec,
    ``SourceOriginalSuccessorRaw.dispatch_absent,
    ``SourceOriginalSuccessorRaw.dispatch_valid,
    ``SourceOriginalSuccessorRaw.malformed_exec,
    ``SourceOriginalSuccessorRaw.valid_exec,
    ``SourceOriginalSuccessorState.core_exec,
    ``SourceOriginalSuccessorState.failure_exec,
    ``SourceOriginalSuccessorState.field_get,
    ``SourceOriginalSuccessorState.prepend_exec,
    ``SourceOriginalSuccessorState.reset_exec,
    ``SourceOriginalSuccessorState.save_exec,
    ``SourceOriginalSuccessorState.step_none,
    ``SourceOriginalSuccessorState.step_some,
    ``SourceOriginalSuccessorState.toInput_exec,
    ``SourceOriginalSuccessorState.use15_exec,
    ``SourceOriginalSuccessorState.use29_exec,
    ``SourceOriginalSuccessorState.use48_exec,
    ``SourceOriginalSuccessorState.working_get]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"ORIGINAL_SUCCESSOR_AXIOMS_GREEN: {names.length} theorems"

#print axioms PNP.Concrete.ResidualReduction.SourceOriginalSuccessorInput.select_exec
#print axioms PNP.Concrete.ResidualReduction.SourceOriginalSuccessorRaw.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceOriginalSuccessorPolynomial.acceptsWithin
#print axioms PNP.Concrete.ResidualReduction.SourceOriginalSuccessorPolynomial.polynomial_output
#print axioms PNP.Concrete.ResidualReduction.SourceOriginalSuccessorPolynomial.exact_decoded_step
#print axioms PNP.Concrete.ResidualReduction.SourceOriginalSuccessorPolynomial.polynomial_step_sound
#print axioms PNP.Concrete.ResidualReduction.SourceOriginalSuccessorPolynomial.polynomial_output_bound
#print axioms PNP.Concrete.ResidualReduction.SourceOriginalSuccessorPolynomial.polynomial_machine_accepts

end PNP.Concrete.ResidualReduction.SourceOriginalSuccessorRegression

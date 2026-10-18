import PNP.Concrete.ResidualReduction.SourceHistoryPolynomial
import Lean

/-! Focused connection tests for the new complete-history boundary. Unchanged
selector and single-step suites are not imported or rerun. General kernel
contracts cover every input; finite executions challenge serialization order,
multi-step recursion, stopped inputs, malformed packets and protected state. -/

namespace PNP.Concrete.ResidualReduction.SourceHistoryRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceHistoryEncoding
open PNP.Concrete.ResidualReduction.SourceHistoryState
open PNP.Concrete.ResidualReduction.SourceHistoryPolynomial

private def unit : Family 1 := [⟨false,(true,false),(false,true)⟩]
private def unitStep : SourceClosure.ConstructedStep 0 1 := ⟨(true,()),0,(),[⟨true,false,true⟩]⟩
private def unitRecord : SourceChain.StepRecord := ⟨0,unit,unitStep⟩
private def unitResult : SourceEncoding.ReductionData := ⟨0,unitStep.output,[unitRecord]⟩
private def x : Affine 2 := (true,(false,false))
private def y : Affine 2 := (false,(true,false))
private def two : Family 2 := [⟨false,x,aConst 2 true⟩,⟨false,y,aConst 2 true⟩]
private def three : Family 3 :=
  [⟨false,(true,(false,(false,false))),aConst 3 true⟩,
   ⟨false,(false,(true,(false,false))),aConst 3 true⟩,
   ⟨false,(false,(false,(true,false))),aConst 3 true⟩]
private def nonlinear : Family 3 :=
  [⟨true,(false,x),(true,y)⟩,
   ⟨true,(false,aAdd x (aConst 2 true)),(true,aConst 2 false)⟩]

example : SourceHistoryRaw.answer [] = [false] := rfl
example : SourceHistoryRaw.answer [false] = [false] := rfl
example : (SourceHistoryState.initial [true,false]).get 0 = [true,false] := rfl
example : (SourceHistoryState.initial [true,false]).get 59 = [] := rfl
example (input : BitString) :
    ∃ used after, Exec SourceHistoryRaw.block (initial input) used after ∧
      used ≤ SourceHistoryRaw.budget input.length ∧ after.get 8 = SourceHistoryRaw.answer input :=
  SourceHistoryRaw.block_exec input
example : CompilerIO.AcceptsWithin program SourceHistoryRaw.sourceFuel := acceptsWithin
example : polynomial.program = .machine (CompilerIO.rawMachine program)
    (CompilerIO.runtimePolynomial 63 SourceHistoryRaw.sourceFuel) := polynomial_program
example (input : BitString) : polynomial.output input = SourceHistoryRaw.answer input := polynomial_output input
example (n : Nat) (F : Family n) :
    SourceHistoryRaw.outputCodec.decode (polynomial.output (packet F)) =
      some (some (SourceEncoding.toData (SourceChain.reduce n F))) := exact_decoded_result n F
example (n : Nat) (F : Family n) (r : SourceEncoding.ReductionData)
    (h : SourceHistoryRaw.outputCodec.decode (polynomial.output (packet F)) = some (some r)) :
    SourceChain.Linked F r.history r.core := history_linked n F r h
example (n : Nat) (F : Family n) (r : SourceEncoding.ReductionData)
    (h : SourceHistoryRaw.outputCodec.decode (polynomial.output (packet F)) = some (some r)) :
    SourceChain.stopped r.core := terminal n F r h
example (n : Nat) (F : Family n) (r : SourceEncoding.ReductionData)
    (h : SourceHistoryRaw.outputCodec.decode (polynomial.output (packet F)) = some (some r)) :
    r.history.length + r.dimension = n := dimension_accounting n F r h
example (input : BitString) :
    (polynomial.output input).length ≤ outputPolynomial.eval input.length := polynomial_output_bound input
example (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 63 SourceHistoryRaw.sourceFuel).eval input.length) input = .accept :=
  polynomial_machine_accepts input

private def runBounded (p : Program 63) (start : Store 63) (limit : Nat) :
    IO (Nat × BitRegister.Configuration 63) := do
  let mut state : BitRegister.Configuration 63 := ⟨.running 0,start⟩
  let mut used := 0
  for _ in [0:limit] do
    if state.control == .accepted then break
    state := BitRegister.run p 1 state
    used := used + 1
  if state.control != .accepted then throw (IO.userError "History regression instruction cap reached")
  return (used,state)

private def sameStore (counter : IO.Ref Nat) (actual : BitRegister.Configuration 63)
    (expected : Store 63) (label : String) : IO Unit := do
  if actual.control != .accepted then throw (IO.userError (label ++ ": did not halt"))
  for i in List.finRange 63 do
    if actual.store.get i != expected.get i then throw (IO.userError (label ++ ": state mismatch"))
  counter.modify (· + 1)

private def checkInput (counter : IO.Ref Nat) (p : Program 63) (input expected : BitString) : IO Nat := do
  let start := initial input
  for i in List.finRange 63 do
    if start.get i != (if i.val == 0 then input else []) then
      throw (IO.userError "History runner has hidden startup data")
  let (used,actual) ← runBounded p start 1000000
  if used > SourceHistoryRaw.sourceFuel.eval input.length ||
      actual.store.get 8 != expected || actual.store.get 8 != SourceHistoryRaw.answer input then
    throw (IO.userError "History output or original-input polynomial budget differs")
  let target := match SourceMatrixEncoding.codec.decode input with
    | none => SourceHistoryInput.failed input
    | some ⟨n,F⟩ => work [] expected (SourceHistoryLoop.finished n F [])
  sameStore counter actual target "Complete history"
  return used

private def dirty : (n : Nat) → Store n
  | 0 => .nil
  | n + 1 => .cons [true,false,true] (dirty n)

#eval (show IO Unit from do
  let counter ← IO.mkRef 0
  let saved : Saved := ⟨[true],[false],[true,false],[false,true],[true,true],[false,false],[true,false,true]⟩
  let cleared := BitRegister.run (reset.program 0 8) 58 ⟨.running 0,full (dirty 56) saved⟩
  sameStore counter cleared (work [] [] saved) "Protected history workspace reset"
  for field in [Field.current,.dimension,.rows,.history,.count,.step,.active] do
    let actual := BitRegister.run ((prepend field).program 0 8) (8 * (field.word saved).length + 11)
      ⟨.running 0,work [] [false,true] saved⟩
    sameStore counter actual (work [] (field.word saved ++ [false,true]) saved) "Protected field serialization"
  let prior := [unitRecord,unitRecord]
  let recordStart := work [] [] (SourceHistoryRecord.before unit prior unitStep)
  let (_,recorded) ← runBounded (SourceHistoryRecord.block.program 0 8) recordStart 10000
  sameStore counter recorded (work [] [] (SourceHistoryRecord.after unit prior unitStep)) "Nonempty history append"
  let (_,advanced) ← runBounded (SourceHistoryAdvance.block.program 0 8)
    (work [] [] (SourceHistoryRecord.after unit prior unitStep)) 10000
  sameStore counter advanced (work [] [] (data unitStep.output (prior ++ [unitRecord]))) "Successor packet extraction"
  let (_,emitted) ← runBounded (SourceHistoryOutput.block.program 0 8)
    (work [] [] (stopped (data unitStep.output (prior ++ [unitRecord])))) 10000
  sameStore counter emitted
    (work [] (SourceHistoryOutput.bytes unitStep.output (prior ++ [unitRecord]))
      (stopped (data unitStep.output (prior ++ [unitRecord])))) "Chronological history emission"
  IO.println "HISTORY_PHASE: protected state and serialization passed"
  let p := program
  let unitBytes := SourceHistoryRaw.outputCodec.encode (some unitResult)
  if SourceHistoryRaw.canonicalAnswer 1 unit != unitBytes then
    throw (IO.userError "Independent one-step complete-history fixture differs")
  let unitTicks ← checkInput counter p (packet unit) unitBytes
  let short := BitRegister.run p (unitTicks - 1) (BitRegister.initial p (packet unit))
  if short.control == .accepted then throw (IO.userError "History accepted one instruction early")
  counter.modify (· + 1)
  for F in [([] : Family 0),[⟨true,false,true⟩],[⟨false,true,true⟩]] do
    let _ ← checkInput counter p (packet F) (SourceHistoryRaw.canonicalAnswer 0 F)
  for n in [1,2,4] do
    let F : Family n := []
    let expected := SourceHistoryRaw.outputCodec.encode (some ⟨n,F,[]⟩)
    let _ ← checkInput counter p (packet F) expected
  if (SourceChain.reduce 2 two).history.length != 2 ||
      (SourceChain.reduce 3 three).history.length != 3 then
    throw (IO.userError "Repeated-reduction fixtures did not exercise the complete loop")
  for F in [two,two.reverse,[⟨true,x,y⟩],two ++ [⟨true,x,y⟩]] do
    let _ ← checkInput counter p (packet F) (SourceHistoryRaw.canonicalAnswer 2 F)
  for F in [three,three.reverse,nonlinear] do
    let _ ← checkInput counter p (packet F) (SourceHistoryRaw.canonicalAnswer 3 F)
  IO.println "HISTORY_PHASE: complete zero-, one- and multi-step executions passed"
  let original := packet two
  let malformed : List BitString := [[],[true],[false],[true,false],[false,true,false],
    [false,false,true],[true,false,false,true],List.replicate 7 true,
    original.take (original.length - 1),original ++ [false],original ++ [true]]
  for input in malformed do
    if (SourceMatrixEncoding.codec.decode input).isSome then
      throw (IO.userError "Invalid history-input fixture became canonical")
    let _ ← checkInput counter p input [false]
  IO.println s!"HISTORY_REGRESSIONS_GREEN: {← counter.get} executions")

run_cmd do
  let names := [
    ``SourceHistoryEncoding.packet_bits,
    ``SourceHistoryEncoding.positive_packet,
    ``SourceHistoryEncoding.record_bits,
    ``SourceHistoryEncoding.records_append,
    ``SourceHistoryEncoding.records_singleton,
    ``SourceHistoryEncoding.record_accumulator,
    ``SourceHistoryEncoding.data_bits,
    ``SourceHistoryEncoding.step_bits,
    ``SourceHistoryEncoding.packet_length,
    ``SourceHistoryEncoding.successor_packet_bound,
    ``SourceHistoryState.core_exec,
    ``SourceHistoryState.use56_exec,
    ``SourceHistoryState.query_initial,
    ``SourceHistoryState.field_get,
    ``SourceHistoryState.working_get,
    ``SourceHistoryState.field_set,
    ``SourceHistoryState.field_push_exec,
    ``SourceHistoryState.field_clear_exec,
    ``SourceHistoryState.field_pop_exec,
    ``SourceHistoryState.save_exec,
    ``SourceHistoryState.reset_exec,
    ``SourceHistoryState.prepend_exec,
    ``SourceHistoryRecord.block_exec,
    ``SourceHistoryAdvance.skipHeader_exec,
    ``SourceHistoryAdvance.block_exec,
    ``SourceHistoryQuery.block_exec,
    ``SourceHistoryQuery.queried_positive,
    ``SourceHistoryQuery.stop_exec,
    ``SourceHistoryLoop.body_zero,
    ``SourceHistoryLoop.body_absent,
    ``SourceHistoryLoop.body_selected,
    ``SourceHistoryLoop.block_exec,
    ``SourceHistoryOutput.block_exec,
    ``SourceHistoryOutput.fuel_bound,
    ``SourceHistoryOutput.complete_exec,
    ``SourceHistoryBounds.stepPolynomial_eval,
    ``SourceHistoryBounds.selected_bound,
    ``SourceHistoryBounds.fuel_bound_at,
    ``SourceHistoryBounds.loop_bound,
    ``SourceHistoryBounds.output_bound,
    ``SourceHistoryBounds.complete_bound,
    ``SourceHistoryInput.use16_exec,
    ``SourceHistoryInput.loader_get,
    ``SourceHistoryInput.retain_exec,
    ``SourceHistoryInput.failure_exec,
    ``SourceHistoryInput.capture_exec,
    ``SourceHistoryInput.polynomial_eval,
    ``SourceHistoryInput.headers_exec,
    ``SourceHistoryInput.complete_check,
    ``SourceHistoryInput.short_check,
    ``SourceHistoryInput.extra_check,
    ``SourceHistoryInput.valid_exec,
    ``SourceHistoryInput.failed_header,
    ``SourceHistoryInput.failed_payload,
    ``SourceHistoryInput.block_exec,
    ``SourceHistoryRaw.answer_canonical,
    ``SourceHistoryRaw.answer_malformed,
    ``SourceHistoryRaw.sourceFuel_eval,
    ``SourceHistoryRaw.valid_exec,
    ``SourceHistoryRaw.malformed_exec,
    ``SourceHistoryRaw.block_exec,
    ``SourceHistoryPolynomial.source_result,
    ``SourceHistoryPolynomial.acceptsWithin,
    ``SourceHistoryPolynomial.source_output,
    ``SourceHistoryPolynomial.polynomial_program,
    ``SourceHistoryPolynomial.polynomial_output,
    ``SourceHistoryPolynomial.polynomial_canonical,
    ``SourceHistoryPolynomial.polynomial_malformed,
    ``SourceHistoryPolynomial.exact_decoded_result,
    ``SourceHistoryPolynomial.result_eq,
    ``SourceHistoryPolynomial.history_linked,
    ``SourceHistoryPolynomial.terminal,
    ``SourceHistoryPolynomial.dimension_accounting,
    ``SourceHistoryPolynomial.row_count,
    ``SourceHistoryPolynomial.canonical_output_bound,
    ``SourceHistoryPolynomial.polynomial_output_bound,
    ``SourceHistoryPolynomial.polynomial_machine_accepts]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"HISTORY_AXIOMS_GREEN: {names.length} theorems"

#print axioms PNP.Concrete.ResidualReduction.SourceHistoryLoop.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceHistoryRaw.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceHistoryPolynomial.acceptsWithin
#print axioms PNP.Concrete.ResidualReduction.SourceHistoryPolynomial.polynomial_output
#print axioms PNP.Concrete.ResidualReduction.SourceHistoryPolynomial.history_linked
#print axioms PNP.Concrete.ResidualReduction.SourceHistoryPolynomial.polynomial_machine_accepts

end PNP.Concrete.ResidualReduction.SourceHistoryRegression

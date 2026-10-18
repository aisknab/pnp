import PNP.Concrete.ResidualReduction.SourceReductionPolynomial
import Lean

/-! Focused tests at the original-input reduction boundary. Earlier system,
selector, history and normalization regression suites are not rerun. General
kernel contracts establish the all-input machine; executions challenge the new
relays, packet variants, original-dimension prefix, and complete composition. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeEnvelopeRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization NativeBitCodec
open PNP.Concrete.ResidualReduction.SourceNativeEnvelopeState

example (input : BitString) :
    ∃ used after, Exec SourceNativeEnvelopeInput.block (initial input) used after ∧
      used + 1 ≤ SourceNativeEnvelopeInput.sourceFuel.eval input.length ∧
      after.get 8 = SourceNativeEnvelopeInput.answer input := SourceNativeEnvelopeInput.block_exec input
example (input : BitString) :
    ∃ used, Exec SourceNativeHistoryBridge.block (work input [] []) used
      (SourceNativeHistoryBridge.result input) ∧
      used ≤ SourceNativeHistoryBridge.costPolynomial.eval input.length :=
  SourceNativeHistoryBridge.block_exec input
example (packet : NativeOutputPacket.Packet) :
    SourceNativeEnvelopePolynomial.polynomial.output (NativeOutputPacket.encode packet) =
      SourceEncoding.encodeNativePacket packet := SourceNativeEnvelopePolynomial.polynomial_canonical packet
example : CompilerIO.AcceptsWithin SourceNativeEnvelopePolynomial.program SourceNativeEnvelopeInput.sourceFuel :=
  SourceNativeEnvelopePolynomial.acceptsWithin
example (input : BitString) :
    boundedDecide (CompilerIO.rawMachine SourceNativeEnvelopePolynomial.program)
      ((CompilerIO.runtimePolynomial 64 SourceNativeEnvelopeInput.sourceFuel).eval input.length) input = .accept :=
  SourceNativeEnvelopePolynomial.machine_accepts input
example : SourceReductionPolynomial.polynomial.program =
    .compose SerializedNormalizer.polynomial.program SourceNativeEnvelopePolynomial.polynomial.program := rfl
example (input : BitString) :
    SourceReductionPolynomial.polynomial.output input = SourceEncoding.sourceEncode input :=
  SourceReductionPolynomial.polynomial_output input
example (input : BitString) :
    SourceReductionPolynomial.output input = SourceEncoding.sourceEncode input :=
  SourceReductionPolynomial.output_eq input
example (input : BitString) :
    boundedDecide SourceReductionPolynomial.rawRefinement.machine
      (SourceReductionPolynomial.rawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout :=
  SourceReductionPolynomial.halts input
example (input : BitString) :
    (SourceReductionPolynomial.output input).length ≤ SourceEncoding.sourceOutputPolynomial.eval input.length :=
  SourceReductionPolynomial.encoded_size input
example (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (packet : NativeSerializedNormalizer.packet input = .system c D) :
    SourceReductionPolynomial.output input = [true,true] ++ natural (2 * c) ++ SourceEncoding.dataCodec.encode
      (SourceEncoding.toData (SourceChain.reduce (2 * c) (NativeSource.family D))) :=
  SourceReductionPolynomial.system_output input c D packet
example (input assignment : BitString)
    (packet : NativeSerializedNormalizer.packet input = .model assignment) :
    SourceReductionPolynomial.output input = [true,false] ++ (listCodec bitCodec).encode assignment :=
  SourceReductionPolynomial.model_output input assignment packet
example : SourceNativeEnvelopeInput.answer [] = [false] := rfl
example : SourceNativeEnvelopeInput.answer [false,false,false] = [false] := rfl
example : SourceNativeEnvelopeInput.answer [false,false,true,false] = [true,false,false] := rfl

private def runBounded (p : Program 64) (start : Store 64) (limit : Nat) :
    IO (Nat × BitRegister.Configuration 64) := do
  let mut state : BitRegister.Configuration 64 := ⟨.running 0,start⟩
  let mut used := 0
  for _ in [0:limit] do
    if state.control == .accepted then break
    state := BitRegister.run p 1 state
    used := used + 1
  if state.control != .accepted then throw (IO.userError "Native envelope instruction cap reached")
  return (used,state)

private def sameStore (counter : IO.Ref Nat) (actual : BitRegister.Configuration 64)
    (expected : Store 64) (label : String) (countExecution : Bool := true) : IO Unit := do
  if actual.control != .accepted then throw (IO.userError (label ++ ": did not halt"))
  for i in List.finRange 64 do
    if actual.store.get i != expected.get i then
      throw (IO.userError (label ++ ": scratch or protected state differs"))
  if countExecution then counter.modify (· + 1)

private def dirty : (n : Nat) → Store n
  | 0 => .nil
  | n + 1 => .cons [true,false,true] (dirty n)

private def checkInput (counter : IO.Ref Nat) (p : Program 64) (input expected : BitString) :
    IO (Nat × BitRegister.Configuration 64) := do
  let start := initial input
  for i in List.finRange 64 do
    if start.get i != (if i.val == 0 then input else []) then
      throw (IO.userError "Native envelope has hidden initial data")
  let (used,actual) ← runBounded p start 2000000
  if used > SourceNativeEnvelopeInput.sourceFuel.eval input.length || actual.store.get 8 != expected then
    throw (IO.userError "Native envelope output or original-input cost bound differs")
  counter.modify (· + 1)
  return (used,actual)

#eval (show IO Unit from do
  let counter ← IO.mkRef 0
  let saved := [false,true,false]
  let workspace := ((dirty 63).set 0 [false,true]).set 8 [false,false,true]
  let relayed := BitRegister.run (relay.program 0 8) 65 ⟨.running 0,frame workspace saved⟩
  sameStore counter relayed (work [false,false,true] [] saved) "Relay clears every history register"
  let captured := BitRegister.run (captureDimension.program 0 8) 2 ⟨.running 0,frame workspace saved⟩
  sameStore counter captured (frame workspace (workspace.get 14)) "Original dimension capture"
  for dimension in [[],[true],[true,true],[false,true,false]] do
    for data in [[],[false,true,true]] do
      let input := true :: data
      let expected := true :: true :: (dimension.reverse ++ false :: data)
      let actual := BitRegister.run (SourceNativeEnvelopeOutput.block.program 0 8)
        (4 * dimension.length + 10) ⟨.running 0,work input [] dimension⟩
      sameStore counter actual (work [] expected dimension) "Original-dimension prefix"
    for input in [[],[false],[false,true]] do
      let actual := BitRegister.run (SourceNativeEnvelopeOutput.block.program 0 8) 3
        ⟨.running 0,work input [] dimension⟩
      sameStore counter actual (work input [false] dimension) "Failed history has no success prefix"
  IO.println "NATIVE_ENVELOPE_PHASE: protected dimension, complete scratch reset and exact prefixes passed"
  let p := SourceNativeEnvelopePolynomial.program
  let (used,_) ← checkInput counter p (NativeOutputPacket.encode .malformed) [false]
  let early := BitRegister.run p (used - 1) (BitRegister.initial p (NativeOutputPacket.encode .malformed))
  if early.control == .accepted then throw (IO.userError "Native envelope accepted one instruction early")
  counter.modify (· + 1)
  for assignment in [[],[false],[true],[true,false,true],[false,false,true,true]] do
    let expected := [true,false] ++ (listCodec bitCodec).encode assignment
    let (_,actual) ← checkInput counter p (NativeOutputPacket.encode (.model assignment)) expected
    sameStore counter actual (work ((listCodec bitCodec).encode assignment) expected []) "Model packet" false
  let changedDimension ← IO.mkRef false
  for c in [0,1,2] do
    let terms : NativeCoefficients.Coefficients c := (List.finRange c).map (fun i => (i,false))
    let systems : List (NativeSparseSystem.System c) :=
      [⟨[],[],[]⟩,⟨terms,[],[]⟩,⟨terms ++ terms,[],[terms.reverse]⟩]
    for D in systems do
      let packet := NativeOutputPacket.Packet.system c D
      let reduced := SourceEncoding.toData (SourceChain.reduce (2 * c) (NativeSource.family D))
      if reduced.dimension < 2 * c then changedDimension.set true
      let expected := [true,true] ++ natural (2 * c) ++ SourceEncoding.dataCodec.encode reduced
      let (_,actual) ← checkInput counter p (NativeOutputPacket.encode packet) expected
      sameStore counter actual (work [] expected (List.replicate (2 * c) true)) "Complete native history" false
  if !(← changedDimension.get) then
    throw (IO.userError "Native history fixtures did not distinguish original and reduced dimensions")
  let productSystem : NativeSparseSystem.System 1 := ⟨[(0,false)],[((0,false),[(0,true)])],[]⟩
  let productPacket := NativeOutputPacket.Packet.system 1 productSystem
  let productExpected := SourceEncoding.encodeNativePacket productPacket
  let (_,productActual) ← checkInput counter p (NativeOutputPacket.encode productPacket) productExpected
  sameStore counter productActual (work [] productExpected [true,true]) "Product-system history" false
  IO.println "NATIVE_ENVELOPE_PHASE: canonical malformed, model and complete system histories passed"
  let rejected : List BitString := [[],[true],[false],[false,false],[false,true],[false,true,true],
    [true,false,false],[true,true,true],[false,true,false],[false,true,false,true]]
  for input in rejected do
    let _ ← checkInput counter p input [false]
  for input in [[],[false],[true],[true,false],[false,false],[true,true,false]] do
    let packet := NativeSerializedNormalizer.packet input
    let _ ← checkInput counter p (NativeOutputPacket.encode packet) (SourceEncoding.sourceEncode input)
  IO.println s!"NATIVE_ENVELOPE_REGRESSIONS_GREEN: {← counter.get} executions")

run_cmd do
  let names := [
    ``SourceNativeEnvelopeState.core_exec,
    ``SourceNativeEnvelopeState.relay_cleared,
    ``SourceNativeEnvelopeState.relay63_exec,
    ``SourceNativeEnvelopeState.relay_exec,
    ``SourceNativeEnvelopeState.capture_exec,
    ``SourceNativeEnvelopeState.system_exec,
    ``SourceNativeEnvelopeState.system_output,
    ``SourceNativeEnvelopeState.system_dimension,
    ``SourceNativeEnvelopeState.history_exec,
    ``SourceNativeEnvelopeOutput.reverse_exec,
    ``SourceNativeEnvelopeOutput.success_exec,
    ``SourceNativeEnvelopeOutput.block_exec,
    ``SourceNativeEnvelopeOutput.result_output,
    ``SourceNativeEnvelopeOutput.fuel_bound,
    ``SourceNativeHistoryBridge.costPolynomial_eval,
    ``SourceNativeHistoryBridge.family_bound,
    ``SourceNativeHistoryBridge.dimension_bound,
    ``SourceNativeHistoryBridge.block_exec,
    ``SourceNativeHistoryBridge.result_output,
    ``SourceNativeHistoryBridge.canonical_answer,
    ``SourceNativeEnvelopeInput.reject_exec,
    ``SourceNativeEnvelopeInput.model_exec,
    ``SourceNativeEnvelopeInput.consume_exec,
    ``SourceNativeEnvelopeInput.modelTag_exec,
    ``SourceNativeEnvelopeInput.systemTag_exec,
    ``SourceNativeEnvelopeInput.kind_exec,
    ``SourceNativeEnvelopeInput.sourceFuel_eval,
    ``SourceNativeEnvelopeInput.block_exec,
    ``SourceNativeEnvelopeInput.canonical_answer,
    ``SourceNativeEnvelopePolynomial.source_result,
    ``SourceNativeEnvelopePolynomial.acceptsWithin,
    ``SourceNativeEnvelopePolynomial.source_output,
    ``SourceNativeEnvelopePolynomial.polynomial_program,
    ``SourceNativeEnvelopePolynomial.polynomial_output,
    ``SourceNativeEnvelopePolynomial.polynomial_canonical,
    ``SourceNativeEnvelopePolynomial.output_length,
    ``SourceNativeEnvelopePolynomial.machine_accepts,
    ``SourceNativeEnvelopePolynomial.machine_output,
    ``SourceReductionPolynomial.polynomial_output,
    ``SourceReductionPolynomial.output_eq,
    ``SourceReductionPolynomial.halts,
    ``SourceReductionPolynomial.output_size,
    ``SourceReductionPolynomial.encoded_size,
    ``SourceReductionPolynomial.malformed_output,
    ``SourceReductionPolynomial.model_output,
    ``SourceReductionPolynomial.system_output,
    ``SourceNativeEnvelopePolynomial.rawRefinement,
    ``SourceReductionPolynomial.rawRefinement]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"NATIVE_ENVELOPE_AXIOMS_GREEN: {names.length} declarations"

#print axioms PNP.Concrete.ResidualReduction.SourceNativeHistoryBridge.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceNativeHistoryBridge.canonical_answer
#print axioms PNP.Concrete.ResidualReduction.SourceNativeEnvelopePolynomial.machine_accepts
#print axioms PNP.Concrete.ResidualReduction.SourceReductionPolynomial.polynomial_output
#print axioms PNP.Concrete.ResidualReduction.SourceReductionPolynomial.output_eq
#print axioms PNP.Concrete.ResidualReduction.SourceReductionPolynomial.halts
#print axioms PNP.Concrete.ResidualReduction.SourceReductionPolynomial.encoded_size

end PNP.Concrete.ResidualReduction.SourceNativeEnvelopeRegression

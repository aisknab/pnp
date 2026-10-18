import PNP.Concrete.ResidualReduction.SourceReplayEndpointClosed
import Lean

/-! Focused encoded-output boundary checks. The previous observed-answer
suite is not imported or rerun. These tests inspect the actual program's
configured output register and compare with the original request answer and
existing canonical option/list codec, including failures after partial work. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEndpointClosedRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence (Registers)
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceReplayEndpointRunState (Parameters)

example (count : Nat) (r : Registers) :
    Exec SourceReplayEndpointOutput.unaryLoop ({r with input := List.replicate count true}).store
      (3 * count + 1) ({r with input := [],output := List.replicate count true ++ r.output}).store :=
  SourceReplayEndpointOutput.unary_exec count r
example (cursor point : BitString) (p : Parameters) (loopGood good : Bool) :
    Exec SourceReplayEndpointOutput.block (SourceReplayEndpointRunState.work 0 cursor point p loopGood good)
      (SourceReplayEndpointOutput.fuel p good) (SourceReplayEndpointOutput.result cursor point p loopGood good) :=
  SourceReplayEndpointOutput.block_exec cursor point p loopGood good
example (input : BitString) :
    Exec SourceReplayEndpointClosed.block (SourceReplayEndpointState.initial input)
      (SourceReplayEndpointClosed.fuel input) (SourceReplayEndpointClosed.result input) :=
  SourceReplayEndpointClosed.block_exec input
example : SourceReplayEndpointClosed.program.input = 0 ∧ SourceReplayEndpointClosed.program.output = 8 ∧
    SourceReplayEndpointClosed.program.entry = 0 := SourceReplayEndpointClosed.program_ports
example (input : BitString) (accepted : SourceReplayEndpointClosed.accepted input = true) :
    (SourceReplayEndpointClosed.replayed input).point.length =
      SourceReplayEndpointOutput.width (SourceReplayEndpointExecute.parameters input) :=
  SourceReplayEndpointClosed.accepted_width input accepted
example (input : BitString) :
    (SourceReplayEndpointClosed.result input).get 8 =
      SourceReplayEndpointOutput.codec.encode (SourceReplayRequest.answer input) := SourceReplayEndpointClosed.output_eq input
example (input : BitString) :
    SourceReplayEndpointOutput.codec.decode ((SourceReplayEndpointClosed.result input).get 8) =
      some (SourceReplayRequest.answer input) := SourceReplayEndpointClosed.decode_output input
example (input : BitString) : ((SourceReplayEndpointClosed.result input).get 8).length ≤ 2 * input.length + 2 :=
  SourceReplayEndpointClosed.output_size_bound input
example (input : BitString) :
    SourceReplayEndpointClosed.fuel input ≤ input.length * (SourceReplayHistoryStack.allowance input.length +
      SourceReplayLoopMachine.allowance input.length (2 * input.length)) +
      (16 * input.length + 36) * input.length + 80 * input.length + 380 := SourceReplayEndpointClosed.fuel_bound input
example (input : BitString) :
    ∃ after, Exec SourceReplayEndpointClosed.block (SourceReplayEndpointState.initial input)
        (SourceReplayEndpointClosed.fuel input) after ∧
      after.get 8 = SourceReplayEndpointOutput.codec.encode (SourceReplayRequest.answer input) ∧
      SourceReplayEndpointClosed.fuel input ≤ input.length * (SourceReplayHistoryStack.allowance input.length +
        SourceReplayLoopMachine.allowance input.length (2 * input.length)) +
        (16 * input.length + 36) * input.length + 80 * input.length + 380 ∧
      (after.get 8).length ≤ 2 * input.length + 2 := SourceReplayEndpointClosed.all_input input

run_cmd do
  let names := [
    ``SourceReplayEndpointOutput.bit_sequence,
    ``SourceReplayEndpointOutput.some_bytes,
    ``SourceReplayEndpointOutput.none_bytes,
    ``SourceReplayEndpointOutput.unary_exec,
    ``SourceReplayEndpointOutput.push_output_exec,
    ``SourceReplayEndpointOutput.selectWidth_exec,
    ``SourceReplayEndpointOutput.success_exec,
    ``SourceReplayEndpointOutput.block_exec,
    ``SourceReplayEndpointOutput.read_output,
    ``SourceReplayEndpointOutput.result_output,
    ``SourceReplayEndpointOutput.bytes_codec,
    ``SourceReplayEndpointOutput.width_bound,
    ``SourceReplayEndpointOutput.fuel_bound,
    ``SourceReplayEndpointClosed.program_ports,
    ``SourceReplayEndpointClosed.block_exec,
    ``SourceReplayEndpointClosed.accepted_width,
    ``SourceReplayEndpointClosed.answer_view,
    ``SourceReplayEndpointClosed.output_eq,
    ``SourceReplayEndpointClosed.decode_output,
    ``SourceReplayEndpointClosed.output_size_bound,
    ``SourceReplayEndpointClosed.fuel_bound,
    ``SourceReplayEndpointClosed.all_input]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"REPLAY_ENDPOINT_CLOSED_AXIOMS_GREEN: {names.length} declarations"

private def words : Nat → List BitString
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun w => [false :: w,true :: w])
private def constantPoint : (n : Nat) → Bool → Point n
  | 0,_ => ()
  | n + 1,b => (b,constantPoint n b)
private def emptyRecord (n : Nat) : StepRecord :=
  ⟨n,[],⟨(),0,constantPoint n false,[]⟩⟩
private def descending : Nat → List StepRecord
  | 0 => []
  | n + 1 => emptyRecord n :: descending n
private def q0 : StepRecord := emptyRecord 0
private def q1 : StepRecord :=
  let F : Family 2 := [⟨false,(false,(true,false)),aConst 2 true⟩]
  ⟨1,F,⟨(true,()),0,(true,()),[⟨true,aConst 1 false,aConst 1 true⟩]⟩⟩
private def q2 : StepRecord :=
  let F : Family 3 := [⟨true,aConst 3 false,aConst 3 true⟩,⟨false,aConst 3 true,aConst 3 true⟩]
  ⟨2,F,⟨(true,(false,())),2,(true,(false,())),[]⟩⟩

private def expectedCodec : Codec (Option BitString) := MatrixSolutionEncoding.optionCodec (listCodec bitCodec)
private def record (counts : IO.Ref (Nat × Nat)) (reference : Option BitString) : IO Unit :=
  if reference.isSome then counts.modify (fun (good,bad) => (good + 1,bad))
  else counts.modify (fun (good,bad) => (good,bad + 1))
private def same (actual expected : Store 40) : IO Unit := do
  for i in List.finRange 40 do
    if actual.get i != expected.get i then throw (IO.userError "Serialized replay complete register state differs")

private def serializerCheck (program : Program 40) (counts : IO.Ref (Nat × Nat))
    (point : BitString) (recover loopGood good : Bool) : IO Unit := do
  let n := point.length
  let p : Parameters := ⟨recover,(if recover then n else n + 1),(if recover then n + 1 else n),[false,true,false]⟩
  let cursor := [true,false,true]
  let supplied := if good then point else true :: point
  let start := SourceReplayEndpointRunState.work 0 cursor supplied p loopGood good
  let ticks := SourceReplayEndpointOutput.fuel p good
  if ticks > 3 * (n + 1) + 7 then throw (IO.userError "Serializer exceeded its proved instruction bound")
  let actual := BitRegister.run program (ticks + 1) ⟨.running program.entry,start⟩
  if actual.control != .accepted then throw (IO.userError "Serializer did not halt")
  same actual.store (SourceReplayEndpointOutput.result cursor supplied p loopGood good)
  let reference := if good then some point else none
  if actual.store.get program.output != expectedCodec.encode reference then
    throw (IO.userError "Serializer did not emit the canonical optional witness")
  if !good && actual.store.get program.output != [false] then
    throw (IO.userError "Serializer returned a retained intermediate witness after rejection")
  record counts reference

private def closedCheck (program : Program 40) (counts : IO.Ref (Nat × Nat)) (input : BitString) : IO (Store 40) := do
  let ticks := SourceReplayEndpointClosed.fuel input
  if ticks > input.length * (SourceReplayHistoryStack.allowance input.length +
      SourceReplayLoopMachine.allowance input.length (2 * input.length)) +
      (16 * input.length + 36) * input.length + 80 * input.length + 380 then
    throw (IO.userError "Serialized endpoint exceeded its proved input-size instruction bound")
  let actual := BitRegister.run program (ticks + 1) ⟨.running program.entry,SourceReplayEndpointState.initial input⟩
  if actual.control != .accepted then throw (IO.userError "Serialized endpoint did not halt")
  same actual.store (SourceReplayEndpointClosed.result input)
  let reference := SourceReplayRequest.answer input
  let output := actual.store.get program.output
  if output != expectedCodec.encode reference then
    throw (IO.userError "Serialized endpoint differs from the original request and canonical codec")
  if output.length > 2 * input.length + 2 then throw (IO.userError "Serialized output exceeded its encoded-input size bound")
  match reference with
  | none => if output != [false] then throw (IO.userError "Rejected request returned an intermediate witness")
  | some point =>
    if output.length != 2 * point.length + 2 then throw (IO.userError "Serialized success has the wrong exact encoded length")
  record counts reference
  pure actual.store

#eval (show IO Unit from do
  let serializerCounts ← IO.mkRef (0,0)
  let rawCounts ← IO.mkRef (0,0)
  let serializer := SourceReplayEndpointOutput.block.program 0 8
  let program := SourceReplayEndpointClosed.program
  if program.input != 0 || program.output != 8 || program.entry != 0 then
    throw (IO.userError "Closed endpoint program ports differ")
  for n in List.range 5 do
    for point in words n do
      for recover in [false,true] do
        for loopGood in [false,true] do
          for good in [false,true] do
            serializerCheck serializer serializerCounts point recover loopGood good
  IO.println "REPLAY_ENDPOINT_CLOSED_PHASE: canonical success/failure serializer passed"
  for length in List.range 5 do
    for input in words length do
      discard (closedCheck program rawCounts input)
  for history in [[],[q0],[q1,q0],[q2,q1,q0]] do
    let n := history.length
    let data := SourceEncoding.dataCodec.encode (⟨0,[],history⟩ : SourceEncoding.ReductionData)
    for recover in [false,true] do
      let points := if recover then [[]] else words n
      for point in points do
        let r : SourceReplayRequest.Request := ⟨recover,n,data,point⟩
        let input := SourceReplayRequest.codec.encode r
        discard (closedCheck program rawCounts input)
        discard (closedCheck program rawCounts (input ++ [true]))
        discard (closedCheck program rawCounts (input.take (input.length - 1)))
        discard (closedCheck program rawCounts (SourceReplayRequest.codec.encode {r with dimension := n + 1}))
  let data := SourceEncoding.dataCodec.encode (⟨0,[],[q1,q0]⟩ : SourceEncoding.ReductionData)
  for bad in [[],[false],data ++ [true]] do
    for recover in [false,true] do
      discard (closedCheck program rawCounts (SourceReplayRequest.codec.encode ⟨recover,2,bad,[]⟩))
  let wrongStart ← closedCheck program rawCounts (SourceReplayRequest.codec.encode ⟨true,2,data,[true]⟩)
  let wrongEnd ← closedCheck program rawCounts (SourceReplayRequest.codec.encode ⟨true,3,data,[]⟩)
  if wrongStart.get 8 != [false] || wrongEnd.get 8 != [false] || wrongEnd.get 28 != [true] then
    throw (IO.userError "Width rejection was not encoded independently of replay termination")
  let late := SourceEncoding.dataCodec.encode (⟨0,[],[q1,q1,q0]⟩ : SourceEncoding.ReductionData)
  let failed ← closedCheck program rawCounts (SourceReplayRequest.codec.encode ⟨true,3,late,[]⟩)
  if failed.get 8 != [false] || (failed.get 26).length != 2 then
    throw (IO.userError "Late failure exposed a partial witness as the final output")
  for n in [4,8] do
    let history := SourceEncoding.dataCodec.encode (⟨0,[],descending n⟩ : SourceEncoding.ReductionData)
    for recover in [false,true] do
      let point := if recover then [] else List.replicate n true
      discard (closedCheck program rawCounts (SourceReplayRequest.codec.encode ⟨recover,n,history,point⟩))
  for width in [8,32,64] do
    let empty := SourceEncoding.dataCodec.encode (⟨width,[],[]⟩ : SourceEncoding.ReductionData)
    for recover in [false,true] do
      for bit in [false,true] do
        discard (closedCheck program rawCounts (SourceReplayRequest.codec.encode ⟨recover,width,empty,List.replicate width bit⟩))
  let emptyData := SourceEncoding.dataCodec.encode (⟨0,[],[]⟩ : SourceEncoding.ReductionData)
  let emptyInput := SourceReplayRequest.codec.encode ⟨false,0,emptyData,[]⟩
  let emptySuccess ← closedCheck program rawCounts emptyInput
  let rejection ← closedCheck program rawCounts []
  if emptySuccess.get 8 != [true,false] || rejection.get 8 != [false] then
    throw (IO.userError "Empty successful witness was confused with rejection")
  if expectedCodec.decode (emptySuccess.get 8) != some (some []) ||
      expectedCodec.decode (rejection.get 8) != some none then
    throw (IO.userError "Output consumer could not distinguish success from failure")
  let ticks := SourceReplayEndpointClosed.fuel emptyInput
  let early := BitRegister.run program ticks ⟨.running program.entry,SourceReplayEndpointState.initial emptyInput⟩
  if early.control == .accepted then throw (IO.userError "Serialized endpoint accepted before its terminal instruction")
  let (sg,sb) ← serializerCounts.get
  let (rg,rb) ← rawCounts.get
  if sg == 0 || sb == 0 || rg == 0 || rb == 0 then throw (IO.userError "Encoded-output checks missed an outcome")
  IO.println s!"REPLAY_ENDPOINT_CLOSED_REGRESSIONS_GREEN: {sg + sb + rg + rb} literal executions; {sg + sb} serializer runs; {rg + rb} raw-request runs; {sg + rg} accepted; {sb + rb} rejected")

#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointOutput.unary_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointOutput.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointOutput.bytes_codec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointClosed.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointClosed.output_eq
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointClosed.decode_output
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointClosed.output_size_bound
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointClosed.fuel_bound
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointClosed.all_input

end PNP.Concrete.ResidualReduction.SourceReplayEndpointClosedRegression

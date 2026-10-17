import PNP.Concrete.ResidualReduction.SourceReplayParser
import Lean

/-! Focused strict-request boundary checks. Earlier affine, contraction and
normalization suites are reused, not rerun. Canonical requests, truncations,
trailing bytes and exhaustive small malformed strings are compared with the
independent codec. General theorems retain authority over arbitrary inputs. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayParserRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.SourceReplayParserState

example (input : BitString) :
    (listCodec bitCodec).parse input =
      if SourceReplayBlob.valid input then some (SourceReplayBlob.bytes input,SourceReplayBlob.rest input) else none :=
  SourceReplayBlob.parse_eq input
example (r : Registers) (input : BitString) :
    Exec SourceReplayBlob.block ({r with input := input}).store (SourceReplayBlob.fuel input)
      (SourceReplayBlob.result r input).store := SourceReplayBlob.block_exec r input
example (input : BitString) : SourceReplayBlob.fuel input ≤ 13 * input.length + 18 :=
  SourceReplayBlob.fuel_bound input
example (input : BitString) : SourceReplayRequest.codec.parse input = SourceReplayRequest.parse input :=
  SourceReplayRequest.codec_parse input
example (r : SourceReplayRequest.Request) : SourceReplayRequest.accepted (SourceReplayRequest.codec.encode r) = some r :=
  SourceReplayRequest.roundtrip r
example (input : BitString) :
    Exec SourceReplayParser.block (initial input) (SourceReplayParser.fuel input) (SourceReplayParser.result input) :=
  SourceReplayParser.block_exec input
example (input : BitString) :
    SourceReplayParser.view (SourceReplayParser.completedSaved input) = SourceReplayRequest.codec.decode input :=
  SourceReplayParser.parsed_fields input
example (input : BitString) : SourceReplayParser.fuel input ≤ 30 * input.length + 83 :=
  SourceReplayParser.fuel_bound input
example (r : SourceReplayRequest.Request) : SourceReplayRequest.answer (SourceReplayRequest.codec.encode r) =
    (if r.recover then SourceEncoding.recoverBytes r.dimension r.data r.witness
      else SourceEncoding.projectBytes r.dimension r.data r.witness) :=
  SourceReplayRequest.answer_canonical r

private def words : Nat → List BitString
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun w => [false :: w,true :: w])
private def same {n : Nat} (counter : IO.Ref Nat) (p : Program n) (start expected : Store n)
    (ticks : Nat) (label : String) : IO Unit := do
  let actual := BitRegister.run p (ticks + 1) ⟨.running 0,start⟩
  if actual.control != .accepted then throw (IO.userError (label ++ ": instruction bound did not halt"))
  for i in List.finRange n do
    if actual.store.get i != expected.get i then throw (IO.userError (label ++ ": complete store differs"))
  counter.modify (· + 1)

private def checkRequest (counter : IO.Ref Nat) (p : Program 14) (input : BitString) : IO Bool := do
  let expected := SourceReplayParser.result input
  let ticks := SourceReplayParser.fuel input
  if ticks > 30 * input.length + 83 then throw (IO.userError "Outer request exceeded its linear bound")
  for i in List.finRange 14 do
    if (initial input).get i != (if i.val == 0 then input else []) then
      throw (IO.userError "Request parser has hidden initial fields")
  same counter p (initial input) expected ticks "All-input request parse"
  match SourceReplayRequest.codec.decode input with
  | none =>
    if expected.get 13 != [] then throw (IO.userError "Malformed request was accepted")
    return false
  | some r =>
    let fields : Saved := ⟨[r.recover],List.replicate r.dimension true,r.data,r.witness,[true]⟩
    for i in List.finRange 14 do
      if expected.get i != (work [] [] fields).get i then
        throw (IO.userError "Accepted request fields disagree with canonical codec")
    return true

#eval (show IO Unit from do
  let count ← IO.mkRef 0
  let blob := SourceReplayBlob.block.program 0 8
  for width in List.range 9 do
    for input in words width do
      let r : Registers := ⟨[],[false,true],[true],[false,true],[false],[false],[true],[false,true,false],[true]⟩
      let expected := SourceReplayBlob.result r input
      let parsed := (listCodec bitCodec).parse input
      match parsed with
      | none =>
        if expected.mode != [] then throw (IO.userError "Malformed byte field was accepted")
      | some (bytes,suffix) =>
        if expected.mode != [true] || expected.output != bytes || expected.input != suffix then
          throw (IO.userError "Byte field disagrees with existing codec")
      let ticks := SourceReplayBlob.fuel input
      if ticks > 13 * input.length + 18 then throw (IO.userError "Byte field exceeded its linear bound")
      same count blob ({r with input := input}).store expected.store ticks "Strict byte field"
  IO.println "REPLAY_PARSER_PHASE: exhaustive byte fields, truncations and protected state passed"
  let p := SourceReplayParser.block.program 0 8
  let modes ← IO.mkRef (false,false)
  for width in List.range 10 do
    for input in words width do
      let _ ← checkRequest count p input
  for mode in [false,true] do
    for dimension in [0,1,2,5] do
      for data in [[],[true],[false,true,false],[true,true,false,true]] do
        for witness in [[],[false],[true,true],[false,true,false]] do
          let r : SourceReplayRequest.Request := ⟨mode,dimension,data,witness⟩
          let input := SourceReplayRequest.codec.encode r
          if !(← checkRequest count p input) then throw (IO.userError "Canonical request was rejected")
          modes.modify (fun seen => if mode then (seen.1,true) else (true,seen.2))
          for cut in List.range input.length do
            if (← checkRequest count p (input.take cut)) then
              throw (IO.userError "A truncated canonical request was accepted")
          for extra in [false,true] do
            if (← checkRequest count p (input ++ [extra])) then
              throw (IO.userError "A trailing request byte was accepted")
  if (← modes.get) != (true,true) then throw (IO.userError "Both replay directions were not covered")
  let input := SourceReplayRequest.codec.encode ⟨true,0,[],[]⟩
  let early := BitRegister.run p (SourceReplayParser.fuel input) ⟨.running 0,initial input⟩
  if early.control == .accepted then throw (IO.userError "Outer request accepted one instruction early")
  IO.println s!"REPLAY_PARSER_REGRESSIONS_GREEN: {← count.get} executions")

run_cmd do
  let names := [
    ``SourceReplayBlob.parseN_bits,
    ``SourceReplayBlob.parse_eq,
    ``SourceReplayBlob.bytes_bound,
    ``SourceReplayBlob.rest_bound,
    ``SourceReplayBlob.block_exec,
    ``SourceReplayBlob.fuel_bound,
    ``SourceReplayRequest.codec_parse,
    ``SourceReplayRequest.accepted_eq,
    ``SourceReplayRequest.roundtrip,
    ``SourceReplayRequest.first_bound,
    ``SourceReplayRequest.second_bound,
    ``SourceReplayRequest.suffix_bound,
    ``SourceReplayRequest.answer_canonical,
    ``SourceReplayRequest.malformed,
    ``SourceReplayParserState.core_exec,
    ``SourceReplayParserState.reset_exec,
    ``SourceReplayParserState.guard_exec,
    ``SourceReplayParserState.saveHeader_exec,
    ``SourceReplayParserState.dataFinish_exec,
    ``SourceReplayParserState.witnessFinish_exec,
    ``SourceReplayParserState.finish_exec,
    ``SourceReplayParserState.mode_exec,
    ``SourceReplayParserState.modeFuel_bound,
    ``SourceReplayParser.headers_exec,
    ``SourceReplayParser.readData_exec,
    ``SourceReplayParser.readWitness_exec,
    ``SourceReplayParser.block_exec,
    ``SourceReplayParser.fuel_bound,
    ``SourceReplayParser.parsed_fields,
    ``SourceReplayParser.all_input]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"REPLAY_PARSER_AXIOMS_GREEN: {names.length} declarations"

#print axioms PNP.Concrete.ResidualReduction.SourceReplayBlob.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayBlob.parse_eq
#print axioms PNP.Concrete.ResidualReduction.SourceReplayParser.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayParser.parsed_fields
#print axioms PNP.Concrete.ResidualReduction.SourceReplayParser.fuel_bound

end PNP.Concrete.ResidualReduction.SourceReplayParserRegression

import PNP.Concrete.ResidualReduction.SourceReplayRecordStack
import Lean

/-! Regression coverage for the new parser-to-stack boundary. The unchanged
record parser's exhaustive cases are not repeated: this suite targets stack
preservation, exact consumed bytes, delimiter order and protected registers. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayRecordStackRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain

example (input out : BitString) (s : SourceReplayRecordState.Saved) :
    Exec SourceReplayRecordStack.block (SourceReplayRecordStack.writing input out s)
      (SourceReplayRecordStack.fuel s) (SourceReplayRecordStack.writing input (SourceReplayRecordStack.bytes s ++ out) s) :=
  SourceReplayRecordStack.block_exec input out s
example (q : StepRecord) (good : Bool) :
    SourceReplayRecordStack.bytes (SourceReplayRecordState.fromFields (SourceReplayRecordFields.recordFields q) good) =
      SourceEncoding.recordCodec.encode q := SourceReplayRecordStack.bytes_record q good
example (input : BitString) (good : SourceReplayRecordFields.valid input = true) :
    SourceReplayRecordStack.bytes (SourceReplayRecordState.capture input) ++ SourceReplayRecordFields.rest input = input :=
  SourceReplayRecordStack.captured_prefix input good
example (input history : BitString) :
    Exec SourceReplayRecordStack.oneBlock (SourceReplayRecordStack.inputState input history)
      (SourceReplayRecordStack.oneFuel input) (SourceReplayRecordStack.outputState input history) :=
  SourceReplayRecordStack.one_exec input history
example (input : BitString) :
    SourceReplayRecordStack.oneFuel input ≤ 32 * input.length * input.length + 153 * input.length + 352 :=
  SourceReplayRecordStack.oneFuel_bound input
example (input history : BitString) :
    match SourceEncoding.recordCodec.parse input with
    | none => SourceReplayRecordStack.outputState input history =
        SourceReplayRecordStack.stacked (SourceReplayRecordState.result input) history
    | some (q,suffix) => SourceReplayRecordStack.outputState input history =
        SourceReplayRecordStack.stacked
          (SourceReplayRecordState.work suffix (SourceReplayRecordState.fromFields (SourceReplayRecordFields.recordFields q) true))
          (SourceEncoding.recordCodec.encode q ++ history) :=
  SourceReplayRecordStack.one_parse_contract input history
example (input history : BitString) (q : StepRecord) (suffix : BitString)
    (parsed : SourceEncoding.recordCodec.parse input = some (q,suffix)) :
    Exec SourceReplayRecordStack.oneBlock (SourceReplayRecordStack.inputState input history)
      (SourceReplayRecordStack.oneFuel input)
      (SourceReplayRecordStack.stacked
        (SourceReplayRecordState.work suffix (SourceReplayRecordState.fromFields (SourceReplayRecordFields.recordFields q) true))
        (SourceEncoding.recordCodec.encode q ++ history)) :=
  SourceReplayRecordStack.one_parsed_exec input history q suffix parsed

private def words : Nat → List BitString
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun w => [false :: w,true :: w])
private def points : (n : Nat) → List (Point n)
  | 0 => [()]
  | n + 1 => (points n).flatMap (fun p => [(false,p),(true,p)])
private def zeroPoint : (n : Nat) → Point n
  | 0 => ()
  | n + 1 => (false,zeroPoint n)
private def families (n : Nat) : List (Family n) :=
  let zero := aConst n false
  let one := aConst n true
  [[],[⟨false,one,one⟩],[⟨true,zero,one⟩],[⟨true,one,zero⟩,⟨false,one,one⟩]]
private def compareStore {n : Nat} (a b : Store n) (label : String) : IO Unit := do
  for i in List.finRange n do
    if a.get i != b.get i then throw (IO.userError (label ++ ": register state differs"))
private def check (p : Program 27) (counter : IO.Ref Nat) (input history : BitString) : IO Bool := do
  let ticks := SourceReplayRecordStack.oneFuel input
  if ticks > 32 * input.length * input.length + 153 * input.length + 352 then
    throw (IO.userError "Parser-to-stack step exceeded its proved encoded-size instruction bound")
  let actual := BitRegister.run p (ticks + 1) ⟨.running 0,SourceReplayRecordStack.inputState input history⟩
  if actual.control != .accepted then throw (IO.userError "Parser-to-stack step did not halt within its proved count")
  compareStore actual.store (SourceReplayRecordStack.outputState input history) "Parser-to-stack step"
  counter.modify (· + 1)
  match SourceEncoding.recordCodec.parse input with
  | none =>
    if actual.store.get 24 != [] || actual.store.get 26 != history then
      throw (IO.userError "Malformed record changed the protected stack or was accepted")
    return false
  | some (q,suffix) =>
    let expected := SourceReplayRecordStack.stacked
      (SourceReplayRecordState.work suffix (SourceReplayRecordState.fromFields (SourceReplayRecordFields.recordFields q) true))
      (SourceEncoding.recordCodec.encode q ++ history)
    compareStore actual.store expected "Independent codec and stack order"
    if SourceEncoding.recordCodec.encode q ++ suffix != input then
      throw (IO.userError "Stack prefix is not exactly the consumed input")
    return true

#eval (show IO Unit from do
  let combined ← IO.mkRef 0
  let serial ← IO.mkRef 0
  let program := SourceReplayRecordStack.oneBlock.program 0 26
  let writer := SourceReplayRecordStack.block.program 0 8
  let histories : List BitString := [[],[true,false],[false,true,true,false]]
  for word in [[],[false],[true,false,true],[false,true,true,false]] do
    for validity in [[],[false,true]] do
      let s : SourceReplayRecordState.Saved := ⟨word,[true,false],word.reverse,[false,true],[],[true],word,[false,false,true],validity⟩
      for history in histories do
        for cursor in [[],[true,false,true]] do
          let actual := BitRegister.run writer (SourceReplayRecordStack.fuel s + 1)
            ⟨.running 0,SourceReplayRecordStack.writing cursor history s⟩
          if actual.control != .accepted then throw (IO.userError "Raw field serializer did not halt")
          compareStore actual.store
            (SourceReplayRecordStack.writing cursor (SourceReplayRecordStack.bytes s ++ history) s) "Raw saved fields"
          serial.modify (· + 1)
  for width in List.range 7 do
    for input in words width do
      for history in histories do
        let _ ← check program combined input history
  for n in [0,1,2] do
    for F in families (n + 1) do
      for w in points F.length do
        for k in List.finRange (n + 1) do
          for G in families n do
            let q : StepRecord := ⟨n,F,⟨w,k,zeroPoint n,G⟩⟩
            for history in histories do
              for suffix in [[],[true,false,true]] do
                if !(← check program combined (SourceEncoding.recordCodec.encode q ++ suffix) history) then
                  throw (IO.userError "Canonical record was not prepended to the stack")
            let badPivot := natural n ++ ((SourceEncoding.familyCodec (n + 1)).encode F ++
              ((SourceEncoding.pointCodec F.length).encode w ++
                (natural (n + 1) ++ ((SourceEncoding.pointCodec n).encode (zeroPoint n) ++ (SourceEncoding.familyCodec n).encode G))))
            if (← check program combined badPivot [true,false]) then
              throw (IO.userError "Invalid pivot was placed on the stack")
    let q : StepRecord := ⟨n,[],⟨(),0,zeroPoint n,[]⟩⟩
    let encoded := SourceEncoding.recordCodec.encode q
    for cut in List.range encoded.length do
      if (← check program combined (encoded.take cut) [true,false,true]) then
        throw (IO.userError "Truncated record changed the stack")
  IO.println s!"REPLAY_RECORD_STACK_REGRESSIONS_GREEN: {← combined.get} combined executions; {← serial.get} serializer executions")

run_cmd do
  let names := [
    ``SourceReplayRecordStack.word_exec,
    ``SourceReplayRecordStack.header_exec,
    ``SourceReplayRecordStack.content_exec,
    ``SourceReplayRecordStack.block_exec,
    ``SourceReplayRecordStack.bytes_record,
    ``SourceReplayRecordStack.captured_prefix,
    ``SourceReplayRecordStack.captured_fuel_bound,
    ``SourceReplayRecordStack.append_exec,
    ``SourceReplayRecordStack.one_exec,
    ``SourceReplayRecordStack.oneFuel_bound,
    ``SourceReplayRecordStack.one_parse_contract,
    ``SourceReplayRecordStack.one_parsed_exec]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"REPLAY_RECORD_STACK_AXIOMS_GREEN: {names.length} declarations"

#print axioms PNP.Concrete.ResidualReduction.SourceReplayRecordStack.captured_prefix
#print axioms PNP.Concrete.ResidualReduction.SourceReplayRecordStack.one_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayRecordStack.oneFuel_bound
#print axioms PNP.Concrete.ResidualReduction.SourceReplayRecordStack.one_parsed_exec

end PNP.Concrete.ResidualReduction.SourceReplayRecordStackRegression

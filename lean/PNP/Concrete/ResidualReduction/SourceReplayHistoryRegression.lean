import PNP.Concrete.ResidualReduction.SourceReplayHistoryStack
import Lean

/-! Regression tests for the new unbounded counted-history loop and encoded
count boundary. Earlier single-record and serializer suites are not repeated.
History syntax is separate from the downstream dimension-link and semantic
checks; a prefix reader preserves following bytes rather than assuming EOF. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayHistoryRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain

example (count : Nat) (input history : BitString) :
    match parseN SourceEncoding.recordCodec.parse count input with
    | none => (SourceReplayHistoryFields.scan count input history).valid = false
    | some (records,suffix) => SourceReplayHistoryFields.scan count input history =
        ⟨suffix,encodeSeq SourceEncoding.recordCodec.encode records.reverse ++ history,true⟩ :=
  SourceReplayHistoryFields.parse_contract count input history
example (count : Nat) (input history : BitString) :
    (SourceReplayHistoryFields.scan count input history).input.length ≤ input.length ∧
      (SourceReplayHistoryFields.scan count input history).input.length +
        (SourceReplayHistoryFields.scan count input history).history.length ≤ input.length + history.length :=
  SourceReplayHistoryFields.bounds count input history
example (count : Nat) (input history : BitString) :
    Exec SourceReplayHistoryStack.loop (SourceReplayHistoryStack.work count input history true)
      (SourceReplayHistoryStack.loopFuel count input)
      (SourceReplayHistoryStack.finalState (SourceReplayHistoryFields.scan count input history)) :=
  SourceReplayHistoryStack.loop_exec count input history
example (count : Nat) (input : BitString) :
    SourceReplayHistoryStack.loopFuel count input ≤ count * SourceReplayHistoryStack.allowance input.length + 1 :=
  SourceReplayHistoryStack.loopFuel_bound count input
example (input history : BitString) :
    Exec SourceReplayHistoryStack.prefixBlock (SourceReplayHistoryStack.work 0 input history false)
      (SourceReplayHistoryStack.prefixFuel input)
      (SourceReplayHistoryStack.finalState (SourceReplayHistoryFields.readHistory input history)) :=
  SourceReplayHistoryStack.prefix_exec input history
example (input : BitString) :
    SourceReplayHistoryStack.prefixFuel input ≤ input.length * SourceReplayHistoryStack.allowance input.length + 4 * input.length + 43 :=
  SourceReplayHistoryStack.prefixFuel_bound input
example (input history : BitString) (records : List StepRecord) (suffix : BitString)
    (parsed : (listCodec SourceEncoding.recordCodec).parse input = some (records,suffix)) :
    Exec SourceReplayHistoryStack.prefixBlock (SourceReplayHistoryStack.work 0 input history false)
      (SourceReplayHistoryStack.prefixFuel input)
      (SourceReplayHistoryStack.work 0 suffix (encodeSeq SourceEncoding.recordCodec.encode records.reverse ++ history) true) :=
  SourceReplayHistoryStack.prefix_parsed_exec input history records suffix parsed
example (input history : BitString) (bad : (listCodec SourceEncoding.recordCodec).parse input = none) :
    (SourceReplayHistoryStack.finalState (SourceReplayHistoryFields.readHistory input history)).get 28 = [] :=
  SourceReplayHistoryStack.prefix_rejected input history bad
example (records : List StepRecord) (suffix history : BitString) :
    Exec SourceReplayHistoryStack.prefixBlock
      (SourceReplayHistoryStack.work 0 ((listCodec SourceEncoding.recordCodec).encode records ++ suffix) history false)
      (SourceReplayHistoryStack.prefixFuel ((listCodec SourceEncoding.recordCodec).encode records ++ suffix))
      (SourceReplayHistoryStack.work 0 suffix (encodeSeq SourceEncoding.recordCodec.encode records.reverse ++ history) true) :=
  SourceReplayHistoryStack.prefix_parsed_exec _ history records suffix
    ((listCodec SourceEncoding.recordCodec).roundtrip records suffix)

private def sample0 : StepRecord := ⟨0,[],⟨(),0,(),[]⟩⟩
private def sample1 : StepRecord :=
  let F : Family 2 := [⟨false,aConst 2 true,aConst 2 false⟩]
  ⟨1,F,⟨(true,()),1,(true,()),[⟨true,aConst 1 false,aConst 1 true⟩]⟩⟩
private def sample2 : StepRecord :=
  let F : Family 3 := [⟨true,aConst 3 false,aConst 3 true⟩,⟨false,aConst 3 true,aConst 3 true⟩]
  ⟨2,F,⟨(true,(false,())),2,(true,(false,())),[]⟩⟩
private def samples : List StepRecord := [sample0,sample1,sample2]
private def historiesOfLength : Nat → List (List StepRecord)
  | 0 => [[]]
  | n + 1 => (historiesOfLength n).flatMap (fun rest => samples.map (fun q => q :: rest))
private def words : Nat → List BitString
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun w => [false :: w,true :: w])
private def compareStore (a b : Store 30) (label : String) : IO Unit := do
  for i in List.finRange 30 do
    if a.get i != b.get i then throw (IO.userError (label ++ ": register state differs"))
private def checkBound (actual : Store 30) (input history : BitString) : IO Unit := do
  if (actual.get 0).length > input.length ||
      (actual.get 0).length + (actual.get 26).length > input.length + history.length then
    throw (IO.userError "History scan exceeded its consumed-byte storage bound")
private def checkLoop (p : Program 30) (counter : IO.Ref Nat) (count : Nat) (input history : BitString) : IO Unit := do
  let ticks := SourceReplayHistoryStack.loopFuel count input
  if ticks > count * SourceReplayHistoryStack.allowance input.length + 1 then
    throw (IO.userError "Counted history exceeded its proved instruction bound")
  let actual := BitRegister.run p (ticks + 1) ⟨.running 0,SourceReplayHistoryStack.work count input history true⟩
  if actual.control != .accepted then throw (IO.userError "Counted history did not halt within its proved count")
  compareStore actual.store (SourceReplayHistoryStack.finalState (SourceReplayHistoryFields.scan count input history)) "Counted history"
  checkBound actual.store input history
  match parseN SourceEncoding.recordCodec.parse count input with
  | none => if actual.store.get 28 != [] then throw (IO.userError "Incomplete counted history was accepted")
  | some (records,suffix) =>
    compareStore actual.store (SourceReplayHistoryStack.work 0 suffix
      (encodeSeq SourceEncoding.recordCodec.encode records.reverse ++ history) true) "Independent counted decoder"
  counter.modify (· + 1)
private def checkHeader (p : Program 30) (counter : IO.Ref Nat) (input history : BitString) : IO Bool := do
  let ticks := SourceReplayHistoryStack.prefixFuel input
  if ticks > input.length * SourceReplayHistoryStack.allowance input.length + 4 * input.length + 43 then
    throw (IO.userError "History reader exceeded its cubic encoded-size instruction bound")
  let actual := BitRegister.run p (ticks + 1) ⟨.running 0,SourceReplayHistoryStack.work 0 input history false⟩
  if actual.control != .accepted then throw (IO.userError "History reader did not halt within its proved count")
  compareStore actual.store (SourceReplayHistoryStack.finalState (SourceReplayHistoryFields.readHistory input history)) "Encoded-count history"
  checkBound actual.store input history
  counter.modify (· + 1)
  match (listCodec SourceEncoding.recordCodec).parse input with
  | none =>
    if actual.store.get 28 != [] then throw (IO.userError "Malformed encoded history was accepted")
    return false
  | some (records,suffix) =>
    compareStore actual.store (SourceReplayHistoryStack.work 0 suffix
      (encodeSeq SourceEncoding.recordCodec.encode records.reverse ++ history) true) "Independent list decoder and reverse order"
    return true

#eval (show IO Unit from do
  let loops ← IO.mkRef 0
  let headers ← IO.mkRef 0
  let loopProgram := SourceReplayHistoryStack.loop.program 0 26
  let fullProgram := SourceReplayHistoryStack.prefixBlock.program 0 26
  let accumulated : List BitString := [[],[true,false],[false,true,false]]
  for count in [0,1,2,3] do
    for width in List.range 6 do
      for input in words width do
        for history in accumulated.take 2 do
          checkLoop loopProgram loops count input history
  for count in List.range 4 do
    for records in historiesOfLength count do
      let encoded := (listCodec SourceEncoding.recordCodec).encode records
      for history in accumulated do
        for suffix in [[],[false],[true,false,true]] do
          if !(← checkHeader fullProgram headers (encoded ++ suffix) history) then
            throw (IO.userError "Canonical history or following suffix was rejected")
      let tooMany := natural (records.length + 1) ++ encodeSeq SourceEncoding.recordCodec.encode records
      if (← checkHeader fullProgram headers tooMany [true,false]) then
        throw (IO.userError "Missing final record was manufactured")
      if !records.isEmpty then
        let fewer := natural (records.length - 1) ++ encodeSeq SourceEncoding.recordCodec.encode records
        if !(← checkHeader fullProgram headers fewer [false,true]) then
          throw (IO.userError "Prefix reader discarded legitimate following record bytes")
  let encoded := (listCodec SourceEncoding.recordCodec).encode [sample1,sample0,sample2]
  for cut in List.range encoded.length do
    if (← checkHeader fullProgram headers (encoded.take cut) [true,false]) then
      throw (IO.userError "Truncated multi-record history was accepted")
  for count in List.range 13 do
    if (← checkHeader fullProgram headers (List.replicate count true) [true,false]) then
      throw (IO.userError "Unterminated history count was accepted")
  for count in [8,32,64] do
    if (← checkHeader fullProgram headers (natural count ++ SourceEncoding.recordCodec.encode sample0) []) then
      throw (IO.userError "Inflated history count was accepted")
  let badRecord : BitString := [false,false,true,false,false]
  let input := natural 3 ++ (SourceEncoding.recordCodec.encode sample1 ++
    (badRecord ++ SourceEncoding.recordCodec.encode sample2))
  let history : BitString := [false,true,false]
  let actual := BitRegister.run fullProgram (SourceReplayHistoryStack.prefixFuel input + 1)
    ⟨.running 0,SourceReplayHistoryStack.work 0 input history false⟩
  if actual.control != .accepted || actual.store.get 28 != [] ||
      actual.store.get 27 != [] || actual.store.get 29 != [] ||
      actual.store.get 26 != SourceEncoding.recordCodec.encode sample1 ++ history ||
      actual.store.get 0 != SourceEncoding.recordCodec.encode sample2 then
    throw (IO.userError "Middle-record rejection failed to preserve exactly the accepted prefix")
  compareStore actual.store (SourceReplayHistoryStack.finalState (SourceReplayHistoryFields.readHistory input history)) "Middle failure"
  headers.modify (· + 1)
  IO.println s!"REPLAY_HISTORY_REGRESSIONS_GREEN: {← loops.get} counted executions; {← headers.get} encoded-history executions")

run_cmd do
  let names := [
    ``SourceReplayHistoryFields.parse_contract,
    ``SourceReplayHistoryFields.bounds,
    ``SourceReplayHistoryFields.prefix_contract,
    ``SourceReplayHistoryFields.prefix_canonical,
    ``SourceReplayHistoryFields.prefix_bounds,
    ``SourceReplayHistoryStack.lift26_exec,
    ``SourceReplayHistoryStack.clearWork_exec,
    ``SourceReplayHistoryStack.reset_exec,
    ``SourceReplayHistoryStack.record_exec,
    ``SourceReplayHistoryStack.body_success,
    ``SourceReplayHistoryStack.body_failure,
    ``SourceReplayHistoryStack.loop_exec,
    ``SourceReplayHistoryStack.loopFuel_bound,
    ``SourceReplayHistoryStack.header_exec,
    ``SourceReplayHistoryStack.headerFinish_exec,
    ``SourceReplayHistoryStack.prefix_exec,
    ``SourceReplayHistoryStack.prefixFuel_bound,
    ``SourceReplayHistoryStack.prefix_parsed_exec,
    ``SourceReplayHistoryStack.prefix_rejected]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"REPLAY_HISTORY_AXIOMS_GREEN: {names.length} declarations"

#print axioms PNP.Concrete.ResidualReduction.SourceReplayHistoryFields.parse_contract
#print axioms PNP.Concrete.ResidualReduction.SourceReplayHistoryFields.prefix_bounds
#print axioms PNP.Concrete.ResidualReduction.SourceReplayHistoryStack.loop_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayHistoryStack.prefix_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayHistoryStack.prefixFuel_bound

end PNP.Concrete.ResidualReduction.SourceReplayHistoryRegression

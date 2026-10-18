import PNP.Concrete.ResidualReduction.SourceReplayLoopPrefix
import Lean

/-! Focused complete-history integration. The already verified per-record
suite is not repeated. Independent decoding and original mathematical maps
check complete multi-record runs, prefix boundaries and late rejection.
Kernel examples and axiom guards cover arbitrary inputs and histories. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayLoopRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain

example (recover : Bool) (count : Nat) (input point : BitString) :
    SourceReplayLoopFields.observe (SourceReplayLoopFields.scan recover count input point) =
      (parseN SourceEncoding.recordCodec.parse count input).bind fun (records,cursor) =>
        (SourceReplayTraversal.walk (SourceReplayStepApply.mapOne recover) records point).map fun output => (cursor,output) :=
  SourceReplayLoopFields.parse_contract recover count input point
example (recover : Bool) (count : Nat) (input point : BitString) :
    (SourceReplayLoopFields.scan recover count input point).input.length ≤ input.length ∧
      (SourceReplayLoopFields.scan recover count input point).point.length ≤ point.length + count :=
  SourceReplayLoopFields.bounds recover count input point
example (recover : Bool) (count : Nat) (input point : BitString) :
    Exec SourceReplayLoopMachine.block (SourceReplayLoopMachine.work count input point recover true)
      (SourceReplayLoopMachine.fuel recover count input point)
      (SourceReplayLoopMachine.finalState recover (SourceReplayLoopFields.scan recover count input point)) :=
  SourceReplayLoopMachine.block_exec recover count input point
example (recover : Bool) (count : Nat) (input point : BitString) :
    SourceReplayLoopMachine.fuel recover count input point ≤
      count * SourceReplayLoopMachine.allowance input.length (point.length + count) + 1 :=
  SourceReplayLoopMachine.fuel_bound recover count input point
example (recover : Bool) (input point : BitString) :
    Exec SourceReplayLoopPrefix.block (SourceReplayLoopPrefix.initial recover input point)
      (SourceReplayLoopPrefix.fuel recover input point) (SourceReplayLoopPrefix.result recover input point) :=
  SourceReplayLoopPrefix.block_exec recover input point
example (recover : Bool) (input point : BitString) :
    SourceReplayLoopPrefix.fuel recover input point ≤
      input.length * SourceReplayLoopMachine.allowance input.length (point.length + input.length) +
        4 * input.length + 43 := SourceReplayLoopPrefix.fuel_bound recover input point
example (recover : Bool) (input point : BitString) :
    SourceReplayLoopPrefix.observed (SourceReplayLoopPrefix.result recover input point) =
      ((listCodec SourceEncoding.recordCodec).parse input).bind fun (records,cursor) =>
        (SourceReplayTraversal.walk (SourceReplayStepApply.mapOne recover) records point).map fun output => (cursor,output) :=
  SourceReplayLoopPrefix.result_contract recover input point
example (history : List StepRecord) (n d : Nat) (z : Point d) (suffix : BitString) :
    (SourceReplayLoopPrefix.observed (SourceReplayLoopPrefix.result true
      ((listCodec SourceEncoding.recordCodec).encode history.reverse ++ suffix)
      ((SourceEncoding.pointCodec d).encode z))).bind (fun pair => (SourceEncoding.pointCodec n).decode pair.2) =
        SourceEncoding.liftHistory n d history z := SourceReplayLoopPrefix.recovery_contract history n d z suffix
example (history : List StepRecord) (n d : Nat) (x : Point n) (suffix : BitString) :
    (SourceReplayLoopPrefix.observed (SourceReplayLoopPrefix.result false
      ((listCodec SourceEncoding.recordCodec).encode history ++ suffix)
      ((SourceEncoding.pointCodec n).encode x))).bind (fun pair => (SourceEncoding.pointCodec d).decode pair.2) =
        SourceEncoding.projectHistory n d history x := SourceReplayLoopPrefix.projection_contract history n d x suffix
example (recover : Bool) (input point : BitString) :
    (SourceReplayLoopFields.readHistory recover input point).input.length ≤ input.length ∧
      (SourceReplayLoopFields.readHistory recover input point).point.length ≤ point.length + input.length :=
  SourceReplayLoopFields.prefix_bounds recover input point

run_cmd do
  let names := [
    ``SourceReplayLoopFields.parse_contract,
    ``SourceReplayLoopFields.canonical,
    ``SourceReplayLoopFields.direction_walk,
    ``SourceReplayLoopFields.bounds,
    ``SourceReplayLoopFields.prefix_contract,
    ``SourceReplayLoopFields.prefix_canonical,
    ``SourceReplayLoopFields.prefix_bounds,
    ``SourceReplayLoopMachine.lift_exec,
    ``SourceReplayLoopMachine.body_success,
    ``SourceReplayLoopMachine.body_failure,
    ``SourceReplayLoopMachine.block_exec,
    ``SourceReplayLoopMachine.allowance_mono,
    ``SourceReplayLoopMachine.fuel_bound,
    ``SourceReplayLoopPrefix.header_exec,
    ``SourceReplayLoopPrefix.reset_exec,
    ``SourceReplayLoopPrefix.headerFinish_exec,
    ``SourceReplayLoopPrefix.block_exec,
    ``SourceReplayLoopPrefix.fuel_bound,
    ``SourceReplayLoopPrefix.observed_final,
    ``SourceReplayLoopPrefix.result_contract,
    ``SourceReplayLoopPrefix.recovery_contract,
    ``SourceReplayLoopPrefix.projection_contract]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"REPLAY_LOOP_AXIOMS_GREEN: {names.length} declarations"

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

private def originalOne (recover : Bool) (q : StepRecord) (point : BitString) : Option BitString := do
  if recover then
    let z ← (SourceEncoding.pointCodec q.dimension).decode point
    pure ((SourceEncoding.pointCodec (q.dimension + 1)).encode
      (decode (SourceBalance.markSource q.source q.step.weights) q.step.pivot q.step.tail z))
  else
    let x ← (SourceEncoding.pointCodec (q.dimension + 1)).decode point
    pure ((SourceEncoding.pointCodec q.dimension).encode (encode q.step.pivot q.step.tail x))
private def originalWalk (recover : Bool) : List StepRecord → BitString → Option BitString
  | [],point => some point
  | q :: rest,point => (originalOne recover q point).bind (originalWalk recover rest)
private def originalResult (recover : Bool) (parsed : Option (List StepRecord × BitString))
    (point : BitString) : Option (BitString × BitString) := do
  let (records,cursor) ← parsed
  let output ← originalWalk recover records point
  pure (cursor,output)

private def same (p : Program 31) (counts : IO.Ref (Nat × Nat)) (start expected : Store 31)
    (recover : Bool) (ticks bound inputLength witnessBound : Nat)
    (independent : Option (BitString × BitString)) : IO (Store 31) := do
  if ticks > bound then throw (IO.userError "History replay exceeded its proved instruction bound")
  let actual := BitRegister.run p (ticks + 1) ⟨.running 0,start⟩
  if actual.control != .accepted then throw (IO.userError "History replay did not halt within its exact instruction count")
  for i in List.finRange 31 do
    if actual.store.get i != expected.get i then throw (IO.userError "History replay complete register state differs")
    if (0 < i.val && i.val < 26) || 29 ≤ i.val then
      if actual.store.get i != [] then throw (IO.userError "History replay left workspace or countdown data")
  if actual.store.get 27 != [recover] then throw (IO.userError "History replay changed its direction")
  if (actual.store.get 0).length > inputLength || (actual.store.get 26).length > witnessBound then
    throw (IO.userError "History replay exceeded cursor or witness size bounds")
  if SourceReplayLoopPrefix.observed actual.store != independent then
    throw (IO.userError "History replay differs from independent decoding and original maps")
  if independent.isSome then counts.modify (fun (good,bad) => (good + 1,bad))
  else counts.modify (fun (good,bad) => (good,bad + 1))
  pure actual.store

private def prefixCheck (p : Program 31) (counts : IO.Ref (Nat × Nat))
    (recover : Bool) (input point : BitString) : IO (Store 31) :=
  same p counts (SourceReplayLoopPrefix.initial recover input point)
    (SourceReplayLoopPrefix.result recover input point) recover
    (SourceReplayLoopPrefix.fuel recover input point)
    (input.length * SourceReplayLoopMachine.allowance input.length (point.length + input.length) + 4 * input.length + 43)
    input.length (point.length + input.length)
    (originalResult recover ((listCodec SourceEncoding.recordCodec).parse input) point)
private def loopCheck (p : Program 31) (counts : IO.Ref (Nat × Nat))
    (recover : Bool) (count : Nat) (input point : BitString) : IO (Store 31) :=
  same p counts (SourceReplayLoopMachine.work count input point recover true)
    (SourceReplayLoopMachine.finalState recover (SourceReplayLoopFields.scan recover count input point)) recover
    (SourceReplayLoopMachine.fuel recover count input point)
    (count * SourceReplayLoopMachine.allowance input.length (point.length + count) + 1)
    input.length (point.length + count)
    (originalResult recover (parseN SourceEncoding.recordCodec.parse count input) point)

#eval (show IO Unit from do
  let counts ← IO.mkRef (0,0)
  let p := SourceReplayLoopPrefix.block.program 0 26
  let bare := SourceReplayLoopMachine.block.program 0 26
  for length in List.range 6 do
    for input in words length do
      for point in [[],[true,false]] do
        for recover in [false,true] do
          discard (prefixCheck p counts recover input point)
  IO.println "REPLAY_LOOP_PHASE: hostile headers and raw history rejection passed"
  for history in [[],[q2,q1,q0],[q0,q1,q2],[q1,q1],[q0,q2],[q2,q0],[q1,q0]] do
    for suffix in [[],[true,false,true]] do
      let input := (listCodec SourceEncoding.recordCodec).encode history ++ suffix
      for width in List.range 4 do
        for point in words width do
          for recover in [false,true] do
            discard (prefixCheck p counts recover input point)
  let raw := encodeSeq SourceEncoding.recordCodec.encode [q2,q1,q0] ++ [true,false]
  for count in List.range 5 do
    for point in [[],[true],[true,false],[true,false,true]] do
      for recover in [false,true] do
        discard (loopCheck bare counts recover count raw point)
  for bad in [[],List.replicate 12 true,natural 4 ++ encodeSeq SourceEncoding.recordCodec.encode [q2,q1,q0],
      natural 2 ++ SourceEncoding.recordCodec.encode q1,natural 32 ++ SourceEncoding.recordCodec.encode q0] do
    for point in [[],[true,false,true]] do
      for recover in [false,true] do
        discard (prefixCheck p counts recover bad point)
  for n in [0,1,4,8] do
    let history := descending n
    let backward := (listCodec SourceEncoding.recordCodec).encode history.reverse
    discard (prefixCheck p counts true backward [])
    for point in [List.replicate n false,List.replicate n true] do
      let forward := (listCodec SourceEncoding.recordCodec).encode history
      discard (prefixCheck p counts false forward point)
  let failing := (listCodec SourceEncoding.recordCodec).encode [q1,q1,q0] ++ [true,false]
  for recover in [false,true] do
    let point := if recover then [true] else [true,false]
    let afterFirst := originalOne recover q1 point
    let actual ← prefixCheck p counts recover failing point
    if afterFirst.isNone || actual.get 28 != [] || afterFirst != some (actual.get 26) then
      throw (IO.userError "Late rejection did not preserve the last computed witness")
  let empty := (listCodec SourceEncoding.recordCodec).encode ([] : List StepRecord)
  let ticks := SourceReplayLoopPrefix.fuel true empty []
  let early := BitRegister.run p ticks ⟨.running 0,SourceReplayLoopPrefix.initial true empty []⟩
  if early.control == .accepted then throw (IO.userError "History replay accepted before its terminal instruction")
  let (good,bad) ← counts.get
  if good == 0 || bad == 0 then throw (IO.userError "History replay did not exercise both outcomes")
  IO.println s!"REPLAY_LOOP_REGRESSIONS_GREEN: {good + bad} literal executions; {good} accepted; {bad} rejected")

#print axioms PNP.Concrete.ResidualReduction.SourceReplayLoopFields.parse_contract
#print axioms PNP.Concrete.ResidualReduction.SourceReplayLoopMachine.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayLoopMachine.fuel_bound
#print axioms PNP.Concrete.ResidualReduction.SourceReplayLoopPrefix.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayLoopPrefix.fuel_bound
#print axioms PNP.Concrete.ResidualReduction.SourceReplayLoopPrefix.recovery_contract
#print axioms PNP.Concrete.ResidualReduction.SourceReplayLoopPrefix.projection_contract

end PNP.Concrete.ResidualReduction.SourceReplayLoopRegression

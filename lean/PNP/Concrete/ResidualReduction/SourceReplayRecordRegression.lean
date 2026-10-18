import PNP.Concrete.ResidualReduction.SourceReplayRecordFields
import Lean

/-! Independent codec comparisons at the new inner-field boundary.
Finite executions exercise the literal family and point readers. Complete
record checks compare the raw-field specification with the existing codec;
they do not claim that the full record machine or history loop is finished. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayRecordRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain

example (n : Nat) (input : BitString) :
    Exec SourceReplayFamily.block (SourceReplayFamily.initial n input).store
      (SourceReplayFamily.fuel n input) (SourceReplayFamily.result n input).store :=
  SourceReplayFamily.block_exec n input
example (n : Nat) (input : BitString) :
    SourceReplayFamily.fuel n input ≤ (16 * n + 36) * input.length + 3 * n + 26 :=
  SourceReplayFamily.fuel_bound n input
example {n : Nat} (input : BitString) (F : Family n) (suffix : BitString) :
    (SourceEncoding.familyCodec n).parse input = some (F,suffix) ↔
      SourceReplayFamilyFields.valid n input = true ∧ SourceReplayFamilyFields.count input = F.length ∧
        SourceReplayFamilyFields.payload n input = SourceMatrixEncoding.familyBits F ∧
        SourceReplayFamilyFields.rest n input = suffix :=
  SourceReplayFamilyFields.parse_iff input F suffix
example (r : Registers) (count : Nat) (input : BitString) :
    Exec SourceReplayFixed.block ({r with input := input,remaining := List.replicate count true}).store
      (SourceReplayFixed.fuel count input) (SourceReplayFixed.result r count input).store :=
  SourceReplayFixed.block_exec r count input
example {n : Nat} (input : BitString) (x : Point n) (suffix : BitString) :
    (SourceEncoding.pointCodec n).parse input = some (x,suffix) ↔
      n ≤ input.length ∧ (SourceEncoding.pointCodec n).encode x = input.take n ∧ suffix = input.drop n :=
  SourceReplayFixed.parse_iff input x suffix
example (input : BitString) (good : SourceReplayRecordFields.valid input = true) :
    ∃ q : StepRecord, SourceEncoding.recordCodec.parse input = some (q,SourceReplayRecordFields.rest input) ∧
      SourceReplayRecordFields.capture input = SourceReplayRecordFields.recordFields q :=
  SourceReplayRecordFields.valid_parse input good
example (q : StepRecord) (suffix : BitString) :
    let input := SourceEncoding.recordCodec.encode q ++ suffix
    SourceReplayRecordFields.valid input = true ∧
      SourceReplayRecordFields.capture input = SourceReplayRecordFields.recordFields q ∧
      SourceReplayRecordFields.rest input = suffix :=
  SourceReplayRecordFields.canonical q suffix
example (input : BitString) (bad : SourceReplayRecordFields.valid input = false) :
    SourceEncoding.recordCodec.parse input = none := SourceReplayRecordFields.invalid_parse input bad
example (input : BitString) :
    match SourceEncoding.recordCodec.parse input with
    | none => SourceReplayRecordFields.valid input = false
    | some (q,suffix) => SourceReplayRecordFields.valid input = true ∧
        SourceReplayRecordFields.capture input = SourceReplayRecordFields.recordFields q ∧
        SourceReplayRecordFields.rest input = suffix :=
  SourceReplayRecordFields.parse_contract input

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
private def same {n : Nat} (counter : IO.Ref Nat) (p : Program n) (before after : Store n)
    (ticks : Nat) (label : String) : IO Unit := do
  let actual := BitRegister.run p (ticks + 1) ⟨.running 0,before⟩
  if actual.control != .accepted then throw (IO.userError (label ++ ": did not halt within its proved count"))
  for i in List.finRange n do
    if actual.store.get i != after.get i then throw (IO.userError (label ++ ": complete register state differs"))
  counter.modify (· + 1)
private def compareFields (a b : SourceReplayRecordFields.Fields) : Bool :=
  a.dimension == b.dimension && a.rows == b.rows && a.source == b.source &&
    a.weights == b.weights && a.pivot == b.pivot && a.tail == b.tail &&
    a.outputRows == b.outputRows && a.output == b.output
private def checkRecord (counter : IO.Ref Nat) (input : BitString) : IO Bool := do
  counter.modify (· + 1)
  match SourceEncoding.recordCodec.parse input with
  | none =>
    if SourceReplayRecordFields.valid input then throw (IO.userError "Raw record validator accepted malformed bytes")
    return false
  | some (q,suffix) =>
    if !SourceReplayRecordFields.valid input ||
        !compareFields (SourceReplayRecordFields.capture input) (SourceReplayRecordFields.recordFields q) ||
        SourceReplayRecordFields.rest input != suffix then
      throw (IO.userError "Raw record fields disagree with the independent codec")
    return true

#eval (show IO Unit from do
  let executions ← IO.mkRef 0
  let records ← IO.mkRef 0
  let familyProgram := SourceReplayFamily.block.program 0 8
  for n in [0,1,2,3] do
    for width in List.range 9 do
      for input in words width do
        let before := (SourceReplayFamily.initial n input).store
        let after := (SourceReplayFamily.result n input).store
        let ticks := SourceReplayFamily.fuel n input
        if ticks > (16 * n + 36) * input.length + 3 * n + 26 then
          throw (IO.userError "Family prefix exceeded its encoded-size bound")
        same executions familyProgram before after ticks "Arbitrary family prefix"
        match (SourceEncoding.familyCodec n).parse input with
        | none => if after.get 5 != [] then throw (IO.userError "Family prefix accepted truncation")
        | some (F,suffix) =>
          if after.get 5 != [true] || after.get 0 != suffix || after.get 8 != SourceMatrixEncoding.familyBits F ||
              after.get 9 != List.replicate n true || after.get 15 != List.replicate F.length true then
            throw (IO.userError "Family prefix differs from the canonical codec")
    for F in families n do
      for suffix in [[],[false],[true,false,true]] do
        let input := (SourceEncoding.familyCodec n).encode F ++ suffix
        let after := (SourceReplayFamily.result n input).store
        same executions familyProgram (SourceReplayFamily.initial n input).store after
          (SourceReplayFamily.fuel n input) "Family with following fields"
        if after.get 0 != suffix || after.get 5 != [true] then
          throw (IO.userError "Family reader discarded or rejected a legitimate suffix")
  IO.println "REPLAY_RECORD_PHASE: family prefixes, truncation and suffix preservation passed"
  let fixedProgram := SourceReplayFixed.block.program 0 8
  for count in [0,1,2,3,4,5] do
    for width in List.range 9 do
      for input in words width do
        let r : Registers := ⟨[],[true,false],[],[true],[false,true],[false],[true,false],[false,true],[true]⟩
        let after := SourceReplayFixed.result r count input
        let ticks := SourceReplayFixed.fuel count input
        if ticks > 5 * count + 4 * input.length + 6 then throw (IO.userError "Point field exceeded its bound")
        same executions fixedProgram ({r with input := input,remaining := List.replicate count true}).store
          after.store ticks "Fixed point field with protected data"
        match (SourceEncoding.pointCodec count).parse input with
        | none => if after.mode != [] then throw (IO.userError "Point reader manufactured a missing bit")
        | some (point,suffix) =>
          if after.mode != [true] || after.output != (SourceEncoding.pointCodec count).encode point ||
              after.input != suffix then throw (IO.userError "Point reader differs from codec")
  for width in List.range 12 do
    for input in words width do
      let _ ← checkRecord records input
  let changedRows ← IO.mkRef false
  for n in [0,1,2] do
    for F in families (n + 1) do
      for w in points F.length do
        for k in List.finRange (n + 1) do
          for v in points n do
            for G in families n do
              let q : StepRecord := ⟨n,F,⟨w,k,v,G⟩⟩
              if G.length != F.length then changedRows.set true
              for suffix in [[],[false],[true,false,true]] do
                if !(← checkRecord records (SourceEncoding.recordCodec.encode q ++ suffix)) then
                  throw (IO.userError "Canonical record or preserved suffix was rejected")
              let badPivot := natural n ++ ((SourceEncoding.familyCodec (n + 1)).encode F ++
                ((SourceEncoding.pointCodec F.length).encode w ++
                  (natural (n + 1) ++ ((SourceEncoding.pointCodec n).encode v ++ (SourceEncoding.familyCodec n).encode G))))
              if (← checkRecord records badPivot) then throw (IO.userError "Out-of-range pivot was accepted")
    let q : StepRecord := ⟨n,[],⟨(),0,zeroPoint n,[]⟩⟩
    let input := SourceEncoding.recordCodec.encode q
    for cut in List.range input.length do
      if (← checkRecord records (input.take cut)) then throw (IO.userError "Incomplete record was accepted")
  if !(← changedRows.get) then throw (IO.userError "Record tests assumed equal source and output row counts")
  IO.println s!"REPLAY_RECORD_REGRESSIONS_GREEN: {← executions.get} executions; {← records.get} record cases")

run_cmd do
  let names := [
    ``SourceReplayFamilyFields.encode_bytes,
    ``SourceReplayFamilyFields.canonical,
    ``SourceReplayFamilyFields.valid_parts,
    ``SourceReplayFamilyFields.parse_iff,
    ``SourceReplayFamilyFields.valid_parse,
    ``SourceReplayFamilyFields.invalid_parse,
    ``SourceReplayFamilyFields.count_bound,
    ``SourceReplayFamilyFields.payload_bound,
    ``SourceReplayFamilyFields.rest_bound,
    ``SourceReplayFamily.clearCore_exec,
    ``SourceReplayFamily.clearWorking_exec,
    ``SourceReplayFamily.success_exec,
    ``SourceReplayFamily.header_exec,
    ``SourceReplayFamily.failure_exec,
    ``SourceReplayFamily.block_exec,
    ``SourceReplayFamily.loader_cost,
    ``SourceReplayFamily.fuel_bound,
    ``SourceReplayFixed.point_prefix,
    ``SourceReplayFixed.parse_iff,
    ``SourceReplayFixed.valid_parse,
    ``SourceReplayFixed.invalid_parse,
    ``SourceReplayFixed.block_exec,
    ``SourceReplayFixed.fuel_bound,
    ``SourceReplayRecordFields.valid_parts,
    ``SourceReplayRecordFields.assemble,
    ``SourceReplayRecordFields.valid_parse,
    ``SourceReplayRecordFields.input_bounds,
    ``SourceReplayRecordFields.canonical,
    ``SourceReplayRecordFields.parsed_fields,
    ``SourceReplayRecordFields.invalid_parse,
    ``SourceReplayRecordFields.parse_contract]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"REPLAY_RECORD_AXIOMS_GREEN: {names.length} declarations"

#print axioms PNP.Concrete.ResidualReduction.SourceReplayFamily.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayFixed.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayRecordFields.valid_parse
#print axioms PNP.Concrete.ResidualReduction.SourceReplayRecordFields.parse_contract

end PNP.Concrete.ResidualReduction.SourceReplayRecordRegression

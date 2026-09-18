import PNP.NANDWireOpenCertificate

namespace PNP.Regression.RecodingProgram

open PNP.DirectWire WireOpenProgram
open Concrete.LockedNAND (RawCandidate)
open WireObligationHistory (State)

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    (before : State source) (event : RawEvent) (rawEncoder rawDecoder : RawCandidate)
    (kind : event.action = .recoding rawEncoder rawDecoder)
    (receipt : WireRecodingInput.Receipt before rawEncoder rawDecoder) :
    (Transition.recoding before event rawEncoder rawDecoder kind receipt).charged =
      receipt.encoder.gateCount + receipt.decoder.gateCount := rfl

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    (before : State source) (event : RawEvent) (rawEncoder rawDecoder : RawCandidate)
    (_kind : event.action = .recoding rawEncoder rawDecoder)
    (receipt : WireRecodingInput.Receipt before rawEncoder rawDecoder)
    (field : Fin fields) (snapshot : WireObligationHistory.Snapshot source field)
    (pending : before.pending field = some snapshot) :
    receipt.next.pending field = some snapshot :=
  pending

#print axioms PNP.DirectWire.WireOpenProgram.Transition.charged_eq
#print axioms PNP.DirectWire.WireOpenProgram.Transition.removed_eq
#print axioms PNP.DirectWire.WireOpenProgram.Transition.causalInvariant
#print axioms PNP.DirectWire.WireOpenProgram.Transition.local_physical_ownership
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.full_output
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.full_field
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.gate_balance
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.creation_lifecycle
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.physical_ownership
#print axioms PNP.DirectWire.WireOpenCertificate.verify_no_gain

private def identity (width : Nat) : Implementation width width :=
  (Candidate.ofDirectWireWord (.empty : Program width 0)
    ⟨fun field => .input field⟩).toImplementation

private def negation : Implementation 1 1 :=
  (Candidate.ofDirectWireWord
    ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩)
    (⟨fun _ => .gate 0⟩ : DirectWireWord 1 1 1)).toImplementation

private def fixture : WireCarrier 1 1 1 :=
  { implementation := negation, source := fun _ => .gate ⟨0, by decide⟩ }

private def constant : WireCarrier 1 1 1 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 1 0)
      (⟨fun _ => .constant true⟩ : DirectWireWord 1 0 1)).toImplementation
    source := fun _ => .constant true }

private def emptyFixture : WireCarrier 0 0 0 :=
  { implementation := identity 0, source := Fin.elim0 }

private def controlledNot : Implementation 2 2 :=
  (Candidate.ofDirectWireWord
    (.snoc (.snoc (.snoc (.snoc (.empty : Program 2 0)
      ⟨.input 0, .input 1⟩) ⟨.input 0, .gate 0⟩)
      ⟨.input 1, .gate 0⟩) ⟨.gate 1, .gate 2⟩)
    (⟨fun field => if field.val = 0 then .input 0 else .gate 3⟩ :
      DirectWireWord 2 4 2)).toImplementation

private def independent : WireCarrier 2 1 2 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 2 0)
      (⟨fun _ => .constant false⟩ : DirectWireWord 2 0 1)).toImplementation
    source := fun field => .input field }

private def rawIdentity := RawCandidate.ofCandidate (identity 1).candidate
private def rawNegation := RawCandidate.ofCandidate negation.candidate

/-- Dependency order crosses a raw recoder, actual restoration and another
recoder. Only restoration may discharge the captured creation snapshot. -/
private def openAcrossRecoding : List RawEvent :=
  [⟨50, [40], .primitive (.readFull 0)⟩,
   ⟨40, [30], .recoding rawIdentity rawIdentity⟩,
   ⟨30, [20], .primitive (.restoreR8 10)⟩,
   ⟨20, [10], .recoding rawNegation rawNegation⟩,
   ⟨10, [], .primitive (.createR5 0)⟩]

#eval show IO Unit from do
  let some opened := compile fixture openAcrossRecoding
    | throw (IO.userError "complete raw recoding could not cross an open snapshot")
  let [created, recoded, restored, normalized, read] := opened.execution.records
    | throw (IO.userError "complete recoding trace omitted an event")
  if opened.execution.records.map (fun event => event.identity) != [10, 20, 30, 40, 50] then
    throw (IO.userError "raw recoding ignored dependency order")
  if created.creation.isNone || read.fullRead.isNone then
    throw (IO.userError "raw recoding lost a real creation or full read")
  for unchanged in [recoded, normalized] do
    if unchanged.creation.isSome || unchanged.discharge.isSome || unchanged.fullRead.isSome then
      throw (IO.userError "recoding fabricated an obligation lifecycle event")
  let some discharge := restored.discharge
    | throw (IO.userError "the actual restoration lost its discharge record")
  if discharge.creation.identity != 10 ||
      discharge.creation.carrier.implementation.gateCount != 1 then
    throw (IO.userError "raw recoding changed the captured restoration snapshot")
  let expectedCharges : List (ProgramOrigin fixture.implementation.gateCount) :=
    [.allocated 1 0 0 0, .allocated 1 0 1 0, .allocated 2 0 30 0]
  if opened.ownership.charged != expectedCharges ||
      opened.ownership.live != [.original (0 : Fin 1)] ||
      opened.ownership.removed.length != 3 ||
      opened.execution.charged != 3 || opened.execution.removed != 3 then
    throw (IO.userError "complete recoding lost literal or historical physical accounting")
  for origin in expectedCharges do
    if opened.ownership.removed.count origin != 1 then
      throw (IO.userError "a removed allocation was duplicated or lost")
  for value in [false, true] do
    if opened.result.fieldValue (fun _ => value) 0 != !value ||
        opened.result.implementation.candidate.semantics (fun _ => value) 0 != !value then
      throw (IO.userError "complete recoding changed full output or field semantics")
  let repeated : List RawEvent :=
    [⟨6, [5], .recoding rawNegation rawNegation⟩,
     ⟨5, [], .recoding rawNegation rawNegation⟩]
  let some twice := compile constant repeated
    | throw (IO.userError "repeated independent raw recoders rejected")
  let allCharges : List (ProgramOrigin 0) :=
    [.allocated 0 0 0 0, .allocated 0 0 1 0, .allocated 1 0 0 0, .allocated 1 0 1 0]
  if twice.ownership.charged != allCharges || !twice.ownership.live.isEmpty ||
      twice.ownership.removed.length != 4 then
    throw (IO.userError "repeated recoders reused an outer allocation namespace")
  for origin in allCharges do
    if twice.ownership.removed.count origin != 1 then
      throw (IO.userError "repeated recoders conflated separate allocation identities")
  let wrongWidth : RawCandidate := { rawIdentity with inputCount := 2 }
  let badTail : RawCandidate :=
    { rawNegation with gates := rawNegation.gates ++ [⟨.gate 8, .input 0⟩] }
  let failures : List (List RawEvent) :=
    [ [⟨1, [], .primitive (.createR5 0)⟩, ⟨2, [1], .recoding rawIdentity rawIdentity⟩]
    , repeated ++ [⟨7, [6], .recoding wrongWidth rawIdentity⟩]
    , repeated ++ [⟨7, [6], .recoding rawIdentity badTail⟩]
    , repeated ++ [⟨7, [6], .recoding rawIdentity rawNegation⟩]
    , [⟨1, [], .recoding rawIdentity rawIdentity⟩, ⟨1, [], .recoding rawIdentity rawIdentity⟩]
    , [⟨1, [99], .recoding rawIdentity rawIdentity⟩]
    , [⟨1, [1], .recoding rawIdentity rawIdentity⟩] ]
  for rejected in failures do
    if (compile constant rejected).isSome then
      throw (IO.userError "invalid or unclosed recoding tail exposed a successful prefix")
  let rawMix := RawCandidate.ofCandidate controlledNot.candidate
  if (compile independent [⟨1, [], .recoding rawMix rawMix⟩]).isSome then
    throw (IO.userError "complete program bypassed the physical causal guard")
  let rawEmpty := RawCandidate.ofCandidate (identity 0).candidate
  let some empty := compile emptyFixture [⟨1, [], .recoding rawEmpty rawEmpty⟩]
    | throw (IO.userError "empty raw recoding program rejected")
  if empty.execution.records.length != 1 || !empty.ownership.live.isEmpty ||
      !empty.ownership.charged.isEmpty || !empty.ownership.removed.isEmpty then
    throw (IO.userError "empty recoding fabricated a gate or omitted the event")
  IO.println "RECODING_COMPLETE_PROGRAM_RUNTIME_PASSED"

end PNP.Regression.RecodingProgram

import PNP.NANDWireHistoryArbitrarySupport

/-!
General theorem contracts and small executable regression fixtures. The finite
fixtures exercise the constructor; they are not authority for the general proof.
-/

namespace PNP.Regression.WireHistoryArbitrarySupport

open PNP.DirectWire PNP.DirectWire.WireObligationHistory
open PNP.DirectWire.WireHistoryArbitrarySupport

example {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    {raw : List (RawEvent (terminalInterfacePorts candidate records).length)}
    (history : ClosedHistory (extractedCarrier candidate records) raw) :
    ∃ compiled, ArbitrarySupportSplice.compile candidate records
      (fieldCandidate history.state.current) = some compiled :=
  closedHistory_compiles candidate records history

example {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    {raw : List (RawEvent (terminalInterfacePorts candidate records).length)}
    (result : Implementation inputs outputs)
    (accepted : WireHistoryArbitrarySupport.compile candidate records raw = some result) :
    ∃ history : ClosedHistory (extractedCarrier candidate records) raw,
      compileHistory (extractedCarrier candidate records) raw = some history ∧
      result.gateCount + history.execution.removed = gates + history.execution.charged ∧
      (∀ valuation output, result.candidate.semantics valuation output =
        candidate.semantics valuation output) :=
  compile_sound candidate records result accepted

private def chainProgram : Program 1 5 :=
  .snoc (.snoc (.snoc (.snoc (.snoc .empty ⟨.input 0, .input 0⟩)
    ⟨.gate 0, .gate 0⟩) ⟨.gate 1, .gate 1⟩) ⟨.gate 2, .gate 2⟩) ⟨.gate 3, .gate 3⟩

private def chain : Candidate 1 5 9 :=
  Candidate.ofDirectWireWord chainProgram ⟨fun output =>
    match output.val with
    | 0 => .gate 0
    | 1 => .gate 1
    | 2 => .gate 2
    | 3 => .gate 3
    | 4 => .gate 4
    | 5 => .gate 0
    | 6 => .input 0
    | 7 => .constant false
    | _ => .constant true⟩

private def interleaved : List (TerminalPrimitiveRecord 1 5 9 0) :=
  [.gate 0, .gate 2, .gate 4]

example : terminalBoundaryPorts chain.program interleaved =
    [.input 0, .gate 1, .gate 3] := by decide
example : terminalInterfacePorts chain interleaved = [0, 2, 4] := by decide

private def restoreMiddle :
    List (RawEvent (terminalInterfacePorts chain interleaved).length) :=
  [⟨30, [20], .restoreR8 10⟩, ⟨20, [10], .normalize⟩,
    ⟨10, [], .createR5 ⟨1, by decide⟩⟩]

private def savingProgram : Program 1 4 :=
  .snoc (.snoc (.snoc (.snoc .empty ⟨.input 0, .input 0⟩)
    ⟨.gate 0, .gate 0⟩) ⟨.gate 1, .gate 1⟩) ⟨.gate 1, .gate 1⟩

private def saving : Candidate 1 4 8 :=
  Candidate.ofDirectWireWord savingProgram ⟨fun output =>
    match output.val with
    | 0 => .gate 0
    | 1 => .gate 1
    | 2 => .gate 2
    | 3 => .gate 3
    | 4 => .gate 2
    | 5 => .input 0
    | 6 => .constant false
    | _ => .constant true⟩

private def savingRecords : List (TerminalPrimitiveRecord 1 4 8 0) :=
  [.gate 0, .gate 2, .gate 3]

private def zero : Candidate 0 0 2 :=
  Candidate.ofDirectWireWord .empty ⟨fun output => .constant (output.val != 0)⟩
private def zeroRecords : List (TerminalPrimitiveRecord 0 0 2 0) := []

private def unused : Candidate 1 1 0 :=
  Candidate.ofDirectWireWord (.snoc .empty ⟨.input 0, .input 0⟩) ⟨Fin.elim0⟩
private def unusedRecords : List (TerminalPrimitiveRecord 1 1 0 0) := [.gate 0]

/-- M249's hostile shape: open equivalence can hide a later physical dependency. -/
private def witnessProgram : Program 1 3 :=
  .snoc (.snoc (.snoc .empty ⟨.input 0, .input 0⟩) ⟨.gate 0, .gate 0⟩)
    ⟨.gate 1, .gate 1⟩
private def witness : Candidate 1 3 2 :=
  Candidate.ofDirectWireWord witnessProgram ⟨fun output =>
    if output.val = 0 then .gate 0 else .gate 2⟩
private def witnessRecords : List (TerminalPrimitiveRecord 1 3 2 0) :=
  [.gate 0, .gate 2]
private def cyclicReplacement : Candidate
    (terminalBoundaryPorts witness.program witnessRecords).length 3
    (terminalInterfacePorts witness witnessRecords).length :=
  Candidate.ofDirectWireWord
    (.snoc (.snoc (.snoc .empty ⟨.input ⟨1, by decide⟩, .input ⟨1, by decide⟩⟩)
      ⟨.input ⟨1, by decide⟩, .gate 0⟩) ⟨.input ⟨0, by decide⟩, .gate 1⟩)
    ⟨fun output => if output.val = 0 then .gate 2 else .gate 0⟩

example : cyclicReplacement.semantics =
    (extractTerminalSupport witness witnessRecords).extractedCandidate.semantics := by
  funext valuation output
  exact equivalentBool_sound
    (by decide : equivalentBool cyclicReplacement
      (extractTerminalSupport witness witnessRecords).extractedCandidate = true) valuation output

example : ¬ArbitrarySupportSplice.CausalInterfaceBound witness witnessRecords cyclicReplacement := by
  intro bounded
  have impossible := bounded ⟨0, by decide⟩
  change 2 ≤ 1 at impossible
  omega

private def checkRun {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (raw : List (RawEvent (terminalInterfacePorts candidate records).length))
    (expectedGates expectedCharged expectedRemoved : Nat) : IO Unit := do
  let some history := compileHistory (extractedCarrier candidate records) raw
    | throw (IO.userError "valid source-derived history was rejected")
  if history.execution.charged != expectedCharged ||
      history.execution.removed != expectedRemoved then
    throw (IO.userError "actual restoration charge or normalization removal drifted")
  let some result := WireHistoryArbitrarySupport.compile candidate records raw
    | throw (IO.userError "valid closed history did not yield a literal replacement")
  if result.gateCount != expectedGates ||
      result.gateCount + history.execution.removed != gates + history.execution.charged then
    throw (IO.userError "one-copy physical accounting drifted")
  for tuple in allBoolTuples inputs do
    let valuation := tuple.toValuation
    let actual := (List.finRange outputs).map (result.candidate.semantics valuation)
    let expected := (List.finRange outputs).map (candidate.semantics valuation)
    if actual != expected then
      throw (IO.userError "replacement changed an ordered, repeated, constant or primary output")

#eval show IO Unit from do
  checkRun chain interleaved restoreMiddle 5 1 1
  checkRun chain interleaved [] 5 0 0
  checkRun saving savingRecords [⟨10, [], .normalize⟩] 3 0 1
  checkRun zero zeroRecords [] 0 0 0
  checkRun chain ([] : List (TerminalPrimitiveRecord 1 5 9 0)) [] 5 0 0
  checkRun unused unusedRecords [⟨10, [], .normalize⟩] 0 0 1
  if (WireHistoryArbitrarySupport.compile chain interleaved
      [⟨10, [], .createR5 ⟨0, by decide⟩⟩]).isSome then
    throw (IO.userError "unclosed obligation was silently accepted")
  if (WireHistoryArbitrarySupport.compile chain interleaved
      [⟨10, [], .restoreR8 999⟩]).isSome then
    throw (IO.userError "missing creation reference was silently accepted")
  if (ArbitrarySupportSplice.compile witness witnessRecords cyclicReplacement).isSome then
    throw (IO.userError "Boolean equivalence bypassed literal-cycle rejection")
  IO.println "HISTORY_ARBITRARY_SUPPORT_RUNTIME_FIXTURES_GREEN"

end PNP.Regression.WireHistoryArbitrarySupport

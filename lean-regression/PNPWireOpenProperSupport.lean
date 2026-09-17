import PNP.NANDWireOpenProperSupport

namespace PNP.Regression.WireOpenProperSupport

open PNP.DirectWire WireOpenProgram WireOpenProperSupport

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (raw : List RawEvent) (program : CompiledProgram (localSource carrier records) raw)
    (accepted : WireOpenProgram.compile (localSource carrier records) raw = some program) :
    ∃ executed, WireOpenProperSupport.compile carrier records raw = some executed ∧
      executed.program = program :=
  compile_complete carrier records raw program accepted

example {inputs outputs fields : Nat} {carrier : WireCarrier inputs outputs fields}
    {records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0)}
    {raw : List RawEvent} (executed : SplicedProgram carrier records raw) :
    executed.result.implementation.gateCount + executed.program.execution.removed =
      carrier.implementation.gateCount + executed.program.execution.charged :=
  executed.charge_accounting

private def source : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        ((((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩).snoc
          ⟨.input 0, .input 0⟩).snoc ⟨.input 0, .input 0⟩)
        ⟨fun _ => .constant false⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def records : List (TerminalPrimitiveRecord 1 3 2 0) := [.gate 0, .gate 1]

private def removeGate (gate : Nat) : WireDescendantCertificate.RawCertificate :=
  ⟨[.gate gate], [⟨0, [.gate 0], [⟨7, [], .normalize⟩]⟩]⟩

private def raw : List RawEvent :=
  [⟨50, [40], .primitive (.readFull 0)⟩,
   ⟨30, [20], .support (removeGate 0)⟩,
   ⟨40, [30], .primitive (.restoreR8 7)⟩,
   ⟨7, [], .primitive (.createR5 0)⟩,
   ⟨20, [7], .support (removeGate 1)⟩]

private def temporaryGrowth : List RawEvent :=
  [⟨4, [3], .primitive (.readFull 0)⟩,
   ⟨2, [], .primitive (.restoreR8 1)⟩,
   ⟨3, [2], .primitive .normalize⟩,
   ⟨1, [], .primitive (.createR5 0)⟩]

#eval show IO Unit from do
  let some executed := WireOpenProperSupport.compile source records raw
    | throw (IO.userError "closed mixed program failed its derived outer splice")
  if executed.program.result.implementation.gateCount != 1 ||
      executed.result.implementation.gateCount != 2 ||
      executed.program.execution.charged != 1 || executed.program.execution.removed != 2 then
    throw (IO.userError "literal outer splice lost its one-copy exterior or historical costs")
  if executed.program.execution.records.map (fun event => event.identity) != [7, 20, 30, 40, 50] then
    throw (IO.userError "outer embedding did not retain the complete computed program order")
  for input in [false, true] do
    let valuation : Valuation 1 := fun _ => input
    if executed.result.implementation.candidate.semantics valuation 0 !=
        source.implementation.candidate.semantics valuation 0 ||
        executed.result.fieldValue valuation 0 != source.fieldValue valuation 0 then
      throw (IO.userError "outer embedding changed an ordinary output or full field")
  let some grown := WireOpenProperSupport.compile source records temporaryGrowth
    | throw (IO.userError "temporary growth before final saving was rejected")
  if grown.program.execution.charged != 1 || grown.program.execution.removed != 2 ||
      grown.result.implementation.gateCount != 2 then
    throw (IO.userError "temporary expansion was hidden by final size")
  let some identity := WireOpenProperSupport.compile source records []
    | throw (IO.userError "closed identity program failed literal outer compilation")
  if identity.result.implementation.gateCount != 3 then
    throw (IO.userError "identity compilation invented a physical saving")
  if (WireOpenProperSupport.compile source records
      [⟨7, [], .primitive (.createR5 0)⟩, ⟨20, [7], .support (removeGate 1)⟩]).isSome then
    throw (IO.userError "outer compiler accepted a live final obligation")
  if (WireOpenProperSupport.compile source records
      (raw ++ [⟨99, [50], .primitive (.readFull 9)⟩])).isSome then
    throw (IO.userError "failed final action returned a successful prefix splice")
  IO.println "open-proper-support-regressions-passed"

#print axioms PNP.DirectWire.WireOpenProperSupport.program_equivalent
#print axioms PNP.DirectWire.WireOpenProperSupport.program_causalInterfaceBound
#print axioms PNP.DirectWire.WireOpenProperSupport.program_compiles
#print axioms PNP.DirectWire.WireOpenProperSupport.SplicedProgram.output
#print axioms PNP.DirectWire.WireOpenProperSupport.SplicedProgram.field
#print axioms PNP.DirectWire.WireOpenProperSupport.SplicedProgram.gateCount
#print axioms PNP.DirectWire.WireOpenProperSupport.SplicedProgram.charge_accounting
#print axioms PNP.DirectWire.WireOpenProperSupport.SplicedProgram.gain_iff_local_gain
#print axioms PNP.DirectWire.WireOpenProperSupport.SplicedProgram.gain_iff_net_charges
#print axioms PNP.DirectWire.WireOpenProperSupport.SplicedProgram.strictGain
#print axioms PNP.DirectWire.WireOpenProperSupport.SplicedProgram.strictResidualDescent
#print axioms PNP.DirectWire.WireOpenProperSupport.compile_complete
#print axioms PNP.DirectWire.WireOpenProperSupport.compile_exists_iff
#print axioms PNP.DirectWire.WireOpenProperSupport.compile_none_iff

end PNP.Regression.WireOpenProperSupport

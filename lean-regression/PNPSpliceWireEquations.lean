import PNP.NANDArbitrarySupportSplice

open PNP PNP.DirectWire PNP.DirectWire.ArbitrarySupportSplice

section Generic

variable {inputs gates outputs profileWidth replacementGates : Nat}
variable (candidate : Candidate inputs gates outputs)
variable (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
variable (replacement : Candidate
  (terminalBoundaryPorts candidate.program records).length replacementGates
  (terminalInterfacePorts candidate records).length)

example (port : Fin (terminalBoundaryPorts candidate.program records).length)
    (input : Fin inputs)
    (atPort : (terminalBoundaryPorts candidate.program records).get port = .input input) :
    boundarySource (replacementGates := replacementGates) candidate records port = .input input :=
  boundarySource_input candidate records port input atPort

example (port : Fin (terminalBoundaryPorts candidate.program records).length)
    (outside : Fin (exterior records).length)
    (atPort : (terminalBoundaryPorts candidate.program records).get port =
      .gate ((exterior records).get outside)) :
    boundarySource candidate records port = .gate (Fin.castAdd replacementGates outside) :=
  boundarySource_gate candidate records port outside atPort

example (outside : Fin (exterior records).length)
    (visible : Visible candidate records (.gate ((exterior records).get outside))) :
    originalSource candidate records replacement (.gate ((exterior records).get outside)) visible =
      .gate (Fin.castAdd replacementGates outside) :=
  originalSource_exterior candidate records replacement outside visible

example (port : Fin (terminalInterfacePorts candidate records).length)
    (visible : Visible candidate records
      (.gate ((terminalInterfacePorts candidate records).get port))) :
    originalSource candidate records replacement
        (.gate ((terminalInterfacePorts candidate records).get port)) visible =
      replacementSource candidate records (replacement.directWireWord.source port) :=
  originalSource_interface candidate records replacement port visible

end Generic

#print axioms PNP.DirectWire.ArbitrarySupportSplice.boundarySource_input
#print axioms PNP.DirectWire.ArbitrarySupportSplice.boundarySource_gate
#print axioms PNP.DirectWire.ArbitrarySupportSplice.originalSource_exterior
#print axioms PNP.DirectWire.ArbitrarySupportSplice.originalSource_interface

private def exampleProgram : Program 2 3 :=
  ((Program.empty.snoc ⟨.input 0, .input 0⟩).snoc
    ⟨.gate 0, .input 1⟩).snoc ⟨.gate 0, .gate 0⟩

private def candidate : Candidate 2 3 2 :=
  Candidate.ofDirectWireWord exampleProgram
    ⟨fun output => if output.val = 0 then .gate 1 else .gate 2⟩

private def records : List (TerminalPrimitiveRecord 2 3 2 0) := [.gate 1, .gate 1]

private def replacement : Candidate
    (terminalBoundaryPorts candidate.program records).length 1
    (terminalInterfacePorts candidate records).length :=
  Candidate.ofDirectWireWord (Program.empty.snoc
    ⟨.input ⟨1, by decide⟩, .input ⟨0, by decide⟩⟩)
    ⟨fun _ => .gate 0⟩

private def fixtures : List (String × Bool) :=
  [("proper support has two boundary wires and two exterior gates",
      decide ((terminalBoundaryPorts candidate.program records).length = 2) &&
      decide ((exterior records).length = 2) &&
      decide ((terminalInterfacePorts candidate records).length = 1)),
    ("actual primary boundary input keeps its original coordinate",
      decide (boundarySource (replacementGates := 1) candidate records ⟨0, by decide⟩ = .input 1)),
    ("actual gate boundary uses its exact exterior coordinate",
      decide (boundarySource (replacementGates := 1) candidate records ⟨1, by decide⟩ = .gate 0)),
    ("retained and replacement output references are physically distinct",
      decide ((word candidate records replacement).source 0 = .gate 2) &&
      decide ((word candidate records replacement).source 1 = .gate 1)),
    ("replacement gate binds both actual sources without a default wire",
      decide (((graph candidate records replacement).gate 2).left = .gate 0) &&
      decide (((graph candidate records replacement).gate 2).right = .input 1))]

#eval (do
  for (name, checked) in fixtures do
    unless checked do throw (IO.userError ("splice-wire-equations failure: " ++ name))
  IO.println "splice-wire-equations-runtime-regressions: 5 passed"
  : IO Unit)

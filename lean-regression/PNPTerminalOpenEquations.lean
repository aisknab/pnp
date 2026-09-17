import PNP.ResidualTerminalSupportExtraction

open PNP PNP.DirectWire

example {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (valuation : Valuation (terminalBoundaryPorts candidate.program records).length)
    (node : Fin gates) :
    terminalOpenGateEvaluation candidate records valuation node =
      if terminalGateSelected records node then
        boolNand
          (terminalOpenSourceValue candidate records valuation
            (candidate.program.terminalGateSources node).1)
          (terminalOpenSourceValue candidate records valuation
            (candidate.program.terminalGateSources node).2)
      else false :=
  terminalOpenGateEvaluation_sourceEquation candidate records valuation node

#print axioms PNP.DirectWire.terminalOpenSourceValue
#print axioms PNP.DirectWire.terminalOpenGateEvaluation_sourceEquation
#print axioms PNP.DirectWire.terminalOpenWireValue_boundary_get
#print axioms PNP.DirectWire.terminalOpenWireValue_external_absent

-- The two boundary gates always agree under whole-circuit inputs, but their
-- independent open-boundary bits need not agree. Exercise that stronger domain.
private def program : Program 1 3 :=
  ((Program.empty.snoc ⟨.input 0, .input 0⟩).snoc
    ⟨.input 0, .input 0⟩).snoc ⟨.gate 0, .gate 1⟩

private def candidate : Candidate 1 3 1 :=
  Candidate.ofDirectWireWord program ⟨fun _ => .gate 2⟩

private def records : List (TerminalPrimitiveRecord 1 3 1 0) := [.gate 2]

private def valuation :
    Valuation (terminalBoundaryPorts candidate.program records).length :=
  fun index => index.val == 0

#eval (do
  let boundary := terminalBoundaryPorts candidate.program records
  let fixtures : List (String × Bool) :=
    [("two distinct external boundary gates", decide (boundary.length = 2)),
      ("non-induced independent boundary produces the literal NAND result",
        terminalOpenGateEvaluation candidate records valuation 2),
      ("all-true independent boundary produces false",
        !(terminalOpenGateEvaluation candidate records (fun _ => true) 2)),
      ("unselected coordinate is inert but its boundary wire is not",
        !(terminalOpenGateEvaluation candidate records valuation 0) &&
          terminalOpenWireValue candidate records valuation (.gate 0)),
      ("every boundary position reads its independently chosen value",
        (allFin boundary.length).all (fun index =>
          decide (terminalOpenWireValue candidate records valuation (boundary.get index) =
            valuation index))),
      ("absent external input is inert",
        !(terminalOpenWireValue candidate records valuation (.input 0))),
      ("both local constants retain their literal value",
        !(terminalOpenSourceValue candidate records valuation (.constant false)) &&
          terminalOpenSourceValue candidate records valuation (.constant true))]
  for (name, checked) in fixtures do
    unless checked do throw (IO.userError ("terminal-open-equations failure: " ++ name))
  IO.println "terminal-open-equations-runtime-regressions: 7 passed"
  : IO Unit)

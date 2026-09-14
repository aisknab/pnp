import PNP.ResidualTerminalSupportExtraction

namespace PNP.DirectWire

-- Exact unbounded interfaces. Concrete and square-composition regressions are
-- added with the complete construction before this milestone is sealed.
example {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (small large : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (included : forall gate, terminalGateSelected small gate = true ->
      terminalGateSelected large gate = true)
    (valuation : Valuation (terminalBoundaryPorts candidate.program large).length)
    (gate : Fin gates) (selected : terminalGateSelected small gate = true) :
    terminalOpenGateEvaluation candidate small
        (terminalBoundaryPullback candidate small large valuation) gate =
      terminalOpenGateEvaluation candidate large valuation gate :=
  terminalOpenGateEvaluation_pullback candidate small large included valuation gate selected

example {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (small large : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (included : forall gate, terminalGateSelected small gate = true ->
      terminalGateSelected large gate = true)
    (valuation : Valuation (terminalBoundaryPorts candidate.program large).length)
    (output : Fin (terminalInterfacePorts candidate small).length) :
    terminalOpenSupportSemantics candidate small
        (terminalBoundaryPullback candidate small large valuation) output =
      terminalOpenGateEvaluation candidate large valuation
        ((terminalInterfacePorts candidate small).get output) :=
  terminalOpenSupportSemantics_pullback candidate small large included valuation output


example {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (valuation : Valuation (terminalBoundaryPorts candidate.program records).length) :
    terminalBoundaryPullback candidate records records valuation = valuation :=
  terminalBoundaryPullback_identity candidate records valuation

example {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (small middle large :
      List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (smallIncluded : forall gate, terminalGateSelected small gate = true ->
      terminalGateSelected middle gate = true)
    (middleIncluded : forall gate, terminalGateSelected middle gate = true ->
      terminalGateSelected large gate = true)
    (valuation : Valuation (terminalBoundaryPorts candidate.program large).length) :
    terminalBoundaryPullback candidate small middle
        (terminalBoundaryPullback candidate middle large valuation) =
      terminalBoundaryPullback candidate small large valuation :=
  terminalBoundaryPullback_compose candidate small middle large
    smallIncluded middleIncluded valuation

end PNP.DirectWire

import PNP

set_option autoImplicit false
set_option Elab.async false

namespace PNP.DirectWire.GuardedSpineSupportMinimumProbe
open GuardedSpineFamily (candidate)
open GuardedSpineSupportMinimum

variable {profileWidth : Nat}

theorem general_first_only_minimum (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (firstSelected : terminalGateSelected records 0 = true)
    (lastOutside : terminalGateSelected records (Fin.last (n + 1)) = false)
    (gates : Nat)
    (program : Program (terminalBoundaryPorts (candidate n).program records).length gates)
    (word : DirectWireWord (terminalBoundaryPorts (candidate n).program records).length gates
      (terminalInterfacePorts (candidate n) records).length)
    (equivalent : Equivalent program word
      (extractTerminalSupport (candidate n) records).extractedCandidate.program
      (extractTerminalSupport (candidate n) records).extractedCandidate.directWireWord) :
    (extractTerminalSupport (candidate n) records).gateCount ≤ gates :=
  first_only_minimum n records firstSelected lastOutside gates program word equivalent

theorem general_both_ends_minimum (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (firstSelected : terminalGateSelected records 0 = true)
    (lastSelected : terminalGateSelected records (Fin.last (n + 1)) = true)
    (proper : ∃ node, terminalGateSelected records node = false)
    (gates : Nat)
    (program : Program (terminalBoundaryPorts (candidate n).program records).length gates)
    (word : DirectWireWord (terminalBoundaryPorts (candidate n).program records).length gates
      (terminalInterfacePorts (candidate n) records).length)
    (equivalent : Equivalent program word
      (extractTerminalSupport (candidate n) records).extractedCandidate.program
      (extractTerminalSupport (candidate n) records).extractedCandidate.directWireWord) :
    (extractTerminalSupport (candidate n) records).gateCount ≤ gates :=
  both_ends_minimum n records firstSelected lastSelected proper gates program word equivalent

theorem general_proper_minimum (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (proper : ∃ node, terminalGateSelected records node = false)
    (gates : Nat)
    (program : Program (terminalBoundaryPorts (candidate n).program records).length gates)
    (word : DirectWireWord (terminalBoundaryPorts (candidate n).program records).length gates
      (terminalInterfacePorts (candidate n) records).length)
    (equivalent : Equivalent program word
      (extractTerminalSupport (candidate n) records).extractedCandidate.program
      (extractTerminalSupport (candidate n) records).extractedCandidate.directWireWord) :
    (extractTerminalSupport (candidate n) records).gateCount ≤ gates :=
  proper_minimum n records proper gates program word equivalent

private def firstOnly : List (TerminalPrimitiveRecord 4 5 1 0) := [.gate 0,.gate 2]
private def bothEnds : List (TerminalPrimitiveRecord 4 5 1 0) := [.gate 0,.gate 2,.gate 4]
private def repeated : List (TerminalPrimitiveRecord 4 5 1 0) := [.gate 4,.gate 0,.gate 4,.gate 2,.gate 0]
private def initialOnly : List (TerminalPrimitiveRecord 1 2 1 0) := [.gate 0]

theorem first_only_disconnected
    (gates : Nat)
    (program : Program (terminalBoundaryPorts (candidate 3).program firstOnly).length gates)
    (word : DirectWireWord (terminalBoundaryPorts (candidate 3).program firstOnly).length gates
      (terminalInterfacePorts (candidate 3) firstOnly).length)
    (equivalent : Equivalent program word
      (extractTerminalSupport (candidate 3) firstOnly).extractedCandidate.program
      (extractTerminalSupport (candidate 3) firstOnly).extractedCandidate.directWireWord) :
    2 ≤ gates := by
  have lower := proper_minimum 3 firstOnly ⟨1,by decide +kernel⟩ gates program word equivalent
  change 2 ≤ gates at lower
  exact lower

theorem both_ends_disconnected
    (gates : Nat)
    (program : Program (terminalBoundaryPorts (candidate 3).program bothEnds).length gates)
    (word : DirectWireWord (terminalBoundaryPorts (candidate 3).program bothEnds).length gates
      (terminalInterfacePorts (candidate 3) bothEnds).length)
    (equivalent : Equivalent program word
      (extractTerminalSupport (candidate 3) bothEnds).extractedCandidate.program
      (extractTerminalSupport (candidate 3) bothEnds).extractedCandidate.directWireWord) :
    3 ≤ gates := by
  have lower := proper_minimum 3 bothEnds ⟨1,by decide +kernel⟩ gates program word equivalent
  change 3 ≤ gates at lower
  exact lower

theorem repeated_both_ends
    (gates : Nat)
    (program : Program (terminalBoundaryPorts (candidate 3).program repeated).length gates)
    (word : DirectWireWord (terminalBoundaryPorts (candidate 3).program repeated).length gates
      (terminalInterfacePorts (candidate 3) repeated).length)
    (equivalent : Equivalent program word
      (extractTerminalSupport (candidate 3) repeated).extractedCandidate.program
      (extractTerminalSupport (candidate 3) repeated).extractedCandidate.directWireWord) :
    3 ≤ gates := by
  have lower := proper_minimum 3 repeated ⟨1,by decide +kernel⟩ gates program word equivalent
  change 3 ≤ gates at lower
  exact lower

theorem one_gate_initial_support
    (gates : Nat)
    (program : Program (terminalBoundaryPorts (candidate 0).program initialOnly).length gates)
    (word : DirectWireWord (terminalBoundaryPorts (candidate 0).program initialOnly).length gates
      (terminalInterfacePorts (candidate 0) initialOnly).length)
    (equivalent : Equivalent program word
      (extractTerminalSupport (candidate 0) initialOnly).extractedCandidate.program
      (extractTerminalSupport (candidate 0) initialOnly).extractedCandidate.directWireWord) :
    1 ≤ gates := by
  have lower := proper_minimum 0 initialOnly ⟨1,by decide +kernel⟩ gates program word equivalent
  change 1 ≤ gates at lower
  exact lower

theorem full_selection_excluded_and_nonminimum :
    (¬ ∃ node : Fin 5, terminalGateSelected
      ([.gate 0,.gate 1,.gate 2,.gate 3,.gate 4] :
        List (TerminalPrimitiveRecord 4 5 1 0)) node = false) ∧
      0 < residualSlack (candidate 3).toImplementation := by
  exact ⟨by decide +kernel,GuardedSpineFamily.residual_positive 1⟩

end PNP.DirectWire.GuardedSpineSupportMinimumProbe

#print axioms PNP.DirectWire.GuardedSpineSupportMinimumProbe.general_first_only_minimum
#print axioms PNP.DirectWire.GuardedSpineSupportMinimumProbe.general_both_ends_minimum
#print axioms PNP.DirectWire.GuardedSpineSupportMinimumProbe.general_proper_minimum
#print axioms PNP.DirectWire.GuardedSpineSupportMinimumProbe.first_only_disconnected
#print axioms PNP.DirectWire.GuardedSpineSupportMinimumProbe.both_ends_disconnected
#print axioms PNP.DirectWire.GuardedSpineSupportMinimumProbe.repeated_both_ends
#print axioms PNP.DirectWire.GuardedSpineSupportMinimumProbe.one_gate_initial_support
#print axioms PNP.DirectWire.GuardedSpineSupportMinimumProbe.full_selection_excluded_and_nonminimum

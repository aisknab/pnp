import PNP.NANDClosedSupportNestedSelection

/-!
Rebuild only the physical difference after a smaller-support realization.
The common ambient inputs are retained without zero specialization. Final
profile equality, reference-cost bounds and positivity remain later obligations.
-/

namespace PNP.DirectWire.ClosedSupportNestedGain

variable {inputs outputs fields : Nat}

def boundarySource (target : WireCarrier inputs outputs fields)
    (prefixImpl : Implementation (inputs + target.implementation.gateCount)
      target.implementation.gateCount) :
    TerminalSupportWire inputs target.implementation.gateCount →
      Source (inputs + target.implementation.gateCount) prefixImpl.gateCount
  | .input input => .input (Fin.castAdd target.implementation.gateCount input)
  | .gate producer => prefixImpl.candidate.directWireWord.source producer

theorem boundarySource_value (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (realization : TerminalFullRealization
      (ClosedSupportObservation.implementation target keep small))
    (wire : TerminalSupportWire inputs target.implementation.gateCount)
    (member : wire ∈ (difference target keep small large).boundary)
    (valuation : Valuation (inputs + target.implementation.gateCount)) :
    (boundarySource target realization.implementation wire).eval valuation
        (realization.implementation.candidate.program.eval valuation) =
      wire.candidateValue target.implementation.candidate
        (fun input => valuation (Fin.castAdd target.implementation.gateCount input)) := by
  cases wire with
  | input input => rfl
  | gate producer =>
      change realization.implementation.candidate.semantics valuation producer = _
      exact (realization.equivalent valuation producer).trans
        (ClosedSupportFullGain.ambient_output target keep small producer
          (difference_boundary_interface target keep small large producer member) valuation)

def boundaryBinding (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (prefixImpl : Implementation (inputs + target.implementation.gateCount)
      target.implementation.gateCount) :
    Fin (difference target keep small large).boundary.length →
      Source (inputs + target.implementation.gateCount) prefixImpl.gateCount :=
  fun index => boundarySource target prefixImpl
    ((difference target keep small large).boundary.get index)

def program (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (prefixImpl : Implementation (inputs + target.implementation.gateCount)
      target.implementation.gateCount) :
    Program (inputs + target.implementation.gateCount)
      (prefixImpl.gateCount + (difference target keep small large).gateCount) :=
  prefixImpl.candidate.program.appendSubstituted
    (boundaryBinding target keep small large prefixImpl)
    (difference target keep small large).extractedCandidate.program

theorem difference_gate_value (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (realization : TerminalFullRealization
      (ClosedSupportObservation.implementation target keep small))
    (gate : Fin target.implementation.gateCount)
    (selected : terminalGateSelected (differenceRecords target keep small large) gate = true)
    (valuation : Valuation (inputs + target.implementation.gateCount)) :
    (program target keep small large realization.implementation).eval valuation
        (Fin.natAdd realization.implementation.gateCount
          (terminalExtractionGateIndex target.implementation.candidate
            (differenceRecords target keep small large) gate selected)) =
      target.implementation.candidate.program.eval
        (fun input => valuation (Fin.castAdd target.implementation.gateCount input)) gate := by
  have boundaryEqual :
      (fun index => (boundaryBinding target keep small large realization.implementation index).eval
          valuation (realization.implementation.candidate.program.eval valuation)) =
        terminalInducedBoundaryValuation target.implementation.candidate
          (differenceRecords target keep small large)
          (fun input => valuation (Fin.castAdd target.implementation.gateCount input)) := by
    funext index
    exact boundarySource_value target keep small large realization
      ((difference target keep small large).boundary.get index) (List.get_mem _ index) valuation
  unfold program
  rw [Program.eval_appendSubstituted_suffix, boundaryEqual]
  exact extractTerminalSupport_gate_induced target.implementation.candidate
    (differenceRecords target keep small large) _ gate selected

theorem prefix_source_value (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (prefixImpl : Implementation (inputs + target.implementation.gateCount)
      target.implementation.gateCount)
    (source : Source (inputs + target.implementation.gateCount) prefixImpl.gateCount)
    (valuation : Valuation (inputs + target.implementation.gateCount)) :
    (source.weakenGates (difference target keep small large).gateCount).eval valuation
        ((program target keep small large prefixImpl).eval valuation) =
      source.eval valuation (prefixImpl.candidate.program.eval valuation) := by
  rw [Source.eval_weakenGates]
  exact source.eval_congr (fun _ => rfl)
    (fun gate => Program.eval_appendSubstituted_prefix _ _ _ valuation gate)

end PNP.DirectWire.ClosedSupportNestedGain

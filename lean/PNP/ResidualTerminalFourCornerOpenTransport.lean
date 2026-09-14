/-
Copyright (c) 2026 PNP Labs.

Computed open-boundary transport for every terminal support square. A wire
internalized by a larger corner is evaluated in that corner, not independently
assigned an ambient Boolean value. The two join-to-meet substitutions commute,
and retained physical outputs agree for the extracted corners and their actual
full and quotient minimum realizers.

This reconstructs the physical substitution edge of Sections 2.2 and 3 and
BN2-CoherentOptimum in Section 11.1 of the pinned manuscript. It does not change
the existing unconstrained-ambient coherence classifier, prove equality of
arbitrary profile observers, glue minimum circuits or charge ownership, close
obligation dependencies, or prove global route coverage, SaturatePositive,
BCELReady, ZeroSlack, exact PCCMin, polynomial runtime, SAT in P, or P = NP.
-/

import PNP.ResidualTerminalFourCornerOptimumCoherence

namespace PNP
namespace DirectWire

variable {inputs gates outputs profileWidth : Nat}
variable {system : TerminalSaturationSystem inputs gates outputs profileWidth}
variable {carrier : TerminalFourCornerCarrier system}

/-- Gate inclusion is derived from the actual square leg, not supplied as a
    separate transport certificate. -/
theorem TerminalOptimumLegTransport.selectedGateTransport
    (transport : TerminalOptimumLegTransport carrier)
    (gate : Fin gates)
    (selected : terminalGateSelected
      (carrier.square.records transport.leg.source) gate = true) :
    terminalGateSelected (carrier.square.records transport.leg.target) gate = true := by
  have member : TerminalPrimitiveRecord.gate gate ∈
      carrier.square.records transport.leg.source := of_decide_eq_true selected
  exact decide_eq_true (transport.recordsSubset _ member)

/-- Pull an arbitrary target boundary assignment back along the physical leg.
    Internalized source wires use their computed target gate values. -/
def TerminalOptimumLegTransport.boundaryPullback
    (transport : TerminalOptimumLegTransport carrier) :
    Valuation (carrier.extracted transport.leg.target).boundary.length ->
      Valuation (carrier.extracted transport.leg.source).boundary.length :=
  terminalBoundaryPullback carrier.candidate
    (carrier.square.records transport.leg.source)
    (carrier.square.records transport.leg.target)

/-- The left path is the direct join-to-meet boundary substitution. -/
theorem TerminalFourCornerCarrier.boundaryPullback_meet_join_left
    (carrier : TerminalFourCornerCarrier system)
    (valuation : Valuation (carrier.extracted .join).boundary.length) :
    (carrier.optimumLegTransport .meetLeft).boundaryPullback
        ((carrier.optimumLegTransport .leftJoin).boundaryPullback valuation) =
      terminalBoundaryPullback carrier.candidate
        (carrier.square.records .meet) (carrier.square.records .join) valuation :=
  terminalBoundaryPullback_compose carrier.candidate
    (carrier.square.records .meet) (carrier.square.records .left)
    (carrier.square.records .join)
    (carrier.optimumLegTransport .meetLeft).selectedGateTransport
    (carrier.optimumLegTransport .leftJoin).selectedGateTransport valuation

/-- The right path is the same direct join-to-meet substitution. -/
theorem TerminalFourCornerCarrier.boundaryPullback_meet_join_right
    (carrier : TerminalFourCornerCarrier system)
    (valuation : Valuation (carrier.extracted .join).boundary.length) :
    (carrier.optimumLegTransport .meetRight).boundaryPullback
        ((carrier.optimumLegTransport .rightJoin).boundaryPullback valuation) =
      terminalBoundaryPullback carrier.candidate
        (carrier.square.records .meet) (carrier.square.records .join) valuation :=
  terminalBoundaryPullback_compose carrier.candidate
    (carrier.square.records .meet) (carrier.square.records .right)
    (carrier.square.records .join)
    (carrier.optimumLegTransport .meetRight).selectedGateTransport
    (carrier.optimumLegTransport .rightJoin).selectedGateTransport valuation

/-- Both physical square paths agree as complete valuation maps, for every
    arbitrary join-boundary assignment. This is not just coordinate identity. -/
theorem TerminalFourCornerCarrier.boundaryPullback_square
    (carrier : TerminalFourCornerCarrier system)
    (valuation : Valuation (carrier.extracted .join).boundary.length) :
    (carrier.optimumLegTransport .meetLeft).boundaryPullback
        ((carrier.optimumLegTransport .leftJoin).boundaryPullback valuation) =
      (carrier.optimumLegTransport .meetRight).boundaryPullback
        ((carrier.optimumLegTransport .rightJoin).boundaryPullback valuation) :=
  (carrier.boundaryPullback_meet_join_left valuation).trans
    (carrier.boundaryPullback_meet_join_right valuation).symm

/-- Retained extracted outputs agree after physical boundary substitution,
    even when some source-boundary wires become internal at the target. -/
theorem TerminalOptimumLegTransport.extracted_retained_semantics
    (transport : TerminalOptimumLegTransport carrier)
    (valuation : Valuation (carrier.extracted transport.leg.target).boundary.length)
    (sourceIndex : Fin (carrier.extracted transport.leg.source).interface.length)
    (targetIndex : Fin (carrier.extracted transport.leg.target).interface.length)
    (retained : transport.retainedOutput? sourceIndex = some targetIndex) :
    (carrier.cornerImplementation transport.leg.source).candidate.semantics
        (transport.boundaryPullback valuation) sourceIndex =
      (carrier.cornerImplementation transport.leg.target).candidate.semantics
        valuation targetIndex := by
  have producer :=
    (transport.retainedOutput?_eq_some_iff sourceIndex targetIndex).1 retained
  calc
    _ = terminalOpenSupportSemantics carrier.candidate
        (carrier.square.records transport.leg.source)
        (transport.boundaryPullback valuation) sourceIndex :=
      extractTerminalSupport_semantics carrier.candidate
        (carrier.square.records transport.leg.source) _ sourceIndex
    _ = terminalOpenGateEvaluation carrier.candidate
        (carrier.square.records transport.leg.target) valuation
        ((carrier.extracted transport.leg.source).interface.get sourceIndex) :=
      terminalOpenSupportSemantics_pullback carrier.candidate
        (carrier.square.records transport.leg.source)
        (carrier.square.records transport.leg.target)
        transport.selectedGateTransport valuation sourceIndex
    _ = terminalOpenSupportSemantics carrier.candidate
        (carrier.square.records transport.leg.target) valuation targetIndex :=
      congrArg (terminalOpenGateEvaluation carrier.candidate
        (carrier.square.records transport.leg.target) valuation) producer.symm
    _ = _ :=
      (extractTerminalSupport_semantics carrier.candidate
        (carrier.square.records transport.leg.target) valuation targetIndex).symm

/-- Any two valid local realizations inherit the physical comparison from the
    original extracted carrier. No internal gate of a realizer is invented. -/
theorem TerminalOptimumLegTransport.realization_retained_semantics
    (transport : TerminalOptimumLegTransport carrier)
    (sourceRealization : TerminalFullRealization
      (carrier.cornerImplementation transport.leg.source))
    (targetRealization : TerminalFullRealization
      (carrier.cornerImplementation transport.leg.target))
    (valuation : Valuation (carrier.extracted transport.leg.target).boundary.length)
    (sourceIndex : Fin (carrier.extracted transport.leg.source).interface.length)
    (targetIndex : Fin (carrier.extracted transport.leg.target).interface.length)
    (retained : transport.retainedOutput? sourceIndex = some targetIndex) :
    sourceRealization.implementation.candidate.semantics
        (transport.boundaryPullback valuation) sourceIndex =
      targetRealization.implementation.candidate.semantics valuation targetIndex :=
  (sourceRealization.realize_semantics _ sourceIndex).trans
    ((transport.extracted_retained_semantics valuation sourceIndex targetIndex retained).trans
      (targetRealization.realize_semantics valuation targetIndex).symm)

/-- Actual full minimum realizers preserve every physically retained output.
    No equality of arbitrary profile observers follows from this theorem. -/
theorem TerminalFourCornerOptimumFamily.full_retained_semantics
    {observe : Implementation (inputs + gates) gates -> TerminalProfile profileWidth}
    (family : TerminalFourCornerOptimumFamily carrier observe)
    (leg : TerminalOptimumSquareLeg)
    (valuation : Valuation (carrier.extracted leg.target).boundary.length)
    (sourceIndex : Fin (carrier.extracted leg.source).interface.length)
    (targetIndex : Fin (carrier.extracted leg.target).interface.length)
    (retained : (carrier.optimumLegTransport leg).retainedOutput? sourceIndex =
      some targetIndex) :
    (family.fullLocalRealization leg.source).implementation.candidate.semantics
        ((carrier.optimumLegTransport leg).boundaryPullback valuation) sourceIndex =
      (family.fullLocalRealization leg.target).implementation.candidate.semantics
        valuation targetIndex :=
  (carrier.optimumLegTransport leg).realization_retained_semantics
    (family.fullLocalRealization leg.source) (family.fullLocalRealization leg.target)
    valuation sourceIndex targetIndex retained

/-- Actual quotient minimum realizers preserve the same physical outputs.
    This does not upgrade forgotten profile coordinates to full coherence. -/
theorem TerminalFourCornerOptimumFamily.quotient_retained_semantics
    {observe : Implementation (inputs + gates) gates -> TerminalProfile profileWidth}
    (family : TerminalFourCornerOptimumFamily carrier observe)
    (leg : TerminalOptimumSquareLeg)
    (valuation : Valuation (carrier.extracted leg.target).boundary.length)
    (sourceIndex : Fin (carrier.extracted leg.source).interface.length)
    (targetIndex : Fin (carrier.extracted leg.target).interface.length)
    (retained : (carrier.optimumLegTransport leg).retainedOutput? sourceIndex =
      some targetIndex) :
    (family.quotientLocalRealization leg.source).implementation.candidate.semantics
        ((carrier.optimumLegTransport leg).boundaryPullback valuation) sourceIndex =
      (family.quotientLocalRealization leg.target).implementation.candidate.semantics
        valuation targetIndex :=
  (carrier.optimumLegTransport leg).realization_retained_semantics
    (family.quotientLocalRealization leg.source) (family.quotientLocalRealization leg.target)
    valuation sourceIndex targetIndex retained

/-- The computed exhaustive full minima satisfy physical transport without a
    caller-supplied family or comparison certificate. No runtime bound is claimed. -/
theorem TerminalFourCornerCarrier.canonicalFull_retained_semantics
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates -> TerminalProfile profileWidth)
    (leg : TerminalOptimumSquareLeg)
    (valuation : Valuation (carrier.extracted leg.target).boundary.length)
    (sourceIndex : Fin (carrier.extracted leg.source).interface.length)
    (targetIndex : Fin (carrier.extracted leg.target).interface.length)
    (retained : (carrier.optimumLegTransport leg).retainedOutput? sourceIndex =
      some targetIndex) :
    ((carrier.canonicalOptimumFamily observe).fullLocalRealization leg.source).implementation.candidate.semantics
        ((carrier.optimumLegTransport leg).boundaryPullback valuation) sourceIndex =
      ((carrier.canonicalOptimumFamily observe).fullLocalRealization leg.target).implementation.candidate.semantics valuation targetIndex :=
  (carrier.canonicalOptimumFamily observe).full_retained_semantics
    leg valuation sourceIndex targetIndex retained

/-- The computed exhaustive quotient minima satisfy physical transport, without
    inferring full-profile coherence or polynomial execution. -/
theorem TerminalFourCornerCarrier.canonicalQuotient_retained_semantics
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates -> TerminalProfile profileWidth)
    (leg : TerminalOptimumSquareLeg)
    (valuation : Valuation (carrier.extracted leg.target).boundary.length)
    (sourceIndex : Fin (carrier.extracted leg.source).interface.length)
    (targetIndex : Fin (carrier.extracted leg.target).interface.length)
    (retained : (carrier.optimumLegTransport leg).retainedOutput? sourceIndex =
      some targetIndex) :
    ((carrier.canonicalOptimumFamily observe).quotientLocalRealization leg.source).implementation.candidate.semantics
        ((carrier.optimumLegTransport leg).boundaryPullback valuation) sourceIndex =
      ((carrier.canonicalOptimumFamily observe).quotientLocalRealization leg.target).implementation.candidate.semantics valuation targetIndex :=
  (carrier.canonicalOptimumFamily observe).quotient_retained_semantics
    leg valuation sourceIndex targetIndex retained

end DirectWire
end PNP

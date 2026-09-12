/-
Copyright (c) 2026 PNP Labs.

Compute a quotient-visible predecessor cone, complete its frontier from the
actual full computational word, and substitute into the original exterior.
Every exterior gate is retained exactly once, so the matched charge is measured
against the original circuit rather than a potentially larger reference lift.

The local premise is equality of the complete extracted open function. It is
not inferred from ordinary-output or quotient-only agreement. This component
does not construct the full manuscript carrier, every arbitrary-support
Pull/Expand trace, complete Package E, ZeroSlack or polynomial PCCMin.
-/

import PNP.NANDWireQuotientLift

namespace PNP.DirectWire.WireFrontierLift

variable {inputs outputs fields : Nat}

/-- The actual predecessor cone of ordinary outputs and kept field wires. -/
def records (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount
      (outputs + fields) 0) :=
  outputConeRecords (WireObligationRestoration.masked carrier keep).exposed.candidate

/-- Complete the selected cone against all actual observations and consumers.
Forgotten retained wires can therefore occur on the completed interface. -/
def pulled (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    TerminalExtractedSupport (profileWidth := 0) carrier.exposed.candidate :=
  extractTerminalSupport carrier.exposed.candidate (records carrier keep)

/-- This is the number of actual original exterior gates, not a supplied weight. -/
def exteriorCharge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : Nat :=
  (ArbitrarySupportSplice.exterior (records carrier keep)).length

theorem ordinary_output_selected (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (output : Fin outputs)
    (producer : Fin carrier.implementation.gateCount)
    (sourceAt : carrier.implementation.candidate.directWireWord.source output =
      .gate producer) :
    TerminalPrimitiveRecord.gate producer ∈ records carrier keep := by
  apply outputConeRecords_output
    (WireObligationRestoration.masked carrier keep).exposed.candidate producer
  apply (terminalGateIsGlobalOutput_eq_true_iff _ producer).2
  exact ⟨Fin.castAdd fields output,
    ((WireObligationRestoration.masked carrier keep).exposed_output_source output).trans
      sourceAt⟩

theorem kept_field_selected (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (field : Fin fields) (kept : keep field = true)
    (producer : Fin carrier.implementation.gateCount)
    (sourceAt : carrier.source field = .gate producer) :
    TerminalPrimitiveRecord.gate producer ∈ records carrier keep := by
  apply outputConeRecords_output
    (WireObligationRestoration.masked carrier keep).exposed.candidate producer
  apply (terminalGateIsGlobalOutput_eq_true_iff _ producer).2
  refine ⟨Fin.natAdd outputs field,
    ((WireObligationRestoration.masked carrier keep).exposed_field_source field).trans ?_⟩
  change (if keep field then carrier.source field else .constant false) = .gate producer
  rw [kept]
  exact sourceAt

theorem records_predecessor_closed (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (consumer producer : Fin carrier.implementation.gateCount)
    (selected : TerminalPrimitiveRecord.gate consumer ∈ records carrier keep)
    (uses : carrier.implementation.candidate.program.terminalGateUsesWire
      consumer (.gate producer) = true) :
    TerminalPrimitiveRecord.gate producer ∈ records carrier keep :=
  outputConeRecords_closed
    (WireObligationRestoration.masked carrier keep).exposed.candidate
    consumer producer selected uses

/-- Even forgotten selected field producers are exported by the completed frontier. -/
theorem selected_field_in_frontier (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (field : Fin fields)
    (producer : Fin carrier.implementation.gateCount)
    (sourceAt : carrier.source field = .gate producer)
    (selected : terminalGateSelected (records carrier keep) producer = true) :
    producer ∈ (pulled carrier keep).interface :=
  carrier.field_producer_visible (records carrier keep) field producer sourceAt selected

/-- No external gate source enters the derived predecessor-closed cone. -/
theorem primary_boundary (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    ArbitrarySupportSplice.PrimaryBoundary carrier.exposed.candidate (records carrier keep) := by
  intro wire member
  cases wire with
  | input index => exact ⟨index, rfl⟩
  | gate producer =>
      exact False.elim ((outputConeRecords_noExternalGate
        (WireObligationRestoration.masked carrier keep).exposed.candidate producer) member)

/-- The original gates are partitioned into the pulled support and its exterior. -/
theorem original_charge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    carrier.implementation.gateCount =
      (pulled carrier keep).gateCount + exteriorCharge carrier keep :=
  (ArbitrarySupportSplice.exterior_accounting carrier.exposed.candidate
    (records carrier keep)).symm

variable {replacementGates : Nat}

/-- Actual compiler success follows from the input-derived boundary. -/
theorem compile_isSome (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length) :
    (ArbitrarySupportSplice.compile carrier.exposed.candidate
      (records carrier keep) replacement).isSome = true := by
  obtain ⟨compiled, compiledAt⟩ := (ArbitrarySupportSplice.compile_success_iff
    carrier.exposed.candidate (records carrier keep) replacement).2
      (ArbitrarySupportSplice.graph_wellFounded_of_primaryBoundary
        carrier.exposed.candidate (records carrier keep) replacement
        (primary_boundary carrier keep))
  rw [compiledAt]
  rfl

/-- Run the compiler, rather than accepting a compiled result or an order. -/
def compiled (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length) :
    CompiledRawNandGraph (ArbitrarySupportSplice.graph carrier.exposed.candidate
      (records carrier keep) replacement) :=
  (ArbitrarySupportSplice.compile carrier.exposed.candidate
    (records carrier keep) replacement).get (compile_isSome carrier keep replacement)

/-- Substitute into the original exterior and recover the complete carrier. -/
def expanded (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length) : WireCarrier inputs outputs fields :=
  carrier.spliceResult (records carrier keep) replacement (compiled carrier keep replacement)

theorem expanded_charge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length) :
    (expanded carrier keep replacement).implementation.gateCount =
      replacementGates + exteriorCharge carrier keep := by
  have accounting := ArbitrarySupportSplice.result_gateCount carrier.exposed.candidate
    (records carrier keep) replacement (compiled carrier keep replacement)
  change (expanded carrier keep replacement).implementation.gateCount =
    exteriorCharge carrier keep + replacementGates at accounting
  exact accounting.trans (Nat.add_comm _ _)

theorem matched_original_charge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length) :
    (carrier.implementation.gateCount : Int) - (pulled carrier keep).gateCount =
      ((expanded carrier keep replacement).implementation.gateCount : Int) -
        replacementGates := by
  have original := original_charge carrier keep
  have result := expanded_charge carrier keep replacement
  omega

theorem original_gain_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length) :
    (expanded carrier keep replacement).implementation.gateCount <
        carrier.implementation.gateCount ↔
      replacementGates < (pulled carrier keep).gateCount := by
  rw [expanded_charge, original_charge]
  exact ⟨Nat.lt_of_add_lt_add_right,
    fun smaller => Nat.add_lt_add_right smaller (exteriorCharge carrier keep)⟩

theorem expanded_output (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length)
    (sameOpen : replacement.semantics =
      (pulled carrier keep).extractedCandidate.semantics)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (expanded carrier keep replacement).implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output :=
  carrier.splice_output (records carrier keep) replacement sameOpen
    (compiled carrier keep replacement) valuation output

theorem expanded_field (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length)
    (sameOpen : replacement.semantics =
      (pulled carrier keep).extractedCandidate.semantics)
    (valuation : Valuation inputs) (field : Fin fields) :
    (expanded carrier keep replacement).fieldValue valuation field =
      carrier.fieldValue valuation field :=
  carrier.splice_field (records carrier keep) replacement sameOpen
    (compiled carrier keep replacement) valuation field

theorem expanded_equivalent (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length)
    (sameOpen : replacement.semantics =
      (pulled carrier keep).extractedCandidate.semantics) :
    Equivalent (expanded carrier keep replacement).implementation.candidate.program
      (expanded carrier keep replacement).implementation.candidate.directWireWord
      carrier.implementation.candidate.program carrier.implementation.candidate.directWireWord :=
  expanded_output carrier keep replacement sameOpen

/-- The original lost source and the actual expanded source are both bound. -/
structure ExpandedDischarge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length)
    (creation : WireObligationRestoration.R5Creation carrier keep) where
  actualSource : Source inputs (expanded carrier keep replacement).implementation.gateCount
  sourceExact : actualSource = (expanded carrier keep replacement).source creation.coordinate
  fullWitness : ∀ valuation,
    actualSource.eval valuation
        ((expanded carrier keep replacement).implementation.candidate.program.eval valuation) =
      creation.originalSource.eval valuation
        (carrier.implementation.candidate.program.eval valuation)

/-- Full-frontier agreement, not quotient-only equality, justifies this discharge. -/
def discharge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length)
    (sameOpen : replacement.semantics =
      (pulled carrier keep).extractedCandidate.semantics)
    (creation : WireObligationRestoration.R5Creation carrier keep) :
    ExpandedDischarge carrier keep replacement creation :=
  { actualSource := (expanded carrier keep replacement).source creation.coordinate
    sourceExact := rfl
    fullWitness := by
      intro valuation
      rw [creation.sourceExact]
      exact expanded_field carrier keep replacement sameOpen valuation creation.coordinate }

theorem discharge_source_exact (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length)
    (sameOpen : replacement.semantics =
      (pulled carrier keep).extractedCandidate.semantics)
    (creation : WireObligationRestoration.R5Creation carrier keep) :
    (discharge carrier keep replacement sameOpen creation).actualSource =
      (expanded carrier keep replacement).source creation.coordinate := rfl

theorem discharge_full_value (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length)
    (sameOpen : replacement.semantics =
      (pulled carrier keep).extractedCandidate.semantics)
    (creation : WireObligationRestoration.R5Creation carrier keep)
    (valuation : Valuation inputs) :
    (discharge carrier keep replacement sameOpen creation).actualSource.eval valuation
        ((expanded carrier keep replacement).implementation.candidate.program.eval valuation) =
      carrier.fieldValue valuation creation.coordinate :=
  expanded_field carrier keep replacement sameOpen valuation creation.coordinate

/-- Gate-properness means a nonempty actual exterior, not a fictional record. -/
theorem proper_iff_exterior_positive (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (pulled carrier keep).gateCount < carrier.implementation.gateCount ↔
      0 < exteriorCharge carrier keep := by
  rw [original_charge]
  constructor
  · intro smaller
    apply Nat.lt_of_add_lt_add_left
    simpa only [Nat.add_zero] using smaller
  · intro positive
    simpa only [Nat.add_zero] using
      Nat.add_lt_add_left positive (pulled carrier keep).gateCount

/-- Both physical properness and the strict local saving are required.
The local semantic agreement is not discovered by this result type. -/
structure ProperGain (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length) : Type where
  agreement : replacement.semantics = (pulled carrier keep).extractedCandidate.semantics
  proper : (pulled carrier keep).gateCount < carrier.implementation.gateCount
  smaller : replacementGates < (pulled carrier keep).gateCount

/-- Test the two actual counts; no successful result is supplied. -/
def checkedProperGain (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length)
    (sameOpen : replacement.semantics =
      (pulled carrier keep).extractedCandidate.semantics) :
    Option (ProperGain carrier keep replacement) :=
  if proper : (pulled carrier keep).gateCount < carrier.implementation.gateCount then
    if smaller : replacementGates < (pulled carrier keep).gateCount then
      some { agreement := sameOpen, proper := proper, smaller := smaller }
    else none
  else none

theorem checkedProperGain_isSome_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length)
    (sameOpen : replacement.semantics =
      (pulled carrier keep).extractedCandidate.semantics) :
    (checkedProperGain carrier keep replacement sameOpen).isSome = true ↔
      (pulled carrier keep).gateCount < carrier.implementation.gateCount ∧
        replacementGates < (pulled carrier keep).gateCount := by
  unfold checkedProperGain
  split
  next proper =>
    split
    next smaller =>
      exact ⟨fun _accepted => ⟨proper, smaller⟩, fun _valid => rfl⟩
    next notSmaller =>
      constructor
      · intro impossible
        cases impossible
      · intro valid
        exact (notSmaller valid.2).elim
  next notProper =>
    constructor
    · intro impossible
      cases impossible
    · intro valid
      exact (notProper valid.1).elim

def ProperGain.strictGain {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool}
    {replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length}
    (gain : ProperGain carrier keep replacement) :
    StrictEquivalentGain carrier.implementation
      (expanded carrier keep replacement).implementation where
  smaller := (original_gain_iff carrier keep replacement).2 gain.smaller
  equivalent := expanded_equivalent carrier keep replacement gain.agreement

theorem ProperGain.checked {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool}
    {replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length}
    (gain : ProperGain carrier keep replacement) :
    (pulled carrier keep).gateCount < carrier.implementation.gateCount ∧
      StrictEquivalentGain carrier.implementation
        (expanded carrier keep replacement).implementation ∧
      (∀ valuation field,
        (expanded carrier keep replacement).fieldValue valuation field =
          carrier.fieldValue valuation field) ∧
      (expanded carrier keep replacement).implementation.gateCount =
        replacementGates + exteriorCharge carrier keep :=
  ⟨gain.proper, gain.strictGain,
    expanded_field carrier keep replacement gain.agreement,
    expanded_charge carrier keep replacement⟩

end PNP.DirectWire.WireFrontierLift

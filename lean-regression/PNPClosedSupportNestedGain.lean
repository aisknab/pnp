import PNP

/- General theorem contracts and small adversarial examples. These fixtures
   test the unbounded construction; they are not separate milestone credit. -/

namespace PNP.DirectWire.ClosedSupportNestedGainRegression

open ClosedSupportNestedGain

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large) :
    (snapshot target keep large).fullMinimum + (snapshot target keep small).supportSize ≤
      (snapshot target keep small).fullMinimum + (snapshot target keep large).supportSize :=
  full_minimum_cost_balance target keep small large included

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large) :
    (snapshot target keep large).quotientMinimum + (snapshot target keep small).supportSize ≤
      (snapshot target keep small).quotientMinimum + (snapshot target keep large).supportSize :=
  quotient_minimum_cost_balance target keep small large included

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large) :
    (snapshot target keep small).fullSlack ≤ (snapshot target keep large).fullSlack :=
  full_slack_le target keep small large included

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large) :
    (snapshot target keep small).supportSize - (snapshot target keep small).quotientMinimum ≤
      (snapshot target keep large).supportSize - (snapshot target keep large).quotientMinimum :=
  quotient_slack_le target keep small large included

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (within : ∀ record, record ∈ small → record ∈ large)
    (positive : 0 < (snapshot target keep small).fullSlack ∨
      0 < (snapshot target keep small).projectionDefect) :
    0 < (snapshot target keep large).fullSlack ∨
      0 < (snapshot target keep large).projectionDefect :=
  seed_positive target keep small large within positive

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (seed extra : Seed target)
    (positive : 0 < (snapshot target keep seed).fullSlack ∨
      0 < (snapshot target keep seed).projectionDefect) :
    0 < (snapshot target keep (seed ++ extra)).fullSlack ∨
      0 < (snapshot target keep (seed ++ extra)).projectionDefect :=
  append_positive target keep seed extra positive

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large)
    (full : TerminalFullCarrierRealization
      (WireProfileAmbient.model target keep).ambientProfileSystem
      (ClosedSupportObservation.implementation target keep small)) :
    TerminalFullCarrierRealization (WireProfileAmbient.model target keep).ambientProfileSystem
      (ClosedSupportObservation.implementation target keep large) :=
  extendFullComparison target keep small large included full

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large)
    (comparison : TerminalQuotientComparison
      (WireProfileAmbient.model target keep).ambientProfileSystem
      (WireProfileAmbient.model target keep).projection
      (ClosedSupportObservation.implementation target keep small)) :
    TerminalQuotientComparison (WireProfileAmbient.model target keep).ambientProfileSystem
      (WireProfileAmbient.model target keep).projection
      (ClosedSupportObservation.implementation target keep large) :=
  extendQuotientComparison target keep small large included comparison

private def empty : WireCarrier 0 0 0 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 0 0)
      ⟨Fin.elim0⟩).toImplementation
    source := Fin.elim0 }

private def freeFields : WireCarrier 1 2 2 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 1 0)
      ⟨Fin.cases (.input 0) (fun _ => .constant true)⟩).toImplementation
    source := Fin.cases (.constant false) (fun _ => .input 0) }

private def hiddenNot : WireCarrier 1 0 1 :=
  { implementation := (Candidate.ofDirectWireWord
      (.snoc (.empty : Program 1 0) ⟨.input 0, .input 0⟩) ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def crossing : WireCarrier 1 1 0 :=
  { implementation := (Candidate.ofDirectWireWord
      (.snoc (.snoc (.empty : Program 1 0) ⟨.constant false, .constant false⟩)
        ⟨.gate ⟨0, by decide⟩, .input 0⟩) ⟨fun _ => .gate ⟨1, by decide⟩⟩).toImplementation
    source := Fin.elim0 }

private def exteriorField : WireCarrier 1 1 1 :=
  { implementation := (Candidate.ofDirectWireWord
      (.snoc (.snoc (.empty : Program 1 0) ⟨.constant true, .constant true⟩)
        ⟨.input 0, .input 0⟩) ⟨fun _ => .gate ⟨1, by decide⟩⟩).toImplementation
    source := fun _ => .gate ⟨1, by decide⟩ }

private def hiddenSeed : Seed hiddenNot := [.gate ⟨0, by decide⟩]
private def crossingSeed : Seed crossing := [.gate ⟨0, by decide⟩]
private def crossingExtra : Seed crossing := [.gate ⟨1, by decide⟩]
private def exteriorSeed : Seed exteriorField := [.gate ⟨0, by decide⟩]
private def exteriorExtra : Seed exteriorField := [.gate ⟨1, by decide⟩]

/- An unused ambient input changes a latent gate without changing the padded
   ordinary output. Fixing that input would change a false field observation. -/
private def ambientPrefix : Implementation 2 1 :=
  (Candidate.ofDirectWireWord
    (.snoc (.snoc (.empty : Program 2 0) ⟨.input 1, .input 1⟩)
      ⟨.input 0, .gate ⟨0, by decide⟩⟩) ⟨fun _ => .constant false⟩).toImplementation

private def specializedPrefix : Implementation 2 1 :=
  (Candidate.ofDirectWireWord
    ((.empty : Program 2 0).appendSubstituted
      (Fin.cases (.input 0) (fun _ => .constant false))
      ambientPrefix.candidate.program)
    ⟨fun _ => .constant false⟩).toImplementation

theorem hidden_field_nonconstant :
    hiddenNot.fieldValue (fun _ => false) 0 = true ∧
      hiddenNot.fieldValue (fun _ => true) 0 = false := by decide +kernel

theorem ambient_field_unavailable :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget hiddenNot)
      ambientPrefix 0 = false := by decide +kernel

theorem fixing_unused_input_changes_field :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget hiddenNot)
      specializedPrefix 0 = true := by decide +kernel

theorem ambient_observation_is_not_specialization :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget hiddenNot) ambientPrefix 0 ≠
      WireProfileAvailability.available (WireProfileAmbient.ambientTarget hiddenNot) specializedPrefix 0 := by
  rw [ambient_field_unavailable, fixing_unused_input_changes_field]
  exact Bool.noConfusion

theorem reverse_inclusion_rejected :
    ¬ Included hiddenNot (fun _ => false) hiddenSeed [] := by
  intro included
  let gate : Fin hiddenNot.implementation.gateCount := ⟨0, by decide⟩
  have selected : terminalGateSelected
      (ClosedSupportObservation.records hiddenNot (fun _ => false) hiddenSeed) gate = true := by decide +kernel
  have absent : terminalGateSelected
      (ClosedSupportObservation.records hiddenNot (fun _ => false) []) gate = false := by decide +kernel
  have impossible := included gate selected
  rw [absent] at impossible
  cases impossible

theorem crossing_wire_has_real_effect :
    crossing.implementation.candidate.semantics (fun _ => false) 0 = true ∧
      crossing.implementation.candidate.semantics (fun _ => true) 0 = false := by decide +kernel

private def boundsHold {inputs outputs fields : Nat}
    (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (seed extra : Seed target) : Bool :=
  let small := snapshot target keep seed
  let large := snapshot target keep (seed ++ extra)
  decide (small.supportSize + (difference target keep seed (seed ++ extra)).gateCount =
      large.supportSize) &&
    decide (large.fullMinimum + small.supportSize ≤ small.fullMinimum + large.supportSize) &&
    decide (large.quotientMinimum + small.supportSize ≤ small.quotientMinimum + large.supportSize) &&
    decide (small.fullSlack ≤ large.fullSlack) &&
    decide (small.supportSize - small.quotientMinimum ≤
      large.supportSize - large.quotientMinimum)

private def comparisonsHold {inputs outputs fields : Nat}
    (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (seed extra : Seed target) : Bool :=
  let large := seed ++ extra
  let included := included_of_seed_subset target keep seed large
    (fun _ member => List.mem_append_left extra member)
  let model := WireProfileAmbient.model target keep
  let current := ClosedSupportObservation.implementation target keep seed
  let larger := ClosedSupportObservation.implementation target keep large
  let full := terminalFullProfileMinimumRealization model.ambientProfileSystem current
  let quotient := terminalQuotientProfileMinimumComparison
    model.ambientProfileSystem model.projection current
  terminalFullProfileMatchBool model.ambientProfileSystem larger
      (extendFullComparison target keep seed large included full).realization.implementation &&
    terminalQuotientProfileMatchBool model.ambientProfileSystem model.projection larger
      (extendQuotientComparison target keep seed large included quotient).realization.implementation

private def checks : List (String × Bool) :=
  [ ("empty dimensions and no additional gates",
      boundsHold empty Fin.elim0 [] [] && comparisonsHold empty Fin.elim0 [] [] &&
        decide ((snapshot empty Fin.elim0 []).fullSlack = 0))
  , ("free fields stay available with no physical gates",
      boundsHold freeFields (fun _ => true) [] [] &&
        comparisonsHold freeFields (fun _ => true) [] [])
  , ("equal supports preserve the exact full and selected-field observations",
      boundsHold hiddenNot (fun _ => true) hiddenSeed [] &&
        comparisonsHold hiddenNot (fun _ => true) hiddenSeed [] &&
        decide ((difference hiddenNot (fun _ => true) hiddenSeed hiddenSeed).gateCount = 0))
  , ("projection-only positivity is not mislabeled full slack",
      let snap := snapshot hiddenNot (fun _ => false) hiddenSeed
      decide (snap.fullMinimum = 1) && decide (snap.quotientMinimum = 0) &&
        decide (snap.fullSlack = 0) && decide (snap.projectionDefect = 1) &&
        boundsHold hiddenNot (fun _ => false) hiddenSeed [] &&
        comparisonsHold hiddenNot (fun _ => false) hiddenSeed [])
  , ("proper nesting reconnects a real crossing wire and retains strict improvement",
      boundsHold crossing Fin.elim0 crossingSeed crossingExtra &&
        comparisonsHold crossing Fin.elim0 crossingSeed crossingExtra &&
        decide ((snapshot crossing Fin.elim0 crossingSeed).supportSize = 1) &&
        decide ((snapshot crossing Fin.elim0 (crossingSeed ++ crossingExtra)).supportSize = 2) &&
        decide ((snapshot crossing Fin.elim0 crossingSeed).fullSlack = 1) &&
        decide ((snapshot crossing Fin.elim0 (crossingSeed ++ crossingExtra)).fullSlack = 1))
  , ("a previously external field is derived in the larger full comparison",
      boundsHold exteriorField (fun _ => true) exteriorSeed exteriorExtra &&
        comparisonsHold exteriorField (fun _ => true) exteriorSeed exteriorExtra &&
        !(WireProfileAvailability.available (WireProfileAmbient.ambientTarget exteriorField)
          (ClosedSupportObservation.implementation exteriorField (fun _ => true) exteriorSeed) 0) &&
        WireProfileAvailability.available (WireProfileAmbient.ambientTarget exteriorField)
          (ClosedSupportObservation.implementation exteriorField (fun _ => true)
            (exteriorSeed ++ exteriorExtra)) 0)
  , ("dropping the keep mask does not waive ordinary-output preservation",
      boundsHold exteriorField (fun _ => false) exteriorSeed exteriorExtra &&
        comparisonsHold exteriorField (fun _ => false) exteriorSeed exteriorExtra)
  , ("empty-to-whole construction obtains a hidden field from the difference",
      boundsHold hiddenNot (fun _ => false) [] hiddenSeed &&
        comparisonsHold hiddenNot (fun _ => false) [] hiddenSeed &&
        decide ((snapshot hiddenNot (fun _ => false) []).fullMinimum = 0) &&
        decide ((snapshot hiddenNot (fun _ => false) hiddenSeed).fullMinimum = 1))
  , ("a metadata seed derives the physical field support",
      let seed : Seed hiddenNot := [.profile 0]
      boundsHold hiddenNot (fun _ => true) seed hiddenSeed &&
        comparisonsHold hiddenNot (fun _ => true) seed hiddenSeed &&
        decide ((snapshot hiddenNot (fun _ => true) seed).supportSize = 1))
  , ("duplicate seed records do not duplicate physical difference gates",
      let seed := crossingSeed ++ crossingSeed
      let extra := crossingExtra ++ crossingSeed
      boundsHold crossing Fin.elim0 seed extra &&
        comparisonsHold crossing Fin.elim0 seed extra &&
        decide ((difference crossing Fin.elim0 seed (seed ++ extra)).gateCount = 1))
  , ("unchanged ambient inputs preserve false availability",
      !(WireProfileAvailability.available (WireProfileAmbient.ambientTarget hiddenNot)
        (extendedImplementation hiddenNot (fun _ => false) [] [] ambientPrefix) 0) &&
        WireProfileAvailability.available (WireProfileAmbient.ambientTarget hiddenNot)
          specializedPrefix 0) ]

def run : IO Unit := do
  for (name, passed) in checks do
    if !passed then throw (IO.userError ("closed-support-nested-gain: " ++ name))
    IO.println ("passed: " ++ name)

end PNP.DirectWire.ClosedSupportNestedGainRegression

#print axioms PNP.DirectWire.ClosedSupportNestedGainRegression.hidden_field_nonconstant
#print axioms PNP.DirectWire.ClosedSupportNestedGainRegression.ambient_field_unavailable
#print axioms PNP.DirectWire.ClosedSupportNestedGainRegression.fixing_unused_input_changes_field
#print axioms PNP.DirectWire.ClosedSupportNestedGainRegression.ambient_observation_is_not_specialization
#print axioms PNP.DirectWire.ClosedSupportNestedGainRegression.reverse_inclusion_rejected
#print axioms PNP.DirectWire.ClosedSupportNestedGainRegression.crossing_wire_has_real_effect

def main : IO Unit := do
  PNP.DirectWire.ClosedSupportNestedGainRegression.run
  IO.println "closed-support-nested-gain-regressions-complete: 8 general type contracts; 6 kernel guards; 11 runtime checks"

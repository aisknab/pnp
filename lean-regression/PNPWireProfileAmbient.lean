import PNP

namespace PNP.DirectWire.WireProfileAmbientRegression

open WireProfileAvailability WireProfileAmbient

/- Independent contracts keep the arbitrary dimensions and uniform valuations. -/
example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs) (field : Fin fields) :
    available target offered field = true ↔
      ∃ source : Source inputs offered.gateCount, ∀ valuation,
        source.eval valuation (offered.candidate.program.eval valuation) =
          target.fieldValue valuation field :=
  available_iff_exists target offered field

example {inputs outputs : Nat} (offered : Implementation inputs outputs) (extra : Nat) :
    (padImplementation offered extra).gateCount = offered.gateCount :=
  pad_gateCount offered extra

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (extra : Nat) (valuation : Valuation (inputs + extra)) (field : Fin fields) :
    (padCarrier target extra).fieldValue valuation field =
      target.fieldValue (fun index => valuation (Fin.castAdd extra index)) field :=
  pad_fieldValue target extra valuation field

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs) (extra : Nat) (field : Fin fields) :
    available (padCarrier target extra) (padImplementation offered extra) field =
      available target offered field :=
  available_pad target offered extra field

example {inputs outputs newOutputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs)
    (targetWord : DirectWireWord inputs target.implementation.gateCount newOutputs)
    (offeredWord : DirectWireWord inputs offered.gateCount newOutputs) (field : Fin fields) :
    available (rewordCarrier target targetWord)
      (rewordImplementation offered offeredWord) field =
        available target offered field :=
  available_reword target offered targetWord offeredWord field

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (offered : Implementation inputs outputs) (field : Fin fields) :
    (model target keep).observe (ambientImplementation target offered) field =
      available target offered field :=
  model_observe_coherent target keep offered field

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (kind : TerminalSaturationRuleKind)
    (field : Fin fields) (gate : Fin target.implementation.gateCount) :
    (terminalCandidateSaturationSystem target.implementation.candidate
      (model target keep)).requires kind (.profile field) (.gate gate) =
      (decide (kind = terminalSaturationRuleOfProfileRole .carrier) &&
        terminalGateInfluencesProfile target.implementation.candidate
          (model target keep) gate field) :=
  terminalCandidateProfileRequires_eq_influence target.implementation.candidate
    (model target keep) kind field gate

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (field : Fin fields) (gate : Fin target.implementation.gateCount)
    (context : List (Fin target.implementation.gateCount))
    (profileMember : TerminalPrimitiveRecord.profile field ∈
      terminalSaturateRecords
        (terminalCandidateSaturationSystem target.implementation.candidate (model target keep)) seed)
    (gateAbsent : TerminalPrimitiveRecord.gate gate ∉
      terminalSaturateRecords
        (terminalCandidateSaturationSystem target.implementation.candidate (model target keep)) seed)
    (canonicalContext : context ∈ terminalListSubsets
      ((allFin target.implementation.gateCount).filter (fun other => decide (other ≠ gate)))) :
    terminalCandidateProfileObservation target.implementation.candidate
      (model target keep) (gate :: context) field =
        terminalCandidateProfileObservation target.implementation.candidate
          (model target keep) context field :=
  terminalCandidateSaturate_profile_noninterference target.implementation.candidate
    (model target keep) seed field gate context profileMember gateAbsent canonicalContext

private def bit : Fin 1 := ⟨0, by decide⟩

private def negProgram : Program 1 1 :=
  .snoc .empty ⟨.input bit, .input bit⟩

private def target : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord negProgram ⟨fun _ => .input bit⟩).toImplementation
    source := fun _ => .gate bit }

private def emptyOffered : Implementation 1 1 :=
  (Candidate.ofDirectWireWord (.empty : Program 1 0)
    ⟨fun _ => .input bit⟩).toImplementation

theorem base_missing : available target emptyOffered bit = false := by decide +kernel

theorem extra_inputs_cannot_fake_field (extra : Nat) :
    available (padCarrier target extra) (padImplementation emptyOffered extra) bit = false :=
  (available_pad target emptyOffered extra bit).trans base_missing

theorem extra_inputs_preserve_field (extra : Nat) :
    available (padCarrier target extra)
      (padImplementation target.implementation extra) bit = true :=
  (available_pad target target.implementation extra bit).trans (current_available target bit)

theorem ambient_missing :
    (model target (fun _ => true)).observe (ambientImplementation target emptyOffered) bit = false :=
  (model_observe_coherent target (fun _ => true) emptyOffered bit).trans base_missing

theorem ambient_present :
    (model target (fun _ => true)).observe
      (ambientImplementation target target.implementation) bit = true :=
  (model_observe_coherent target (fun _ => true) target.implementation bit).trans
    (current_available target bit)

private def extraConstantProgram : Program 1 2 :=
  .snoc negProgram ⟨.constant true, .constant true⟩

private def withIrrelevantGate : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord extraConstantProgram ⟨fun _ => .input bit⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def duplicated : WireCarrier 1 1 2 :=
  { implementation := target.implementation
    source := fun _ => .gate bit }

private def zeroConstant : WireCarrier 0 0 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 0 0) ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .constant false }

private def differentOutputs : Implementation 1 1 :=
  rewordImplementation target.implementation ⟨fun _ => .constant true⟩

theorem output_wiring_still_matters :
    target.implementation.candidate.semantics (fun _ => false) bit ≠
      differentOutputs.candidate.semantics (fun _ => false) bit := by decide +kernel

private def checks : List (String × Bool) :=
  [ ("self field", available target target.implementation bit)
  , ("missing field", !(available target emptyOffered bit))
  , ("padded valid field", available (padCarrier target 2)
      (padImplementation target.implementation 2) bit)
  , ("padded missing field", !(available (padCarrier target 3)
      (padImplementation emptyOffered 3) bit))
  , ("ambient valid field", (model target (fun _ => true)).observe
      (ambientImplementation target target.implementation) bit)
  , ("ambient missing field", !((model target (fun _ => true)).observe
      (ambientImplementation target emptyOffered) bit))
  , ("needed gate is influential", terminalGateInfluencesProfile
      target.implementation.candidate (model target (fun _ => true)) bit bit)
  , ("irrelevant gate is not influential", !(terminalGateInfluencesProfile
      withIrrelevantGate.implementation.candidate (model withIrrelevantGate (fun _ => true))
      ⟨1, by decide⟩ bit))
  , ("duplicate fields share existing wire",
      available duplicated target.implementation ⟨0, by decide⟩ &&
        available duplicated target.implementation ⟨1, by decide⟩)
  , ("no-input constant survives padding", available (padCarrier zeroConstant 4)
      (padImplementation zeroConstant.implementation 4) bit)
  , ("output rewiring does not invent a field binding",
      available (rewordCarrier target ⟨fun _ => .constant false⟩) differentOutputs bit)
  ]

def run : IO Unit := do
  for (name, passed) in checks do
    if passed then
      IO.println ("ambient-check-passed: " ++ name)
    else
      throw (IO.userError ("ambient-check-failed: " ++ name))
  IO.println "ambient-regressions-complete: 11 runtime checks; 8 general type contracts; 6 kernel guards"

end PNP.DirectWire.WireProfileAmbientRegression

#print axioms PNP.DirectWire.WireProfileAmbientRegression.base_missing
#print axioms PNP.DirectWire.WireProfileAmbientRegression.extra_inputs_cannot_fake_field
#print axioms PNP.DirectWire.WireProfileAmbientRegression.extra_inputs_preserve_field
#print axioms PNP.DirectWire.WireProfileAmbientRegression.ambient_missing
#print axioms PNP.DirectWire.WireProfileAmbientRegression.ambient_present
#print axioms PNP.DirectWire.WireProfileAmbientRegression.output_wiring_still_matters

def main : IO Unit := PNP.DirectWire.WireProfileAmbientRegression.run

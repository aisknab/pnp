import PNP.PCCMinOutputConePruning

open PNP PNP.DirectWire

example {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs)
    (producer : Fin gates)
    (isOutput : terminalGateIsGlobalOutput candidate.directWireWord producer = true) :
    TerminalPrimitiveRecord.gate producer ∈ outputConeRecords candidate :=
  outputConeRecords_output candidate producer isOutput

example {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs)
    (consumer producer : Fin gates)
    (selected : TerminalPrimitiveRecord.gate consumer ∈ outputConeRecords candidate)
    (uses : candidate.program.terminalGateUsesWire consumer (.gate producer) = true) :
    TerminalPrimitiveRecord.gate producer ∈ outputConeRecords candidate :=
  outputConeRecords_closed candidate consumer producer selected uses

example {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs)
    (support : Fin gates → Prop)
    (containsOutputs : ∀ producer,
      terminalGateIsGlobalOutput candidate.directWireWord producer = true → support producer)
    (closed : ∀ consumer producer, support consumer →
      candidate.program.terminalGateUsesWire consumer (.gate producer) = true → support producer)
    (producer : Fin gates)
    (selected : TerminalPrimitiveRecord.gate producer ∈ outputConeRecords candidate) :
    support producer :=
  outputConeRecords_least candidate support containsOutputs closed producer selected

example {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs)
    (producer : Fin gates) :
    TerminalSupportWire.gate producer ∉ terminalBoundaryPorts candidate.program
      (outputConeRecords candidate) :=
  outputConeRecords_noExternalGate candidate producer

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    Equivalent (outputConeImplementation current).candidate.program
      (outputConeImplementation current).candidate.directWireWord
      current.candidate.program current.candidate.directWireWord :=
  outputConeImplementation_equivalent current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    (outputConeImplementation current).gateCount ≤ current.gateCount :=
  outputConeImplementation_gateCount_le current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    (outputConeImplementation current).gateCount + outputConeDeletedGateCount current =
      current.gateCount :=
  outputConeImplementation_exact_accounting current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    referenceMinimum (outputConeImplementation current) = referenceMinimum current :=
  outputConeImplementation_referenceMinimum current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    residualSlack current = residualSlack (outputConeImplementation current) +
      outputConeDeletedGateCount current :=
  outputConeImplementation_residualSlack current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    StrictEquivalentGain current (outputConeImplementation current) ↔
      0 < outputConeDeletedGateCount current :=
  outputConeImplementation_strictGain_iff current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    match outputConeNormalizer.normalize current with
    | .gain next _ => next = outputConeImplementation current ∧
        0 < outputConeDeletedGateCount current
    | .normal normalized => normalized.result = outputConeImplementation current ∧
        outputConeDeletedGateCount current = 0 ∧
        normalized.result.gateCount = current.gateCount :=
  outputConeNormalizer_checked current

/-- Pruning is a concrete stage, not a construction of the required total oracle. -/
example (oracle : PCCMinTotalOracle) {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    let execution := runPCCMinNormalizeOracleLoop outputConeNormalizer oracle current
    Equivalent execution.result.candidate.program execution.result.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      IsSemanticallyMinimum execution.result ∧
      execution.result.gateCount = referenceMinimum current ∧
      residualSlack execution.result = 0 ∧
      execution.gainIterations ≤ residualSlack current :=
  pccmin_normalize_oracle_loop_checked_complete outputConeNormalizer oracle current

private def mixedProgram : Program 2 5 :=
  ((((Program.empty.snoc ⟨.input 0, .input 1⟩).snoc
    ⟨.constant true, .constant false⟩).snoc
    ⟨.gate 0, .gate 0⟩).snoc
    ⟨.gate 1, .gate 1⟩).snoc
    ⟨.gate 0, .gate 2⟩

private def mixedOutputs : Implementation 2 5 :=
  (Candidate.ofDirectWireWord mixedProgram ⟨fun output =>
    match output.val with
    | 0 => .gate 4
    | 1 => .gate 2
    | 2 => .gate 4
    | 3 => .input 1
    | _ => .constant true⟩).toImplementation

private def noOutputs : Implementation 2 0 :=
  (Candidate.ofDirectWireWord mixedProgram ⟨Fin.elim0⟩).toImplementation

private def empty : Implementation 0 0 :=
  (Candidate.ofDirectWireWord Program.empty ⟨Fin.elim0⟩).toImplementation

private def primaryOutputs : Implementation 2 4 :=
  (Candidate.ofDirectWireWord Program.empty ⟨fun output =>
    match output.val with
    | 0 => .input 1
    | 1 => .constant false
    | 2 => .input 0
    | _ => .constant true⟩).toImplementation

private def constantProgram : Program 0 3 :=
  ((Program.empty.snoc ⟨.constant true, .constant true⟩).snoc
    ⟨.gate 0, .gate 0⟩).snoc ⟨.constant true, .constant false⟩

private def constantOutputs : Implementation 0 2 :=
  (Candidate.ofDirectWireWord constantProgram ⟨fun output =>
    if output.val = 0 then .gate 1 else .constant false⟩).toImplementation

private def liveButRedundant : Implementation 1 1 :=
  (Candidate.ofDirectWireWord
    (Program.empty.snoc ⟨.input 0, .constant false⟩)
    ⟨fun _ => .gate 0⟩).toImplementation

private def constantAlternative : Implementation 1 1 :=
  (Candidate.ofDirectWireWord Program.empty
    ⟨fun _ => .constant true⟩).toImplementation

/-- No unused physical gate does not imply a semantic minimum. -/
example : StrictEquivalentGain liveButRedundant constantAlternative :=
  strictEquivalentGainBool_sound (by decide)

example : 0 < residualSlack liveButRedundant :=
  Nat.lt_of_le_of_lt (Nat.zero_le (residualSlack constantAlternative))
    (strictEquivalentGainBool_sound (by decide :
      strictEquivalentGainBool liveButRedundant constantAlternative = true)).strictResidualDescent

private def countObserver : TerminalProfileSystem 2 5 1 where
  role := fun _ => .charge
  observe := fun implementation _ => decide (implementation.gateCount = 5)

/- These are guarded executable fixtures, not replacements for universal
kernel-checked theorem authority. No exhaustive reference-minimum search runs. -/
#eval do
  let pruned := outputConeImplementation mixedOutputs
  let selected := (terminalSelectedGates
    (outputConeRecords mixedOutputs.candidate)).map Fin.val
  if selected != [0, 2, 4] || pruned.gateCount != 3 ||
      outputConeDeletedGateCount mixedOutputs != 2 then
    throw (IO.userError "derived cone, selected order or deletion count changed")
  if !equivalentBool pruned.candidate mixedOutputs.candidate then
    throw (IO.userError "mixed ordered output semantics changed")
  if !strictEquivalentGainBool mixedOutputs pruned then
    throw (IO.userError "positive computed deletion did not produce physical gain")
  if countObserver.observe mixedOutputs 0 == countObserver.observe pruned 0 then
    throw (IO.userError "physical equivalence was confused with full-profile equality")
  match outputConeNormalizer.normalize mixedOutputs with
  | .gain next _ =>
      if next.gateCount != 3 then throw (IO.userError "normalizer gain result changed")
  | .normal _ => throw (IO.userError "positive deletion was not surfaced as gain")
  if (outputConeImplementation noOutputs).gateCount != 0 ||
      outputConeDeletedGateCount noOutputs != 5 then
    throw (IO.userError "empty output cone retained unused gates")
  if (outputConeImplementation empty).gateCount != 0 then
    throw (IO.userError "empty implementation changed")
  if !equivalentBool (outputConeImplementation primaryOutputs).candidate primaryOutputs.candidate then
    throw (IO.userError "primary input or constant output changed")
  if (outputConeImplementation constantOutputs).gateCount != 2 ||
      !equivalentBool (outputConeImplementation constantOutputs).candidate constantOutputs.candidate then
    throw (IO.userError "zero-input constant circuit extraction changed")
  if outputConeDeletedGateCount liveButRedundant != 0 ||
      !strictEquivalentGainBool liveButRedundant constantAlternative then
    throw (IO.userError "no-deletion versus semantic-minimum firewall changed")
  match outputConeNormalizer.normalize liveButRedundant with
  | .gain _ _ => throw (IO.userError "no-deletion branch reported a pruning gain")
  | .normal normalized =>
      if normalized.result.gateCount != 1 then
        throw (IO.userError "no-deletion normalizer result changed")
  IO.println "output-cone-pruning-regression: universal contracts and guarded boundary fixtures passed"

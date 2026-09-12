import PNP.PCCMinPhysicalNormalizationClosure

open PNP PNP.DirectWire

example {inputs outputs : Nat} (pass : PhysicalNormalizationPass)
    (current : Implementation inputs outputs) :
    Equivalent (physicalNormalizationPassResult pass current).candidate.program
      (physicalNormalizationPassResult pass current).candidate.directWireWord
      current.candidate.program current.candidate.directWireWord :=
  physicalNormalizationPass_equivalent pass current

example {inputs outputs : Nat} (pass : PhysicalNormalizationPass)
    (current : Implementation inputs outputs) :
    (physicalNormalizationPassResult pass current).gateCount +
      physicalNormalizationPassSavings pass current = current.gateCount :=
  physicalNormalizationPass_exact_accounting pass current

example {inputs outputs : Nat} {current : Implementation inputs outputs}
    (gain : PhysicalNormalizationGain current) :
    StrictEquivalentGain current gain.result ∧
      gain.result.gateCount + gain.savedGates = current.gateCount ∧
      0 < gain.savedGates ∧
      ∀ earlier, earlier.priority < gain.pass.priority →
        physicalNormalizationPassSavings earlier current = 0 :=
  PhysicalNormalizationGain.checked gain

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    match nextPhysicalNormalizationStep current with
    | .gain selected =>
        StrictEquivalentGain current selected.result ∧
          selected.result.gateCount + selected.savedGates = current.gateCount ∧
          0 < selected.savedGates ∧
          ∀ earlier, earlier.priority < selected.pass.priority →
            physicalNormalizationPassSavings earlier current = 0
    | .quiescent _ => PhysicalNormalizationQuiescent current :=
  nextPhysicalNormalizationStep_checked current

example {inputs outputs : Nat} {current final : Implementation inputs outputs}
    (trace : PhysicalNormalizationTrace current final) :
    Equivalent final.candidate.program final.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      PhysicalNormalizationQuiescent final ∧
      final.gateCount + trace.savedGates = current.gateCount ∧
      trace.gainIterations ≤ trace.savedGates :=
  PhysicalNormalizationTrace.checked trace

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    let execution := runPhysicalNormalization current
    Equivalent execution.result.candidate.program execution.result.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      PhysicalNormalizationQuiescent execution.result ∧
      execution.result.gateCount + execution.trace.savedGates = current.gateCount ∧
      execution.trace.gainIterations ≤ execution.trace.savedGates :=
  runPhysicalNormalization_checked current

example {inputs outputs : Nat} (current : Implementation inputs outputs)
    (quiet : PhysicalNormalizationQuiescent current) :
    (runPhysicalNormalization current).result = current :=
  runPhysicalNormalization_of_quiescent current quiet

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    (runPhysicalNormalization (runPhysicalNormalization current).result).result =
      (runPhysicalNormalization current).result :=
  runPhysicalNormalization_idempotent current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    referenceMinimum (runPhysicalNormalization current).result = referenceMinimum current :=
  runPhysicalNormalization_referenceMinimum current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    residualSlack current = residualSlack (runPhysicalNormalization current).result +
      (runPhysicalNormalization current).trace.savedGates :=
  runPhysicalNormalization_residualSlack current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    (runPhysicalNormalization current).trace.gainIterations ≤ residualSlack current :=
  runPhysicalNormalization_gainIterations_le_residualSlack current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    match physicalClosureNormalizer.normalize current with
    | .gain next _ =>
        next = (runPhysicalNormalization current).result ∧
          PhysicalNormalizationQuiescent next ∧
          0 < (runPhysicalNormalization current).trace.savedGates
    | .normal normalized =>
        normalized.result = (runPhysicalNormalization current).result ∧
          PhysicalNormalizationQuiescent normalized.result ∧
          (runPhysicalNormalization current).trace.savedGates = 0 ∧
          normalized.result.gateCount = current.gateCount :=
  physicalClosureNormalizer_checked current

private def interactingProgram : Program 2 5 :=
  ((((Program.empty.snoc ⟨.constant false, .input 0⟩).snoc
    ⟨.input 0, .input 1⟩).snoc ⟨.input 1, .input 0⟩).snoc
    ⟨.gate 1, .gate 2⟩).snoc ⟨.input 0, .input 0⟩

private def interacting : Implementation 2 7 :=
  (Candidate.ofDirectWireWord interactingProgram ⟨fun output =>
    match output.val with
    | 0 => .gate 3
    | 1 => .gate 1
    | 2 => .gate 2
    | 3 => .gate 0
    | 4 => .input 0
    | 5 => .constant false
    | _ => .gate 3⟩).toImplementation

private def sharingAndPruning : Implementation 2 1 :=
  (Candidate.ofDirectWireWord
    ((Program.empty.snoc ⟨.input 0, .input 1⟩).snoc ⟨.input 1, .input 0⟩)
    ⟨fun _ => .gate 0⟩).toImplementation

private def pruningOnly : Implementation 2 1 :=
  (Candidate.ofDirectWireWord
    ((Program.empty.snoc ⟨.input 0, .input 0⟩).snoc ⟨.input 1, .input 1⟩)
    ⟨fun _ => .gate 0⟩).toImplementation

private def constantsOnly : Implementation 1 1 :=
  (Candidate.ofDirectWireWord
    (Program.empty.snoc ⟨.input 0, .constant false⟩)
    ⟨fun _ => .gate 0⟩).toImplementation

private def noGates : Implementation 0 0 :=
  (Candidate.ofDirectWireWord Program.empty ⟨Fin.elim0⟩).toImplementation

private def correlated : Implementation 1 1 :=
  (Candidate.ofDirectWireWord
    ((Program.empty.snoc ⟨.input 0, .input 0⟩).snoc ⟨.input 0, .gate 0⟩)
    ⟨fun _ => .gate 1⟩).toImplementation

private def constantAlternative : Implementation 1 1 :=
  (Candidate.ofDirectWireWord Program.empty ⟨fun _ => .constant true⟩).toImplementation

/-- Quiescence for the physical family must not be claimed as exactness. -/
example : StrictEquivalentGain correlated constantAlternative :=
  strictEquivalentGainBool_sound (by decide)

example : 0 < residualSlack correlated :=
  Nat.lt_of_le_of_lt (Nat.zero_le (residualSlack constantAlternative))
    (strictEquivalentGainBool_sound (by decide :
      strictEquivalentGainBool correlated constantAlternative = true)).strictResidualDescent

private def selectedPasses {inputs outputs : Nat}
    {current final : Implementation inputs outputs} :
    PhysicalNormalizationTrace current final → List PhysicalNormalizationPass
  | .done _ _ => []
  | .step gain tail => gain.pass :: selectedPasses tail

private def assertQuiet {inputs outputs : Nat}
    (current : Implementation inputs outputs) : IO Unit := do
  for pass in [PhysicalNormalizationPass.constants, .sharing, .pruning] do
    if physicalNormalizationPassSavings pass current != 0 then
      throw (IO.userError "final implementation is not quiet for all three passes")

#eval (show IO Unit from do
  let execution := runPhysicalNormalization interacting
  if selectedPasses execution.trace != [.constants, .sharing, .pruning] then
    throw (IO.userError "interacting passes or deterministic priority changed")
  if execution.result.gateCount != 2 || execution.trace.savedGates != 3 ||
      execution.trace.gainIterations != 3 then
    throw (IO.userError "actual trace savings or iteration accounting changed")
  assertQuiet execution.result
  let repeated := runPhysicalNormalization execution.result
  if repeated.result.gateCount != 2 || repeated.trace.gainIterations != 0 then
    throw (IO.userError "completed closure was not operationally idempotent")
  for left in [false, true] do
    for right in [false, true] do
      let input : Valuation 2 := fun index => if index.val = 0 then left else right
      let a := boolNand left right
      let expected := [!a, a, a, true, left, false, !a]
      let observed := (allFin 7).map
        (fun output => execution.result.candidate.semantics input output)
      if observed != expected then
        throw (IO.userError "ordered complete output semantics changed")
  let sharing := runPhysicalNormalization sharingAndPruning
  if selectedPasses sharing.trace != [.sharing] || sharing.result.gateCount != 1 then
    throw (IO.userError "sharing must precede an available pruning gain")
  let pruning := runPhysicalNormalization pruningOnly
  if selectedPasses pruning.trace != [.pruning] || pruning.result.gateCount != 1 then
    throw (IO.userError "pruning-only route changed")
  let constants := runPhysicalNormalization constantsOnly
  if selectedPasses constants.trace != [.constants] || constants.result.gateCount != 0 then
    throw (IO.userError "constant-only route changed")
  let empty := runPhysicalNormalization noGates
  if empty.result.gateCount != 0 || empty.trace.gainIterations != 0 then
    throw (IO.userError "empty-dimension stopping changed")
  let nonminimum := runPhysicalNormalization correlated
  assertQuiet nonminimum.result
  if nonminimum.result.gateCount != 2 || nonminimum.trace.gainIterations != 0 then
    throw (IO.userError "nonminimum quiescent boundary example changed")
  match physicalClosureNormalizer.normalize interacting with
  | .gain result _ =>
      if result.gateCount != 2 then
        throw (IO.userError "normalizer did not expose the computed strict saving")
  | .normal _ => throw (IO.userError "strict saving was hidden as normal")
  match physicalClosureNormalizer.normalize correlated with
  | .gain _ _ => throw (IO.userError "normalizer invented a physical gain")
  | .normal result => assertQuiet result.result
  IO.println "computed-physical-normalization-closure-fixtures: passed")

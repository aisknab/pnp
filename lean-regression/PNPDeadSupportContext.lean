import PNP.PCCMinDeadSupportContext

open PNP PNP.DirectWire

example {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs)
    (input : Valuation inputs)
    (output : Fin (terminalInterfacePorts candidate (outputConeRecords candidate)).length) :
    (outputConeFrontierCandidate candidate).semantics input output =
      candidate.program.eval input
        ((terminalInterfacePorts candidate (outputConeRecords candidate)).get output) :=
  outputConeFrontierCandidate_semantics candidate input output

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    terminalInterfacePorts current.candidate (deadSupportRecords current) = [] :=
  deadSupport_interface_empty current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    (outputConeImplementation current).gateCount + deadSupportGateCount current =
      current.gateCount :=
  deadSupportGateCount_partition current

example {inputs outputs : Nat} (current : Implementation inputs outputs)
    (input : Valuation inputs) (index : Fin (deadSupportBoundary current).length) :
    (deadSupportEnvironment current).semantics input (Fin.castAdd outputs index) =
      terminalInducedBoundaryValuation current.candidate (deadSupportRecords current)
        input index :=
  deadSupportEnvironment_boundary current input index

example {inputs outputs : Nat} (current : Implementation inputs outputs)
    (input : Valuation inputs) (output : Fin outputs) :
    (deadSupportEnvironment current).semantics input
        (Fin.natAdd (deadSupportBoundary current).length output) =
      current.candidate.semantics input output :=
  deadSupportEnvironment_bypass current input output

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    HEq (deadSupportCandidate current)
      (extractTerminalSupport current.candidate (deadSupportRecords current)).extractedCandidate :=
  deadSupportCandidate_extracted current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    Equivalent (deadSupportEmptyReplacement current).program
      (deadSupportEmptyReplacement current).directWireWord
      (deadSupportCandidate current).program (deadSupportCandidate current).directWireWord :=
  deadSupportEmptyReplacement_equivalent current

example {inputs outputs replacementGates : Nat}
    (current : Implementation inputs outputs)
    (replacement : Candidate (deadSupportBoundary current).length replacementGates 0) :
    Equivalent ((deadSupportContext current).plug replacement).program
      ((deadSupportContext current).plug replacement).directWireWord
      current.candidate.program current.candidate.directWireWord :=
  deadSupportContext_plug_equivalent current replacement

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    ((deadSupportContext current).plug (deadSupportCandidate current)).program.size =
      current.gateCount :=
  deadSupportContext_original_size current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    (deadSupportReplacementImplementation current).gateCount + deadSupportGateCount current =
      current.gateCount :=
  deadSupportReplacement_accounting current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    residualSlack current = residualSlack (deadSupportReplacementImplementation current) +
      deadSupportGateCount current :=
  deadSupportReplacement_residualSlack current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    (deadSupportProperGain current).isSome = true ↔
      0 < deadSupportGateCount current ∧ 0 < (outputConeImplementation current).gateCount :=
  deadSupportProperGain_isSome_iff current

example {inputs outputs : Nat} (current : Implementation inputs outputs)
    (witness : DeadSupportPhysicalGain current)
    (found : deadSupportProperGain current = some witness) :
    0 < deadSupportGateCount current ∧
      deadSupportGateCount current < current.gateCount ∧
      StrictEquivalentGain current (deadSupportReplacementImplementation current) ∧
      residualSlack (deadSupportReplacementImplementation current) < residualSlack current :=
  deadSupportProperGain_sound current witness found

example {inputs outputs : Nat} (current : Implementation inputs outputs)
    (allDead : (outputConeImplementation current).gateCount = 0) :
    deadSupportProperGain current = none :=
  deadSupportProperGain_none_of_all_dead current allDead

example {inputs outputs : Nat} (current : Implementation inputs outputs)
    (noDead : deadSupportGateCount current = 0) :
    deadSupportProperGain current = none :=
  deadSupportProperGain_none_of_no_dead current noDead

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    deadSupportGateCount current = outputConeDeletedGateCount current :=
  deadSupportGateCount_eq_deleted current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    (deadSupportCandidate current).program =
      (extractTerminalSupport current.candidate (deadSupportRecords current)).extractedCandidate.program :=
  deadSupportCandidate_program current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    (deadSupportReplacementImplementation current).gateCount =
      (outputConeImplementation current).gateCount :=
  deadSupportReplacement_gateCount current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    Equivalent (deadSupportReplacementImplementation current).candidate.program
      (deadSupportReplacementImplementation current).candidate.directWireWord
      current.candidate.program current.candidate.directWireWord :=
  deadSupportReplacement_equivalent current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    StrictEquivalentGain current (deadSupportReplacementImplementation current) ↔
      0 < deadSupportGateCount current :=
  deadSupportReplacement_strictGain_iff current

private def interleavedProgram : Program 2 5 :=
  ((((Program.empty.snoc ⟨.input 0, .input 1⟩).snoc
    ⟨.gate 0, .input 0⟩).snoc
    ⟨.gate 0, .input 1⟩).snoc
    ⟨.gate 1, .gate 2⟩).snoc
    ⟨.gate 0, .gate 2⟩

private def mixed : Implementation 2 5 :=
  (Candidate.ofDirectWireWord interleavedProgram ⟨fun output =>
    match output.val with
    | 0 => .gate 4
    | 1 => .gate 2
    | 2 => .gate 4
    | 3 => .input 1
    | _ => .constant true⟩).toImplementation

private def allUnused : Implementation 2 0 :=
  (Candidate.ofDirectWireWord interleavedProgram ⟨Fin.elim0⟩).toImplementation

private def empty : Implementation 0 0 :=
  (Candidate.ofDirectWireWord Program.empty ⟨Fin.elim0⟩).toImplementation

private def primaryOutputs : Implementation 2 3 :=
  (Candidate.ofDirectWireWord Program.empty ⟨fun output =>
    match output.val with
    | 0 => .input 1
    | 1 => .constant false
    | _ => .input 0⟩).toImplementation

private def allLive : Implementation 1 1 :=
  (Candidate.ofDirectWireWord
    (Program.empty.snoc ⟨.input 0, .constant false⟩)
    ⟨fun _ => .gate 0⟩).toImplementation

private def constantAlternative : Implementation 1 1 :=
  (Candidate.ofDirectWireWord Program.empty ⟨fun _ => .constant true⟩).toImplementation

private def constantCircuit : Implementation 0 1 :=
  (Candidate.ofDirectWireWord
    ((Program.empty.snoc ⟨.constant true, .constant true⟩).snoc
      ⟨.gate 0, .constant false⟩)
    ⟨fun _ => .gate 0⟩).toImplementation

private def countObserver : TerminalProfileSystem 2 5 1 where
  role := fun _ => .charge
  observe := fun implementation _ => decide (implementation.gateCount = 5)

/-- Rejecting this proper-deletion route does not prove semantic minimality. -/
example : StrictEquivalentGain allLive constantAlternative :=
  strictEquivalentGainBool_sound (by decide)

/- Bounded guarded runtime fixtures exercise constructions, not proof authority.
They do not run any exhaustive reference-minimum search. -/
#eval (show IO Unit from do
  let replaced := deadSupportReplacementImplementation mixed
  let support := deadSupportCandidate mixed
  let originalFrame := (deadSupportContext mixed).plug support
  let selected := (terminalSelectedGates (deadSupportRecords mixed)).map Fin.val
  let boundary : List Nat := (deadSupportBoundary mixed).map fun (wire : TerminalSupportWire 2 5) =>
    match wire with
    | .input index => index.val
    | .gate index => 2 + index.val
  if selected != [1, 3] || boundary != [0, 2, 4] ||
      !(terminalInterfacePorts mixed.candidate (deadSupportRecords mixed)).isEmpty then
    throw (IO.userError "actual dead support, live frontier input or empty interface changed")
  if support.program.size != 2 || originalFrame.program.size != 5 ||
      replaced.gateCount != 3 then
    throw (IO.userError "physical extraction or exact frame accounting changed")
  if !equivalentBool originalFrame mixed.candidate ||
      !equivalentBool replaced.candidate mixed.candidate then
    throw (IO.userError "frame insertion or replacement changed ordered output semantics")
  if !(deadSupportProperGain mixed).isSome then
    throw (IO.userError "nonempty proper dead support was not accepted")
  if countObserver.observe mixed 0 == countObserver.observe replaced 0 then
    throw (IO.userError "physical deletion was confused with full-profile preservation")
  for bits in ([0, 1, 2, 3] : List Nat) do
    let input : Valuation 2 := fun index => (bits / (2 ^ index.val)) % 2 == 1
    for index in List.finRange (deadSupportBoundary mixed).length do
      if (deadSupportEnvironment mixed).semantics input (Fin.castAdd 5 index) !=
          terminalInducedBoundaryValuation mixed.candidate (deadSupportRecords mixed) input index then
        throw (IO.userError "computed dead-support input differs from its original value")
  if (deadSupportProperGain allUnused).isSome ||
      (deadSupportReplacementImplementation allUnused).gateCount != 0 then
    throw (IO.userError "all-unused circuit was accepted as a proper subset")
  if (deadSupportProperGain empty).isSome || (deadSupportProperGain primaryOutputs).isSome ||
      !equivalentBool (deadSupportReplacementImplementation primaryOutputs).candidate
        primaryOutputs.candidate then
    throw (IO.userError "empty dimensions or primary-output boundary changed")
  if (deadSupportProperGain allLive).isSome ||
      !strictEquivalentGainBool allLive constantAlternative then
    throw (IO.userError "no proper deletion was confused with a semantic minimum")
  if !(deadSupportProperGain constantCircuit).isSome ||
      (deadSupportReplacementImplementation constantCircuit).gateCount != 1 ||
      !equivalentBool (deadSupportReplacementImplementation constantCircuit).candidate
        constantCircuit.candidate then
    throw (IO.userError "zero-input constant circuit replacement changed")
  IO.println "computed-dead-support-context-fixtures: passed"
)

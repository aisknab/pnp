import PNP.PCCMinConstantPropagation

open PNP PNP.DirectWire

example {inputs gates : Nat} (gate : Gate inputs gates) (value : Bool)
    (checked : constantGateValue gate = some value)
    (input : Valuation inputs) (retained : Valuation gates) :
    value = gate.eval input retained :=
  constantGateValue_sound gate value checked input retained

example {inputs gates : Nat} (program : Program inputs gates)
    (input : Valuation inputs) (index : Fin gates) :
    ((compileNANDConstantPropagation program).alias index).eval input
        ((compileNANDConstantPropagation program).program.eval input) =
      program.eval input index :=
  compileNANDConstantPropagation_alias_semantics program input index

example {inputs gates : Nat} (program : Program inputs gates) :
    (compileNANDConstantPropagation program).gateCount +
      (compileNANDConstantPropagation program).eliminationCount = gates :=
  compileNANDConstantPropagation_exact_accounting program

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    Equivalent (constantPropagationImplementation current).candidate.program
      (constantPropagationImplementation current).candidate.directWireWord
      current.candidate.program current.candidate.directWireWord :=
  constantPropagationImplementation_equivalent current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    (constantPropagationImplementation current).gateCount ≤ current.gateCount :=
  constantPropagationImplementation_gateCount_le current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    referenceMinimum (constantPropagationImplementation current) = referenceMinimum current :=
  constantPropagationImplementation_referenceMinimum current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    residualSlack current = residualSlack (constantPropagationImplementation current) +
      (compileNANDConstantPropagation current.candidate.program).eliminationCount :=
  constantPropagationImplementation_residualSlack current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    StrictEquivalentGain current (constantPropagationImplementation current) ↔
      0 < (compileNANDConstantPropagation current.candidate.program).eliminationCount :=
  constantPropagationImplementation_strictGain_iff current

example {inputs outputs : Nat} (current : Implementation inputs outputs)
    (positive : 0 <
      (compileNANDConstantPropagation current.candidate.program).eliminationCount) :
    residualSlack (constantPropagationImplementation current) < residualSlack current :=
  constantPropagationImplementation_strictResidualDescent current positive

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    match nandConstantPropagationNormalizer.normalize current with
    | .gain next _ =>
        next = constantPropagationImplementation current ∧
          0 < (compileNANDConstantPropagation current.candidate.program).eliminationCount
    | .normal normalized =>
        normalized.result = constantPropagationImplementation current ∧
          (compileNANDConstantPropagation current.candidate.program).eliminationCount = 0 ∧
          normalized.result.gateCount = current.gateCount :=
  nandConstantPropagationNormalizer_checked current

private def cascadeProgram : Program 2 4 :=
  (((Program.empty.snoc ⟨.constant false, .input 0⟩).snoc
    ⟨.gate 0, .constant true⟩).snoc ⟨.input 0, .gate 1⟩).snoc
    ⟨.input 0, .input 1⟩

private def cascade : Implementation 2 7 :=
  (Candidate.ofDirectWireWord cascadeProgram ⟨fun output =>
    match output.val with
    | 0 => .gate 0
    | 1 => .gate 1
    | 2 => .gate 2
    | 3 => .gate 3
    | 4 => .input 0
    | 5 => .constant false
    | _ => .gate 3⟩).toImplementation

private def noGates : Implementation 0 0 :=
  (Candidate.ofDirectWireWord Program.empty ⟨Fin.elim0⟩).toImplementation

private def correlatedProgram : Program 1 2 :=
  (Program.empty.snoc ⟨.input 0, .input 0⟩).snoc ⟨.input 0, .gate 0⟩

private def correlated : Implementation 1 1 :=
  (Candidate.ofDirectWireWord correlatedProgram ⟨fun _ => .gate 1⟩).toImplementation

private def constantAlternative : Implementation 1 1 :=
  (Candidate.ofDirectWireWord Program.empty ⟨fun _ => .constant true⟩).toImplementation

/-- Literal constant propagation can stop while a strictly smaller word exists. -/
example : (compileNANDConstantPropagation correlatedProgram).eliminationCount = 0 := by
  decide
example : StrictEquivalentGain correlated constantAlternative :=
  strictEquivalentGainBool_sound (by decide)
example : 0 < residualSlack correlated :=
  Nat.lt_of_le_of_lt (Nat.zero_le (residualSlack constantAlternative))
    (strictEquivalentGainBool_sound (by decide :
      strictEquivalentGainBool correlated constantAlternative = true)).strictResidualDescent

#eval (show IO Unit from do
  for left in [false, true] do
    for right in [false, true] do
      let gate : Gate 0 0 := ⟨.constant left, .constant right⟩
      if constantGateValue gate != some (boolNand left right) then
        throw (IO.userError "constant NAND truth case changed")
  let leftFalse : Gate 1 0 := ⟨.constant false, .input 0⟩
  let rightFalse : Gate 1 0 := ⟨.input 0, .constant false⟩
  if constantGateValue leftFalse != some true || constantGateValue rightFalse != some true then
    throw (IO.userError "one-sided false source was not recognized")
  let retained : Gate 1 0 := ⟨.input 0, .constant true⟩
  if constantGateValue retained != none then
    throw (IO.userError "nonconstant NAND source was eliminated")
  let compiled := compileNANDConstantPropagation cascadeProgram
  if compiled.gateCount != 1 || compiled.eliminationCount != 3 then
    throw (IO.userError "cascading constant elimination accounting changed")
  let result := constantPropagationImplementation cascade
  for left in [false, true] do
    for right in [false, true] do
      let input : Valuation 2 := fun index => if index.val = 0 then left else right
      let expected := [true, false, true, boolNand left right, left, false, boolNand left right]
      let observed := (allFin 7).map (fun output => result.candidate.semantics input output)
      if observed != expected then
        throw (IO.userError "ordered gate, input, constant or repeated output changed")
  if (constantPropagationImplementation noGates).gateCount != 0 then
    throw (IO.userError "empty constant propagation changed")
  if (compileNANDConstantPropagation correlatedProgram).eliminationCount != 0 then
    throw (IO.userError "no-elimination boundary fixture changed")
  IO.println "computed-nand-constant-propagation-fixtures: passed")

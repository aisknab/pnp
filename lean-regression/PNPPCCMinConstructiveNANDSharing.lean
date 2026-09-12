import PNP.PCCMinConstructiveNANDSharing

open PNP PNP.DirectWire

example {inputs gates : Nat} (program : Program inputs gates)
    (input : Valuation inputs) (index : Fin gates) :
    (compileNANDSharing program).program.eval input
        ((compileNANDSharing program).alias index) = program.eval input index :=
  compileNANDSharing_alias_semantics program input index

example {inputs gates : Nat} (program : Program inputs gates) :
    (compileNANDSharing program).gateCount +
      (compileNANDSharing program).foldCount = gates :=
  compileNANDSharing_exact_accounting program

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    Equivalent (sharingImplementation current).candidate.program
      (sharingImplementation current).candidate.directWireWord
      current.candidate.program current.candidate.directWireWord :=
  sharingImplementation_equivalent current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    (sharingImplementation current).gateCount ≤ current.gateCount :=
  sharingImplementation_gateCount_le current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    referenceMinimum (sharingImplementation current) = referenceMinimum current :=
  sharingImplementation_referenceMinimum current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    residualSlack current = residualSlack (sharingImplementation current) +
      (compileNANDSharing current.candidate.program).foldCount :=
  sharingImplementation_residualSlack current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    StrictEquivalentGain current (sharingImplementation current) ↔
      0 < (compileNANDSharing current.candidate.program).foldCount :=
  sharingImplementation_strictGain_iff current

example {inputs outputs : Nat} (current : Implementation inputs outputs)
    (positive : 0 < (compileNANDSharing current.candidate.program).foldCount) :
    residualSlack (sharingImplementation current) < residualSlack current :=
  sharingImplementation_strictResidualDescent current positive

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    match nandSharingNormalizer.normalize current with
    | .gain next _ =>
        next = sharingImplementation current ∧
          0 < (compileNANDSharing current.candidate.program).foldCount
    | .normal normalized =>
        normalized.result = sharingImplementation current ∧
          (compileNANDSharing current.candidate.program).foldCount = 0 ∧
          normalized.result.gateCount = current.gateCount :=
  nandSharingNormalizer_checked current

/-- The remaining oracle is still an explicit construction boundary. -/
example (oracle : PCCMinTotalOracle) {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    let execution := runPCCMinNormalizeOracleLoop nandSharingNormalizer oracle current
    Equivalent execution.result.candidate.program execution.result.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      IsSemanticallyMinimum execution.result ∧
      execution.result.gateCount = referenceMinimum current ∧
      residualSlack execution.result = 0 ∧
      execution.gainIterations ≤ residualSlack current :=
  pccmin_normalize_oracle_loop_checked_complete nandSharingNormalizer oracle current

private def cascadeProgram : Program 2 6 :=
  (((((Program.empty.snoc ⟨.input 0, .input 1⟩).snoc
    ⟨.input 1, .input 0⟩).snoc
    ⟨.gate 0, .gate 1⟩).snoc
    ⟨.gate 1, .gate 0⟩).snoc
    ⟨.gate 2, .gate 3⟩).snoc
    ⟨.gate 3, .gate 2⟩

private def cascade : Implementation 2 8 :=
  (Candidate.ofDirectWireWord cascadeProgram ⟨fun output =>
    match output.val with
    | 0 => .gate 5
    | 1 => .gate 4
    | 2 => .gate 3
    | 3 => .gate 2
    | 4 => .gate 1
    | 5 => .gate 0
    | 6 => .input 0
    | _ => .constant false⟩).toImplementation

example : (compileNANDSharing cascadeProgram).foldCount = 3 := by decide
example : (sharingImplementation cascade).gateCount = 3 := by decide
example : (allFin 6).map (fun index =>
    ((compileNANDSharing cascadeProgram).alias index).val) = [0, 0, 1, 1, 2, 2] := by
  decide
example : strictEquivalentGainBool cascade (sharingImplementation cascade) = true := by
  decide

private def twoGateAlternative : Implementation 2 8 :=
  (Candidate.ofDirectWireWord
    ((Program.empty.snoc ⟨.input 0, .input 1⟩).snoc ⟨.gate 0, .gate 0⟩)
    ⟨fun output =>
      match output.val with
      | 0 => .gate 0
      | 1 => .gate 0
      | 2 => .gate 1
      | 3 => .gate 1
      | 4 => .gate 0
      | 5 => .gate 0
      | 6 => .input 0
      | _ => .constant false⟩).toImplementation

/-- No structural fold does not imply semantic minimality or ZeroSlack. -/
example :
    (compileNANDSharing (sharingImplementation cascade).candidate.program).foldCount = 0 := by
  decide
example : StrictEquivalentGain (sharingImplementation cascade) twoGateAlternative :=
  strictEquivalentGainBool_sound (by decide)
example : 0 < residualSlack (sharingImplementation cascade) :=
  Nat.lt_of_le_of_lt (Nat.zero_le (residualSlack twoGateAlternative))
    (strictEquivalentGainBool_sound (by decide :
      strictEquivalentGainBool (sharingImplementation cascade) twoGateAlternative = true)).strictResidualDescent

private def noGates : Implementation 0 0 :=
  (Candidate.ofDirectWireWord Program.empty ⟨Fin.elim0⟩).toImplementation

example : (sharingImplementation noGates).gateCount = 0 := by decide
example : (compileNANDSharing (Program.empty : Program 0 0)).foldCount = 0 := by decide

private def constantPair : Program 0 2 :=
  (Program.empty.snoc ⟨.constant true, .constant false⟩).snoc
    ⟨.constant false, .constant true⟩
example : (compileNANDSharing constantPair).gateCount = 1 := by decide
example : (compileNANDSharing constantPair).foldCount = 1 := by decide

private def unequalPair : Program 2 2 :=
  (Program.empty.snoc ⟨.input 0, .input 1⟩).snoc ⟨.input 0, .input 0⟩
example : (compileNANDSharing unequalPair).foldCount = 0 := by decide
example : (compileNANDSharing unequalPair).gateCount = 2 := by decide

#eval do
  let compiled := compileNANDSharing cascadeProgram
  if compiled.gateCount != 3 || compiled.foldCount != 3 then
    throw (IO.userError "computed sharing gate accounting changed")
  if (sharingImplementation noGates).gateCount != 0 then
    throw (IO.userError "empty sharing implementation changed")
  IO.println "constructive-nand-sharing-regression: all-input contracts and boundary fixtures passed"

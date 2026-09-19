import PNP

namespace PNP.DirectWire.SemanticGateRetractionRegression

open SemanticGateRetraction

example {inputs gates outputs outerInputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (erased : GateRecords inputs gates outputs) (values : Fin gates → Bool)
    (binding : Fin inputs → Source outerInputs 0)
    (constantOn : ∀ valuation gate, terminalGateSelected erased gate = true →
      candidate.program.eval (inducedInput binding valuation) gate = values gate)
    (valuation : Valuation outerInputs) (output : Fin outputs) :
    (implementation candidate erased values binding).candidate.semantics valuation output =
      candidate.semantics (inducedInput binding valuation) output :=
  SemanticGateRetraction.semantics candidate erased values binding constantOn valuation output

example {inputs gates outputs outerInputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (erased : GateRecords inputs gates outputs) (values : Fin gates → Bool)
    (binding : Fin inputs → Source outerInputs 0) :
    (implementation candidate erased values binding).gateCount +
      (extractTerminalSupport candidate erased).gateCount = gates :=
  gateCount_partition candidate erased values binding

example {inputs gates outputs outerInputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (erased : GateRecords inputs gates outputs) (values : Fin gates → Bool)
    (binding : Fin inputs → Source outerInputs 0) :
    (implementation candidate erased values binding).gateCount =
      gates - (extractTerminalSupport candidate erased).gateCount :=
  gateCount_eq_sub candidate erased values binding

private def bit : Fin 1 := ⟨0, by decide⟩
private def g0 : Fin 3 := ⟨0, by decide⟩
private def g1 : Fin 3 := ⟨1, by decide⟩
private def g2 : Fin 3 := ⟨2, by decide⟩

private def negProgram : Program 1 1 := .snoc .empty ⟨.input bit, .input bit⟩
private def trueProgram : Program 1 2 := .snoc negProgram ⟨.input bit, .gate bit⟩
private def threeProgram : Program 1 3 :=
  .snoc trueProgram ⟨.gate ⟨1, by decide⟩, .gate ⟨1, by decide⟩⟩

private def original : Candidate 1 3 4 :=
  Candidate.ofDirectWireWord threeProgram
    ⟨fun output => if output.val = 0 then .input bit
      else if output.val = 1 then .gate g0
      else if output.val = 2 then .gate g1 else .gate g2⟩

private def identityBinding : Fin 1 → Source 1 0 := fun index => .input index
private def single : GateRecords 1 3 4 := [.gate g1]
private def both : GateRecords 1 3 4 := [.gate g1, .gate g2]
private def bothValues (gate : Fin 3) : Bool := decide (gate.val = 1)

theorem single_constant : ∀ valuation gate, terminalGateSelected single gate = true →
    original.program.eval (inducedInput identityBinding valuation) gate = true := by
  intro valuation gate marked
  have member := (terminalGateSelected_eq_true_iff single gate).mp marked
  have equal : gate = g1 := TerminalPrimitiveRecord.gate.inj (List.mem_singleton.mp member)
  subst gate
  change boolNand (valuation bit) (boolNand (valuation bit) (valuation bit)) = true
  cases valuation bit <;> rfl

theorem both_constant : ∀ valuation gate, terminalGateSelected both gate = true →
    original.program.eval (inducedInput identityBinding valuation) gate = bothValues gate := by
  intro valuation gate marked
  have member := (terminalGateSelected_eq_true_iff both gate).mp marked
  rcases List.mem_cons.mp member with equal | tail
  · have gateEqual : gate = g1 := TerminalPrimitiveRecord.gate.inj equal
    subst gate
    change boolNand (valuation bit) (boolNand (valuation bit) (valuation bit)) = true
    cases valuation bit <;> rfl
  · have gateEqual : gate = g2 := TerminalPrimitiveRecord.gate.inj (List.mem_singleton.mp tail)
    subst gate
    change boolNand
      (boolNand (valuation bit) (boolNand (valuation bit) (valuation bit)))
      (boolNand (valuation bit) (boolNand (valuation bit) (valuation bit))) = false
    cases valuation bit <;> rfl

theorem single_preserves_all_outputs (valuation : Valuation 1) (output : Fin 4) :
    (implementation original single (fun _ => true) identityBinding).candidate.semantics
        valuation output = original.semantics valuation output :=
  SemanticGateRetraction.semantics original single (fun _ => true) identityBinding single_constant valuation output

theorem exact_one_gate_removed :
    (implementation original single (fun _ => true) identityBinding).gateCount = 2 := by decide +kernel

theorem literal_propagation_does_not_remove_semantic_constant :
    (constantPropagationImplementation original.toImplementation).gateCount = 3 := by decide +kernel

theorem invalid_erasure_changes_output :
    (implementation original [.gate g0] (fun _ => false) identityBinding).candidate.semantics
        (fun _ => false) ⟨1, by decide⟩ ≠
      original.semantics (fun _ => false) ⟨1, by decide⟩ := by decide +kernel

private def freshInput : Fin 2 := ⟨1, by decide⟩
private def restrictedOriginal : Candidate 2 1 2 :=
  Candidate.ofDirectWireWord (.snoc .empty ⟨.input freshInput, .input freshInput⟩)
    ⟨fun output => if output.val = 0 then .input ⟨0, by decide⟩ else .gate bit⟩
private def freshBinding : Fin 2 → Source 1 0 :=
  fun index => if index.val = 0 then .input bit else .constant false
private def restrictedErased : GateRecords 2 1 2 := [.gate bit]

theorem restricted_constant : ∀ valuation gate,
    terminalGateSelected restrictedErased gate = true →
      restrictedOriginal.program.eval (inducedInput freshBinding valuation) gate = true := by
  intro valuation gate marked
  have member := (terminalGateSelected_eq_true_iff restrictedErased gate).mp marked
  have equal : gate = bit := TerminalPrimitiveRecord.gate.inj (List.mem_singleton.mp member)
  subst gate
  rfl

theorem restricted_preserves_old_input (valuation : Valuation 1) :
    (implementation restrictedOriginal restrictedErased (fun _ => true) freshBinding).candidate.semantics
        valuation ⟨0, by decide⟩ = valuation bit := by
  exact SemanticGateRetraction.semantics restrictedOriginal restrictedErased (fun _ => true) freshBinding
    restricted_constant valuation ⟨0, by decide⟩

private def empty : Candidate 0 0 0 := Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩
private def emptyResult : Implementation 0 0 := implementation empty [] Fin.elim0 Fin.elim0

private def checks : List (String × Bool) :=
  [ ("semantic constant is erased",
      decide ((implementation original single (fun _ => true) identityBinding).gateCount = 2))
  , ("all outputs retained after semantic erasure", equivalentBool
      (implementation original single (fun _ => true) identityBinding).candidate original)
  , ("literal-only propagation misses this constant",
      decide ((constantPropagationImplementation original.toImplementation).gateCount = 3))
  , ("two semantic constants removed", decide
      ((implementation original both bothValues identityBinding).gateCount = 1) &&
        equivalentBool (implementation original both bothValues identityBinding).candidate original)
  , ("duplicate records do not double-charge", decide
      ((implementation original [.gate g1, .gate g1] (fun _ => true) identityBinding).gateCount = 2))
  , ("no erasure preserves all gates", decide
      ((implementation original [] (fun _ => false) identityBinding).gateCount = 3) &&
        equivalentBool (implementation original [] (fun _ => false) identityBinding).candidate original)
  , ("invalid constant condition is observable", !(equivalentBool
      (implementation original [.gate g0] (fun _ => false) identityBinding).candidate original))
  , ("restriction removes fresh gate at zero cost", decide
      ((implementation restrictedOriginal restrictedErased (fun _ => true) freshBinding).gateCount = 0))
  , ("restriction preserves the unrestricted old input", allTrue (allBoolTuples 1) fun tuple =>
      allTrue (allFin 2) fun output => boolEqual
        ((implementation restrictedOriginal restrictedErased (fun _ => true) freshBinding).candidate.semantics
          tuple.toValuation output)
        (restrictedOriginal.semantics (inducedInput freshBinding tuple.toValuation) output))
  , ("empty dimensions", decide (emptyResult.gateCount = 0))
  ]

def run : IO Unit := do
  for (name, passed) in checks do
    if passed then
      IO.println ("retraction-check-passed: " ++ name)
    else
      throw (IO.userError ("retraction-check-failed: " ++ name))
  IO.println "semantic-retraction-regressions-complete: 10 runtime checks; 3 general type contracts; 8 kernel guards"

end PNP.DirectWire.SemanticGateRetractionRegression

#print axioms PNP.DirectWire.SemanticGateRetractionRegression.single_constant
#print axioms PNP.DirectWire.SemanticGateRetractionRegression.both_constant
#print axioms PNP.DirectWire.SemanticGateRetractionRegression.single_preserves_all_outputs
#print axioms PNP.DirectWire.SemanticGateRetractionRegression.exact_one_gate_removed
#print axioms PNP.DirectWire.SemanticGateRetractionRegression.literal_propagation_does_not_remove_semantic_constant
#print axioms PNP.DirectWire.SemanticGateRetractionRegression.invalid_erasure_changes_output
#print axioms PNP.DirectWire.SemanticGateRetractionRegression.restricted_constant
#print axioms PNP.DirectWire.SemanticGateRetractionRegression.restricted_preserves_old_input

def main : IO Unit := PNP.DirectWire.SemanticGateRetractionRegression.run

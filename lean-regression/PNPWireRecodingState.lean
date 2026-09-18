import PNP.NANDWireRecodingState

namespace PNP.DirectWire.WireRecodingState.Regression

def identity (width : Nat) : Implementation width width :=
  (Candidate.ofDirectWireWord (.empty : Program width 0)
    ⟨fun field => .input field⟩).toImplementation

def negation : Implementation 1 1 :=
  (Candidate.ofDirectWireWord
    ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩)
    (⟨fun _ => .gate 0⟩ : DirectWireWord 1 1 1)).toImplementation

def controlledNot : Implementation 2 2 :=
  (Candidate.ofDirectWireWord
    (.snoc
      (.snoc
        (.snoc
          (.snoc (.empty : Program 2 0) ⟨.input 0, .input 1⟩)
          ⟨.input 0, .gate 0⟩)
        ⟨.input 1, .gate 0⟩)
      ⟨.gate 1, .gate 2⟩)
    (⟨fun field => if field.val = 0 then .input 0 else .gate 3⟩ :
      DirectWireWord 2 4 2)).toImplementation

def constantTrue : Candidate 1 0 1 :=
  Candidate.ofDirectWireWord .empty ⟨fun _ => .constant true⟩

/-- Constant true semantically, but the literal output still depends on input zero. -/
def cancelledPath : Candidate 1 2 1 :=
  Candidate.ofDirectWireWord
    (.snoc (.snoc .empty ⟨.input 0, .input 0⟩) ⟨.input 0, .gate 0⟩)
    ⟨fun _ => .gate 1⟩

def unusedPath : Candidate 1 2 1 :=
  Candidate.ofDirectWireWord cancelledPath.program ⟨fun _ => .constant true⟩

def hiddenBefore : WireCarrier 1 1 1 :=
  { implementation := constantTrue.toImplementation
    source := fun _ => .constant true }

def hiddenAfter : WireCarrier 1 1 1 :=
  { implementation := unusedPath.toImplementation
    source := fun _ => .gate ⟨1, by decide⟩ }

def free : WireCarrier 2 1 2 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 2 0)
      (⟨fun _ => .constant false⟩ : DirectWireWord 2 0 1)).toImplementation
    source := fun field => .input field }

def commonDependencies : WireCarrier 2 1 2 :=
  { implementation := (Candidate.ofDirectWireWord
      (.snoc (.snoc (.empty : Program 2 0) ⟨.input 0, .input 1⟩)
        ⟨.input 0, .gate 0⟩)
      (⟨fun _ => .constant false⟩ : DirectWireWord 2 2 1)).toImplementation
    source := fun field =>
      if field.val = 0 then .gate ⟨0, by decide⟩ else .gate ⟨1, by decide⟩ }

def unary : WireCarrier 1 1 1 :=
  { implementation := (Candidate.ofDirectWireWord
      ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩)
      (⟨fun _ => .input 0⟩ : DirectWireWord 1 1 1)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def empty : WireCarrier 0 0 0 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 0 0)
      (⟨Fin.elim0⟩ : DirectWireWord 0 0 0)).toImplementation
    source := Fin.elim0 }

example {inputs leftGates rightGates : Nat}
    (left : Program inputs leftGates) (leftWire : Source inputs leftGates)
    (right : Program inputs rightGates) (rightWire : Source inputs rightGates) :
    CausalBound.sourceDependencyGuard left leftWire right rightWire = true ↔
      ∀ labels, CausalBound.source rightWire labels (CausalBound.levels right labels) ≤
        CausalBound.source leftWire labels (CausalBound.levels left labels) :=
  CausalBound.sourceDependencyGuard_iff left leftWire right rightWire

example {inputs outputs fields : Nat} (before after : WireCarrier inputs outputs fields) :
    before.dependencyGuard after = true ↔
      ∀ labels, after.CausalBounds labels
        (CausalBound.outputLevel before.implementation.candidate labels)
        (before.fieldLevel labels) :=
  WireCarrier.dependencyGuard_iff before after

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    (before : WireObligationHistory.State source)
    (encoder decoder : Implementation fields fields) (receipt : Receipt before encoder decoder) :
    receipt.next.pending = before.pending :=
  receipt.pending

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    (before : WireObligationHistory.State source)
    (encoder decoder : Implementation fields fields) (receipt : Receipt before encoder decoder)
    (labels : Fin inputs → Nat) (bounded : before.CausalInvariant labels) :
    receipt.next.CausalInvariant labels :=
  receipt.causalInvariant labels bounded

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    (before : WireObligationHistory.State source)
    (encoder decoder : Implementation fields fields) :
    (∃ receipt, execute before encoder decoder = some receipt) ↔
      WireCarrierRecoding.check encoder decoder = true ∧
        before.current.dependencyGuard
          (WireCarrierRecoding.result before.current encoder decoder) = true :=
  execute_success_iff before encoder decoder

#print axioms PNP.DirectWire.CausalBound.levels_bounded_iff
#print axioms PNP.DirectWire.CausalBound.source_bounded_iff
#print axioms PNP.DirectWire.CausalBound.sourceDependencyGuard_iff
#print axioms PNP.DirectWire.CausalBound.candidateDependencyGuard_iff
#print axioms PNP.DirectWire.WireCarrier.dependencyGuard_iff
#print axioms PNP.DirectWire.WireObligationHistory.State.recode_pending
#print axioms PNP.DirectWire.WireRecodingState.execute_success_iff
#print axioms PNP.DirectWire.WireRecodingState.execute_failure_iff
#print axioms PNP.DirectWire.WireRecodingState.Receipt.causalInvariant
#print axioms PNP.DirectWire.WireRecodingState.Receipt.gate_balance

-- All finite executions below are guarded test evidence, not proof authority.
#eval show IO Unit from do
  if !(equivalentBool constantTrue cancelledPath) then
    throw (IO.userError "the hostile semantic-cancellation fixture is wrong")
  if CausalBound.candidateDependencyGuard constantTrue cancelledPath then
    throw (IO.userError "semantic cancellation hid a new physical dependency")
  if !(CausalBound.candidateDependencyGuard cancelledPath constantTrue) then
    throw (IO.userError "safe dependency removal was rejected")
  if !(CausalBound.candidateDependencyGuard constantTrue unusedPath) then
    throw (IO.userError "unobserved gates were treated as an output dependency")
  if hiddenBefore.dependencyGuard hiddenAfter then
    throw (IO.userError "a hidden computational field escaped the dependency guard")
  if !(hiddenBefore.dependencyGuard hiddenBefore) then
    throw (IO.userError "reflexive carrier dependency guard failed")
  if !(WireCarrierRecoding.check controlledNot controlledNot) then
    throw (IO.userError "the interacting recoder is not genuinely reversible")
  let independent := WireObligationHistory.State.initial free
  if (execute independent controlledNot controlledNot).isSome then
    throw (IO.userError "a valid inverse bypassed the independent causal guard")
  let common := WireObligationHistory.State.initial commonDependencies
  match execute common controlledNot controlledNot with
  | none => throw (IO.userError "safe interacting recoding was rejected")
  | some receipt =>
      for tuple in allBoolTuples 2 do
        for field in allFin 2 do
          if receipt.next.current.fieldValue tuple.toValuation field !=
              common.current.fieldValue tuple.toValuation field then
            throw (IO.userError "accepted interacting recoding changed a field")
      if receipt.next.current.implementation.gateCount + receipt.next.removed !=
          commonDependencies.implementation.gateCount + receipt.next.charged then
        throw (IO.userError "accepted recoding has a false physical balance")
  let before := (WireObligationHistory.State.initial unary).create 314
    ⟨0, by decide⟩ rfl
  match execute before negation negation with
  | none => throw (IO.userError "recoding a state with an open snapshot was rejected")
  | some receipt =>
      let creationID : Option Nat := (receipt.next.pending (0 : Fin 1)).map
        (fun snapshot => snapshot.identity)
      match creationID with
      | none => throw (IO.userError "recoding discharged an obligation")
      | some identity =>
          if identity != 314 then
            throw (IO.userError "recoding changed a captured creation identity")
      if receipt.next.charged != 2 || receipt.next.removed != 3 ||
          receipt.next.current.implementation.gateCount != 0 then
        throw (IO.userError "recoding hid an actual allocation or deletion")
  if (execute before negation (identity 1)).isSome then
    throw (IO.userError "the executor accepted an incorrect inverse")
  if !(execute (WireObligationHistory.State.initial empty)
      (identity 0) (identity 0)).isSome then
    throw (IO.userError "empty dimensions failed the exact guards")
  IO.println "RECODING_CAUSAL_STATE_RUNTIME_PASSED"

end PNP.DirectWire.WireRecodingState.Regression

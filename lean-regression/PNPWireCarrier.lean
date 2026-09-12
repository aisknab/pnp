import PNP

namespace PNP.DirectWire

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (valuation : Valuation inputs) (output : Fin outputs) :
    carrier.normalize.implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output :=
  carrier.normalize_output valuation output

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (valuation : Valuation inputs) (field : Fin fields) :
    carrier.normalize.fieldValue valuation field = carrier.fieldValue valuation field :=
  carrier.normalize_field valuation field

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields) :
    carrier.normalize.normalize = carrier.normalize := carrier.normalize_idempotent

example {inputs outputs fields : Nat} (combined : Implementation inputs (outputs + fields)) :
    (WireCarrier.unpack (outputs := outputs) (fields := fields) combined).exposed = combined :=
  WireCarrier.exposed_unpack combined

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields) :
    carrier.normalize.implementation.gateCount +
      (runPhysicalNormalization carrier.exposed).trace.savedGates =
        carrier.implementation.gateCount :=
  carrier.normalize_exact_accounting

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (field : Fin fields) (producer : Fin carrier.implementation.gateCount)
    (sourceAt : carrier.source field = .gate producer)
    (selected : terminalGateSelected records producer = true) :
    producer ∈ (extractTerminalSupport carrier.exposed.candidate records).interface :=
  carrier.field_producer_visible records field producer sourceAt selected

example {inputs outputs fields replacementGates : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (replacement : Candidate
      (extractTerminalSupport carrier.exposed.candidate records).boundary.length
      replacementGates
      (extractTerminalSupport carrier.exposed.candidate records).interface.length)
    (sameOpen : replacement.semantics =
      (extractTerminalSupport carrier.exposed.candidate records).extractedCandidate.semantics)
    (result : WireCarrier inputs outputs fields)
    (accepted : carrier.splice records replacement = some result) :
    (∀ valuation output, result.implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output) ∧
    (∀ valuation field, result.fieldValue valuation field =
      carrier.fieldValue valuation field) ∧
    result.implementation.gateCount +
      (extractTerminalSupport carrier.exposed.candidate records).gateCount =
        carrier.implementation.gateCount + replacementGates :=
  carrier.splice_checked records replacement sameOpen result accepted

example {inputs outputs fields replacementGates : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (seed : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (replacement : Candidate
      (extractTerminalSupport carrier.exposed.candidate
        (carrier.productionRecords seed)).boundary.length replacementGates
      (extractTerminalSupport carrier.exposed.candidate
        (carrier.productionRecords seed)).interface.length) :
    ∃ result, carrier.splice (carrier.productionRecords seed) replacement = some result :=
  carrier.production_compiles seed replacement

private def duplicateProgram : Program 1 2 :=
  .snoc (.snoc .empty ⟨.input 0, .input 0⟩) ⟨.input 0, .input 0⟩

/-- Neither ordinary output reaches either NAND; the field must retain NOT x. -/
private def hiddenCarrier : WireCarrier 1 1 1 :=
  { implementation := (Candidate.ofDirectWireWord duplicateProgram
      ⟨fun _ => .input 0⟩).toImplementation
    source := fun _ => .gate ⟨1, by decide⟩ }

private def richCarrier : WireCarrier 1 1 6 :=
  { implementation := hiddenCarrier.implementation
    source := fun field =>
      match field.val with
      | 0 => .gate ⟨1, by decide⟩
      | 1 => .input 0
      | 2 => .constant false
      | 3 => .gate ⟨0, by decide⟩
      | 4 => .constant true
      | _ => .gate ⟨1, by decide⟩ }

private def fieldsOnly : WireCarrier 1 0 1 :=
  { implementation := (Candidate.ofDirectWireWord duplicateProgram ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .gate ⟨1, by decide⟩ }

private def noFields : WireCarrier 1 1 0 :=
  { implementation := hiddenCarrier.implementation, source := Fin.elim0 }

private def emptyCarrier : WireCarrier 0 0 0 :=
  { implementation := (Candidate.ofDirectWireWord Program.empty ⟨Fin.elim0⟩).toImplementation
    source := Fin.elim0 }

/-- Ordinary semantics alone does not recover the hidden field. -/
private def lostField : WireCarrier 1 1 1 :=
  { implementation := (Candidate.ofDirectWireWord Program.empty ⟨fun _ => .input 0⟩).toImplementation
    source := fun _ => .constant false }

example : lostField.implementation.candidate.semantics =
    hiddenCarrier.implementation.candidate.semantics := by
  funext input output
  exact equivalentBool_sound (by decide :
    equivalentBool lostField.implementation.candidate hiddenCarrier.implementation.candidate = true)
    input output

example : lostField.fieldValue (fun _ => false) 0 ≠
    hiddenCarrier.fieldValue (fun _ => false) 0 := by decide

private def chainProgram : Program 1 3 :=
  .snoc (.snoc (.snoc .empty ⟨.input 0, .input 0⟩) ⟨.gate ⟨0, by decide⟩, .gate ⟨0, by decide⟩⟩)
    ⟨.gate ⟨1, by decide⟩, .gate ⟨1, by decide⟩⟩

private def chainCarrier : WireCarrier 1 1 2 :=
  { implementation := (Candidate.ofDirectWireWord chainProgram
      ⟨fun _ => .input 0⟩).toImplementation
    source := fun field => if field.val = 0 then .gate ⟨0, by decide⟩ else .gate ⟨2, by decide⟩ }

private def interleaved : List (TerminalPrimitiveRecord 1 3 3 0) := [.gate ⟨0, by decide⟩, .gate ⟨2, by decide⟩]
private def chainSupport := extractTerminalSupport chainCarrier.exposed.candidate interleaved

example : chainSupport.boundary = [.input 0, .gate ⟨1, by decide⟩] := by decide
example : chainSupport.interface = [⟨0, by decide⟩, ⟨2, by decide⟩] := by decide

private def safeReplacement :
    Candidate chainSupport.boundary.length 2 chainSupport.interface.length :=
  Candidate.ofDirectWireWord
    (.snoc (.snoc .empty
      ⟨.input ⟨0, by decide⟩, .input ⟨0, by decide⟩⟩)
      ⟨.input ⟨1, by decide⟩, .input ⟨1, by decide⟩⟩)
    ⟨fun output => if output.val = 0 then .gate ⟨0, by decide⟩ else .gate ⟨1, by decide⟩⟩

private theorem safe_equivalent :
    safeReplacement.semantics = chainSupport.extractedCandidate.semantics := by
  funext input output
  exact equivalentBool_sound (by decide :
    equivalentBool safeReplacement chainSupport.extractedCandidate = true) input output

/-- Acyclic as a standalone replacement, but its rebinding creates a cycle. -/
private def cyclicReplacement :
    Candidate chainSupport.boundary.length 3 chainSupport.interface.length :=
  Candidate.ofDirectWireWord
    (.snoc (.snoc (.snoc .empty
      ⟨.input ⟨1, by decide⟩, .input ⟨1, by decide⟩⟩)
      ⟨.input ⟨1, by decide⟩, .gate ⟨0, by decide⟩⟩)
      ⟨.input ⟨0, by decide⟩, .gate ⟨1, by decide⟩⟩)
    ⟨fun output => if output.val = 0 then .gate ⟨2, by decide⟩ else .gate ⟨0, by decide⟩⟩

private theorem cyclic_equivalent :
    cyclicReplacement.semantics = chainSupport.extractedCandidate.semantics := by
  funext input output
  exact equivalentBool_sound (by decide :
    equivalentBool cyclicReplacement chainSupport.extractedCandidate = true) input output

private def cyclicGraph := ArbitrarySupportSplice.graph
  chainCarrier.exposed.candidate interleaved cyclicReplacement

example : chainCarrier.splice interleaved cyclicReplacement = none := by
  apply (chainCarrier.splice_failure_iff interleaved cyclicReplacement).2
  intro wellFounded
  have first : cyclicGraph.Depends (3 : Fin 4) (0 : Fin 4) := by
    unfold RawNandGraph.Depends
    decide
  have second : cyclicGraph.Depends (2 : Fin 4) (3 : Fin 4) := by
    unfold RawNandGraph.Depends
    decide
  have third : cyclicGraph.Depends (0 : Fin 4) (2 : Fin 4) := by
    unfold RawNandGraph.Depends
    decide
  have impossible (node : Fin 4) (accessible : Acc cyclicGraph.Depends node) :
      node = 0 ∨ node = 2 ∨ node = 3 → False := by
    induction accessible with
    | intro node previous ih =>
        intro onCycle
        rcases onCycle with rfl | rfl | rfl
        · exact ih 3 first (Or.inr (Or.inr rfl))
        · exact ih 0 third (Or.inl rfl)
        · exact ih 2 second (Or.inr (Or.inl rfl))
  exact impossible 0 (wellFounded.apply 0) (Or.inl rfl)

private def productionSeed : List (TerminalPrimitiveRecord 1 3 3 0) := [.gate ⟨2, by decide⟩]
private def closedRecords := chainCarrier.productionRecords productionSeed
private def closedSupport := extractTerminalSupport chainCarrier.exposed.candidate closedRecords

example : closedSupport.selectedGates = [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] := by decide
example : closedSupport.boundary = [.input 0] := by decide
example : closedSupport.interface = [⟨0, by decide⟩, ⟨2, by decide⟩] := by decide

private def productionSmaller :
    Candidate closedSupport.boundary.length 1 closedSupport.interface.length :=
  Candidate.ofDirectWireWord
    (.snoc .empty ⟨.input ⟨0, by decide⟩, .input ⟨0, by decide⟩⟩)
    ⟨fun _ => .gate ⟨0, by decide⟩⟩

private theorem production_equivalent :
    productionSmaller.semantics = closedSupport.extractedCandidate.semantics := by
  funext input output
  exact equivalentBool_sound (by decide :
    equivalentBool productionSmaller closedSupport.extractedCandidate = true) input output

/-- Dead replacement gates are real gates and must not disappear from accounting. -/
private def productionLarger :
    Candidate closedSupport.boundary.length 4 closedSupport.interface.length :=
  Candidate.ofDirectWireWord
    (.snoc (.snoc (.snoc (.snoc .empty
      ⟨.input ⟨0, by decide⟩, .input ⟨0, by decide⟩⟩)
      ⟨.constant false, .constant false⟩)
      ⟨.constant false, .constant false⟩)
      ⟨.constant false, .constant false⟩)
    ⟨fun _ => .gate ⟨0, by decide⟩⟩

private theorem larger_equivalent :
    productionLarger.semantics = closedSupport.extractedCandidate.semantics := by
  funext input output
  exact equivalentBool_sound (by decide :
    equivalentBool productionLarger closedSupport.extractedCandidate = true) input output

/-- Runtime checks are bounded examples, never theorem authority. -/
private def checkCarrierFixtures : IO Unit := do
  let hidden := hiddenCarrier.normalize
  if hidden.implementation.gateCount != 1 then
    throw (IO.userError "hidden field producer was lost or duplicate gates were retained")
  if noFields.normalize.implementation.gateCount != 0 then
    throw (IO.userError "zero-field ordinary-only pruning changed")
  if fieldsOnly.normalize.implementation.gateCount != 1 ||
      emptyCarrier.normalize.implementation.gateCount != 0 then
    throw (IO.userError "zero ordinary outputs or empty dimensions changed")
  let rich := richCarrier.normalize
  if rich.implementation.gateCount != 1 ||
      rich.normalize.implementation.gateCount != 1 then
    throw (IO.userError "field wiring was charged as gates or normalization was not idempotent")
  for value in [false, true] do
    let valuation : Valuation 1 := fun _ => value
    if hidden.implementation.candidate.semantics valuation 0 != value ||
        hidden.fieldValue valuation 0 != !value ||
        fieldsOnly.normalize.fieldValue valuation 0 != !value then
      throw (IO.userError "ordinary and hidden field semantics were conflated")
    let observed := (allFin 6).map (rich.fieldValue valuation)
    if observed != [!value, value, false, !value, true, !value] then
      throw (IO.userError "ordered repeated, input or constant fields changed")
  match chainCarrier.splice interleaved safeReplacement with
  | none => throw (IO.userError "safe interleaved carrier splice was rejected")
  | some result =>
      if result.implementation.gateCount != 3 then
        throw (IO.userError "safe splice exterior accounting changed")
      for value in [false, true] do
        let valuation : Valuation 1 := fun _ => value
        if result.implementation.candidate.semantics valuation 0 != value ||
            (allFin 2).map (result.fieldValue valuation) != [!value, !value] then
          throw (IO.userError "safe splice lost a hidden carrier field")
  match chainCarrier.splice interleaved cyclicReplacement with
  | none => pure ()
  | some _ => throw (IO.userError "cyclic literal carrier wiring was accepted")
  match chainCarrier.splice closedRecords productionSmaller with
  | none => throw (IO.userError "computed production closure did not compile")
  | some result =>
      if result.implementation.gateCount != 1 then
        throw (IO.userError "production splice did not expose the real strict saving")
      for value in [false, true] do
        let valuation : Valuation 1 := fun _ => value
        if result.implementation.candidate.semantics valuation 0 != value ||
            (allFin 2).map (result.fieldValue valuation) != [!value, !value] then
          throw (IO.userError "production strict gain lost ordinary or field values")
  match chainCarrier.splice closedRecords productionLarger with
  | none => throw (IO.userError "a larger valid replacement was incorrectly rejected")
  | some result =>
      if result.implementation.gateCount != 4 then
        throw (IO.userError "unused replacement gates were omitted from physical accounting")
  IO.println "M250_WIRE_BACKED_CARRIER_RUNTIME_FIXTURES_GREEN"

#eval checkCarrierFixtures

end PNP.DirectWire

import PNP

namespace PNP.DirectWire.WireCausalExpansionRegression

open WireCausalExpansion

section GeneralContracts

variable {inputs gates outputs profileWidth replacementGates : Nat}
variable (candidate : Candidate inputs gates outputs)
variable (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
variable (replacement : Candidate
  (terminalBoundaryPorts candidate.program records).length replacementGates
  (terminalInterfacePorts candidate records).length)

-- The constructor has no supplied rank, acyclicity, compiler or semantic premise.
example : WellFounded (graph candidate records replacement).Depends :=
  graph_wellFounded candidate records replacement

example : compile candidate records replacement = some (compiled candidate records replacement) :=
  compiled_spec candidate records replacement

example :
    (expanded candidate records replacement).gateCount =
      (ArbitrarySupportSplice.exterior records).length +
        (terminalInterfacePorts candidate records).length * replacementGates :=
  expanded_gateCount candidate records replacement

example
    (sameOpen : replacement.semantics =
      (extractTerminalSupport candidate records).extractedCandidate.semantics)
    (input : Valuation inputs) (output : Fin outputs) :
    (expanded candidate records replacement).candidate.semantics input output =
      candidate.semantics input output :=
  expanded_semantics candidate records replacement sameOpen input output

-- Agreement is over arbitrary open valuations, not just whole-circuit inputs.
example
    (sameOpen : replacement.semantics =
      (extractTerminalSupport candidate records).extractedCandidate.semantics)
    (owner : Fin (terminalInterfacePorts candidate records).length)
    (valuation : Valuation (terminalBoundaryPorts candidate.program records).length) :
    replacement.semantics (maskedBoundary candidate records owner valuation) owner =
      (extractTerminalSupport candidate records).extractedCandidate.semantics valuation owner :=
  masked_replacement_output candidate records replacement sameOpen owner valuation

-- A local reduction in R is insufficient unless the full K*R bill is smaller.
example :
    (expanded candidate records replacement).gateCount < gates ↔
      (terminalInterfacePorts candidate records).length * replacementGates <
        (extractTerminalSupport candidate records).gateCount :=
  expanded_smaller_iff candidate records replacement

example
    (oneProducer : (terminalInterfacePorts candidate records).length = 1)
    (smaller : replacementGates < (extractTerminalSupport candidate records).gateCount) :
    (expanded candidate records replacement).gateCount < gates :=
  single_interface_smaller candidate records replacement oneProducer smaller

example
    (leftOwner rightOwner : Fin (terminalInterfacePorts candidate records).length)
    (leftGate rightGate : Fin replacementGates)
    (same : copyPosition candidate records replacement leftOwner leftGate =
      copyPosition candidate records replacement rightOwner rightGate) :
    leftOwner = rightOwner ∧ leftGate = rightGate :=
  copyPosition_injective candidate records replacement leftOwner rightOwner leftGate rightGate same

example (gate : Fin (expanded candidate records replacement).gateCount) :
    (∃ outside, gate = exteriorPosition candidate records replacement outside) ∨
    (∃ owner localGate, gate = copyPosition candidate records replacement owner localGate) :=
  expanded_gate_ownership candidate records replacement gate

end GeneralContracts

private def chainProgram : Program 1 3 :=
  .snoc (.snoc (.snoc .empty ⟨.input 0, .input 0⟩)
    ⟨.gate 0, .gate 0⟩) ⟨.gate 1, .gate 1⟩

private def chain : Candidate 1 3 7 :=
  Candidate.ofDirectWireWord chainProgram ⟨fun output =>
    match output.val with
    | 0 => .gate 0
    | 1 => .gate 1
    | 2 => .gate 2
    | 3 => .gate 0
    | 4 => .input 0
    | 5 => .constant false
    | _ => .constant true⟩

private def interleaved : List (TerminalPrimitiveRecord 1 3 7 0) :=
  [.gate 0, .gate 2]
private def chainSupport := extractTerminalSupport chain interleaved

example : chainSupport.boundary = [.input 0, .gate 1] := by decide
example : chainSupport.interface = [0, 2] := by decide

-- Preserve the M249 obstruction fixture; only the new causal construction changes.
private def cyclicReplacement :
    Candidate chainSupport.boundary.length 3 chainSupport.interface.length :=
  Candidate.ofDirectWireWord
    (.snoc (.snoc (.snoc .empty ⟨.input ⟨1, by decide⟩, .input ⟨1, by decide⟩⟩)
      ⟨.input ⟨1, by decide⟩, .gate 0⟩) ⟨.input ⟨0, by decide⟩, .gate 1⟩)
    ⟨fun output => if output.val = 0 then .gate 2 else .gate 0⟩

private theorem cyclic_agreement :
    cyclicReplacement.semantics = chainSupport.extractedCandidate.semantics := by
  funext input output
  exact equivalentBool_sound
    (by decide : equivalentBool cyclicReplacement chainSupport.extractedCandidate = true)
    input output

private def safeReplacement :
    Candidate chainSupport.boundary.length 2 chainSupport.interface.length :=
  Candidate.ofDirectWireWord
    (.snoc (.snoc .empty ⟨.input ⟨0, by decide⟩, .input ⟨0, by decide⟩⟩)
      ⟨.input ⟨1, by decide⟩, .input ⟨1, by decide⟩⟩)
    ⟨fun output => if output.val = 0 then .gate 0 else .gate 1⟩

private def savingProgram : Program 1 4 :=
  .snoc (.snoc (.snoc (.snoc .empty ⟨.input 0, .input 0⟩)
    ⟨.gate 0, .gate 0⟩) ⟨.gate 1, .gate 1⟩) ⟨.gate 0, .gate 0⟩

private def savingCandidate : Candidate 1 4 7 :=
  Candidate.ofDirectWireWord savingProgram ⟨fun output =>
    match output.val with
    | 0 => .gate 0
    | 1 => .gate 1
    | 2 => .gate 2
    | 3 => .gate 3
    | 4 => .gate 1
    | 5 => .input 0
    | _ => .constant false⟩

private def savingRecords : List (TerminalPrimitiveRecord 1 4 7 0) :=
  [.gate 1, .gate 3]
private def savingSupport := extractTerminalSupport savingCandidate savingRecords
private def smallerReplacement :
    Candidate savingSupport.boundary.length 1 savingSupport.interface.length :=
  Candidate.ofDirectWireWord (.snoc .empty
    ⟨.input ⟨0, by decide⟩, .input ⟨0, by decide⟩⟩) ⟨fun _ => .gate 0⟩

example : 1 < savingSupport.gateCount := by decide
example : (expanded savingCandidate savingRecords smallerReplacement).gateCount = 4 :=
  expanded_gateCount savingCandidate savingRecords smallerReplacement

example (input : Valuation 1) (output : Fin 7) :
    (expanded chain interleaved cyclicReplacement).candidate.semantics input output =
      chain.semantics input output :=
  expanded_semantics chain interleaved cyclicReplacement cyclic_agreement input output


private def emptyRecords : List (TerminalPrimitiveRecord 1 3 7 0) := []
private def fullRecords : List (TerminalPrimitiveRecord 1 3 7 0) :=
  [.gate 0, .gate 1, .gate 2]
private def fullSupport := extractTerminalSupport chain fullRecords
private def fullSmaller :
    Candidate fullSupport.boundary.length 1 fullSupport.interface.length :=
  Candidate.ofDirectWireWord (.snoc .empty
    ⟨.input ⟨0, by decide⟩, .input ⟨0, by decide⟩⟩)
    ⟨fun output => if output.val = 1 then .input ⟨0, by decide⟩ else .gate 0⟩
private def fullLarger :
    Candidate fullSupport.boundary.length 4 fullSupport.interface.length :=
  Candidate.ofDirectWireWord
    (.snoc (.snoc (.snoc (.snoc .empty
      ⟨.input ⟨0, by decide⟩, .input ⟨0, by decide⟩⟩)
      ⟨.constant false, .constant false⟩)
      ⟨.constant true, .constant true⟩) ⟨.constant false, .constant true⟩)
    ⟨fun output => if output.val = 1 then .input ⟨0, by decide⟩ else .gate 0⟩

private def zeroCandidate : Candidate 0 0 0 :=
  Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩
private def zeroRecords : List (TerminalPrimitiveRecord 0 0 0 0) := []
private def constantsCandidate : Candidate 0 0 2 :=
  Candidate.ofDirectWireWord .empty ⟨fun output => .constant (output.val != 0)⟩
private def constantsRecords : List (TerminalPrimitiveRecord 0 0 2 0) := []
private def unusedCandidate : Candidate 1 1 0 :=
  Candidate.ofDirectWireWord (.snoc .empty ⟨.input 0, .input 0⟩) ⟨Fin.elim0⟩
private def unusedRecords : List (TerminalPrimitiveRecord 1 1 0 0) := [.gate 0]
private def unusedReplacement :
    Candidate (terminalBoundaryPorts unusedCandidate.program unusedRecords).length 0
      (terminalInterfacePorts unusedCandidate unusedRecords).length :=
  Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩

-- Two distinct incoming primary ports and one retained producer. No unary bound.
private def andCore : Program 2 3 :=
  .snoc (.snoc (.snoc .empty ⟨.input 0, .input 1⟩)
    ⟨.input 0, .input 1⟩) ⟨.gate 0, .gate 1⟩
private def andExterior : Candidate 2 4 2 :=
  Candidate.ofDirectWireWord (.snoc andCore ⟨.gate 2, .gate 2⟩)
    ⟨fun output => if output.val = 0 then .gate 2 else .gate 3⟩
private def andRecords : List (TerminalPrimitiveRecord 2 4 2 0) :=
  [.gate 0, .gate 1, .gate 2]
private def andSupport := extractTerminalSupport andExterior andRecords
private def andReplacement :
    Candidate andSupport.boundary.length 2 andSupport.interface.length :=
  Candidate.ofDirectWireWord (.snoc (.snoc .empty
    ⟨.input ⟨0, by decide⟩, .input ⟨1, by decide⟩⟩) ⟨.gate 0, .gate 0⟩)
    ⟨fun _ => .gate 1⟩

private def andFull : Candidate 2 3 1 :=
  Candidate.ofDirectWireWord andCore ⟨fun _ => .gate 2⟩
private def andFullRecords : List (TerminalPrimitiveRecord 2 3 1 0) :=
  [.gate 0, .gate 1, .gate 2]
private def andFullReplacement :
    Candidate (terminalBoundaryPorts andFull.program andFullRecords).length 2
      (terminalInterfacePorts andFull andFullRecords).length := andReplacement

example : andSupport.boundary.length = 2 := by decide
example : andSupport.interface.length = 1 := by decide
example : andSupport.gateCount < 4 := by decide
example :
    (expanded andExterior andRecords andReplacement).gateCount < 4 :=
  single_interface_smaller andExterior andRecords andReplacement (by decide) (by decide)
example : ¬ (extractTerminalSupport andFull andFullRecords).gateCount < 3 := by decide


private def repeatedCarrier : WireCarrier 1 7 6 :=
  { implementation := chain.toImplementation
    source := fun field =>
      match field.val with
      | 0 => .gate ⟨2, by decide⟩
      | 1 => .gate ⟨0, by decide⟩
      | 2 => .gate ⟨2, by decide⟩
      | 3 => .input 0
      | 4 => .constant false
      | _ => .gate ⟨1, by decide⟩ }
private def repeatedRecords : List (TerminalPrimitiveRecord 1 3 13 0) :=
  [.gate 0, .gate 2]
private def repeatedReplacement :
    Candidate (terminalBoundaryPorts repeatedCarrier.exposed.candidate.program repeatedRecords).length 3
      (terminalInterfacePorts repeatedCarrier.exposed.candidate repeatedRecords).length :=
  cyclicReplacement

-- No ordinary output exposes these selected producers: the fields alone retain them.
private def fieldOnlyCarrier : WireCarrier 1 0 4 :=
  { implementation := (Candidate.ofDirectWireWord chainProgram ⟨Fin.elim0⟩).toImplementation
    source := fun field =>
      match field.val with
      | 0 => .gate ⟨0, by decide⟩
      | 1 => .gate ⟨2, by decide⟩
      | 2 => .gate ⟨2, by decide⟩
      | _ => .constant true }
private def fieldOnlyRecords : List (TerminalPrimitiveRecord 1 3 4 0) :=
  [.gate 0, .gate 2]
private def fieldOnlyReplacement :
    Candidate (terminalBoundaryPorts fieldOnlyCarrier.exposed.candidate.program fieldOnlyRecords).length 3
      (terminalInterfacePorts fieldOnlyCarrier.exposed.candidate fieldOnlyRecords).length :=
  cyclicReplacement
private def fieldOnlyWrong :
    Candidate (terminalBoundaryPorts fieldOnlyCarrier.exposed.candidate.program fieldOnlyRecords).length 0
      (terminalInterfacePorts fieldOnlyCarrier.exposed.candidate fieldOnlyRecords).length :=
  Candidate.ofDirectWireWord .empty ⟨fun _ => .constant false⟩

private theorem fieldOnly_agreement :
    fieldOnlyReplacement.semantics =
      (extractTerminalSupport fieldOnlyCarrier.exposed.candidate fieldOnlyRecords).extractedCandidate.semantics := by
  funext input output
  exact equivalentBool_sound
    (by decide : equivalentBool fieldOnlyReplacement
      (extractTerminalSupport fieldOnlyCarrier.exposed.candidate fieldOnlyRecords).extractedCandidate = true)
    input output

example (input : Valuation 1) (field : Fin 4) :
    (expandedCarrier fieldOnlyCarrier fieldOnlyRecords fieldOnlyReplacement).fieldValue input field =
      fieldOnlyCarrier.fieldValue input field :=
  expandedCarrier_field fieldOnlyCarrier fieldOnlyRecords fieldOnlyReplacement
    fieldOnly_agreement input field

example :
    (expandedCarrier repeatedCarrier repeatedRecords repeatedReplacement).source 0 =
      (expandedCarrier repeatedCarrier repeatedRecords repeatedReplacement).source 2 :=
  expandedCarrier_source_equal repeatedCarrier repeatedRecords repeatedReplacement 0 2 rfl

section CarrierContracts

variable {inputs outputs fields profileWidth replacementGates : Nat}
variable (carrier : WireCarrier inputs outputs fields)
variable (records : List (TerminalPrimitiveRecord inputs carrier.exposed.gateCount
  (outputs + fields) profileWidth))
variable (replacement : Candidate
  (terminalBoundaryPorts carrier.exposed.candidate.program records).length replacementGates
  (terminalInterfacePorts carrier.exposed.candidate records).length)
variable (sameOpen : replacement.semantics =
  (extractTerminalSupport carrier.exposed.candidate records).extractedCandidate.semantics)

example (input : Valuation inputs) (field : Fin fields) :
    (expandedCarrier carrier records replacement).fieldValue input field =
      carrier.fieldValue input field :=
  expandedCarrier_field carrier records replacement sameOpen input field

example (keep : Fin fields → Bool)
    (creation : WireObligationRestoration.R5Creation carrier keep)
    (input : Valuation inputs) :
    (expandedR5Creation carrier records replacement keep creation).originalSource.eval input
        ((expandedCarrier carrier records replacement).implementation.candidate.program.eval input) =
      creation.originalSource.eval input (carrier.implementation.candidate.program.eval input) :=
  expandedR5Creation_fullWitness carrier records replacement sameOpen keep creation input

end CarrierContracts

private def checkExpansion
    {inputs gates outputs profileWidth replacementGates : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (replacement : Candidate (terminalBoundaryPorts candidate.program records).length
      replacementGates (terminalInterfacePorts candidate records).length)
    (expectedCount : Nat) : IO Unit := do
  unless equivalentBool replacement (extractTerminalSupport candidate records).extractedCandidate do
    throw (IO.userError "fixture does not agree on the complete open interface")
  let actual := expanded candidate records replacement
  unless actual.gateCount == expectedCount do
    throw (IO.userError "physical copy charge drifted")
  let built := compiled candidate records replacement
  let positions := (List.finRange (nodeCount candidate records replacementGates)).map
    (fun node => (built.position node).val)
  for position in List.range expectedCount do
    unless positions.count position == 1 do
      throw (IO.userError "actual gate is unowned or multiply owned")
  let raw := graph candidate records replacement
  for consumer in List.finRange (nodeCount candidate records replacementGates) do
    for source in [(raw.gate consumer).left, (raw.gate consumer).right] do
      match source with
      | .gate producer =>
          unless decide (rank candidate records producer < rank candidate records consumer) do
            throw (IO.userError "actual dependency fails the source-derived rank")
      | _ => pure ()
  for tuple in allBoolTuples inputs do
    let input := tuple.toValuation
    let actualWord := (List.finRange outputs).map
      (fun output => actual.candidate.semantics input output)
    let originalWord := (List.finRange outputs).map
      (fun output => candidate.semantics input output)
    unless actualWord == originalWord do
      throw (IO.userError "complete ordered output changed")
  let localCost := (terminalInterfacePorts candidate records).length * replacementGates
  unless decide (actual.gateCount < gates) ==
      decide (localCost < (extractTerminalSupport candidate records).gateCount) do
    throw (IO.userError "unpaid local saving was treated as global saving")


private def checkCarrier
    {inputs outputs fields profileWidth replacementGates : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs carrier.exposed.gateCount
      (outputs + fields) profileWidth))
    (replacement : Candidate
      (terminalBoundaryPorts carrier.exposed.candidate.program records).length replacementGates
      (terminalInterfacePorts carrier.exposed.candidate records).length)
    (expectedCount : Nat) : IO Unit := do
  checkExpansion carrier.exposed.candidate records replacement expectedCount
  let actual := expandedCarrier carrier records replacement
  unless actual.implementation.gateCount == expectedCount do
    throw (IO.userError "unpacking hid a physical copy")
  for left in List.finRange fields do
    for right in List.finRange fields do
      if decide (carrier.source left = carrier.source right) then
        unless decide (actual.source left = actual.source right) do
          throw (IO.userError "repeated fields lost their shared literal wire")
  for tuple in allBoolTuples inputs do
    let input := tuple.toValuation
    for output in List.finRange outputs do
      unless actual.implementation.candidate.semantics input output ==
          carrier.implementation.candidate.semantics input output do
        throw (IO.userError "unpacking changed an ordinary output")
    for field in List.finRange fields do
      unless actual.fieldValue input field == carrier.fieldValue input field do
        throw (IO.userError "a complete computational field was changed")

private def checkCausalExpansions : IO Unit := do
  unless (ArbitrarySupportSplice.compile chain interleaved cyclicReplacement).isNone do
    throw (IO.userError "the inherited literal cyclic splice stopped failing closed")
  checkExpansion chain interleaved cyclicReplacement 7
  checkExpansion chain interleaved safeReplacement 5
  checkExpansion savingCandidate savingRecords smallerReplacement 4
  unless (expanded savingCandidate savingRecords smallerReplacement).gateCount ==
      savingCandidate.toImplementation.gateCount do
    throw (IO.userError "copy costs failed to cancel the apparent local saving")

  checkExpansion chain emptyRecords
    (extractTerminalSupport chain emptyRecords).extractedCandidate 3
  checkExpansion chain fullRecords fullSmaller 3
  checkExpansion chain fullRecords fullLarger 12
  checkExpansion zeroCandidate zeroRecords
    (extractTerminalSupport zeroCandidate zeroRecords).extractedCandidate 0
  checkExpansion constantsCandidate constantsRecords
    (extractTerminalSupport constantsCandidate constantsRecords).extractedCandidate 0
  checkExpansion unusedCandidate unusedRecords unusedReplacement 0
  checkExpansion andExterior andRecords andReplacement 3
  checkExpansion andFull andFullRecords andFullReplacement 2
  unless fullSupport.interface.length == 3 do
    throw (IO.userError "distinct but semantically equal producers were merged")
  unless decide ((extractTerminalSupport andFull andFullRecords).gateCount = 3) do
    throw (IO.userError "strict saving was confused with proper support")
  for tuple in allBoolTuples chainSupport.boundary.length do
    let input := tuple.toValuation
    unless maskedBoundary chain interleaved ⟨0, by decide⟩ input ⟨0, by decide⟩ ==
        input ⟨0, by decide⟩ do
      throw (IO.userError "an actual primary boundary input was masked")
    unless maskedBoundary chain interleaved ⟨0, by decide⟩ input ⟨1, by decide⟩ == false do
      throw (IO.userError "a later gate-valued boundary was wired backwards")
    unless maskedBoundary chain interleaved ⟨1, by decide⟩ input ⟨1, by decide⟩ ==
        input ⟨1, by decide⟩ do
      throw (IO.userError "an earlier required gate-valued boundary was masked")

  checkCarrier repeatedCarrier repeatedRecords repeatedReplacement 7
  checkCarrier fieldOnlyCarrier fieldOnlyRecords fieldOnlyReplacement 7
  unless (terminalInterfacePorts fieldOnlyCarrier.exposed.candidate fieldOnlyRecords).length == 2 do
    throw (IO.userError "fields-only producers disappeared from the physical interface")
  unless !(equivalentBool fieldOnlyWrong
      (extractTerminalSupport fieldOnlyCarrier.exposed.candidate fieldOnlyRecords).extractedCandidate) do
    throw (IO.userError "output-only agreement was mistaken for full local agreement")
  unless (compile fieldOnlyCarrier.exposed.candidate fieldOnlyRecords fieldOnlyWrong).isSome do
    throw (IO.userError "constructor incorrectly requires a semantic certificate")
  let wrong := expandedCarrier fieldOnlyCarrier fieldOnlyRecords fieldOnlyWrong
  unless !(wrong.fieldValue (fun _ => false) 0 ==
      fieldOnlyCarrier.fieldValue (fun _ => false) 0) do
    throw (IO.userError "wrong full-field replacement failed to expose its semantic mismatch")
  let keep : Fin 4 → Bool := fun _ => false
  let creation := WireObligationRestoration.createR5 fieldOnlyCarrier keep 2 rfl
  let rebound := expandedR5Creation fieldOnlyCarrier fieldOnlyRecords fieldOnlyReplacement keep creation
  let restored := expandedCarrier fieldOnlyCarrier fieldOnlyRecords fieldOnlyReplacement
  unless rebound.coordinate == creation.coordinate do
    throw (IO.userError "R5 transport changed the original lost-wire coordinate")
  for value in [false, true] do
    unless rebound.originalSource.eval (fun _ => value)
        (restored.implementation.candidate.program.eval (fun _ => value)) ==
      creation.originalSource.eval (fun _ => value)
        (fieldOnlyCarrier.implementation.candidate.program.eval (fun _ => value)) do
      throw (IO.userError "R5 transport lost the original full source value")
  IO.println "wire-causal-expansion-regression: 13 constructor/carrier cases; quotient firewall and R5 source transport checked"

#eval checkCausalExpansions

end PNP.DirectWire.WireCausalExpansionRegression

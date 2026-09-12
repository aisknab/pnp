import PNP

namespace PNP.DirectWire

example {inputs nodes : Nat} (graph : RawNandGraph inputs nodes) :
    (∃ compiled, compileRawNandGraph graph = some compiled) ↔
      WellFounded graph.Depends :=
  compileRawNandGraph_success_iff graph

example {inputs nodes : Nat} (graph : RawNandGraph inputs nodes) :
    compileRawNandGraph graph = none ↔ ¬WellFounded graph.Depends :=
  compileRawNandGraph_failure_iff graph

example {inputs nodes : Nat} {graph : RawNandGraph inputs nodes}
    (compiled : CompiledRawNandGraph graph) (left right : Fin nodes)
    (same : compiled.position left = compiled.position right) : left = right :=
  compiled.position_injective left right same

example {inputs nodes outputs : Nat} {graph : RawNandGraph inputs nodes}
    (compiled : CompiledRawNandGraph graph) (word : DirectWireWord inputs nodes outputs) :
    (compiled.candidate word).toImplementation.gateCount = nodes :=
  compiled.candidate_gateCount word

example {inputs nodes outputs : Nat} {graph : RawNandGraph inputs nodes}
    (compiled : CompiledRawNandGraph graph) (word : DirectWireWord inputs nodes outputs)
    (input : Valuation inputs) (values : Valuation nodes)
    (equations : graph.Solution input values) (output : Fin outputs) :
    (compiled.candidate word).semantics input output =
      (word.source output).eval input values :=
  compiled.candidate_semantics word input values equations output

example {inputs nodes : Nat} {graph : RawNandGraph inputs nodes}
    (stop : RawNandCompilationStop graph) (node : Fin nodes)
    (member : node ∈ stop.state.remaining) :
    ∃ producer, producer ∈ stop.state.remaining ∧ graph.Depends producer node :=
  stop.unresolved_predecessor node member

private def reverseNamedGraph : RawNandGraph 1 3 :=
  { gate := fun node =>
      match node.val with
      | 0 => ⟨.gate ⟨2, by decide⟩, .gate ⟨1, by decide⟩⟩
      | 1 => ⟨.input ⟨0, by decide⟩, .input ⟨0, by decide⟩⟩
      | _ => ⟨.gate ⟨1, by decide⟩, .gate ⟨1, by decide⟩⟩ }

private def reverseNamedOutputs : DirectWireWord 1 3 6 :=
  ⟨fun output =>
    match output.val with
    | 0 => .gate ⟨0, by decide⟩
    | 1 => .gate ⟨1, by decide⟩
    | 2 => .gate ⟨0, by decide⟩
    | 3 => .input ⟨0, by decide⟩
    | 4 => .constant false
    | _ => .gate ⟨2, by decide⟩⟩

private def disconnectedGraph : RawNandGraph 0 2 :=
  ⟨fun _ => ⟨.constant false, .constant true⟩⟩

private def emptyRawGraph : RawNandGraph 0 0 := ⟨Fin.elim0⟩

private def emptyRawOutputs : DirectWireWord 0 0 2 :=
  ⟨fun output => .constant (output.val != 0)⟩

/-- This cyclic graph has a solution: its sole value is true. Cyclic wiring
    must nevertheless be rejected, independently of semantic consistency. -/
private def selfCycleGraph : RawNandGraph 0 1 :=
  ⟨fun node => ⟨.gate node, .constant false⟩⟩

private def mutualCycleGraph : RawNandGraph 0 2 :=
  ⟨fun node =>
    if node.val = 0 then ⟨.gate ⟨1, by decide⟩, .constant true⟩
    else ⟨.gate ⟨0, by decide⟩, .constant true⟩⟩

private def partlyReadyGraph : RawNandGraph 0 3 :=
  ⟨fun node =>
    match node.val with
    | 0 => ⟨.constant false, .constant false⟩
    | 1 => ⟨.gate ⟨2, by decide⟩, .constant true⟩
    | _ => ⟨.gate ⟨1, by decide⟩, .constant true⟩⟩

example : selfCycleGraph.Solution (fun index => Fin.elim0 index) (fun _ => true) := by
  intro node
  rfl

example : compileRawNandGraph selfCycleGraph = none := by
  apply (compileRawNandGraph_failure_iff selfCycleGraph).2
  intro wellFounded
  have impossible (node : Fin 1) (accessible : Acc selfCycleGraph.Depends node) :
      False := by
    induction accessible with
    | intro node previous ih =>
        exact ih node (Or.inl rfl)
  exact impossible ⟨0, by decide⟩ (wellFounded.apply ⟨0, by decide⟩)

private def checkRawGraphCompilation : IO Unit := do
  let some reordered := compileRawNandGraph reverseNamedGraph
    | throw (IO.userError "acyclic reverse-named graph was rejected")
  unless reordered.count == 3 do
    throw (IO.userError "reordered graph has wrong physical node count")
  unless (List.finRange 3).map (fun node => (reordered.position node).val) == [2, 0, 1] do
    throw (IO.userError "source-derived canonical execution order drifted")
  for value in [false, true] do
    let actual := (List.finRange 6).map
      (fun output => (reordered.candidate reverseNamedOutputs).semantics (fun _ => value) output)
    unless actual == [true, !value, true, value, false, value] do
      throw (IO.userError "complete ordered-output semantics drifted")

  let some disconnected := compileRawNandGraph disconnectedGraph
    | throw (IO.userError "disconnected acyclic nodes were rejected")
  unless disconnected.count == 2 do
    throw (IO.userError "compiler silently pruned an unused node")
  unless (List.finRange 2).map (fun node => (disconnected.position node).val) == [0, 1] do
    throw (IO.userError "distinct identical nodes were silently merged")

  let some empty := compileRawNandGraph emptyRawGraph
    | throw (IO.userError "empty graph was rejected")
  unless empty.count == 0 do
    throw (IO.userError "empty graph allocated a gate")
  let emptyValues := (List.finRange 2).map
    (fun output => (empty.candidate emptyRawOutputs).semantics (fun index => Fin.elim0 index) output)
  unless emptyValues == [false, true] do
    throw (IO.userError "zero-input constant outputs drifted")

  unless (compileRawNandGraph selfCycleGraph).isNone do
    throw (IO.userError "semantic consistency bypassed self-cycle rejection")
  unless (compileRawNandGraph mutualCycleGraph).isNone do
    throw (IO.userError "mutual source cycle was accepted")
  unless (compileRawNandGraph partlyReadyGraph).isNone do
    throw (IO.userError "partial progress hid a remaining source cycle")
  let stop := runRawNandCompilation (RawNandCompilationState.initial partlyReadyGraph)
  unless stop.state.count == 1 &&
      stop.state.remaining.map Fin.val == [1, 2] do
    throw (IO.userError "stuck remainder did not identify the actual unresolved nodes")
  IO.println "M249_RAW_NAND_COMPILER_RUNTIME_FIXTURES_GREEN"

#eval checkRawGraphCompilation

namespace ArbitrarySpliceRegression

open ArbitrarySupportSplice

example {inputs gates outputs profileWidth replacementGates : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (replacement : Candidate (terminalBoundaryPorts candidate.program records).length
      replacementGates (terminalInterfacePorts candidate records).length)
    (equivalent : replacement.semantics =
      (extractTerminalSupport candidate records).extractedCandidate.semantics)
    (compiled : CompiledRawNandGraph (graph candidate records replacement))
    (input : Valuation inputs) (output : Fin outputs) :
    (result candidate records replacement compiled).semantics input output =
      candidate.semantics input output :=
  result_semantics candidate records replacement equivalent compiled input output

example {inputs gates outputs profileWidth replacementGates : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (replacement : Candidate (terminalBoundaryPorts candidate.program records).length
      replacementGates (terminalInterfacePorts candidate records).length)
    (compiled : CompiledRawNandGraph (graph candidate records replacement)) :
    (result candidate records replacement compiled).toImplementation.gateCount +
      (extractTerminalSupport candidate records).gateCount = gates + replacementGates :=
  result_exact_accounting candidate records replacement compiled

example {inputs gates outputs profileWidth replacementGates : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (replacement : Candidate (terminalBoundaryPorts candidate.program records).length
      replacementGates (terminalInterfacePorts candidate records).length)
    (smaller : replacementGates < (extractTerminalSupport candidate records).gateCount)
    (compiled : CompiledRawNandGraph (graph candidate records replacement)) :
    (result candidate records replacement compiled).toImplementation.gateCount < gates :=
  result_strict_gain candidate records replacement smaller compiled

example {inputs gates outputs profileWidth replacementGates : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (replacement : Candidate
      (terminalBoundaryPorts candidate.program (terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed)).length replacementGates
      (terminalInterfacePorts candidate (terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed)).length) :
    ∃ compiled, compile candidate (terminalSaturateRecords
      (terminalCandidateSaturationSystem candidate model) seed) replacement = some compiled :=
  production_compiles candidate model seed replacement

private def chainProgram : Program 1 3 :=
  .snoc (.snoc (.snoc .empty ⟨.input ⟨0, by decide⟩, .input ⟨0, by decide⟩⟩) ⟨.gate 0, .gate 0⟩)
    ⟨.gate 1, .gate 1⟩

private def chain : Candidate 1 3 7 :=
  Candidate.ofDirectWireWord chainProgram ⟨fun output =>
    match output.val with
    | 0 => .gate 0
    | 1 => .gate 1
    | 2 => .gate 2
    | 3 => .gate 0
    | 4 => .input ⟨0, by decide⟩
    | 5 => .constant false
    | _ => .constant true⟩

private def interleaved : List (TerminalPrimitiveRecord 1 3 7 0) := [.gate 0, .gate 2]
private def chainSupport := extractTerminalSupport chain interleaved

example : chainSupport.boundary = [.input ⟨0, by decide⟩, .gate 1] := by decide
example : chainSupport.interface = [0, 2] := by decide
example : exterior interleaved = [1] := by decide

private def safeReplacement : Candidate chainSupport.boundary.length 2 chainSupport.interface.length :=
  Candidate.ofDirectWireWord
    (.snoc (.snoc .empty ⟨.input ⟨0, by decide⟩, .input ⟨0, by decide⟩⟩) ⟨.input ⟨1, by decide⟩, .input ⟨1, by decide⟩⟩)
    ⟨fun output => if output.val = 0 then .gate 0 else .gate 1⟩

private theorem safe_equivalent :
    safeReplacement.semantics = chainSupport.extractedCandidate.semantics := by
  funext input output
  exact equivalentBool_sound
    (by decide : equivalentBool safeReplacement chainSupport.extractedCandidate = true) input output

/-- Same open function as the support, but literal rewiring introduces a cycle.
    This is not a claim about the unconstructed full-carrier premises. -/
private def cyclicReplacement : Candidate chainSupport.boundary.length 3 chainSupport.interface.length :=
  Candidate.ofDirectWireWord
    (.snoc (.snoc (.snoc .empty ⟨.input ⟨1, by decide⟩, .input ⟨1, by decide⟩⟩)
      ⟨.input ⟨1, by decide⟩, .gate 0⟩) ⟨.input ⟨0, by decide⟩, .gate 1⟩)
    ⟨fun output => if output.val = 0 then .gate 2 else .gate 0⟩

private theorem cyclic_equivalent :
    cyclicReplacement.semantics = chainSupport.extractedCandidate.semantics := by
  funext input output
  exact equivalentBool_sound
    (by decide : equivalentBool cyclicReplacement chainSupport.extractedCandidate = true) input output

private def cyclicGraph := graph chain interleaved cyclicReplacement

example : compile chain interleaved cyclicReplacement = none := by
  apply (compile_failure_iff chain interleaved cyclicReplacement).2
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

private def savingProgram : Program 1 4 :=
  .snoc (.snoc (.snoc (.snoc .empty ⟨.input ⟨0, by decide⟩, .input ⟨0, by decide⟩⟩)
    ⟨.gate 0, .gate 0⟩) ⟨.gate 1, .gate 1⟩) ⟨.gate 0, .gate 0⟩

private def savingCandidate : Candidate 1 4 7 :=
  Candidate.ofDirectWireWord savingProgram ⟨fun output =>
    match output.val with
    | 0 => .gate 0
    | 1 => .gate 1
    | 2 => .gate 2
    | 3 => .gate 3
    | 4 => .gate 1
    | 5 => .input ⟨0, by decide⟩
    | _ => .constant false⟩

private def savingRecords : List (TerminalPrimitiveRecord 1 4 7 0) := [.gate 1, .gate 3]
private def savingSupport := extractTerminalSupport savingCandidate savingRecords

example : savingSupport.boundary = [.gate 0] := by decide
example : savingSupport.interface = [1, 3] := by decide

private def smallerReplacement : Candidate savingSupport.boundary.length 1 savingSupport.interface.length :=
  Candidate.ofDirectWireWord (.snoc .empty ⟨.input ⟨0, by decide⟩, .input ⟨0, by decide⟩⟩) ⟨fun _ => .gate 0⟩

private theorem smaller_equivalent :
    smallerReplacement.semantics = savingSupport.extractedCandidate.semantics := by
  funext input output
  exact equivalentBool_sound
    (by decide : equivalentBool smallerReplacement savingSupport.extractedCandidate = true) input output

/-- Empty profile is only a physical regression, not a derived manuscript carrier. -/
private def physicalModel {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs) :
    TerminalCandidateSaturationModel (profileWidth := 0) candidate :=
  { profileSystem := { role := Fin.elim0, observe := fun _ => Fin.elim0 }
    projection := { keep := Fin.elim0 }
    observe := fun _ => Fin.elim0 }

private def productionRecords := terminalSaturateRecords
  (terminalCandidateSaturationSystem chain (physicalModel chain))
  ([.gate 2] : List (TerminalPrimitiveRecord 1 3 7 0))
private def productionSupport := extractTerminalSupport chain productionRecords

example : productionSupport.selectedGates = [0, 1, 2] := by decide
example : productionSupport.boundary = [.input ⟨0, by decide⟩] := by decide
example : productionSupport.interface = [0, 1, 2] := by decide

private def productionSmaller : Candidate productionSupport.boundary.length 1 productionSupport.interface.length :=
  Candidate.ofDirectWireWord (.snoc .empty ⟨.input ⟨0, by decide⟩, .input ⟨0, by decide⟩⟩)
    ⟨fun output => if output.val = 1 then .input ⟨0, by decide⟩ else .gate 0⟩

private def productionLarger : Candidate productionSupport.boundary.length 4 productionSupport.interface.length :=
  Candidate.ofDirectWireWord
    (.snoc (.snoc (.snoc (.snoc .empty ⟨.input ⟨0, by decide⟩, .input ⟨0, by decide⟩⟩)
      ⟨.constant false, .constant false⟩)
      ⟨.constant true, .constant true⟩) ⟨.constant false, .constant true⟩)
    ⟨fun output => if output.val = 1 then .input ⟨0, by decide⟩ else .gate 0⟩

private theorem productionSmaller_equivalent :
    productionSmaller.semantics = productionSupport.extractedCandidate.semantics := by
  funext input output
  exact equivalentBool_sound
    (by decide : equivalentBool productionSmaller productionSupport.extractedCandidate = true) input output

private theorem productionLarger_equivalent :
    productionLarger.semantics = productionSupport.extractedCandidate.semantics := by
  funext input output
  exact equivalentBool_sound
    (by decide : equivalentBool productionLarger productionSupport.extractedCandidate = true) input output

private def emptyRecords : List (TerminalPrimitiveRecord 1 3 7 0) := []
private def emptySupport := extractTerminalSupport chain emptyRecords

private def zeroCandidate : Candidate 0 0 0 :=
  Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩
private def zeroRecords : List (TerminalPrimitiveRecord 0 0 0 0) := []
private def zeroSupport := extractTerminalSupport zeroCandidate zeroRecords

private def constantsCandidate : Candidate 0 0 2 :=
  Candidate.ofDirectWireWord .empty ⟨fun output => .constant (output.val != 0)⟩
private def constantsRecords : List (TerminalPrimitiveRecord 0 0 2 0) := []
private def constantsSupport := extractTerminalSupport constantsCandidate constantsRecords

private def unusedCandidate : Candidate 1 1 0 :=
  Candidate.ofDirectWireWord (.snoc .empty ⟨.input ⟨0, by decide⟩, .input ⟨0, by decide⟩⟩) ⟨Fin.elim0⟩
private def unusedRecords : List (TerminalPrimitiveRecord 1 1 0 0) := [.gate 0]
private def unusedSupport := extractTerminalSupport unusedCandidate unusedRecords
private def unusedReplacement : Candidate unusedSupport.boundary.length 0 unusedSupport.interface.length :=
  Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩

example (input : Valuation 1) :
    cyclicGraph.Solution input (values chain interleaved cyclicReplacement input) :=
  values_solution chain interleaved cyclicReplacement cyclic_equivalent input

example (compiled : CompiledRawNandGraph (graph savingCandidate savingRecords smallerReplacement)) :
    (result savingCandidate savingRecords smallerReplacement compiled).toImplementation.gateCount < 4 :=
  result_strict_gain savingCandidate savingRecords smallerReplacement (by decide) compiled

private def checkSplice
    {inputs gates outputs profileWidth replacementGates : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (replacement : Candidate (terminalBoundaryPorts candidate.program records).length
      replacementGates (terminalInterfacePorts candidate records).length)
    (expectedCount : Nat) (expectedPositions : Option (List Nat) := none) : IO Unit := do
  let some compiled := compile candidate records replacement
    | throw (IO.userError "valid literal support replacement was rejected")
  unless compiled.count == expectedCount do
    throw (IO.userError "literal splice physical gate count drifted")
  if let some expected := expectedPositions then
    let positions := (List.finRange ((exterior records).length + replacementGates)).map
      (fun node => (compiled.position node).val)
    unless positions == expected do
      throw (IO.userError "actual interleaved splice ordering drifted")
  for tuple in allBoolTuples inputs do
    let input := tuple.toValuation
    let actual := (List.finRange outputs).map
      (fun output => (result candidate records replacement compiled).semantics input output)
    let expected := (List.finRange outputs).map
      (fun output => candidate.semantics input output)
    unless actual == expected do
      throw (IO.userError "literal splice changed a global ordered output")

private def checkArbitrarySplices : IO Unit := do
  checkSplice chain interleaved safeReplacement 3 (some [1, 0, 2])
  unless (compile chain interleaved cyclicReplacement).isNone do
    throw (IO.userError "open Boolean equivalence bypassed literal-cycle rejection")
  checkSplice savingCandidate savingRecords smallerReplacement 3 (some [0, 2, 1])
  checkSplice chain productionRecords productionSmaller 1
  checkSplice chain productionRecords productionLarger 4 (some [0, 1, 2, 3])
  checkSplice chain emptyRecords emptySupport.extractedCandidate 3 (some [0, 1, 2])
  checkSplice zeroCandidate zeroRecords zeroSupport.extractedCandidate 0 (some [])
  checkSplice constantsCandidate constantsRecords constantsSupport.extractedCandidate 0 (some [])
  checkSplice unusedCandidate unusedRecords unusedReplacement 0 (some [])
  IO.println "M249_ARBITRARY_SUPPORT_SPLICE_RUNTIME_FIXTURES_GREEN"

#eval checkArbitrarySplices

end ArbitrarySpliceRegression

end PNP.DirectWire

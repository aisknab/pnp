/-
Copyright (c) 2026 PNP Labs.

Finite linear-block materialization for the grammar-only locked-NAND target
emitter.

A block is a closed list of primitive requests.  Successful compilation
copies each selected local rule table into its own structural graph namespace
and connects adjacent accept endpoints with literal nine-symbol bridges.
-/

import PNP.Concrete.LockedNANDTargetEmitterPrimitiveCompiler
import PNP.Concrete.WorkMachineProgramPath

namespace PNP.Concrete.LockedNAND.TargetEmitterBlockCompiler

open PNP.Concrete
open WorkMachineProgramGraph
open TargetEmitterPrimitiveCompiler
open TargetEmitterPlan

/-- Odd graph names are reserved for compiled block nodes.  The prefix-code
payload makes the pair `(blockCode, index)` injective. -/
def blockNodeName (blockCode index : Nat) : Nat :=
  2 * payloadState blockCode index + 1

theorem blockNodeName_injective
    {leftCode rightCode leftIndex rightIndex : Nat}
    (equality :
      blockNodeName leftCode leftIndex =
        blockNodeName rightCode rightIndex) :
    leftCode = rightCode ∧ leftIndex = rightIndex := by
  unfold blockNodeName at equality
  have payloadEquality :
      payloadState leftCode leftIndex =
        payloadState rightCode rightIndex := by
    omega
  exact payloadState_injective payloadEquality

theorem blockNodeName_odd (blockCode index : Nat) :
    blockNodeName blockCode index % 2 = 1 := by
  unfold blockNodeName
  omega

def machineRef (blockCode index : Nat)
    (program : WorkMachine) : NodeRef :=
  { name := blockNodeName blockCode index
    startState := program.startState }

def nodesFrom (blockCode : Nat) :
    Nat → List WorkMachine → Endpoint → List Node
  | _, [], _ => []
  | index, program :: rest, continuation =>
      let next :=
        match rest with
        | [] => continuation
        | nextProgram :: _ =>
            .node (machineRef blockCode (index + 1) nextProgram)
      { name := blockNodeName blockCode index
        program := program
        onAccept := next
        onReject := .reject } ::
      nodesFrom blockCode (index + 1) rest continuation

def entryRef? (blockCode : Nat) :
    List WorkMachine → Option NodeRef
  | [] => none
  | program :: _ => some (machineRef blockCode 0 program)

def blockMachines (primitives : List Primitive) :
    List WorkMachine :=
  (compileProgram primitives).getD []

theorem blockMachines_eq_of_compiled
    (primitives : List Primitive) (programs : List WorkMachine)
    (compiled : compileProgram primitives = some programs) :
    blockMachines primitives = programs := by
  unfold blockMachines
  rw [compiled]
  rfl

def blockNodes (blockCode : Nat)
    (primitives : List Primitive) (continuation : Endpoint) :
    List Node :=
  nodesFrom blockCode 0 (blockMachines primitives) continuation

def blockEntry? (blockCode : Nat)
    (primitives : List Primitive) : Option NodeRef :=
  entryRef? blockCode (blockMachines primitives)

/-- Closed controller blocks prove separately that this default is
unreachable.  Keeping it explicit makes accidental empty compilation route to
a unique non-controller reference instead of silently selecting a real node. -/
def invalidEntryRef : NodeRef :=
  { name := 0
    startState := 0 }

def blockEntry (blockCode : Nat)
    (primitives : List Primitive) : NodeRef :=
  (blockEntry? blockCode primitives).getD invalidEntryRef

theorem nodesFrom_length (blockCode index : Nat)
    (programs : List WorkMachine) (continuation : Endpoint) :
    (nodesFrom blockCode index programs continuation).length =
      programs.length := by
  induction programs generalizing index with
  | nil =>
      rfl
  | cons program rest inductionHypothesis =>
      simp only [nodesFrom, List.length_cons]
      rw [inductionHypothesis]

theorem blockNodes_length (blockCode : Nat)
    (primitives : List Primitive) (continuation : Endpoint) :
    (blockNodes blockCode primitives continuation).length =
      (blockMachines primitives).length := by
  exact nodesFrom_length blockCode 0
    (blockMachines primitives) continuation

theorem blockMachines_length_of_compiled
    (primitives : List Primitive) (programs : List WorkMachine)
    (compiled : compileProgram primitives = some programs) :
    (blockMachines primitives).length = primitives.length := by
  have lengthEq :
      programs.length = primitives.length := by
    induction primitives generalizing programs with
    | nil =>
        change some [] = some programs at compiled
        have programsEq : programs = [] :=
          (Option.some.inj compiled).symm
        subst programs
        rfl
    | cons primitive rest inductionHypothesis =>
        cases machineEq : primitiveMachine primitive with
        | none =>
            simp [compileProgram, machineEq] at compiled
        | some program =>
            cases tailEq : compileProgram rest with
            | none =>
                simp [compileProgram, machineEq, tailEq] at compiled
            | some tail =>
                simp only [compileProgram, machineEq, tailEq]
                  at compiled
                have programsEq :
                    programs = program :: tail :=
                  (Option.some.inj compiled).symm
                subst programs
                simp only [List.length_cons]
                rw [inductionHypothesis tail tailEq]
  unfold blockMachines
  rw [compiled]
  exact lengthEq

theorem blockNodes_length_of_compiled
    (blockCode : Nat) (primitives : List Primitive)
    (programs : List WorkMachine) (continuation : Endpoint)
    (compiled : compileProgram primitives = some programs) :
    (blockNodes blockCode primitives continuation).length =
      primitives.length := by
  rw [blockNodes_length,
    blockMachines_length_of_compiled primitives programs compiled]

/-! ### Structural certificates for compiled blocks -/

theorem nodesFrom_wellFormed_of_compiled
    (blockCode index : Nat) (primitives : List Primitive)
    (programs : List WorkMachine) (continuation : Endpoint)
    (compiled : compileProgram primitives = some programs) :
    ∀ node,
      node ∈ nodesFrom blockCode index programs continuation →
        node.WellFormed := by
  induction primitives generalizing index programs with
  | nil =>
      change some [] = some programs at compiled
      have programsEq : programs = [] :=
        (Option.some.inj compiled).symm
      subst programs
      intro node member
      contradiction
  | cons primitive rest inductionHypothesis =>
      cases machineEq : primitiveMachine primitive with
      | none =>
          simp [compileProgram, machineEq] at compiled
      | some program =>
          cases tailEq : compileProgram rest with
          | none =>
              simp [compileProgram, machineEq, tailEq] at compiled
          | some tail =>
              simp only [compileProgram, machineEq, tailEq]
                at compiled
              have programsEq :
                  programs = program :: tail :=
                (Option.some.inj compiled).symm
              subst programs
              intro node member
              simp only [nodesFrom, List.mem_cons] at member
              rcases member with nodeEq | tailMember
              · subst node
                apply primitiveMachine_wellFormed_of_eq
                  primitive program machineEq
              · exact inductionHypothesis
                  (index := index + 1)
                  tail tailEq node tailMember

theorem blockNodes_wellFormed_of_compiled
    (blockCode : Nat) (primitives : List Primitive)
    (programs : List WorkMachine) (continuation : Endpoint)
    (compiled : compileProgram primitives = some programs) :
    ∀ node, node ∈ blockNodes blockCode primitives continuation →
      node.WellFormed := by
  intro node member
  unfold blockNodes blockMachines at member
  rw [compiled] at member
  exact nodesFrom_wellFormed_of_compiled
    blockCode 0 primitives programs continuation compiled
    node member

theorem nodesFrom_member_name
    (blockCode index : Nat) (programs : List WorkMachine)
    (continuation : Endpoint) (node : Node)
    (member :
      node ∈ nodesFrom blockCode index programs continuation) :
    ∃ offset < programs.length,
      node.name = blockNodeName blockCode (index + offset) := by
  induction programs generalizing index with
  | nil =>
      contradiction
  | cons program rest inductionHypothesis =>
      simp only [nodesFrom, List.mem_cons] at member
      rcases member with nodeEq | tailMember
      · subst node
        exact ⟨0, by simp, by simp [blockNodeName]⟩
      · rcases inductionHypothesis (index := index + 1)
            tailMember with
          ⟨offset, offsetBound, nameEq⟩
        refine ⟨offset + 1, by simp; omega, ?_⟩
        rw [nameEq]
        congr 1
        omega

theorem nodesFrom_names_pairwise
    (blockCode index : Nat) (programs : List WorkMachine)
    (continuation : Endpoint) :
    (nodesFrom blockCode index programs continuation).Pairwise
      (fun left right => left.name ≠ right.name) := by
  induction programs generalizing index with
  | nil =>
      exact List.Pairwise.nil
  | cons program rest inductionHypothesis =>
      simp only [nodesFrom]
      apply List.pairwise_cons.mpr
      constructor
      · intro right rightMember nameEq
        rcases nodesFrom_member_name blockCode (index + 1)
            rest continuation right rightMember with
          ⟨offset, _offsetBound, rightName⟩
        have parts := blockNodeName_injective
          (nameEq.trans rightName)
        omega
      · exact inductionHypothesis (index := index + 1)

theorem blockNodes_names_pairwise
    (blockCode : Nat) (primitives : List Primitive)
    (continuation : Endpoint) :
    (blockNodes blockCode primitives continuation).Pairwise
      (fun left right => left.name ≠ right.name) :=
  nodesFrom_names_pairwise blockCode 0
    (blockMachines primitives) continuation

theorem nodesFrom_cross_names
    (leftCode rightCode leftIndex rightIndex : Nat)
    (leftPrograms rightPrograms : List WorkMachine)
    (leftContinuation rightContinuation : Endpoint)
    (codeNe : leftCode ≠ rightCode) :
    ∀ left,
      left ∈ nodesFrom leftCode leftIndex
        leftPrograms leftContinuation →
      ∀ right,
        right ∈ nodesFrom rightCode rightIndex
          rightPrograms rightContinuation →
        left.name ≠ right.name := by
  intro left leftMember right rightMember nameEq
  rcases nodesFrom_member_name leftCode leftIndex
      leftPrograms leftContinuation left leftMember with
    ⟨leftOffset, _leftBound, leftName⟩
  rcases nodesFrom_member_name rightCode rightIndex
      rightPrograms rightContinuation right rightMember with
    ⟨rightOffset, _rightBound, rightName⟩
  have parts := blockNodeName_injective
    (leftName.symm.trans (nameEq.trans rightName))
  exact codeNe parts.1

theorem blockNodes_cross_names
    (leftCode rightCode : Nat)
    (leftPrimitives rightPrimitives : List Primitive)
    (leftContinuation rightContinuation : Endpoint)
    (codeNe : leftCode ≠ rightCode) :
    ∀ left,
      left ∈ blockNodes leftCode leftPrimitives leftContinuation →
      ∀ right,
        right ∈ blockNodes rightCode rightPrimitives
          rightContinuation →
        left.name ≠ right.name :=
  nodesFrom_cross_names leftCode rightCode 0 0
    (blockMachines leftPrimitives)
    (blockMachines rightPrimitives)
    leftContinuation rightContinuation codeNe

def entryEndpoint (blockCode index : Nat)
    (programs : List WorkMachine)
    (continuation : Endpoint) : Endpoint :=
  match programs with
  | [] => continuation
  | program :: _ => .node (machineRef blockCode index program)

theorem blockEntry_eq_entryEndpoint_of_compiled
    (blockCode : Nat) (primitives : List Primitive)
    (programs : List WorkMachine) (continuation : Endpoint)
    (compiled : compileProgram primitives = some programs)
    (nonempty : programs ≠ []) :
    (.node (blockEntry blockCode primitives) : Endpoint) =
      entryEndpoint blockCode 0 programs continuation := by
  cases programs with
  | nil =>
      contradiction
  | cons program rest =>
      unfold blockEntry blockEntry? blockMachines
      rw [compiled]
      rfl

theorem nodesFrom_entry_resolves
    (universeNodes : List Node) (blockCode index : Nat)
    (programs : List WorkMachine) (continuation : Endpoint)
    (included :
      ∀ node,
          node ∈ nodesFrom blockCode index programs continuation →
          node ∈ universeNodes)
    (continuationResolves :
      Endpoint.Resolves universeNodes continuation) :
    Endpoint.Resolves universeNodes
      (entryEndpoint blockCode index programs continuation) := by
  cases programs with
  | nil =>
      exact continuationResolves
  | cons program rest =>
      let node : Node :=
        { name := blockNodeName blockCode index
          program := program
          onAccept :=
            entryEndpoint blockCode (index + 1)
              rest continuation
          onReject := .reject }
      refine ⟨node, ?_, rfl, rfl⟩
      apply included node
      simp [nodesFrom, entryEndpoint, node, machineRef]

theorem nodesFrom_endpoints_resolve
    (universeNodes : List Node) (blockCode index : Nat)
    (programs : List WorkMachine) (continuation : Endpoint)
    (included :
      ∀ node,
          node ∈ nodesFrom blockCode index programs continuation →
          node ∈ universeNodes)
    (continuationResolves :
      Endpoint.Resolves universeNodes continuation) :
    ∀ node,
      node ∈ nodesFrom blockCode index programs continuation →
        Endpoint.Resolves universeNodes node.onAccept ∧
          Endpoint.Resolves universeNodes node.onReject := by
  induction programs generalizing index with
  | nil =>
      intro node member
      contradiction
  | cons program rest inductionHypothesis =>
      intro node member
      simp only [nodesFrom, List.mem_cons] at member
      rcases member with nodeEq | tailMember
      · subst node
        constructor
        · exact nodesFrom_entry_resolves universeNodes
            blockCode (index + 1) rest continuation
            (fun tailNode tailNodeMember =>
              included tailNode <| by
                simp only [nodesFrom, List.mem_cons]
                exact Or.inr tailNodeMember)
            continuationResolves
        · trivial
      · exact inductionHypothesis (index := index + 1)
          (fun tailNode tailNodeMember =>
            included tailNode <| by
              simp only [nodesFrom, List.mem_cons]
              exact Or.inr tailNodeMember)
          node tailMember

/-! ### Exact linear-block paths -/

inductive LinearAcceptRuns :
    List WorkMachine → Nat → WorkTape → WorkTape → Prop where
  | terminal (tape : WorkTape) :
      LinearAcceptRuns [] 0 tape tape
  | step (program : WorkMachine) (rest : List WorkMachine)
      (localSteps tailSteps : Nat)
      (initialTape middleTape finalTape : WorkTape)
      (localRun :
        workRunExact? program localSteps
            { state := program.startState, tape := initialTape } =
          some
            { state := program.acceptState, tape := middleTape })
      (tail :
        LinearAcceptRuns rest tailSteps middleTape finalTape) :
      LinearAcceptRuns (program :: rest)
        (localSteps + 1 + tailSteps) initialTape finalTape

theorem nodesFrom_acceptPath
    (graph : Graph) (blockCode index : Nat)
    (programs : List WorkMachine) (continuation : Endpoint)
    (steps : Nat) (initialTape finalTape : WorkTape)
    (included :
      ∀ node,
        node ∈ nodesFrom blockCode index programs continuation →
          node ∈ graph.nodes)
    (runs :
      LinearAcceptRuns programs steps initialTape finalTape) :
    WorkMachineProgramPath.AcceptPath graph
      (entryEndpoint blockCode index programs continuation)
      continuation steps initialTape finalTape := by
  induction runs generalizing index with
  | terminal tape =>
      exact WorkMachineProgramPath.AcceptPath.terminal
        continuation tape
  | @step program rest localSteps tailSteps
      initialTape middleTape finalTape localRun tail
      inductionHypothesis =>
      let next : Endpoint :=
        entryEndpoint blockCode (index + 1) rest continuation
      let node : Node :=
        { name := blockNodeName blockCode index
          program := program
          onAccept := next
          onReject := .reject }
      have nodeMember :
          node ∈ graph.nodes := by
        apply included node
        simp [nodesFrom, node, next, entryEndpoint,
          machineRef]
      have tailIncluded :
          ∀ tailNode,
            tailNode ∈ nodesFrom blockCode (index + 1)
                rest continuation →
              tailNode ∈ graph.nodes := by
        intro tailNode tailMember
        apply included tailNode
        simp only [nodesFrom, List.mem_cons]
        exact Or.inr tailMember
      have tailPath :=
        inductionHypothesis (index := index + 1)
          tailIncluded
      have prefixed :=
        WorkMachineProgramPath.AcceptPath.step
          node continuation localSteps tailSteps
          initialTape middleTape finalTape
          nodeMember localRun tailPath
      simpa [entryEndpoint, node, next, machineRef,
        WorkMachineProgramGraph.Node.reference] using prefixed

theorem blockNodes_acceptPath_of_compiled
    (graph : Graph) (blockCode : Nat)
    (primitives : List Primitive)
    (programs : List WorkMachine) (continuation : Endpoint)
    (steps : Nat) (initialTape finalTape : WorkTape)
    (compiled : compileProgram primitives = some programs)
    (included :
      ∀ node,
        node ∈ blockNodes blockCode primitives continuation →
          node ∈ graph.nodes)
    (runs :
      LinearAcceptRuns programs steps initialTape finalTape) :
    WorkMachineProgramPath.AcceptPath graph
      (entryEndpoint blockCode 0 programs continuation)
      continuation steps initialTape finalTape := by
  apply nodesFrom_acceptPath graph blockCode 0 programs
    continuation steps initialTape finalTape
  · intro node member
    apply included node
    unfold blockNodes blockMachines
    rw [compiled]
    exact member
  · exact runs

def localRuleCount (programs : List WorkMachine) : Nat :=
  (programs.map (fun program => program.rules.length)).sum

def materializedRuleCount (programs : List WorkMachine) : Nat :=
  localRuleCount programs + 18 * programs.length

theorem nodesFrom_rule_count (blockCode index : Nat)
    (programs : List WorkMachine) (continuation : Endpoint) :
    ((nodesFrom blockCode index programs continuation).map
      (fun node => node.rules.length)).sum =
        materializedRuleCount programs := by
  induction programs generalizing index with
  | nil =>
      rfl
  | cons program rest inductionHypothesis =>
      simp only [nodesFrom, List.map_cons, List.sum_cons]
      rw [Node.rules_length, inductionHypothesis]
      unfold materializedRuleCount localRuleCount
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

end PNP.Concrete.LockedNAND.TargetEmitterBlockCompiler

/-
Copyright (c) 2026 PNP Labs.

Finite control for the full bit-register language. Ordinary register indices
are lifted past a compiler-owned scratch register; each source copy is an
actual invocation of the verified closed copy-free machine. This second
compiler layer does not recurse through itself or require copy-free input.

Exact scratch-store semantics and execution bounds are established by the
following simulation modules, not by graph well-formedness alone.
-/

import PNP.Concrete.BitRegisterExecution

namespace PNP.Concrete.BitRegister.Compiler

open Operation WorkMachineProgramGraph

def liftInstruction {count : Nat} : Instruction count → Instruction (count + 1)
  | .clear destination next => .clear destination.succ next
  | .copy destination source next => .copy destination.succ source.succ next
  | .push destination bit next => .push destination.succ bit next
  | .pop destination next => .pop destination.succ next
  | .branch source empty zeroBranch oneBranch => .branch source.succ empty zeroBranch oneBranch
  | .jump next => .jump next
  | .accept => .accept
  | .reject => .reject

def localProgram {count : Nat} : Instruction count → WorkMachine
  | .copy destination source _ => CopyFreeCompiler.machine (CopyProgram.program destination source)
  | instruction => CopyFreeCompiler.localProgram (liftInstruction instruction)

def auxiliaryProgram {count : Nat} (instruction : Instruction count) : WorkMachine :=
  CopyFreeCompiler.auxiliaryProgram (liftInstruction instruction)

theorem localProgram_wellFormed {count : Nat} (instruction : Instruction count) :
    ProgramWellFormed (localProgram instruction) := by
  cases instruction with
  | clear destination next => exact clearAt_wellFormed destination.succ.val
  | copy destination source next => exact CopyFreeCompiler.machine_wellFormed _
  | push destination bit next => exact pushAt_wellFormed destination.succ.val bit
  | pop destination next => exact popAt_wellFormed destination.succ.val
  | branch source empty zeroBranch oneBranch => exact emptyAt_wellFormed source.succ.val
  | jump next => exact idle_wellFormed
  | accept => exact idle_wellFormed
  | reject => exact idle_wellFormed

theorem auxiliaryProgram_wellFormed {count : Nat} (instruction : Instruction count) :
    ProgramWellFormed (auxiliaryProgram instruction) :=
  CopyFreeCompiler.auxiliaryProgram_wellFormed (liftInstruction instruction)

def mainRef {count : Nat} (address : Nat) (instruction : Instruction count) : NodeRef :=
  ⟨2 * address, (localProgram instruction).startState⟩

def auxiliaryRef {count : Nat} (address : Nat) (instruction : Instruction count) : NodeRef :=
  ⟨2 * address + 1, (auxiliaryProgram instruction).startState⟩

def fallbackNode {count : Nat} (program : Program count) : Node :=
  { name := 2 * program.code.length, program := idle, onAccept := .reject, onReject := .reject }

def addressRef {count : Nat} (program : Program count) (address : Nat) : NodeRef :=
  match lookup program.code address with
  | none => (fallbackNode program).reference
  | some instruction => mainRef address instruction

def target {count : Nat} (program : Program count) (address : Nat) : Endpoint :=
  .node (addressRef program address)

def mainAccept {count : Nat} (program : Program count) : Instruction count → Endpoint
  | .clear _ next | .copy _ _ next | .push _ _ next | .pop _ next | .jump next => target program next
  | .branch _ empty _ _ => target program empty
  | .accept => .accept
  | .reject => .reject

def mainReject {count : Nat} (address : Nat) (instruction : Instruction count) : Endpoint :=
  match instruction with
  | .branch _ _ _ _ => .node (auxiliaryRef address instruction)
  | _ => .reject

def auxiliaryAccept {count : Nat} (program : Program count) : Instruction count → Endpoint
  | .branch _ _ _ oneBranch => target program oneBranch
  | _ => .reject

def auxiliaryReject {count : Nat} (program : Program count) : Instruction count → Endpoint
  | .branch _ _ zeroBranch _ => target program zeroBranch
  | _ => .reject

def mainNode {count : Nat} (program : Program count) (address : Nat)
    (instruction : Instruction count) : Node :=
  { name := 2 * address, program := localProgram instruction
    onAccept := mainAccept program instruction, onReject := mainReject address instruction }

def auxiliaryNode {count : Nat} (program : Program count) (address : Nat)
    (instruction : Instruction count) : Node :=
  { name := 2 * address + 1, program := auxiliaryProgram instruction
    onAccept := auxiliaryAccept program instruction, onReject := auxiliaryReject program instruction }

theorem mainNode_reference {count : Nat} (program : Program count) (address : Nat)
    (instruction : Instruction count) :
    (mainNode program address instruction).reference = mainRef address instruction := by rfl

theorem auxiliaryNode_reference {count : Nat} (program : Program count) (address : Nat)
    (instruction : Instruction count) :
    (auxiliaryNode program address instruction).reference = auxiliaryRef address instruction := by rfl

def nodePairs {count : Nat} (program : Program count) :
    Nat → List (Instruction count) → List Node
  | _, [] => []
  | address, instruction :: rest =>
      mainNode program address instruction :: auxiliaryNode program address instruction ::
        nodePairs program (address + 1) rest

def graph {count : Nat} (program : Program count) : Graph :=
  { nodes := nodePairs program 0 program.code ++ [fallbackNode program]
    entry := addressRef program program.entry }

theorem nodePairs_length {count : Nat} (program : Program count)
    (address : Nat) (code : List (Instruction count)) :
    (nodePairs program address code).length = 2 * code.length := by
  induction code generalizing address with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [nodePairs, List.length_cons, ih]
      omega

private theorem node_interval_head (address size : Nat) :
    2 * address ≤ 2 * address ∧ 2 * address < 2 * (address + (size + 1)) :=
  ⟨Nat.le_refl _, Nat.mul_lt_mul_of_pos_left
    (Nat.lt_add_of_pos_right (Nat.zero_lt_succ size)) (by decide)⟩

private theorem node_interval_auxiliary (address size : Nat) :
    2 * address ≤ 2 * address + 1 ∧ 2 * address + 1 < 2 * (address + (size + 1)) := by
  refine ⟨Nat.le_add_right _ _, Nat.lt_of_lt_of_le (m := 2 * (address + 1)) ?_ ?_⟩
  · show 2 * address + 1 < 2 * (address + 1)
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.lt_succ_self (2 * address + 1)
  · exact Nat.mul_le_mul_left 2
      (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le size)) address)

private theorem node_interval_tail (address size name : Nat)
    (bound : 2 * (address + 1) ≤ name ∧ name < 2 * (address + 1 + size)) :
    2 * address ≤ name ∧ name < 2 * (address + (size + 1)) := by
  refine ⟨Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.le_succ address)) bound.1, ?_⟩
  simpa only [Nat.add_assoc, Nat.add_comm 1 size] using bound.2

theorem nodePairs_member_bounds {count : Nat} (program : Program count)
    (address : Nat) (code : List (Instruction count)) (node : Node)
    (member : node ∈ nodePairs program address code) :
    2 * address ≤ node.name ∧ node.name < 2 * (address + code.length) := by
  induction code generalizing address with
  | nil => cases member
  | cons instruction rest ih =>
      simp only [nodePairs, List.mem_cons] at member
      rcases member with rfl | rfl | member
      · exact node_interval_head address rest.length
      · exact node_interval_auxiliary address rest.length
      · exact node_interval_tail address rest.length node.name (ih (address + 1) member)

theorem nodePairs_pairwise {count : Nat} (program : Program count)
    (address : Nat) (code : List (Instruction count)) :
    (nodePairs program address code).Pairwise (fun left right => left.name ≠ right.name) := by
  induction code generalizing address with
  | nil => exact List.Pairwise.nil
  | cons instruction rest ih =>
      rw [nodePairs, List.pairwise_cons]
      refine ⟨?_, ?_⟩
      · intro node member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · change 2 * address ≠ 2 * address + 1
          omega
        · have h := nodePairs_member_bounds program (address + 1) rest node member
          change 2 * address ≠ node.name
          omega
      · rw [List.pairwise_cons]
        refine ⟨?_, ih (address + 1)⟩
        intro node member
        have h := nodePairs_member_bounds program (address + 1) rest node member
        change 2 * address + 1 ≠ node.name
        omega

theorem nodePairs_lookup_members {count : Nat} (program : Program count)
    (address : Nat) (code : List (Instruction count)) (offset : Nat)
    (instruction : Instruction count) (found : lookup code offset = some instruction) :
    mainNode program (address + offset) instruction ∈ nodePairs program address code ∧
      auxiliaryNode program (address + offset) instruction ∈ nodePairs program address code := by
  induction code generalizing address offset with
  | nil => cases offset <;> cases found
  | cons first rest ih =>
      cases offset with
      | zero =>
          change some first = some instruction at found
          have equal := Option.some.inj found
          subst first
          exact ⟨List.Mem.head _, List.Mem.tail _ (List.Mem.head _)⟩
      | succ offset =>
          change lookup rest offset = some instruction at found
          have h := ih (address + 1) offset found
          have hAddress : address + (offset + 1) = (address + 1) + offset := by omega
          rw [hAddress]
          exact ⟨List.Mem.tail _ (List.Mem.tail _ h.1), List.Mem.tail _ (List.Mem.tail _ h.2)⟩

theorem nodePairs_member_cases {count : Nat} (program : Program count)
    (address : Nat) (code : List (Instruction count)) (node : Node)
    (member : node ∈ nodePairs program address code) :
    ∃ offset instruction, lookup code offset = some instruction ∧
      (node = mainNode program (address + offset) instruction ∨
        node = auxiliaryNode program (address + offset) instruction) := by
  induction code generalizing address with
  | nil => cases member
  | cons first rest ih =>
      simp only [nodePairs, List.mem_cons] at member
      rcases member with rfl | rfl | member
      · exact ⟨0, first, rfl, Or.inl rfl⟩
      · exact ⟨0, first, rfl, Or.inr rfl⟩
      · rcases ih (address + 1) member with ⟨offset, instruction, found, shape⟩
        have hAddress : address + (offset + 1) = (address + 1) + offset := by omega
        refine ⟨offset + 1, instruction, found, ?_⟩
        rw [hAddress]
        exact shape

theorem fallback_member {count : Nat} (program : Program count) :
    fallbackNode program ∈ (graph program).nodes :=
  List.mem_append_right _ (List.Mem.head [])

theorem instruction_members {count : Nat} (program : Program count) (address : Nat)
    (instruction : Instruction count) (found : lookup program.code address = some instruction) :
    mainNode program address instruction ∈ (graph program).nodes ∧
      auxiliaryNode program address instruction ∈ (graph program).nodes := by
  have h := nodePairs_lookup_members program 0 program.code address instruction found
  simp only [Nat.zero_add] at h
  exact ⟨List.mem_append_left _ h.1, List.mem_append_left _ h.2⟩

theorem graph_member_cases {count : Nat} (program : Program count) (node : Node)
    (member : node ∈ (graph program).nodes) :
    node = fallbackNode program ∨
      ∃ address instruction, lookup program.code address = some instruction ∧
        (node = mainNode program address instruction ∨ node = auxiliaryNode program address instruction) := by
  simp only [graph, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with paired | fallback
  · right
    simpa only [Nat.zero_add] using nodePairs_member_cases program 0 program.code node paired
  · exact Or.inl fallback

theorem target_resolves {count : Nat} (program : Program count) (address : Nat) :
    Endpoint.Resolves (graph program).nodes (target program address) := by
  cases found : lookup program.code address with
  | none =>
      simpa only [target, addressRef, found] using
        resolves_member _ (fallbackNode program) (fallback_member program)
  | some instruction =>
      simpa only [target, addressRef, found, mainNode_reference] using
        resolves_member _ (mainNode program address instruction)
          (instruction_members program address instruction found).1

theorem graph_wellFormed {count : Nat} (program : Program count) : (graph program).WellFormed := by
  refine ⟨?_, ?_, target_resolves program program.entry, ?_⟩
  · change (nodePairs program 0 program.code ++ [fallbackNode program]).Pairwise _
    rw [List.pairwise_append]
    refine ⟨nodePairs_pairwise program 0 program.code, by simp, ?_⟩
    intro left leftMember right rightMember
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at rightMember
    subst right
    have h := nodePairs_member_bounds program 0 program.code left leftMember
    change left.name ≠ 2 * program.code.length
    simp only [Nat.zero_add] at h
    omega
  · intro node member
    rcases graph_member_cases program node member with rfl | ⟨address, instruction, found, shape⟩
    · exact idle_wellFormed
    · rcases shape with rfl | rfl
      · exact localProgram_wellFormed instruction
      · exact auxiliaryProgram_wellFormed instruction
  · intro node member
    rcases graph_member_cases program node member with rfl | ⟨address, instruction, found, shape⟩
    · exact ⟨True.intro, True.intro⟩
    · rcases shape with rfl | rfl
      · cases instruction with
        | clear destination next => exact ⟨target_resolves program next, True.intro⟩
        | copy destination source next => exact ⟨target_resolves program next, True.intro⟩
        | push destination bit next => exact ⟨target_resolves program next, True.intro⟩
        | pop destination next => exact ⟨target_resolves program next, True.intro⟩
        | branch source empty zeroBranch oneBranch =>
            exact ⟨target_resolves program empty,
              resolves_member _ (auxiliaryNode program address (.branch source empty zeroBranch oneBranch))
                (instruction_members program address _ found).2⟩
        | jump next => exact ⟨target_resolves program next, True.intro⟩
        | accept => exact ⟨True.intro, True.intro⟩
        | reject => exact ⟨True.intro, True.intro⟩
      · cases instruction with
        | branch source empty zeroBranch oneBranch =>
            exact ⟨target_resolves program oneBranch, target_resolves program zeroBranch⟩
        | clear destination next => exact ⟨True.intro, True.intro⟩
        | copy destination source next => exact ⟨True.intro, True.intro⟩
        | push destination bit next => exact ⟨True.intro, True.intro⟩
        | pop destination next => exact ⟨True.intro, True.intro⟩
        | jump next => exact ⟨True.intro, True.intro⟩
        | accept => exact ⟨True.intro, True.intro⟩
        | reject => exact ⟨True.intro, True.intro⟩

def machine {count : Nat} (program : Program count) : WorkMachine :=
  WorkMachineProgramGraph.machine (graph program)

theorem machine_wellFormed {count : Nat} (program : Program count) :
    ProgramWellFormed (machine program) :=
  ⟨WorkMachineProgramGraph.rules_pairwise _ (graph_wellFormed program),
    noRuleAt_globalAccept _, noRuleAt_globalReject _, machine_accept_ne_reject _⟩

theorem graph_node_count {count : Nat} (program : Program count) :
    (graph program).nodes.length = 2 * program.code.length + 1 := by
  simp only [graph, List.length_append, nodePairs_length, List.length_cons, List.length_nil]

end PNP.Concrete.BitRegister.Compiler

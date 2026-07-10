/-
Copyright (c) 2026 PNP Labs.

Finite, exact-width enumeration of the intrinsically topological direct-wire
NAND language.  The construction deliberately enumerates ordered gate inputs:
it makes no commutativity quotient and therefore makes no deduplication claim.
-/

import PNP.NANDSemantics

namespace PNP
namespace DirectWire

/-- Map a witnessed list member without using a propositional rewrite. -/
theorem mem_map_of_mem {α β : Type} (function : α → β)
    {item : α} {items : List α} (member : item ∈ items) :
    function item ∈ items.map function := by
  induction member with
  | head => exact List.Mem.head _
  | tail other _ ih => exact List.Mem.tail (function other) ih

/-- Place a witnessed member into the corresponding branch of a flat map. -/
theorem mem_flatMap_of_mem {α β : Type} {function : α → List β}
    {outer : α} {item : β} {items : List α}
    (outerMember : outer ∈ items) (innerMember : item ∈ function outer) :
    item ∈ items.flatMap function := by
  induction outerMember with
  | head =>
      exact List.mem_append_left _ innerMember
  | tail other _ ih =>
      exact List.mem_append_right (function other) ih

/-- Every element of `Fin width`, in its canonical order. -/
def allFin : (width : Nat) → List (Fin width)
  | 0 => []
  | width + 1 =>
      ⟨0, Nat.zero_lt_succ width⟩ :: (allFin width).map Fin.succ

theorem mem_allFin {width : Nat} (index : Fin width) :
    index ∈ allFin width := by
  induction width with
  | zero =>
      exact False.elim (Nat.not_lt_zero index.val index.isLt)
  | succ width ih =>
      cases index with
      | mk value isLt =>
          cases value with
          | zero => exact List.Mem.head _
          | succ earlier =>
              apply List.Mem.tail
              exact mem_map_of_mem Fin.succ
                (ih ⟨earlier, Nat.lt_of_succ_lt_succ isLt⟩)

/-- Every source available at an exact topological position. -/
def allSources (inputs gates : Nat) : List (Source inputs gates) :=
  (allFin inputs).map Source.input ++
    [Source.constant false, Source.constant true] ++
    (allFin gates).map Source.gate

theorem mem_allSources {inputs gates : Nat} (source : Source inputs gates) :
    source ∈ allSources inputs gates := by
  cases source with
  | input index =>
      apply List.mem_append_left
      apply List.mem_append_left
      exact mem_map_of_mem Source.input (mem_allFin index)
  | constant value =>
      apply List.mem_append_left
      apply List.mem_append_right
      cases value with
      | false => exact List.Mem.head _
      | true => exact List.Mem.tail _ (List.Mem.head _)
  | gate index =>
      apply List.mem_append_right
      exact mem_map_of_mem Source.gate (mem_allFin index)

/-- Every ordered NAND gate over the currently available sources. -/
def allGates (inputs priorGates : Nat) : List (Gate inputs priorGates) :=
  (allSources inputs priorGates).flatMap fun left =>
    (allSources inputs priorGates).map fun right => ⟨left, right⟩

theorem mem_allGates {inputs priorGates : Nat}
    (gate : Gate inputs priorGates) : gate ∈ allGates inputs priorGates := by
  cases gate with
  | mk left right =>
      exact mem_flatMap_of_mem (mem_allSources left)
        (mem_map_of_mem (fun right => Gate.mk left right) (mem_allSources right))

/-- Every intrinsically topological NAND program with exactly `gates` gates. -/
def allPrograms (inputs : Nat) : (gates : Nat) → List (Program inputs gates)
  | 0 => [.empty]
  | gates + 1 =>
      (allPrograms inputs gates).flatMap fun initial =>
        (allGates inputs gates).map fun gate => .snoc initial gate

theorem mem_allPrograms {inputs gates : Nat} (program : Program inputs gates) :
    program ∈ allPrograms inputs gates := by
  induction program with
  | empty => exact List.Mem.head _
  | snoc initial gate ih =>
      exact mem_flatMap_of_mem ih
        (mem_map_of_mem (fun gate => Program.snoc initial gate)
          (mem_allGates gate))

/-- A recursively typed output tuple.  Unlike `DirectWireWord`, its finite
    structure can be enumerated without enumerating a function space. -/
inductive OutputWord (inputs gates : Nat) : Nat → Type where
  | nil : OutputWord inputs gates 0
  | cons {outputs : Nat} :
      Source inputs gates → OutputWord inputs gates outputs →
        OutputWord inputs gates (outputs + 1)

/-- Pointwise lookup in a recursively typed output tuple. -/
def OutputWord.get {inputs gates outputs : Nat}
    (word : OutputWord inputs gates outputs) : Fin outputs → Source inputs gates :=
  match word with
  | .nil => fun index => False.elim (Nat.not_lt_zero index.val index.isLt)
  | .cons head tail => fun index =>
      match index with
      | ⟨0, _⟩ => head
      | ⟨position + 1, isLt⟩ =>
          tail.get ⟨position, Nat.lt_of_succ_lt_succ isLt⟩

/-- Convert the recursive tuple to the function-shaped semantics interface. -/
def OutputWord.toDirectWireWord {inputs gates outputs : Nat}
    (word : OutputWord inputs gates outputs) : DirectWireWord inputs gates outputs :=
  ⟨word.get⟩

@[simp] theorem OutputWord.get_cons_zero {inputs gates outputs : Nat}
    (head : Source inputs gates) (tail : OutputWord inputs gates outputs) :
    (OutputWord.cons head tail).get ⟨0, Nat.zero_lt_succ outputs⟩ = head := rfl

@[simp] theorem OutputWord.get_cons_succ {inputs gates outputs : Nat}
    (head : Source inputs gates) (tail : OutputWord inputs gates outputs)
    (index : Fin outputs) :
    (OutputWord.cons head tail).get index.succ = tail.get index := by
  cases index
  rfl

theorem OutputWord.toDirectWireWord_pointwise {inputs gates outputs : Nat}
    (word : OutputWord inputs gates outputs) (output : Fin outputs) :
    word.toDirectWireWord.source output = word.get output := rfl

/-- Every recursively typed output tuple of exactly `outputs` wires. -/
def allOutputWords (inputs gates : Nat) :
    (outputs : Nat) → List (OutputWord inputs gates outputs)
  | 0 => [.nil]
  | outputs + 1 =>
      (allSources inputs gates).flatMap fun head =>
        (allOutputWords inputs gates outputs).map fun tail => .cons head tail

theorem mem_allOutputWords {inputs gates outputs : Nat}
    (word : OutputWord inputs gates outputs) :
    word ∈ allOutputWords inputs gates outputs := by
  induction word with
  | nil => exact List.Mem.head _
  | cons head tail ih =>
      exact mem_flatMap_of_mem (mem_allSources head)
        (mem_map_of_mem (fun tail => OutputWord.cons head tail) ih)

/-- The zero-output tuple is constructively unique. -/
theorem OutputWord.eq_nil {inputs gates : Nat}
    (word : OutputWord inputs gates 0) : word = .nil := by
  cases word
  rfl

/-- Reify a function-shaped direct-wire word into the recursive tuple. -/
def OutputWord.ofFn {inputs gates : Nat} :
    {outputs : Nat} → (Fin outputs → Source inputs gates) →
      OutputWord inputs gates outputs
  | 0, _ => .nil
  | outputs + 1, source =>
      .cons (source ⟨0, Nat.zero_lt_succ outputs⟩)
        (OutputWord.ofFn fun output => source output.succ)

/-- Reification preserves every output source pointwise. -/
theorem OutputWord.get_ofFn {inputs gates outputs : Nat}
    (source : Fin outputs → Source inputs gates) (output : Fin outputs) :
    (OutputWord.ofFn source).get output = source output := by
  induction outputs with
  | zero =>
      exact False.elim (Nat.not_lt_zero output.val output.isLt)
  | succ outputs ih =>
      cases output with
      | mk position isLt =>
          cases position with
          | zero => rfl
          | succ earlier =>
              exact ih (fun output => source output.succ)
                ⟨earlier, Nat.lt_of_succ_lt_succ isLt⟩

/-- A complete exact-size direct-wire implementation candidate. -/
structure Candidate (inputs gates outputs : Nat) where
  program : Program inputs gates
  outputs : OutputWord inputs gates outputs

def Candidate.directWireWord {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) :
    DirectWireWord inputs gates outputs :=
  candidate.outputs.toDirectWireWord

def Candidate.semantics {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) : OpenFunction inputs outputs :=
  DirectWire.semantics candidate.program candidate.directWireWord

/-- Reify an implementation already expressed through `DirectWireWord`. -/
def Candidate.ofDirectWireWord {inputs gates outputs : Nat}
    (program : Program inputs gates)
    (word : DirectWireWord inputs gates outputs) : Candidate inputs gates outputs :=
  ⟨program, OutputWord.ofFn word.source⟩

/-- Every candidate with the exact requested input, gate, and output widths. -/
def allCandidates (inputs gates outputs : Nat) :
    List (Candidate inputs gates outputs) :=
  (allPrograms inputs gates).flatMap fun program =>
    (allOutputWords inputs gates outputs).map fun outputWord =>
      ⟨program, outputWord⟩

theorem mem_allCandidates {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) :
    candidate ∈ allCandidates inputs gates outputs := by
  cases candidate with
  | mk program outputs =>
      exact mem_flatMap_of_mem (mem_allPrograms program)
        (mem_map_of_mem (fun outputWord => Candidate.mk program outputWord)
          (mem_allOutputWords outputs))

theorem Candidate.ofDirectWireWord_program {inputs gates outputs : Nat}
    (program : Program inputs gates)
    (word : DirectWireWord inputs gates outputs) :
    (Candidate.ofDirectWireWord program word).program = program := rfl

theorem Candidate.ofDirectWireWord_pointwise {inputs gates outputs : Nat}
    (program : Program inputs gates)
    (word : DirectWireWord inputs gates outputs) (output : Fin outputs) :
    (Candidate.ofDirectWireWord program word).directWireWord.source output =
      word.source output := by
  exact OutputWord.get_ofFn word.source output

/-- Completeness for the pre-existing `Program` / `DirectWireWord` interface.
    The correspondence is pointwise, so it needs no function extensionality. -/
theorem exactWidthEnumeration_complete {inputs gates outputs : Nat}
    (program : Program inputs gates)
    (word : DirectWireWord inputs gates outputs) :
    ∃ candidate : Candidate inputs gates outputs,
      candidate ∈ allCandidates inputs gates outputs ∧
      candidate.program = program ∧
      ∀ output, candidate.directWireWord.source output = word.source output := by
  refine ⟨Candidate.ofDirectWireWord program word, ?_, rfl, ?_⟩
  · exact mem_allCandidates (Candidate.ofDirectWireWord program word)
  · intro output
    exact Candidate.ofDirectWireWord_pointwise program word output

/-- A candidate existentially paired with an exact gate count no larger than
    `gateBound`.  The finite index carries the bound intrinsically. -/
abbrev BoundedCandidate (inputs outputs gateBound : Nat) :=
  Sigma fun gateCount : Fin (gateBound + 1) =>
    Candidate inputs gateCount.val outputs

/-- All exact-width candidates using at most `gateBound` NAND gates. -/
def allBoundedCandidates (inputs outputs gateBound : Nat) :
    List (BoundedCandidate inputs outputs gateBound) :=
  (allFin (gateBound + 1)).flatMap fun gateCount =>
    (allCandidates inputs gateCount.val outputs).map fun candidate =>
      ⟨gateCount, candidate⟩

theorem mem_allBoundedCandidates {inputs outputs gateBound : Nat}
    (candidate : BoundedCandidate inputs outputs gateBound) :
    candidate ∈ allBoundedCandidates inputs outputs gateBound := by
  cases candidate with
  | mk gateCount exactCandidate =>
      exact mem_flatMap_of_mem (mem_allFin gateCount)
        (mem_map_of_mem (fun candidate => Sigma.mk gateCount candidate)
          (mem_allCandidates exactCandidate))

/-- Embed an exact candidate whenever its gate count satisfies the bound. -/
def boundedCandidateOfLE {inputs gates outputs gateBound : Nat}
    (withinBound : gates ≤ gateBound)
    (candidate : Candidate inputs gates outputs) :
    BoundedCandidate inputs outputs gateBound :=
  ⟨⟨gates, Nat.lt_succ_of_le withinBound⟩, candidate⟩

theorem mem_allBoundedCandidates_of_le
    {inputs gates outputs gateBound : Nat}
    (withinBound : gates ≤ gateBound)
    (candidate : Candidate inputs gates outputs) :
    boundedCandidateOfLE withinBound candidate ∈
      allBoundedCandidates inputs outputs gateBound :=
  mem_allBoundedCandidates (boundedCandidateOfLE withinBound candidate)

/-- Every direct-wire implementation satisfying the bound occurs in the
    bounded enumeration.  `HEq` states the dependent program/source identities
    without transporting them through a separately proved index equality. -/
theorem boundedDirectInterface_complete
    {inputs gates outputs gateBound : Nat}
    (withinBound : gates ≤ gateBound)
    (program : Program inputs gates)
    (word : DirectWireWord inputs gates outputs) :
    ∃ candidate : BoundedCandidate inputs outputs gateBound,
      candidate ∈ allBoundedCandidates inputs outputs gateBound ∧
      candidate.1.val = gates ∧
      candidate.2.program ≍ program ∧
      ∀ output, candidate.2.directWireWord.source output ≍ word.source output := by
  let exactCandidate := Candidate.ofDirectWireWord program word
  let boundedCandidate := boundedCandidateOfLE withinBound exactCandidate
  refine ⟨boundedCandidate, mem_allBoundedCandidates boundedCandidate, rfl, ?_, ?_⟩
  · exact HEq.rfl
  · intro output
    change (Candidate.ofDirectWireWord program word).directWireWord.source output ≍
      word.source output
    rw [Candidate.ofDirectWireWord_pointwise program word output]

theorem Candidate.program_size_eq_gateCount {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) :
    candidate.program.size = gates :=
  Program.size_eq_gateCount candidate.program

theorem Candidate.directWire_size_eq_gateCount {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) :
    candidate.directWireWord.size candidate.program = gates :=
  DirectWireWord.size_eq_gateCount candidate.directWireWord candidate.program

theorem Candidate.semantics_is_typed {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (input : Valuation inputs) (output : Fin outputs) :
    candidate.semantics input output =
      (candidate.outputs.get output).eval input (candidate.program.eval input) := rfl

/-- Proof-bearing summary of exact-width finite NAND enumeration. -/
structure NANDEnumeratorCertificate : Prop where
  finComplete : ∀ {width} (index : Fin width), index ∈ allFin width
  sourceComplete : ∀ {inputs gates} (source : Source inputs gates),
    source ∈ allSources inputs gates
  orderedGateComplete : ∀ {inputs gates} (gate : Gate inputs gates),
    gate ∈ allGates inputs gates
  programComplete : ∀ {inputs gates} (program : Program inputs gates),
    program ∈ allPrograms inputs gates
  outputWordComplete : ∀ {inputs gates outputs}
      (word : OutputWord inputs gates outputs),
    word ∈ allOutputWords inputs gates outputs
  candidateComplete : ∀ {inputs gates outputs}
      (candidate : Candidate inputs gates outputs),
    candidate ∈ allCandidates inputs gates outputs
  directInterfaceComplete : ∀ {inputs gates outputs}
      (program : Program inputs gates)
      (word : DirectWireWord inputs gates outputs),
    ∃ candidate : Candidate inputs gates outputs,
      candidate ∈ allCandidates inputs gates outputs ∧
      candidate.program = program ∧
      ∀ output, candidate.directWireWord.source output = word.source output
  boundedComplete : ∀ {inputs outputs gateBound}
      (candidate : BoundedCandidate inputs outputs gateBound),
    candidate ∈ allBoundedCandidates inputs outputs gateBound
  exactCandidateWithinBound : ∀ {inputs gates outputs gateBound}
      (withinBound : gates ≤ gateBound)
      (candidate : Candidate inputs gates outputs),
    boundedCandidateOfLE withinBound candidate ∈
      allBoundedCandidates inputs outputs gateBound
  boundedDirectInterfaceComplete : ∀ {inputs gates outputs gateBound}
      (_withinBound : gates ≤ gateBound)
      (program : Program inputs gates)
      (word : DirectWireWord inputs gates outputs),
    ∃ candidate : BoundedCandidate inputs outputs gateBound,
      candidate ∈ allBoundedCandidates inputs outputs gateBound ∧
      candidate.1.val = gates ∧
      candidate.2.program ≍ program ∧
      ∀ output, candidate.2.directWireWord.source output ≍ word.source output
  zeroOutputUnique : ∀ {inputs gates} (word : OutputWord inputs gates 0),
    word = .nil
  conversionPointwise : ∀ {inputs gates outputs}
      (word : OutputWord inputs gates outputs) (output : Fin outputs),
    word.toDirectWireWord.source output = word.get output
  programSizeExact : ∀ {inputs gates outputs}
      (candidate : Candidate inputs gates outputs),
    candidate.program.size = gates
  implementationSizeExact : ∀ {inputs gates outputs}
      (candidate : Candidate inputs gates outputs),
    candidate.directWireWord.size candidate.program = gates
  semanticsTyped : ∀ {inputs gates outputs}
      (candidate : Candidate inputs gates outputs)
      (input : Valuation inputs) (output : Fin outputs),
    candidate.semantics input output =
      (candidate.outputs.get output).eval input (candidate.program.eval input)

def nandEnumeratorCertificate : NANDEnumeratorCertificate :=
  { finComplete := mem_allFin
    sourceComplete := mem_allSources
    orderedGateComplete := mem_allGates
    programComplete := mem_allPrograms
    outputWordComplete := mem_allOutputWords
    candidateComplete := mem_allCandidates
    directInterfaceComplete := exactWidthEnumeration_complete
    boundedComplete := mem_allBoundedCandidates
    exactCandidateWithinBound := mem_allBoundedCandidates_of_le
    boundedDirectInterfaceComplete := boundedDirectInterface_complete
    zeroOutputUnique := OutputWord.eq_nil
    conversionPointwise := OutputWord.toDirectWireWord_pointwise
    programSizeExact := Candidate.program_size_eq_gateCount
    implementationSizeExact := Candidate.directWire_size_eq_gateCount
    semanticsTyped := Candidate.semantics_is_typed }

end DirectWire
end PNP

/-
Copyright (c) 2026 PNP Labs.

Exact search-result serialization. A terminal result contains the full
generated trace. An augment result contains the selected index and the
suffix path, with an empty path when reconstruction returns none.
-/
import PNP.Concrete.NormalizerSearchPath

namespace PNP.Concrete.NormalizerBlocks.Search
open BitRegister Occurrence

inductive Output where
  | terminal (trace : List TraceData.Row)
  | augment (index : Nat) (path : List CNFLiteral)
  deriving DecidableEq

def answer : Output → BitString
  | .terminal trace => false :: TraceData.encode trace
  | .augment index path => true :: TableInit.encodeCount index (PathData.encode path)

def value (variables : Nat) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) : Output :=
  let trace := traceValue variables clauses entries
  match Candidate.selectFrom entries (SeenTrace.value trace) variables 0 with
  | none => .terminal trace
  | some index => .augment index ((TracePath.value trace ⟨false, index⟩).getD [])

theorem path_answer_tail (path : Option (List CNFLiteral)) :
    (PathData.answer path).tail = PathData.encode (path.getD []) := by
  cases path <;> rfl

def prepareAugmentPrefix : Block 13 :=
  .seq (.action (.copy 0 8)) (.seq (.action (.pop 0)) (.seq (.action (.push 0 false)) (.seq (.action (.copy 2 12)) (.action (.pop 2)))))
def augmentPrefixPrepared (r : Candidate.State) : Candidate.State :=
  {r with core := {r.core with input := false :: r.core.output.tail, remaining := r.output.tail}}
theorem prepareAugmentPrefix_exec (r : Candidate.State) :
    Exec prepareAugmentPrefix r.store 5 (augmentPrefixPrepared r).store := by
  let first := {r with core := {r.core with input := r.core.output}}
  let second := {r with core := {r.core with input := r.core.output.tail}}
  let third := {r with core := {r.core with input := false :: r.core.output.tail}}
  let fourth := {third with core := {third.core with remaining := r.output}}
  have a : Exec (.action (.copy 0 8)) r.store 1 first.store := .action _ _
  have b : Exec (.action (.pop 0)) first.store 1 second.store := .action _ _
  have c : Exec (.action (.push 0 false)) second.store 1 third.store := .action _ _
  have d : Exec (.action (.copy 2 12)) third.store 1 fourth.store := .action _ _
  have e : Exec (.action (.pop 2)) fourth.store 1 (augmentPrefixPrepared r).store := .action _ _
  exact Exec.seq a (Exec.seq b (Exec.seq c (Exec.seq d e)))

def prepareAugment : Block 29 := liftCandidate prepareAugmentPrefix
def augmentPrepared (r : State) : State := r.withCandidate (augmentPrefixPrepared r.candidate)
theorem prepareAugment_exec (r : State) : Exec prepareAugment r.store 5 (augmentPrepared r).store :=
  liftCandidate_exec _ r _ _ (prepareAugmentPrefix_exec r.candidate)

def prependIndex : Block 29 := liftCore ParentQuery.prependLoop
def indexPrepended (r : State) : State := r.withRegisters (ParentQuery.prepended r.registers.remaining r.registers)
theorem prependIndex_exec (r : State) :
    Exec prependIndex r.store (3 * r.registers.remaining.length + 1) (indexPrepended r).store :=
  liftCore_exec _ r _ _ (ParentQuery.prepend_exec r.registers.remaining r.registers)

def finishAugmentCore : Block 9 := .seq (.action (.push 0 true)) (.action (.copy 8 0))
def augmentCoreFinished (r : Registers) : Registers := {r with input := true :: r.input, output := true :: r.input}
theorem finishAugmentCore_exec (r : Registers) :
    Exec finishAugmentCore r.store 2 (augmentCoreFinished r).store :=
  Exec.seq (.action _ _) (.action _ _)
def finishAugment : Block 29 := liftCore finishAugmentCore
def augmentFinished (r : State) : State := r.withRegisters (augmentCoreFinished r.registers)
theorem finishAugment_exec (r : State) : Exec finishAugment r.store 2 (augmentFinished r).store :=
  liftCore_exec _ r _ _ (finishAugmentCore_exec r.registers)

def packAugment : Block 29 := .seq prepareAugment (.seq prependIndex finishAugment)
def augmentPacked (r : State) : State := augmentFinished (indexPrepended (augmentPrepared r))
def packAugmentFuel (r : State) : Nat := 3 * r.parent.graph.core.matching.tail.length + 8
theorem packAugment_exec (r : State) :
    Exec packAugment r.store (packAugmentFuel r) (augmentPacked r).store := by
  have checked := Exec.seq (prepareAugment_exec r) (Exec.seq (prependIndex_exec (augmentPrepared r)) (finishAugment_exec (indexPrepended (augmentPrepared r))))
  change Exec packAugment r.store (5 + ((3 * r.parent.graph.core.matching.tail.length + 1) + 2)) (augmentPacked r).store at checked
  have cost : 5 + ((3 * r.parent.graph.core.matching.tail.length + 1) + 2) = packAugmentFuel r := by unfold packAugmentFuel; omega
  rw [cost] at checked
  exact checked

theorem augmentPacked_output (r : State) :
    (augmentPacked r).registers.output =
      true :: (List.replicate r.parent.graph.core.matching.tail.length true ++ (false :: r.registers.output.tail)) := rfl

def packTerminal : Block 29 := .seq (.action (.copy 8 24)) (.action (.push 8 false))
def terminalPacked (r : State) : State := r.withRegisters {r.registers with output := false :: r.core.core.trace}
theorem packTerminal_exec (r : State) : Exec packTerminal r.store 2 (terminalPacked r).store := by
  let copied := r.withRegisters {r.registers with output := r.core.core.trace}
  have source : r.store.get (24 : Fin 29) = r.core.core.trace := rfl
  have output (word : BitString) : r.store.set (8 : Fin 29) word =
      (r.withRegisters {r.registers with output := word}).store := rfl
  have first : Exec (.action (.copy 8 24)) r.store 1 copied.store := by
    have checked := Exec.action (.copy (8 : Fin 29) 24) r.store
    simpa only [Action.update, Action.instruction, Instruction.update, source, output, copied] using checked
  have lastCore : Exec (.action (.push 8 false)) copied.registers.store 1
      ({copied.registers with output := false :: copied.registers.output}).store := .action _ _
  have second := liftCore_exec (.action (.push 8 false)) copied 1 _ lastCore
  exact Exec.seq first second

def augment : Block 29 := .seq reconstruct packAugment
def augmented (r : State) : State := augmentPacked (reconstructed r)
def augmentFuel (r : State) : Nat := reconstructFuel r + packAugmentFuel (reconstructed r)
theorem augment_exec (r : State) : Exec augment r.store (augmentFuel r) (augmented r).store :=
  Exec.seq (reconstruct_exec r) (packAugment_exec (reconstructed r))

theorem augmented_canonical (r : State) (index : Nat) (trace : List TraceData.Row)
    (chosen : r.parent.graph.core.matching = TableOwner.answer (some index))
    (read : r.core.core.trace = TraceData.encode trace) :
    (augmented r).registers.output = answer (.augment index ((TracePath.value trace ⟨false, index⟩).getD [])) := by
  have kept := (reconstructed_frame r).2.2
  have path := reconstructed_canonical r index trace chosen read
  change (augmentPacked (reconstructed r)).registers.output = _
  rw [augmentPacked_output, kept, chosen, path, path_answer_tail]
  simp only [TableOwner.answer, List.tail_cons, List.length_replicate, answer, TableInit.encodeCount]

def decideResult : Block 29 := .branch 12 packTerminal packTerminal augment
def decided (r : State) : State := if ForwardEdge.present r.parent.graph.core.matching then augmented r else terminalPacked r
def decideFuel (r : State) : Nat := 1 + if ForwardEdge.present r.parent.graph.core.matching then augmentFuel r else 2
theorem decideResult_exec (r : State) : Exec decideResult r.store (decideFuel r) (decided r).store := by
  have checked := EdgeKinds.branch_head (12 : Fin 29) r.store packTerminal augment 2 (augmentFuel r)
    (terminalPacked r).store (augmented r).store (packTerminal_exec r) (augment_exec r)
  change Exec decideResult r.store (decideFuel r)
    (if ForwardEdge.present r.parent.graph.core.matching then (augmented r).store else (terminalPacked r).store) at checked
  cases tag : ForwardEdge.present r.parent.graph.core.matching <;>
    simpa only [decided, tag, Bool.false_eq_true, ite_false, ite_true] using checked

theorem decided_canonical (r : State) (candidate : Option Nat) (trace : List TraceData.Row)
    (chosen : r.parent.graph.core.matching = TableOwner.answer candidate)
    (read : r.core.core.trace = TraceData.encode trace) :
    (decided r).registers.output = answer (match candidate with
      | none => .terminal trace
      | some index => .augment index ((TracePath.value trace ⟨false, index⟩).getD [])) := by
  cases candidate with
  | none =>
      have tag : ForwardEdge.present r.parent.graph.core.matching = false := by rw [chosen]; rfl
      simp only [decided, tag, Bool.false_eq_true, ite_false]
      change false :: r.core.core.trace = false :: TraceData.encode trace
      rw [read]
  | some index =>
      have tag : ForwardEdge.present r.parent.graph.core.matching = true := by rw [chosen]; rfl
      simp only [decided, tag, ite_true]
      exact augmented_canonical r index trace chosen read

end PNP.Concrete.NormalizerBlocks.Search

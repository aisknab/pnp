/-
Copyright (c) 2026 PNP Labs.

Closed clause-query handoff for the literal-position chooser. The raw
semantics are total; on a source triple they equal the first/middle/last
rule. The optional output uses the existing canonical matching encoding.
-/
import PNP.Concrete.NormalizerCacheSlotChoose

namespace PNP.Concrete.NormalizerBlocks.CacheSlot
open BitRegister Occurrence

def rawValue (pending : BitString) (target : Nat) : Nat :=
  value (CompactClause.index pending).length
    (CompactClause.index (CompactClause.next pending)).length target
theorem chosen_output (r : State) :
    (chosen r).registers.output = TableOwner.answer (some (rawValue r.core.pending r.index.length)) := by
  have firstFlag : ForwardEdge.present (probed r).registers.output =
      ((CompactClause.index r.core.pending).length == r.index.length) := by
    rw [probed_output]
    rfl
  have secondFlag : ForwardEdge.present (probed (probed r)).registers.output =
      ((CompactClause.index (CompactClause.next r.core.pending)).length == r.index.length) := by
    rw [probed_output, (probed_fields r).2.2.2.2.2, (probed_fields r).2.2.1]
    rfl
  unfold chosen firstChosen
  rw [firstFlag]
  cases hf : (CompactClause.index r.core.pending).length == r.index.length <;>
    simp only [Bool.false_eq_true, ite_false, ite_true]
  · unfold secondResult secondChosen
    rw [secondFlag]
    cases hm : (CompactClause.index (CompactClause.next r.core.pending)).length == r.index.length <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, rawValue, value, hf, hm] <;> rfl
  · simp only [rawValue, value, hf, ite_true]
    rfl

def prepare : Block 16 := .seq (.action (.copy 9 8)) (.action (.pop 9))
def prepared (r : State) : State := r.withCompact {r.core with pending := r.registers.output.tail}
theorem prepare_exec (r : State) : Exec prepare r.store 2 (prepared r).store :=
  Exec.seq (.action _ _) (.action _ _)
def call : Block 16 := .seq prepare choose
def called (r : State) : State := chosen (prepared r)
def callFuel (r : State) : Nat := 2 + chooseFuel (prepared r)
theorem call_exec (r : State) : Exec call r.store (callFuel r) (called r).store :=
  Exec.seq (prepare_exec r) (choose_exec (prepared r))
theorem callFuel_bound (r : State) : callFuel r ≤ 14 * r.registers.output.length + 68 := by
  have chosen := chooseFuel_bound (prepared r)
  change chooseFuel (prepared r) ≤ 14 * r.registers.output.tail.length + 66 at chosen
  have tail := ParentQuery.input_tail_bound r.registers.output
  unfold callFuel
  omega
theorem called_fields (r : State) :
    (called r).formula = r.formula ∧ (called r).remaining = r.remaining ∧
    (called r).index = r.index ∧ (called r).core.variables = r.core.variables ∧
    (called r).core.buffer = r.core.buffer :=
  chosen_fields (prepared r)
theorem called_output_length (r : State) : (called r).registers.output.length ≤ 3 :=
  chosen_output_length (prepared r)
def encodedValue (literals : List CNFLiteral) (target : Nat) : Nat :=
  rawValue (CompactClause.bits literals ++ [true,false]) target
theorem called_canonical (r : State) (literals : List CNFLiteral) (target : Nat)
    (query : r.registers.output = Occurrence.encodeQuery 0 literals)
    (index : r.index = List.replicate target true) :
    (called r).registers.output = TableOwner.answer (some (encodedValue literals target)) := by
  rw [called, chosen_output]
  change TableOwner.answer (some (rawValue r.registers.output.tail r.index.length)) = _
  rw [query, index, List.length_replicate, CompactClause.occurrence_data]
  rfl
theorem encodedValue_cons_cons (first middle : CNFLiteral) (rest : List CNFLiteral) (target : Nat) :
    encodedValue (first :: middle :: rest) target = value first.variableIndex middle.variableIndex target := by
  have one := CompactClause.parsed_canonical first
    (CompactClause.bits (middle :: rest) ++ [true,false])
  have two := CompactClause.parsed_canonical middle (CompactClause.bits rest ++ [true,false])
  unfold encodedValue rawValue
  rw [CompactClause.bits_cons, List.append_assoc, one.1, one.2.1, List.length_replicate,
    CompactClause.bits_cons, List.append_assoc, two.1, List.length_replicate]

end PNP.Concrete.NormalizerBlocks.CacheSlot

/-
Copyright (c) 2026 PNP Labs.

Framed query kernel for graph construction. The existing indexed-clause
selector and occurrence scanner execute sequentially with an explicit
register handoff. No lookup answer or predicate is supplied to the program.
-/

import PNP.Concrete.NormalizerCandidatePacketOperations
import PNP.Concrete.NormalizerMatchingRelation

namespace PNP.Concrete.NormalizerBlocks.GraphQuery

open BitRegister Occurrence

def handoff : Block 9 := .seq (.action (.copy 0 8)) CandidatePacket.resetCore

theorem handoff_exec (r : Registers) :
    Exec handoff r.store 9 (initialRegisters r.output).store := by
  have first : Exec (.action (.copy 0 8)) r.store 1 ({r with input := r.output}).store := .action _ _
  have checked := Exec.seq first (CandidatePacket.resetCore_exec {r with input := r.output})
  exact checked

def selected (r : Registers) : Registers := ClauseQuery.packed (ClauseQuery.queryResult r).state
def selectionFuel (r : Registers) : Nat :=
  (ClauseQuery.queryResult r).fuel + ClauseQuery.packFuel (ClauseQuery.queryResult r).state
def selection : Block 9 := .seq ClauseQuery.loop ClauseQuery.pack

theorem selection_exec (r : Registers) :
    Exec selection r.store (selectionFuel r) (selected r).store :=
  Exec.seq (ClauseQuery.query_exec r) (ClauseQuery.pack_exec (ClauseQuery.queryResult r).state)

def block : Block 9 := .seq selection (.seq handoff Occurrence.block)
def result (r : Registers) : Registers := (Occurrence.result (selected r).output).state
def fuel (r : Registers) : Nat :=
  selectionFuel r + (9 + Occurrence.sourceSteps (selected r).output)

theorem block_exec (r : Registers) : Exec block r.store (fuel r) (result r).store :=
  Exec.seq (selection_exec r) (Exec.seq (handoff_exec (selected r)) (Occurrence.block_exec (selected r).output))

theorem fuel_bound (r : Registers) (bound : Nat) (bounded : r.store.Bounded bound) :
    fuel r + 1 ≤ 168 * r.input.length + 20 * bound + 264 := by
  have scan := ClauseQuery.query_fuel_bound r
  have size := (ClauseQuery.query_exec r).bounded bound bounded
  have buffer := Store.get_length_le (ClauseQuery.queryResult r).state.store (3 : Fin 9) size
  change (ClauseQuery.queryResult r).state.excess.length ≤ bound + (ClauseQuery.queryResult r).fuel at buffer
  have occurrence := Occurrence.sourceSteps_bound (selected r).output
  have outputLength : (selected r).output.length = (ClauseQuery.queryResult r).state.excess.length + 2 := by
    simp only [selected, ClauseQuery.packed, List.length_append, List.length_reverse,
      List.length_cons, List.length_nil]
  rw [outputLength] at occurrence
  simp only [fuel, selectionFuel, ClauseQuery.packFuel]
  omega

def prepared (target index data : BitString) : Registers :=
  ⟨data, index, index, false :: target, [], [], [true], target, []⟩

theorem prepared_bounded (target index data : BitString) :
    (prepared target index data).store.Bounded (target.length + index.length + data.length + 1) := by
  change data.length ≤ _ ∧ index.length ≤ _ ∧ index.length ≤ _ ∧
    (false :: target).length ≤ _ ∧ 0 ≤ _ ∧ 0 ≤ _ ∧ [true].length ≤ _ ∧
    target.length ≤ _ ∧ 0 ≤ _ ∧ True
  simp only [List.length_cons, List.length_nil]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, trivial⟩

theorem prepared_fuel_bound (target index data : BitString) :
    fuel (prepared target index data) + 1 ≤
      188 * data.length + 20 * target.length + 20 * index.length + 284 := by
  have bounded := fuel_bound (prepared target index data) _ (prepared_bounded target index data)
  change fuel (prepared target index data) + 1 ≤
    168 * data.length + 20 * (target.length + index.length + data.length + 1) + 264 at bounded
  omega

def clauseData (clauses : List (List CNFLiteral)) : BitString :=
  encodeTokenPairs (encodeClauseListTokens clauses ++ [.finish])

theorem selected_canonical (target index : Nat) (clauses : List (List CNFLiteral)) :
    (selected (prepared (List.replicate target true) (List.replicate index true) (clauseData clauses))).output =
      Occurrence.encodeQuery target (clauses[index]?.getD []) := by
  let values := encodeClauseListTokens clauses ++ [.finish]
  let start := prepared (List.replicate target true) (List.replicate index true) (clauseData clauses)
  obtain ⟨steps, canonical⟩ := ClauseQuery.tokenScan_exec values (ClauseQuery.selectionInitial target index)
  have actual := ClauseQuery.query_exec start
  have same := NANDFrontend.accepted_store_unique (ClauseQuery.loop.program 0 8)
    _ _ ⟨.running 0, start.store⟩
    (ClauseQuery.queryResult start).state.store
    (ClauseQuery.tokenScan values (ClauseQuery.selectionInitial target index)).store
    (actual.program_run 0 8) (canonical.program_run 0 8)
  have buffer := congrArg (fun store : Store 9 => store.get 3) same
  change (ClauseQuery.queryResult start).state.excess =
    (ClauseQuery.tokenScan values (ClauseQuery.selectionInitial target index)).excess at buffer
  change (ClauseQuery.queryResult start).state.excess.reverse ++ [true, false] = _
  rw [buffer]
  exact ClauseQuery.packed_canonical target index clauses

theorem result_canonical (target index : Nat) (clauses : List (List CNFLiteral)) :
    (result (prepared (List.replicate target true) (List.replicate index true) (clauseData clauses))).output =
      Occurrence.answer ((clauses[index]?.getD []).find? (fun literal => literal.variableIndex == target)) := by
  change (Occurrence.result (selected (prepared _ _ _)).output).state.output = _
  rw [← Occurrence.polynomial_output, selected_canonical, Occurrence.polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.GraphQuery

/-
Copyright (c) 2026 PNP Labs.

Derive a retained variable's owner in two finite scans: original matching
finds the source clause, then the selected-clause list determines its dense
position. Missing owners remain absent rather than becoming an invented row.
-/
import PNP.Concrete.NormalizerSelectedFoldCall

namespace PNP.Concrete.NormalizerBlocks.CacheOwner
open BitRegister Occurrence
abbrev State := DenseClauses.State

def loadOriginal : Block 16 := .seq (.action (.copy 0 13)) (.action (.copy 1 15))
def originalLoaded (r : State) : State :=
  r.withRegisters {r.registers with input := r.formula, target := r.index}
theorem loadOriginal_exec (r : State) : Exec loadOriginal r.store 2 (originalLoaded r).store :=
  Exec.seq (.action _ _) (.action _ _)
def prepareOriginal : Block 16 := .seq loadOriginal (DenseClauses.liftCore CompactClause.resetOwner)
def originalPrepared (r : State) : State := r.withRegisters (TableOwner.prepared r.index r.formula)
theorem prepareOriginal_exec (r : State) : Exec prepareOriginal r.store 11 (originalPrepared r).store :=
  Exec.seq (loadOriginal_exec r)
    (DenseClauses.liftCore_exec _ (originalLoaded r) _ _ (CompactClause.resetOwner_exec _))
def original : Block 16 := .seq prepareOriginal (DenseClauses.liftCore TableOwner.loop)
def originalResult (r : State) : State :=
  r.withRegisters (TableOwner.queryResult (TableOwner.prepared r.index r.formula)).state
def originalFuel (r : State) : Nat :=
  11 + (TableOwner.queryResult (TableOwner.prepared r.index r.formula)).fuel
theorem original_exec (r : State) : Exec original r.store (originalFuel r) (originalResult r).store :=
  Exec.seq (prepareOriginal_exec r)
    (DenseClauses.liftCore_exec _ (originalPrepared r) _ _ (TableOwner.query_exec _))
theorem original_fields (r : State) :
    (originalResult r).formula = r.formula ∧ (originalResult r).remaining = r.remaining ∧
    (originalResult r).core.variables = r.core.variables ∧
    (originalResult r).core.buffer = r.core.buffer := ⟨rfl,rfl,rfl,rfl⟩
theorem originalFuel_bound (r : State) : originalFuel r ≤ 12 * r.formula.length + 24 := by
  have checked := TableOwner.query_fuel_bound (TableOwner.prepared r.index r.formula)
  change (TableOwner.queryResult (TableOwner.prepared r.index r.formula)).fuel ≤
    12 * (r.formula.length + 1) + 1 at checked
  unfold originalFuel
  omega
theorem original_output_bound (r : State) :
    (originalResult r).registers.output.length ≤ r.index.length + 13 * r.formula.length + 14 := by
  have bounded := (TableOwner.query_exec (TableOwner.prepared r.index r.formula)).bounded
    (r.index.length + r.formula.length + 1) (CompactClause.preparedOwner_bounded r.index r.formula)
  have output := Store.get_length_le
    (TableOwner.queryResult (TableOwner.prepared r.index r.formula)).state.store (8 : Fin 9) bounded
  have fuel := originalFuel_bound r
  change (originalResult r).registers.output.length ≤ r.index.length + r.formula.length + 1 +
    (TableOwner.queryResult (TableOwner.prepared r.index r.formula)).fuel at output
  unfold originalFuel at fuel
  omega
theorem original_canonical (r : State) (target : Nat) (table : MatchingTable.Entries)
    (index : r.index = List.replicate target true) (matching : r.formula = MatchingTable.encode table) :
    (originalResult r).registers.output = TableOwner.answer (TableOwner.owner table target) := by
  change (TableOwner.queryResult (TableOwner.prepared r.index r.formula)).state.output = _
  rw [index, matching]
  exact TableOwner.prepared_canonical target table

def loadDense : Block 16 := .seq (.action (.copy 1 8)) (.action (.pop 1))
def denseLoaded (r : State) : State :=
  r.withRegisters {r.registers with target := r.registers.output.tail}
theorem loadDense_exec (r : State) : Exec loadDense r.store 2 (denseLoaded r).store :=
  Exec.seq (.action _ _) (.action _ _)
def dense : Block 16 := .seq loadDense (DenseClauses.liftCompact CompactClause.lookup)
def denseResult (r : State) : State :=
  (denseLoaded r).withCompact (CompactClause.looked (denseLoaded r).core)
def denseFuel (r : State) : Nat := 2 + CompactClause.lookupFuel (denseLoaded r).core
theorem dense_exec (r : State) : Exec dense r.store (denseFuel r) (denseResult r).store :=
  Exec.seq (loadDense_exec r)
    (DenseClauses.liftCompact_exec _ (denseLoaded r) _ _ (CompactClause.lookup_exec _))
theorem dense_fields (r : State) :
    (denseResult r).formula = r.formula ∧ (denseResult r).remaining = r.remaining ∧
    (denseResult r).core.variables = r.core.variables ∧ (denseResult r).core.buffer = r.core.buffer :=
  ⟨rfl,rfl,rfl,rfl⟩
theorem denseFuel_bound (r : State) : denseFuel r ≤ 12 * r.core.variables.length + 25 := by
  have checked := CompactClause.lookupFuel_bound (denseLoaded r).core
  change CompactClause.lookupFuel (denseLoaded r).core ≤ 12 * r.core.variables.length + 23 at checked
  unfold denseFuel
  omega
theorem dense_output_bound (r : State) :
    (denseResult r).registers.output.length ≤ r.registers.output.length + 13 * r.core.variables.length + 14 := by
  have checked := CompactClause.lookup_output_bound (denseLoaded r).core
  change (denseResult r).registers.output.length ≤
    r.registers.output.tail.length + 13 * r.core.variables.length + 14 at checked
  have tail := ParentQuery.input_tail_bound r.registers.output
  omega
theorem dense_canonical (r : State) (index : Nat) (clauses : List CNFLiteral)
    (found : r.registers.output = TableOwner.answer (some index))
    (selected : r.core.variables = SearchVertices.encodeVertices clauses) :
    (denseResult r).registers.output = TableOwner.answer (TableOwner.vertexOwner clauses index) := by
  apply CompactClause.lookup_canonical (denseLoaded r).core index clauses
  · change r.registers.output.tail = List.replicate index true
    rw [found]
    rfl
  · exact selected

def choose : Block 16 := .branch 8 .skip .skip dense
def chosen (r : State) : State :=
  if ForwardEdge.present r.registers.output then denseResult r else r
def chooseFuel (r : State) : Nat :=
  if ForwardEdge.present r.registers.output then 1 + denseFuel r else 2
theorem choose_exec (r : State) : Exec choose r.store (chooseFuel r) (chosen r).store := by
  cases found : r.registers.output with
  | nil =>
      simpa only [choose, chosen, chooseFuel, ForwardEdge.present, found, List.headD,
        Bool.false_eq_true, ite_false] using
        (Exec.empty (source := (8 : Fin 16)) (before := r.store) found (Exec.skip r.store))
  | cons bit rest =>
      cases bit with
      | false =>
          simpa only [choose, chosen, chooseFuel, ForwardEdge.present, found, List.headD,
            Bool.false_eq_true, ite_false] using
            (Exec.zero (source := (8 : Fin 16)) (before := r.store) found (Exec.skip r.store))
      | true =>
          simpa only [choose, chosen, chooseFuel, ForwardEdge.present, found, List.headD, ite_true] using
            (Exec.one (source := (8 : Fin 16)) (before := r.store) found (dense_exec r))
theorem chosen_fields (r : State) :
    (chosen r).formula = r.formula ∧ (chosen r).remaining = r.remaining ∧
    (chosen r).core.variables = r.core.variables ∧ (chosen r).core.buffer = r.core.buffer := by
  unfold chosen
  split
  · exact dense_fields r
  · exact ⟨rfl,rfl,rfl,rfl⟩
theorem chooseFuel_bound (r : State) : chooseFuel r ≤ 12 * r.core.variables.length + 26 := by
  have checked := denseFuel_bound r
  unfold chooseFuel
  split <;> omega
theorem chosen_output_bound (r : State) :
    (chosen r).registers.output.length ≤ r.registers.output.length + 13 * r.core.variables.length + 14 := by
  have checked := dense_output_bound r
  unfold chosen
  split <;> omega
theorem chosen_canonical (r : State) (owner : Option Nat) (clauses : List CNFLiteral)
    (found : r.registers.output = TableOwner.answer owner)
    (selected : r.core.variables = SearchVertices.encodeVertices clauses) :
    (chosen r).registers.output =
      TableOwner.answer (owner.bind (TableOwner.vertexOwner clauses)) := by
  cases owner with
  | none =>
      have absent : ForwardEdge.present r.registers.output = false := by rw [found]; rfl
      simp only [chosen, absent, Bool.false_eq_true, ite_false, Option.bind_none]
      exact found
  | some index =>
      have present : ForwardEdge.present r.registers.output = true := by rw [found]; rfl
      simp only [chosen, present, ite_true, Option.bind_some]
      exact dense_canonical r index clauses found selected

def lookup : Block 16 := .seq original choose
def looked (r : State) : State := chosen (originalResult r)
def lookupFuel (r : State) : Nat := originalFuel r + chooseFuel (originalResult r)
theorem lookup_exec (r : State) : Exec lookup r.store (lookupFuel r) (looked r).store :=
  Exec.seq (original_exec r) (choose_exec (originalResult r))
theorem lookup_fields (r : State) :
    (looked r).formula = r.formula ∧ (looked r).remaining = r.remaining ∧
    (looked r).core.variables = r.core.variables ∧ (looked r).core.buffer = r.core.buffer := by
  have before := original_fields r
  have after := chosen_fields (originalResult r)
  exact ⟨after.1.trans before.1,after.2.1.trans before.2.1,
    after.2.2.1.trans before.2.2.1,after.2.2.2.trans before.2.2.2⟩
theorem lookupFuel_bound (r : State) :
    lookupFuel r ≤ 12 * r.formula.length + 12 * r.core.variables.length + 50 := by
  have first := originalFuel_bound r
  have second := chooseFuel_bound (originalResult r)
  rw [(original_fields r).2.2.1] at second
  unfold lookupFuel
  omega
theorem lookup_output_bound (r : State) :
    (looked r).registers.output.length ≤
      r.index.length + 13 * r.formula.length + 13 * r.core.variables.length + 28 := by
  have first := original_output_bound r
  have second := chosen_output_bound (originalResult r)
  rw [(original_fields r).2.2.1] at second
  change (looked r).registers.output.length ≤ _ at second
  omega
def value (table : MatchingTable.Entries) (clauses : List CNFLiteral) (target : Nat) : Option Nat :=
  (TableOwner.owner table target).bind (TableOwner.vertexOwner clauses)
theorem lookup_canonical (r : State) (target : Nat) (table : MatchingTable.Entries)
    (clauses : List CNFLiteral) (index : r.index = List.replicate target true)
    (matching : r.formula = MatchingTable.encode table)
    (selected : r.core.variables = SearchVertices.encodeVertices clauses) :
    (looked r).registers.output = TableOwner.answer (value table clauses target) :=
  chosen_canonical (originalResult r) (TableOwner.owner table target) clauses
    (original_canonical r target table index matching) ((original_fields r).2.2.1.trans selected)

end PNP.Concrete.NormalizerBlocks.CacheOwner

/-
Copyright (c) 2026 PNP Labs.

One mode-table transition derives the matching choice, emits an explicit
absent or first/middle/last cell, and advances the original-clause cursor
and dense ordinal together. The growing output does not enter the cost.
-/
import PNP.Concrete.NormalizerCacheModeQuery
import PNP.Concrete.NormalizerCacheOwnerFold

namespace PNP.Concrete.NormalizerBlocks.CacheMode
open BitRegister Occurrence

def emitNone : Block 19 := liftCore (TraceCount.emit false)
def noneEmitted (r : State) : State := r.withRegisters {r.registers with output := [false]}
theorem emitNone_exec (r : State) : Exec emitNone r.store 2 (noneEmitted r).store :=
  liftCore_exec _ r _ _ (TraceCount.emit_exec false r.registers)
def choose : Block 19 := .branch 8 emitNone emitNone chooseSlot
def chosen (r : State) : State :=
  if ForwardEdge.present r.registers.output then slotChosen r else noneEmitted r
def chooseFuel (r : State) : Nat :=
  1 + if ForwardEdge.present r.registers.output then chooseSlotFuel r else 2
theorem choose_exec (r : State) : Exec choose r.store (chooseFuel r) (chosen r).store := by
  have checked := EdgeKinds.branch_head (8 : Fin 19) r.store emitNone chooseSlot 2 (chooseSlotFuel r)
    (noneEmitted r).store (slotChosen r).store (emitNone_exec r) (chooseSlot_exec r)
  change Exec choose r.store (1 + if ForwardEdge.present r.registers.output then chooseSlotFuel r else 2)
    (if ForwardEdge.present r.registers.output then (slotChosen r).store else (noneEmitted r).store) at checked
  cases h : ForwardEdge.present r.registers.output <;>
    simpa only [chooseFuel, chosen, h, Bool.false_eq_true, ite_false, ite_true] using checked
theorem chosen_fields (r : State) :
    (chosen r).core.formula = r.core.formula ∧
    (chosen r).core.remaining = r.core.remaining ∧
    (chosen r).core.core.variables = r.core.core.variables ∧
    (chosen r).core.core.buffer = r.core.core.buffer ∧
    (chosen r).matching = r.matching ∧ (chosen r).counter = r.counter := by
  unfold chosen
  split
  · exact slotChosen_fields r
  · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem chooseFuel_bound (r : State) :
    chooseFuel r ≤ 2834 * r.core.formula.length + 314 * r.counter.length + 4360 := by
  have bound := chooseSlotFuel_bound r
  unfold chooseFuel
  split <;> omega
theorem chosen_output_length (r : State) : (chosen r).registers.output.length ≤ 3 := by
  unfold chosen
  split
  · exact slotChosen_output_length r
  · change 1 ≤ 3
    omega

def mode : Block 19 := .seq transport choose
def modeResult (r : State) : State := chosen (transported r)
def modeFuel (r : State) : Nat := transportFuel r + chooseFuel (transported r)
theorem mode_exec (r : State) : Exec mode r.store (modeFuel r) (modeResult r).store :=
  Exec.seq (transport_exec r) (choose_exec (transported r))
theorem mode_fields (r : State) :
    (modeResult r).core.formula = r.core.formula ∧
    (modeResult r).core.remaining = r.core.remaining ∧
    (modeResult r).core.core.variables = r.core.core.variables ∧
    (modeResult r).core.core.buffer = r.core.core.buffer ∧
    (modeResult r).matching = r.matching ∧ (modeResult r).counter = r.counter := by
  have before := transported_fields r
  have after := chosen_fields (transported r)
  exact ⟨after.1.trans before.1,after.2.1.trans before.2.1,
    after.2.2.1.trans before.2.2.1,after.2.2.2.1.trans before.2.2.2.1,
    after.2.2.2.2.1.trans before.2.2.2.2.1,after.2.2.2.2.2.trans before.2.2.2.2.2⟩
theorem modeFuel_bound (r : State) :
    modeFuel r ≤ 755 * r.matching.length + 83 * r.core.index.length + 12 * r.core.core.variables.length +
      2834 * r.core.formula.length + 314 * r.counter.length + 5557 := by
  have matching := transportFuel_bound r
  have choice := chooseFuel_bound (transported r)
  rw [(transported_fields r).1,(transported_fields r).2.2.2.2.2] at choice
  unfold modeFuel
  omega
def value (table : MatchingTable.Entries) (variables : List CNFLiteral)
    (formula : List (List CNFLiteral)) (original row : Nat) : Option Nat :=
  (transportedValue table variables original).map (CacheSlot.encodedValue (formula[row]?.getD []))
theorem mode_canonical (r : State) (original row : Nat) (table : MatchingTable.Entries)
    (variables : List CNFLiteral) (formula : List (List CNFLiteral))
    (index : r.core.index = List.replicate original true)
    (counter : r.counter = List.replicate row true)
    (matching : r.matching = MatchingTable.encode table)
    (selected : r.core.core.variables = SearchVertices.encodeVertices variables)
    (dense : r.core.formula = GraphQuery.clauseData formula) :
    (modeResult r).registers.output = TableOwner.answer (value table variables formula original row) := by
  have found := transported_canonical r original table variables index matching selected
  cases h : transportedValue table variables original with
  | none =>
      have absent : ForwardEdge.present (transported r).registers.output = false := by rw [found,h]; rfl
      simp only [modeResult,chosen,absent,Bool.false_eq_true,ite_false,value,h,Option.map_none]
      rfl
  | some target =>
      have present : ForwardEdge.present (transported r).registers.output = true := by rw [found,h]; rfl
      simp only [modeResult,chosen,present,ite_true,value,h,Option.map_some]
      exact slotChosen_canonical (transported r) row target formula
        ((transported_fields r).2.2.2.2.2.trans counter)
        ((transported_fields r).1.trans dense) (by rw [found,h])

def entryRead (r : State) : State := r.withDense (DenseClauses.entryRead r.core)
def appended (r : State) : State := r.withDense (CacheOwner.appended r.core)
def advance : Block 19 := .action (.push 17 true)
def advanced (r : State) : State := {r with counter := true :: r.counter}
theorem advance_exec (r : State) : Exec advance r.store 1 (advanced r).store := .action _ _
def body : Block 19 :=
  .seq (liftDense DenseClauses.readEntry) (.seq mode (.seq (liftDense CacheOwner.appendEntry) advance))
def bodyResult (r : State) : State := advanced (appended (modeResult (entryRead r)))
def bodyFuel (r : State) : Nat :=
  DenseClauses.readFuel r.core + (modeFuel (entryRead r) + (CacheOwner.appendFuel (modeResult (entryRead r)).core + 1))
theorem body_exec (r : State) : Exec body r.store (bodyFuel r) (bodyResult r).store :=
  Exec.seq (liftDense_exec _ r _ _ (DenseClauses.readEntry_exec r.core))
    (Exec.seq (mode_exec (entryRead r))
      (Exec.seq (liftDense_exec _ (modeResult (entryRead r)) _ _ (CacheOwner.appendEntry_exec _))
        (advance_exec _)))
theorem body_fields (r : State) :
    (bodyResult r).core.formula = r.core.formula ∧
    (bodyResult r).core.remaining = UnseenData.next r.core.remaining ∧
    (bodyResult r).core.core.variables = r.core.core.variables ∧
    (bodyResult r).matching = r.matching ∧ (bodyResult r).counter = true :: r.counter := by
  have before := DenseClauses.read_fields r.core
  have mode := mode_fields (entryRead r)
  have append := CacheOwner.appended_fields (modeResult (entryRead r)).core
  refine ⟨append.1.trans (mode.1.trans before.2.2.1),
    append.2.1.trans (mode.2.1.trans before.2.1),
    append.2.2.trans (mode.2.2.1.trans before.2.2.2.1),mode.2.2.2.2.1,?_⟩
  change true :: (modeResult (entryRead r)).counter = true :: r.counter
  rw [mode.2.2.2.2.2]
  rfl
def bodyBound : NatPolynomial := .linear 4001 5619
theorem bodyFuel_bound (r : State) (n : Nat)
    (cursor : r.core.remaining.length ≤ n) (counter : r.counter.length ≤ n)
    (matching : r.matching.length ≤ n) (formula : r.core.formula.length ≤ n)
    (variables : r.core.core.variables.length ≤ n) : bodyFuel r ≤ bodyBound.eval n := by
  have read := DenseClauses.readFuel_bound r.core
  have index := DenseClauses.read_index_bound r.core
  have cost := modeFuel_bound (entryRead r)
  have fields := DenseClauses.read_fields r.core
  change modeFuel (entryRead r) ≤ 755 * r.matching.length + 83 * (DenseClauses.entryRead r.core).index.length +
    12 * (DenseClauses.entryRead r.core).core.variables.length +
    2834 * (DenseClauses.entryRead r.core).formula.length + 314 * r.counter.length + 5557 at cost
  rw [fields.2.2.1,fields.2.2.2.1] at cost
  have output := chosen_output_length (transported (entryRead r))
  have append := CacheOwner.appendFuel_bound (modeResult (entryRead r)).core
  change (modeResult (entryRead r)).core.registers.output.length ≤ 3 at output
  change bodyFuel r ≤ 4001 * n + 5619
  unfold bodyFuel
  omega
theorem body_canonical (r : State) (first : CNFLiteral) (rest variables : List CNFLiteral)
    (table : MatchingTable.Entries) (formula : List (List CNFLiteral)) (row : Nat)
    (remaining : r.core.remaining = SearchVertices.encodeVertices (first :: rest))
    (counter : r.counter = List.replicate row true)
    (matching : r.matching = MatchingTable.encode table)
    (selected : r.core.core.variables = SearchVertices.encodeVertices variables)
    (dense : r.core.formula = GraphQuery.clauseData formula) :
    (bodyResult r).core.remaining = SearchVertices.encodeVertices rest ∧
    (bodyResult r).counter = List.replicate (row + 1) true ∧
    (bodyResult r).core.core.buffer =
      (DenseClauses.clauseBits (MatchingTable.entryClause (value table variables formula first.variableIndex row))).reverse ++
        r.core.core.buffer := by
  have read := DenseClauses.read_canonical r.core first rest remaining
  have fields := DenseClauses.read_fields r.core
  have mode := mode_canonical (entryRead r) first.variableIndex row table variables formula
    read.1 counter matching (fields.2.2.2.1.trans selected) (fields.2.2.1.trans dense)
  have append := CacheOwner.appended_buffer (modeResult (entryRead r)).core _ mode
  refine ⟨?_,?_,?_⟩
  · exact (CacheOwner.appended_fields (modeResult (entryRead r)).core).2.1.trans
      ((mode_fields (entryRead r)).2.1.trans read.2)
  · rw [(body_fields r).2.2.2.2,counter,List.replicate_succ]
  · change (CacheOwner.appended (modeResult (entryRead r)).core).core.buffer = _
    rw [append,(mode_fields (entryRead r)).2.2.2.1]
    rfl

end PNP.Concrete.NormalizerBlocks.CacheMode

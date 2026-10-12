/-
Copyright (c) 2026 PNP Labs.

Materialize runtime cache dimensions from the actual stored selections.
The existing delimiter-counting machine is used twice. No proof-only size
is installed as data, and every completed table remains protected.
-/
import PNP.Concrete.NormalizerSourceCacheSlots
import PNP.Concrete.NormalizerClauseCountCanonical

namespace PNP.Concrete.NormalizerBlocks.SourceCacheDriver
open BitRegister Occurrence

def countInput (column : Bool) (r : State) : BitString := if column then r.variables else r.clauses
def prepareCount (column : Bool) : Block 36 :=
  .seq (.action (.copy 0 (if column then 35 else 34))) (.action (.clear 1))
def countPrepared (column : Bool) (r : State) : State :=
  r.withRegisters {r.registers with input := countInput column r, target := []}
theorem prepareCount_exec (column : Bool) (r : State) :
    Exec (prepareCount column) r.store 2 (countPrepared column r).store := by
  cases column <;>
    dsimp only [prepareCount,countPrepared,countInput,Bool.false_eq_true,ite_false,ite_true,
      CutDriver.State.withRegisters,CutDriver.State.withCore,CutDriver.State.store,CutDriver.State.frame,
      CutDriver.State.registers,MatchingDriver.State.withRegisters,MatchingDriver.State.withCore,
      MatchingDriver.State.store,MatchingDriver.State.frame,MatchingDriver.State.registers,
      Search.State.withRegisters,Search.State.withCore,Search.State.store,Search.State.frame,
      Search.State.registers,Search.State.parent,Exploration.State.withRegisters,Exploration.State.withCore,
      Exploration.State.store,Exploration.State.frame,Exploration.State.registers,
      Extraction.State.withRegisters,Extraction.State.withParent,Extraction.State.store,Extraction.State.frame,
      Extraction.State.parent,Extraction.State.registers,Eligibility.State.store,Eligibility.State.frame,
      ParentQuery.State.withRegisters,ParentQuery.State.store,ParentQuery.State.frame,ParentQuery.State.registers,
      EdgeKinds.State.store,EdgeKinds.State.frame,
      ForwardEdge.State.store,ForwardEdge.State.frame,Occurrence.Registers.store,Frame.join]
  all_goals exact .seq (.action _ _) (.action _ _)

def count (column : Bool) : Block 36 := .seq (prepareCount column) (CutDriver.liftCore ClauseCount.loop)
def counted (column : Bool) (r : State) : State :=
  r.withRegisters {r.registers with input := [], target := List.replicate (ClauseCount.count (countInput column r)) true}
def countFuel (column : Bool) (r : State) : Nat :=
  2 + (ClauseCount.run (countInput column r) (countPrepared column r).registers).fuel
theorem count_exec (column : Bool) (r : State) :
    Exec (count column) r.store (countFuel column r) (counted column r).store := by
  have run := ClauseCount.run_exec (countInput column r) (countPrepared column r).registers
  have resultEq :
      (ClauseCount.run (countInput column r) (countPrepared column r).registers).state =
        {r.registers with input := [], target := List.replicate (ClauseCount.count (countInput column r)) true} := by
    rw [ClauseCount.run_result]
    change {r.registers with input := [], target := List.replicate (ClauseCount.count (countInput column r)) true ++ []} = _
    rw [List.append_nil]
  rw [resultEq] at run
  have tail := CutDriver.liftCore_exec _ (countPrepared column r) _ _ run
  exact Exec.seq (prepareCount_exec column r) tail
theorem countFuel_bound (column : Bool) (r : State) :
    countFuel column r ≤ 6 * (countInput column r).length + 3 := by
  have bound := ClauseCount.run_fuel_bound (countInput column r) (countPrepared column r).registers
  unfold countFuel
  omega

def saveCount (column : Bool) : Block 36 := .action (.copy (if column then 23 else 24) 1)
def countSaved (column : Bool) (r : State) : State :=
  withFields r (if column then {r.core.core.core.core with skipped := r.registers.target}
    else {r.core.core.core.core with trace := r.registers.target})
theorem saveCount_exec (column : Bool) (r : State) :
    Exec (saveCount column) r.store 1 (countSaved column r).store := by
  cases column <;>
    dsimp only [saveCount,countSaved,withFields,Bool.false_eq_true,ite_false,ite_true,
      CutDriver.State.store,CutDriver.State.frame,CutDriver.State.registers,
      MatchingDriver.State.store,MatchingDriver.State.frame,MatchingDriver.State.registers,
      Search.State.store,Search.State.frame,Search.State.registers,Search.State.parent,
      Exploration.State.store,Exploration.State.frame,Exploration.State.registers,
      Extraction.State.store,Extraction.State.frame,Extraction.State.parent,Extraction.State.registers,
      Eligibility.State.store,Eligibility.State.frame,ParentQuery.State.store,ParentQuery.State.frame,
      ParentQuery.State.registers,EdgeKinds.State.store,EdgeKinds.State.frame,
      ForwardEdge.State.store,ForwardEdge.State.frame,Occurrence.Registers.store,Frame.join]
  all_goals exact .action _ _
def measure (column : Bool) : Block 36 := .seq (count column) (saveCount column)
def measured (column : Bool) (r : State) : State := countSaved column (counted column r)
def measureFuel (column : Bool) (r : State) : Nat := countFuel column r + 1
theorem measure_exec (column : Bool) (r : State) :
    Exec (measure column) r.store (measureFuel column r) (measured column r).store :=
  Exec.seq (count_exec column r) (saveCount_exec column (counted column r))
def stashSlots : Block 36 := .action (.copy 25 8)
def slotsStashed (r : State) : State := withFields r {r.core.core.core.core with active := r.registers.output}
theorem stashSlots_exec (r : State) : Exec stashSlots r.store 1 (slotsStashed r).store := by
  dsimp only [stashSlots,slotsStashed,withFields,CutDriver.State.store,CutDriver.State.frame,CutDriver.State.registers,
    MatchingDriver.State.store,MatchingDriver.State.frame,MatchingDriver.State.registers,
    Search.State.store,Search.State.frame,Search.State.registers,Search.State.parent,
    Exploration.State.store,Exploration.State.frame,Exploration.State.registers,
    Extraction.State.store,Extraction.State.frame,Extraction.State.parent,Extraction.State.registers,
    Eligibility.State.store,Eligibility.State.frame,ParentQuery.State.store,ParentQuery.State.frame,
    ParentQuery.State.registers,EdgeKinds.State.store,EdgeKinds.State.frame,
    ForwardEdge.State.store,ForwardEdge.State.frame,Occurrence.Registers.store,Frame.join]
  exact .action _ _
def finishData : Block 36 := .seq stashSlots (.seq (measure true) (measure false))
def dataFinished (r : State) : State := measured false (measured true (slotsStashed r))
def finishSteps (r : State) : Nat :=
  1 + (measureFuel true (slotsStashed r) + measureFuel false (measured true (slotsStashed r)))
theorem finishData_exec (r : State) : Exec finishData r.store (finishSteps r) (dataFinished r).store :=
  Exec.seq (stashSlots_exec r)
    (Exec.seq (measure_exec true (slotsStashed r)) (measure_exec false (measured true (slotsStashed r))))
theorem dataFinished_fields (r : State) :
    columns (dataFinished r) = List.replicate (ClauseCount.count r.variables) true ∧
    rows (dataFinished r) = List.replicate (ClauseCount.count r.clauses) true ∧
    slots (dataFinished r) = r.registers.output ∧
    modes (dataFinished r) = modes r ∧ owners (dataFinished r) = owners r ∧
    literals (dataFinished r) = literals r ∧ (dataFinished r).registers.output = r.registers.output :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem dataFinished_frame (r : State) :
    (dataFinished r).core.width = r.core.width ∧ (dataFinished r).core.formula = r.core.formula ∧
    (dataFinished r).core.table = r.core.table ∧ (dataFinished r).trace = r.trace ∧
    (dataFinished r).clauses = r.clauses ∧ (dataFinished r).variables = r.variables :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem finishSteps_bound (r : State) :
    finishSteps r ≤ 6 * r.variables.length + 6 * r.clauses.length + 9 := by
  have column := countFuel_bound true (slotsStashed r)
  have row := countFuel_bound false (measured true (slotsStashed r))
  change countFuel true (slotsStashed r) ≤ 6 * r.variables.length + 3 at column
  change countFuel false (measured true (slotsStashed r)) ≤ 6 * r.clauses.length + 3 at row
  unfold finishSteps measureFuel
  omega
theorem count_vertices (vertices : List CNFLiteral) :
    ClauseCount.count (SearchVertices.encodeVertices vertices) = vertices.length := by
  have checked := ClauseCount.count_formula (vertices.map (fun v => [v]))
  rw [List.length_map] at checked
  exact checked

end PNP.Concrete.NormalizerBlocks.SourceCacheDriver

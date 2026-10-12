/-
Copyright (c) 2026 PNP Labs.

Check one arbitrary dense three-literal clause. All three literal reads
execute, and their disjunction equals the source short-circuit result.
This is a general clause operation, not a fixed formula instance.
-/
import PNP.Concrete.NormalizerCandidateTruth

namespace PNP.Concrete.NormalizerBlocks.CandidateTruth
open BitRegister Occurrence

def setPosition : Nat → Block 19
  | 0 => .action (.clear 14)
  | n+1 => .seq (setPosition n) (.action (.push 14 true))
def positioned (position : Nat) (r : State) : State :=
  r.withDense {r.core with remaining := List.replicate position true}
theorem setPosition_exec (position : Nat) (r : State) :
    Exec (setPosition position) r.store (position + 1) (positioned position r).store := by
  induction position with
  | zero => exact .action _ _
  | succ n ih =>
      have checked := Exec.seq ih
        (show Exec (.action (.push 14 true)) (positioned n r).store 1
          (positioned (n+1) r).store from .action _ _)
      exact checked
def atPosition (position : Nat) : Block 19 := .seq (setPosition position) literal
def atResult (position : Nat) (r : State) : State := literalResult (positioned position r)
def atFuel (position : Nat) (r : State) : Nat := position + 1 + literalFuel (positioned position r)
theorem atPosition_exec (position : Nat) (r : State) :
    Exec (atPosition position) r.store (atFuel position r) (atResult position r).store :=
  Exec.seq (setPosition_exec position r) (literal_exec (positioned position r))
theorem at_fields (position : Nat) (r : State) :
    (atResult position r).core.formula = r.core.formula ∧
    (atResult position r).core.index = r.core.index ∧
    (atResult position r).matching = r.matching ∧
    (atResult position r).target = r.target := literal_fields (positioned position r)
theorem at_canonical (r : State) (formula : List (List CNFLiteral)) (row : Nat)
    (leading : List CNFLiteral) (lit : CNFLiteral) (rest : List CNFLiteral)
    (formulaRead : r.core.formula = GraphQuery.clauseData formula)
    (rowRead : r.core.index = List.replicate row true)
    (clauseRead : formula[row]?.getD [] = leading ++ lit::rest) :
    (atResult leading.length r).registers.output =
      [decide (r.matching[lit.variableIndex]?.getD false = lit.positive)] :=
  literal_canonical (positioned leading.length r) formula row leading lit rest
    formulaRead rowRead rfl clauseRead

def addTruth : Block 19 :=
  .branch 8 (.action (.copy 18 18)) (.action (.copy 18 18)) (.action (.push 18 true))
def added (r : State) : State :=
  {r with target := if ForwardEdge.present r.registers.output then true::r.target else r.target}
theorem addTruth_exec (r : State) : Exec addTruth r.store 2 (added r).store := by
  have checked := EdgeKinds.branch_head (8 : Fin 19) r.store
    (.action (.copy 18 18)) (.action (.push 18 true)) 1 1
    r.store ({r with target := true::r.target}).store (.action _ _) (.action _ _)
  change Exec addTruth r.store (1 + if ForwardEdge.present r.registers.output then 1 else 1)
    (if ForwardEdge.present r.registers.output then ({r with target := true::r.target}).store
      else r.store) at checked
  cases h : ForwardEdge.present r.registers.output <;>
    simpa only [added,h,Bool.false_eq_true,ite_false,ite_true] using checked
theorem added_truth (r : State) :
    ForwardEdge.present (added r).target =
      (ForwardEdge.present r.target || ForwardEdge.present r.registers.output) := by
  unfold added
  cases h : ForwardEdge.present r.registers.output <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,ForwardEdge.present,
      List.headD_cons,Bool.or_false,Bool.or_true]

def accumulate (position : Nat) : Block 19 := .seq (atPosition position) addTruth
def accumulated (position : Nat) (r : State) : State := added (atResult position r)
def accumulateFuel (position : Nat) (r : State) : Nat := atFuel position r + 2
theorem accumulate_exec (position : Nat) (r : State) :
    Exec (accumulate position) r.store (accumulateFuel position r) (accumulated position r).store :=
  Exec.seq (atPosition_exec position r) (addTruth_exec (atResult position r))
theorem accumulated_fields (position : Nat) (r : State) :
    (accumulated position r).core.formula = r.core.formula ∧
    (accumulated position r).core.index = r.core.index ∧
    (accumulated position r).matching = r.matching :=
  ⟨(at_fields position r).1,(at_fields position r).2.1,(at_fields position r).2.2.1⟩
theorem accumulated_truth (position : Nat) (r : State) :
    ForwardEdge.present (accumulated position r).target =
      (ForwardEdge.present r.target || ForwardEdge.present (atResult position r).registers.output) := by
  rw [accumulated,added_truth,(at_fields position r).2.2.2]
theorem accumulateFuel_bound (position : Nat) (r : State) (n : Nat)
    (small : position ≤ 2) (formula : r.core.formula.length ≤ n)
    (row : r.core.index.length ≤ n) :
    accumulateFuel position r ≤ literalBound.eval (n+2) + 5 := by
  have cost := literalFuel_bound (positioned position r) (n+2)
    (by change r.core.formula.length ≤ n+2; omega)
    (by change r.core.index.length ≤ n+2; omega)
    (by change (List.replicate position true).length ≤ n+2; rw [List.length_replicate]; omega)
  unfold accumulateFuel atFuel
  omega

def start : Block 19 := .action (.clear 18)
def started (r : State) : State := {r with target := []}
theorem start_exec (r : State) : Exec start r.store 1 (started r).store := .action _ _
def first (r : State) : State := accumulated 0 (started r)
def second (r : State) : State := accumulated 1 (first r)
def third (r : State) : State := accumulated 2 (second r)
def finish : Block 19 := .branch 18 (CacheMode.liftCore (TraceCount.emit false))
  (CacheMode.liftCore (TraceCount.emit false)) (CacheMode.liftCore (TraceCount.emit true))
def finished (r : State) : State :=
  r.withRegisters {r.registers with output := [ForwardEdge.present r.target]}
theorem finish_exec (r : State) : Exec finish r.store 3 (finished r).store := by
  have checked := EdgeKinds.branch_head (18 : Fin 19) r.store
    (CacheMode.liftCore (TraceCount.emit false)) (CacheMode.liftCore (TraceCount.emit true)) 2 2
    (r.withRegisters (TraceCount.emitted false r.registers)).store
    (r.withRegisters (TraceCount.emitted true r.registers)).store
    (CacheMode.liftCore_exec _ r _ _ (TraceCount.emit_exec false _))
    (CacheMode.liftCore_exec _ r _ _ (TraceCount.emit_exec true _))
  change Exec finish r.store (1 + if ForwardEdge.present r.target then 2 else 2)
    (if ForwardEdge.present r.target then (r.withRegisters (TraceCount.emitted true r.registers)).store
      else (r.withRegisters (TraceCount.emitted false r.registers)).store) at checked
  cases h : ForwardEdge.present r.target <;>
    simpa only [finished,TraceCount.emitted,h,Bool.false_eq_true,ite_false,ite_true] using checked

theorem finished_fields (r : State) :
    (finished r).core.formula = r.core.formula ∧
    (finished r).core.index = r.core.index ∧ (finished r).matching = r.matching :=
  ⟨rfl,rfl,rfl⟩
def clause : Block 19 :=
  .seq start (.seq (accumulate 0) (.seq (accumulate 1) (.seq (accumulate 2) finish)))
def clauseResult (r : State) : State := finished (third r)
def clauseFuel (r : State) : Nat :=
  1 + (accumulateFuel 0 (started r) + (accumulateFuel 1 (first r) +
    (accumulateFuel 2 (second r) + 3)))
theorem clause_exec (r : State) : Exec clause r.store (clauseFuel r) (clauseResult r).store :=
  Exec.seq (start_exec r) (Exec.seq (accumulate_exec 0 (started r))
    (Exec.seq (accumulate_exec 1 (first r))
      (Exec.seq (accumulate_exec 2 (second r)) (finish_exec (third r)))))
theorem first_fields (r : State) :
    (first r).core.formula = r.core.formula ∧
    (first r).core.index = r.core.index ∧ (first r).matching = r.matching :=
  accumulated_fields 0 (started r)
theorem second_fields (r : State) :
    (second r).core.formula = r.core.formula ∧
    (second r).core.index = r.core.index ∧ (second r).matching = r.matching := by
  have a := first_fields r
  have b := accumulated_fields 1 (first r)
  exact ⟨b.1.trans a.1,b.2.1.trans a.2.1,b.2.2.trans a.2.2⟩
theorem clause_fields (r : State) :
    (clauseResult r).core.formula = r.core.formula ∧
    (clauseResult r).core.index = r.core.index ∧ (clauseResult r).matching = r.matching := by
  change (finished (third r)).core.formula = r.core.formula ∧
    (finished (third r)).core.index = r.core.index ∧ (finished (third r)).matching = r.matching
  rw [(finished_fields (third r)).1,(finished_fields (third r)).2.1,(finished_fields (third r)).2.2]
  have a := second_fields r
  have b := accumulated_fields 2 (second r)
  exact ⟨b.1.trans a.1,b.2.1.trans a.2.1,b.2.2.trans a.2.2⟩
def value (assignment : BitString) (lit : CNFLiteral) : Bool :=
  decide (assignment[lit.variableIndex]?.getD false = lit.positive)
theorem clause_canonical (r : State) (formula : List (List CNFLiteral)) (row : Nat)
    (a b c : CNFLiteral) (formulaRead : r.core.formula = GraphQuery.clauseData formula)
    (rowRead : r.core.index = List.replicate row true)
    (clauseRead : formula[row]?.getD [] = [a,b,c]) :
    (clauseResult r).registers.output =
      [value r.matching a || (value r.matching b || value r.matching c)] := by
  have ha := at_canonical (started r) formula row [] a [b,c] formulaRead rowRead clauseRead
  have hb := at_canonical (first r) formula row [a] b [c]
    ((first_fields r).1.trans formulaRead) ((first_fields r).2.1.trans rowRead) clauseRead
  have hc := at_canonical (second r) formula row [a,b] c []
    ((second_fields r).1.trans formulaRead) ((second_fields r).2.1.trans rowRead) clauseRead
  change (atResult 0 (started r)).registers.output = [value r.matching a] at ha
  change (atResult 1 (first r)).registers.output = [value (first r).matching b] at hb
  change (atResult 2 (second r)).registers.output = [value (second r).matching c] at hc
  rw [(first_fields r).2.2] at hb
  rw [(second_fields r).2.2] at hc
  change [ForwardEdge.present (accumulated 2 (second r)).target] = _
  rw [accumulated_truth,hc]
  change [ForwardEdge.present (accumulated 1 (first r)).target || value r.matching c] = _
  rw [accumulated_truth,hb]
  change [(ForwardEdge.present (accumulated 0 (started r)).target || value r.matching b) ||
    value r.matching c] = _
  rw [accumulated_truth,ha]
  change [((false || value r.matching a) || value r.matching b) || value r.matching c] = _
  cases value r.matching a <;> cases value r.matching b <;> cases value r.matching c <;> rfl

def clauseBound : NatPolynomial := .add
  (.mul (.constant 3) (.add (literalBound.substitute (.linear 1 2)) (.constant 5))) (.constant 4)
theorem clauseBound_eval (n : Nat) :
    clauseBound.eval n = 3 * (literalBound.eval (n+2) + 5) + 4 := by
  change 3 * ((literalBound.substitute (.linear 1 2)).eval n + 5) + 4 = _
  rw [NatPolynomial.eval_substitute]
  change 3 * (literalBound.eval (1 * n + 2) + 5) + 4 = _
  rw [Nat.one_mul]
theorem clauseFuel_bound (r : State) (n : Nat)
    (formula : r.core.formula.length ≤ n) (row : r.core.index.length ≤ n) :
    clauseFuel r ≤ clauseBound.eval n := by
  have a := accumulateFuel_bound 0 (started r) n (by decide) formula row
  have b := accumulateFuel_bound 1 (first r) n (by decide)
    (by rw [(first_fields r).1]; exact formula) (by rw [(first_fields r).2.1]; exact row)
  have c := accumulateFuel_bound 2 (second r) n (by decide)
    (by rw [(second_fields r).1]; exact formula) (by rw [(second_fields r).2.1]; exact row)
  rw [clauseBound_eval]
  unfold clauseFuel
  omega

end PNP.Concrete.NormalizerBlocks.CandidateTruth

/-
Copyright (c) 2026 PNP Labs.

A literal is checked against the computed assignment, not against a supplied
truth value. The assignment and dense formula survive every query. The
polynomial bound includes the actual encoded literal index on raw inputs.
-/
import PNP.Concrete.NormalizerBitLookup
import PNP.Concrete.NormalizerCacheSigmaRead

namespace PNP.Concrete.NormalizerBlocks.CandidateTruth
open BitRegister Occurrence
abbrev State := CacheMode.State

def prepareBit : Block 19 := .seq (.action (.copy 17 8)) (.action (.copy 0 16))
def bitPrepared (r : State) : State :=
  {r.withRegisters {r.registers with input := r.matching} with counter := r.registers.output}
theorem prepareBit_exec (r : State) : Exec prepareBit r.store 2 (bitPrepared r).store :=
  Exec.seq (.action _ _) (.action _ _)
def readBit : Block 19 := .seq prepareBit (CacheMode.liftCore BitLookup.read)
def bitRead (r : State) : State :=
  (bitPrepared r).withRegisters (BitLookup.result (bitPrepared r).registers)
def bitFuel (r : State) : Nat := 2 + BitLookup.fuel (bitPrepared r).registers
theorem readBit_exec (r : State) : Exec readBit r.store (bitFuel r) (bitRead r).store :=
  Exec.seq (prepareBit_exec r)
    (CacheMode.liftCore_exec _ (bitPrepared r) _ _ (BitLookup.read_exec _))

def compareCase (sign : Bool) : Block 19 :=
  .branch 8 (CacheMode.liftCore (TraceCount.emit (!sign)))
    (CacheMode.liftCore (TraceCount.emit (!sign)))
    (CacheMode.liftCore (TraceCount.emit sign))
def caseCompared (sign : Bool) (r : State) : State :=
  r.withRegisters {r.registers with output := [decide (ForwardEdge.present r.registers.output = sign)]}
theorem compareCase_exec (sign : Bool) (r : State) :
    Exec (compareCase sign) r.store 3 (caseCompared sign r).store := by
  have checked := EdgeKinds.branch_head (8 : Fin 19) r.store
    (CacheMode.liftCore (TraceCount.emit (!sign))) (CacheMode.liftCore (TraceCount.emit sign))
    2 2 (r.withRegisters (TraceCount.emitted (!sign) r.registers)).store
    (r.withRegisters (TraceCount.emitted sign r.registers)).store
    (CacheMode.liftCore_exec _ r _ _ (TraceCount.emit_exec (!sign) _))
    (CacheMode.liftCore_exec _ r _ _ (TraceCount.emit_exec sign _))
  change Exec (compareCase sign) r.store (1 + if ForwardEdge.present r.registers.output then 2 else 2)
    (if ForwardEdge.present r.registers.output then
      (r.withRegisters (TraceCount.emitted sign r.registers)).store else
      (r.withRegisters (TraceCount.emitted (!sign) r.registers)).store) at checked
  cases sign <;> cases h : ForwardEdge.present r.registers.output <;>
    simpa only [caseCompared,TraceCount.emitted,h,Bool.false_eq_true,ite_false,ite_true,
      Bool.not_true,Bool.not_false,decide_true,decide_false,Bool.true_eq_false] using checked

def compare : Block 19 := .branch 17 (compareCase false) (compareCase false) (compareCase true)
def compared (r : State) : State := caseCompared (ForwardEdge.present r.counter) r
theorem compare_exec (r : State) : Exec compare r.store 4 (compared r).store := by
  have checked := EdgeKinds.branch_head (17 : Fin 19) r.store
    (compareCase false) (compareCase true) 3 3
    (caseCompared false r).store (caseCompared true r).store
    (compareCase_exec false r) (compareCase_exec true r)
  change Exec compare r.store (1 + if ForwardEdge.present r.counter then 3 else 3)
    (if ForwardEdge.present r.counter then (caseCompared true r).store else
      (caseCompared false r).store) at checked
  cases h : ForwardEdge.present r.counter <;>
    simpa only [compared,h,Bool.false_eq_true,ite_false,ite_true] using checked

def literalRead (r : State) : State := r.withDense (CacheLiteral.result r.core)
def literal : Block 19 :=
  .seq (CacheMode.liftDense CacheLiteral.read) (.seq readBit compare)
def literalResult (r : State) : State := compared (bitRead (literalRead r))
def literalFuel (r : State) : Nat :=
  CacheLiteral.fuel r.core + (bitFuel (literalRead r) + 4)
theorem literal_exec (r : State) :
    Exec literal r.store (literalFuel r) (literalResult r).store :=
  Exec.seq (CacheMode.liftDense_exec _ r _ _ (CacheLiteral.read_exec _))
    (Exec.seq (readBit_exec (literalRead r)) (compare_exec (bitRead (literalRead r))))
theorem literal_fields (r : State) :
    (literalResult r).core.formula = r.core.formula ∧
    (literalResult r).core.index = r.core.index ∧
    (literalResult r).matching = r.matching ∧
    (literalResult r).target = r.target :=
  ⟨(CacheLiteral.result_fields r.core).1,(CacheLiteral.result_fields r.core).2.2.1,rfl,rfl⟩
theorem literal_output (r : State) :
    (literalResult r).registers.output =
      [decide (r.matching[(CacheLiteral.result r.core).registers.target.length]?.getD false =
        ForwardEdge.present (CacheLiteral.result r.core).registers.output)] := by
  change [decide (ForwardEdge.present (BitLookup.result (bitPrepared (literalRead r)).registers).output =
    ForwardEdge.present (CacheLiteral.result r.core).registers.output)] = _
  rw [BitLookup.result_output]
  rfl
theorem literal_canonical (r : State) (formula : List (List CNFLiteral)) (row : Nat)
    (leading : List CNFLiteral) (lit : CNFLiteral) (rest : List CNFLiteral)
    (formulaRead : r.core.formula = GraphQuery.clauseData formula)
    (rowRead : r.core.index = List.replicate row true)
    (positionRead : r.core.remaining = List.replicate leading.length true)
    (clauseRead : formula[row]?.getD [] = leading ++ lit::rest) :
    (literalResult r).registers.output =
      [decide (r.matching[lit.variableIndex]?.getD false = lit.positive)] := by
  have found := CacheLiteral.canonical r.core formula row leading lit rest
    formulaRead rowRead positionRead clauseRead
  rw [literal_output,found.1,found.2,List.length_replicate]
  rfl
def literalBound : NatPolynomial := .add CacheLiteral.bound (.linear 630 865)
theorem literalFuel_bound (r : State) (n : Nat)
    (formula : r.core.formula.length ≤ n) (row : r.core.index.length ≤ n)
    (position : r.core.remaining.length ≤ n) : literalFuel r ≤ literalBound.eval n := by
  have query := CacheLiteral.fuel_bound r.core n formula row position
  have index := CacheLiteral.result_index_bound r.core
  change literalFuel r ≤ CacheLiteral.bound.eval n + (630 * n + 865)
  change CacheLiteral.fuel r.core +
    (2 + (3 * (CacheLiteral.result r.core).registers.target.length + 4) + 4) ≤ _
  omega

end PNP.Concrete.NormalizerBlocks.CandidateTruth

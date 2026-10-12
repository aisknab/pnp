/-
Copyright (c) 2026 PNP Labs.

Closed indexed literal access over the cached dense formula. Both the row
and literal position are runtime unary words. The reader returns the actual
literal index and a normalized sign, preserving the formula and caller buffer.
-/
import PNP.Concrete.NormalizerCacheLiteralScan
import PNP.Concrete.NormalizerDenseQuery

namespace PNP.Concrete.NormalizerBlocks.CacheLiteral
open BitRegister Occurrence

theorem bits_append (left right : List CNFLiteral) :
    CompactClause.bits (left ++ right) = CompactClause.bits left ++ CompactClause.bits right := by
  induction left with
  | nil => rfl
  | cons literal rest ih =>
      rw [List.cons_append,CompactClause.bits_cons,CompactClause.bits_cons,ih,List.append_assoc]

def readAt : Block 16 := .seq CacheSlot.prepare select
def atRead (r : State) : State := selected (CacheSlot.prepared r)
def atFuel (r : State) : Nat := 2 + selectFuel (CacheSlot.prepared r)
theorem readAt_exec (r : State) : Exec readAt r.store (atFuel r) (atRead r).store :=
  Exec.seq (CacheSlot.prepare_exec r) (select_exec (CacheSlot.prepared r))
theorem atFuel_bound (r : State) :
    atFuel r ≤ 2 + (3 * r.registers.output.length + 25) * (r.remaining.length + 1) := by
  have cost := selectFuel_bound (CacheSlot.prepared r)
  have shorter := ParentQuery.input_tail_bound r.registers.output
  have mul := Nat.mul_le_mul_right (r.remaining.length + 1)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 3 shorter) 25)
  change selectFuel (CacheSlot.prepared r) ≤
    (3 * r.registers.output.tail.length + 25) * (r.remaining.length + 1) at cost
  unfold atFuel
  omega
theorem atRead_canonical (r : State) (leading : List CNFLiteral) (literal : CNFLiteral)
    (rest : List CNFLiteral)
    (query : r.registers.output = Occurrence.encodeQuery 0 (leading ++ literal::rest))
    (position : r.remaining = List.replicate leading.length true) :
    (atRead r).registers.target = List.replicate literal.variableIndex true ∧
      ForwardEdge.present (atRead r).core.positive = literal.positive := by
  apply selected_canonical (CacheSlot.prepared r) leading literal
    (CompactClause.bits rest ++ [true,false]) _ position
  change r.registers.output.tail = _
  rw [query,CompactClause.occurrence_data,bits_append,CompactClause.bits_cons]
  simp only [List.append_assoc]

def emitSign : Block 16 :=
  .branch 12 (DenseClauses.liftCore (TraceCount.emit false))
    (DenseClauses.liftCore (TraceCount.emit false))
    (DenseClauses.liftCore (TraceCount.emit true))
def signEmitted (r : State) : State :=
  r.withRegisters {r.registers with output := [ForwardEdge.present r.core.positive]}
theorem emitSign_exec (r : State) : Exec emitSign r.store 3 (signEmitted r).store := by
  have checked := EdgeKinds.branch_head (12 : Fin 16) r.store
    (DenseClauses.liftCore (TraceCount.emit false)) (DenseClauses.liftCore (TraceCount.emit true))
    2 2 (r.withRegisters (TraceCount.emitted false r.registers)).store
    (r.withRegisters (TraceCount.emitted true r.registers)).store
    (DenseClauses.liftCore_exec _ r _ _ (TraceCount.emit_exec false _))
    (DenseClauses.liftCore_exec _ r _ _ (TraceCount.emit_exec true _))
  change Exec emitSign r.store (1 + if ForwardEdge.present r.core.positive then 2 else 2)
    (if ForwardEdge.present r.core.positive then
      (r.withRegisters (TraceCount.emitted true r.registers)).store else
      (r.withRegisters (TraceCount.emitted false r.registers)).store) at checked
  cases h : ForwardEdge.present r.core.positive <;>
    simpa only [signEmitted,TraceCount.emitted,h,Bool.false_eq_true,ite_false,ite_true] using checked

def read : Block 16 := .seq DenseClauses.query (.seq readAt emitSign)
def result (r : State) : State := signEmitted (atRead (DenseClauses.queried r))
def fuel (r : State) : Nat := DenseClauses.queryFuel r + (atFuel (DenseClauses.queried r) + 3)
theorem read_exec (r : State) : Exec read r.store (fuel r) (result r).store :=
  Exec.seq (DenseClauses.query_exec r)
    (Exec.seq (readAt_exec (DenseClauses.queried r)) (emitSign_exec (atRead (DenseClauses.queried r))))
theorem result_fields (r : State) :
    (result r).formula = r.formula ∧ (result r).remaining = [] ∧
    (result r).index = r.index ∧ (result r).core.variables = r.core.variables ∧
    (result r).core.buffer = r.core.buffer :=
  selected_fields (CacheSlot.prepared (DenseClauses.queried r))
theorem result_sign_length (r : State) : (result r).registers.output.length = 1 := rfl
theorem result_index_bound (r : State) :
    (result r).registers.target.length ≤ 189 * r.formula.length + 21 * r.index.length + 285 := by
  have index := selected_index_bound (CacheSlot.prepared (DenseClauses.queried r))
  have tail := ParentQuery.input_tail_bound (DenseClauses.queried r).registers.output
  have size := DenseClauses.query_output_bound r
  change (result r).registers.target.length ≤
    (DenseClauses.queried r).registers.output.tail.length at index
  omega
def bound : NatPolynomial := .add (.linear 208 302) (.mul (.linear 630 880) (.linear 1 1))
theorem fuel_bound (r : State) (n : Nat)
    (formula : r.formula.length ≤ n) (row : r.index.length ≤ n)
    (position : r.remaining.length ≤ n) : fuel r ≤ bound.eval n := by
  have query := DenseClauses.queryFuel_bound r
  have size := DenseClauses.query_output_bound r
  have read := atFuel_bound (DenseClauses.queried r)
  change atFuel (DenseClauses.queried r) ≤ 2 +
    (3 * (DenseClauses.queried r).registers.output.length + 25) * (r.remaining.length + 1) at read
  have factors := Nat.mul_le_mul
    (show 3 * (DenseClauses.queried r).registers.output.length + 25 ≤ 630 * n + 880 by omega)
    (show r.remaining.length + 1 ≤ n + 1 by omega)
  change fuel r ≤ (208 * n + 302) + (630 * n + 880) * (1 * n + 1)
  simp only [Nat.one_mul]
  unfold fuel
  omega
theorem canonical (r : State) (formula : List (List CNFLiteral)) (row : Nat)
    (leading : List CNFLiteral) (literal : CNFLiteral) (rest : List CNFLiteral)
    (formulaRead : r.formula = GraphQuery.clauseData formula)
    (rowRead : r.index = List.replicate row true)
    (positionRead : r.remaining = List.replicate leading.length true)
    (clauseRead : formula[row]?.getD [] = leading ++ literal::rest) :
    (result r).registers.target = List.replicate literal.variableIndex true ∧
      (result r).registers.output = [literal.positive] := by
  have query := DenseClauses.query_canonical r row formula rowRead formulaRead
  rw [clauseRead] at query
  have read := atRead_canonical (DenseClauses.queried r) leading literal rest query positionRead
  exact ⟨read.1,congrArg (fun b => [b]) read.2⟩

end PNP.Concrete.NormalizerBlocks.CacheLiteral

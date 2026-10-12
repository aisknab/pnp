/-
Copyright (c) 2026 PNP Labs.

Append one whole dense clause using the selected-variable list preserved by
the controller. Clause boundaries are emitted explicitly, including empty
clauses. The existing arbitrary-length compactor performs every literal
lookup; its finite execution and full cost are reused without a new scan.
-/
import PNP.Concrete.NormalizerDenseQuery

namespace PNP.Concrete.NormalizerBlocks.DenseClauses
open BitRegister Occurrence

def clauseBits (literals : List CNFLiteral) : BitString :=
  encodeTokenPairs (encodeClauseTokens literals)
theorem clauseBits_data (literals : List CNFLiteral) :
    clauseBits literals = [false,true] ++ CompactClause.bits literals ++ [true,false] := by
  simp only [clauseBits, encodeClauseTokens, CompactClause.bits,
    NANDFrontend.encodeTokenPairs_append, encodeTokenPairs, CNFToken.bits,
    List.cons_append, List.nil_append, List.append_nil]
theorem clauseBits_reverse_append (literals : List CNFLiteral) (buffer : BitString) :
    (clauseBits literals).reverse ++ buffer =
      false :: true :: ((CompactClause.bits literals).reverse ++ true :: false :: buffer) := by
  rw [clauseBits_data]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.cons_append,
    List.nil_append, List.append_assoc]

def prepareClause : Block 16 :=
  .seq (.action (.copy 9 8)) <| .seq (.action (.pop 9)) <|
    .seq (.action (.push 11 false)) (.action (.push 11 true))
def clausePrepared (r : State) : State :=
  {r with core := {r.core with pending := r.registers.output.tail, buffer := true :: false :: r.core.buffer}}
theorem prepareClause_exec (r : State) : Exec prepareClause r.store 4 (clausePrepared r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def compact : Block 16 := liftCompact CompactClause.loop
def compacted (r : State) : State := r.withCompact (CompactClause.whole r.core).state
theorem compact_exec (r : State) :
    Exec compact r.store (CompactClause.whole r.core).fuel (compacted r).store :=
  liftCompact_exec _ r _ _ (CompactClause.whole_exec r.core)

def closeClause : Block 16 := .seq (.action (.push 11 true)) (.action (.push 11 false))
def clauseClosed (r : State) : State :=
  {r with core := {r.core with buffer := false :: true :: r.core.buffer}}
theorem closeClause_exec (r : State) : Exec closeClause r.store 2 (clauseClosed r).store :=
  Exec.seq (.action _ _) (.action _ _)

def appendClause : Block 16 := .seq prepareClause (.seq compact closeClause)
def appended (r : State) : State := clauseClosed (compacted (clausePrepared r))
def appendFuel (r : State) : Nat := 4 + ((CompactClause.whole (clausePrepared r).core).fuel + 2)
theorem appendClause_exec (r : State) : Exec appendClause r.store (appendFuel r) (appended r).store :=
  Exec.seq (prepareClause_exec r)
    (Exec.seq (compact_exec (clausePrepared r)) (closeClause_exec (compacted (clausePrepared r))))

theorem appended_fields (r : State) :
    (appended r).formula = r.formula ∧
    (appended r).remaining = r.remaining ∧
    (appended r).index = r.index ∧
    (appended r).core.variables = r.core.variables :=
  ⟨rfl,rfl,rfl,CompactClause.whole_variables (clausePrepared r).core⟩

def appendBound (querySize variablesSize : Nat) : Nat :=
  (7 * querySize + 64 * variablesSize + 119) * (querySize + 1) + 7
theorem appendFuel_bound (r : State) :
    appendFuel r ≤ appendBound r.registers.output.length r.core.variables.length := by
  have bound := CompactClause.whole_fuel_bound (clausePrepared r).core
  change (CompactClause.whole (clausePrepared r).core).fuel ≤
    (7 * r.registers.output.tail.length + 64 * r.core.variables.length + 119) *
      (r.registers.output.tail.length + 1) + 1 at bound
  have tail := ParentQuery.input_tail_bound r.registers.output
  have product := Nat.mul_le_mul
    (show 7 * r.registers.output.tail.length + 64 * r.core.variables.length + 119 ≤
      7 * r.registers.output.length + 64 * r.core.variables.length + 119 by omega)
    (show r.registers.output.tail.length + 1 ≤ r.registers.output.length + 1 by omega)
  unfold appendFuel appendBound
  omega

theorem appended_buffer (r : State) (vertices literals : List CNFLiteral)
    (selected : r.registers.output = Occurrence.encodeQuery 0 literals)
    (variables : r.core.variables = SearchVertices.encodeVertices vertices) :
    (appended r).core.buffer =
      (clauseBits (CompactClause.value vertices literals)).reverse ++ r.core.buffer := by
  have pending : (clausePrepared r).core.pending = CompactClause.bits literals ++ [true,false] := by
    change r.registers.output.tail = _
    rw [selected, CompactClause.occurrence_data]
  have buffer := CompactClause.whole_buffer vertices literals (clausePrepared r).core pending variables
  change false :: true :: (CompactClause.whole (clausePrepared r).core).state.buffer = _
  rw [buffer, clauseBits_reverse_append]
  rfl

end PNP.Concrete.NormalizerBlocks.DenseClauses

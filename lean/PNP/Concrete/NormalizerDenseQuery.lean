/-
Copyright (c) 2026 PNP Labs.

Read the selected original clause from the protected formula using the
already verified finite indexed-clause scanner. Only the actual decoded
index is used; dense clause data is not supplied. Cost and output bounds
depend on original formula/index sizes, not the growing output buffer.
-/
import PNP.Concrete.NormalizerDenseRead

namespace PNP.Concrete.NormalizerBlocks.DenseClauses
open BitRegister Occurrence

def loadFormula : Block 16 := .action (.copy 0 13)
def formulaLoaded (r : State) : State := r.withRegisters {r.registers with input := r.formula}
theorem loadFormula_exec (r : State) : Exec loadFormula r.store 1 (formulaLoaded r).store := .action _ _

def resetQuery : Block 16 := liftCore CandidatePacket.resetCore
def queryReset (r : State) : State := r.withRegisters (initialRegisters r.registers.input)
theorem resetQuery_exec (r : State) : Exec resetQuery r.store 8 (queryReset r).store :=
  liftCore_exec _ r _ _ (CandidatePacket.resetCore_exec r.registers)

def setupQuery : Block 16 :=
  .seq (.action (.copy 1 15)) <| .seq (.action (.copy 2 15)) <|
    .seq (.action (.push 3 false)) (.action (.push 6 true))
def querySetup (r : State) : State :=
  r.withRegisters {r.registers with target := r.index, remaining := r.index, excess := false :: r.registers.excess, active := true :: r.registers.active}
theorem setupQuery_exec (r : State) : Exec setupQuery r.store 4 (querySetup r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def prepareQuery : Block 16 := .seq loadFormula (.seq resetQuery setupQuery)
def queryPrepared (r : State) : State := r.withRegisters (GraphQuery.prepared [] r.index r.formula)
theorem prepareQuery_exec (r : State) : Exec prepareQuery r.store 13 (queryPrepared r).store :=
  Exec.seq (loadFormula_exec r)
    (Exec.seq (resetQuery_exec (formulaLoaded r)) (setupQuery_exec (queryReset (formulaLoaded r))))

def query : Block 16 := .seq prepareQuery (liftCore GraphQuery.selection)
def queried (r : State) : State :=
  r.withRegisters (GraphQuery.selected (GraphQuery.prepared [] r.index r.formula))
def queryFuel (r : State) : Nat :=
  13 + GraphQuery.selectionFuel (GraphQuery.prepared [] r.index r.formula)
theorem query_exec (r : State) : Exec query r.store (queryFuel r) (queried r).store :=
  Exec.seq (prepareQuery_exec r)
    (liftCore_exec _ (queryPrepared r) _ _ (GraphQuery.selection_exec (queryPrepared r).registers))

theorem selectionFuel_bound (index formula : BitString) :
    GraphQuery.selectionFuel (GraphQuery.prepared [] index formula) ≤
      188 * formula.length + 20 * index.length + 284 := by
  have bound := GraphQuery.prepared_fuel_bound [] index formula
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at bound
  unfold GraphQuery.fuel at bound
  omega

theorem queryFuel_bound (r : State) :
    queryFuel r ≤ 188 * r.formula.length + 20 * r.index.length + 297 := by
  have bound := selectionFuel_bound r.index r.formula
  unfold queryFuel
  omega

theorem queried_fields (r : State) :
    (queried r).formula = r.formula ∧
    (queried r).remaining = r.remaining ∧
    (queried r).index = r.index ∧
    (queried r).core.variables = r.core.variables ∧
    (queried r).core.buffer = r.core.buffer := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem query_output_bound (r : State) :
    (queried r).registers.output.length ≤
      189 * r.formula.length + 21 * r.index.length + 285 := by
  let prepared := GraphQuery.prepared [] r.index r.formula
  have bounded := (GraphQuery.selection_exec prepared).bounded _
    (GraphQuery.prepared_bounded [] r.index r.formula)
  have output := Store.get_length_le (GraphQuery.selected prepared).store (8 : Fin 9) bounded
  change (queried r).registers.output.length ≤
    0 + r.index.length + r.formula.length + 1 + GraphQuery.selectionFuel prepared at output
  have fuel := selectionFuel_bound r.index r.formula
  change GraphQuery.selectionFuel prepared ≤
    188 * r.formula.length + 20 * r.index.length + 284 at fuel
  omega

theorem query_canonical (r : State) (index : Nat) (formula : List (List CNFLiteral))
    (indexRead : r.index = List.replicate index true)
    (formulaRead : r.formula = GraphQuery.clauseData formula) :
    (queried r).registers.output = Occurrence.encodeQuery 0 (formula[index]?.getD []) := by
  change (GraphQuery.selected (GraphQuery.prepared [] r.index r.formula)).output = _
  rw [indexRead, formulaRead]
  exact GraphQuery.selected_canonical 0 index formula

end PNP.Concrete.NormalizerBlocks.DenseClauses

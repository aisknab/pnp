/-
Copyright (c) 2026 PNP Labs.

Protected coefficient-construction state. Formula, three lookup tables,
assignment and failed/current rows are runtime data. Row-count and byte
buffers use the two fields preserved by all cached readers.
-/
import PNP.Concrete.NormalizerCoefficientCache

namespace PNP.Concrete.NormalizerBlocks.Coefficient
open BitRegister Occurrence
structure State where
  core : CoefficientCache.State
  assignment : BitString
  failed : BitString
  variableIndex : BitString
  row : BitString
  auxiliary : BitString
def State.frame (r : State) : Store 5 :=
  .cons r.assignment (.cons r.failed (.cons r.variableIndex (.cons r.row (.cons r.auxiliary .nil))))
def State.store (r : State) : Store 24 := Frame.join r.core.store r.frame
def State.registers (r : State) : Registers := r.core.registers
def State.withCore (r : State) (core : CoefficientCache.State) : State := {r with core := core}
def State.withDense (r : State) (dense : DenseClauses.State) : State := r.withCore (r.core.withDense dense)
def State.withRegisters (r : State) (core : Registers) : State := r.withCore (r.core.withRegisters core)
def State.count (r : State) : BitString := r.core.core.core.variables
def State.buffer (r : State) : BitString := r.core.core.core.buffer
def liftCache (body : Block 19) : Block 24 := Frame.block 5 body
theorem liftCache_exec (body : Block 19) (r : State) (fuel : Nat) (after : CoefficientCache.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (liftCache body) r.store fuel (r.withCore after).store := Frame.execution checked r.frame
def liftCore (body : Block 9) : Block 24 := liftCache (CacheMode.liftCore body)
theorem liftCore_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.registers.store fuel after.store) :
    Exec (liftCore body) r.store fuel (r.withRegisters after).store :=
  liftCache_exec _ r _ _ (CacheMode.liftCore_exec _ r.core _ _ checked)
def liftDense (body : Block 16) : Block 24 := liftCache (CacheMode.liftDense body)
theorem liftDense_exec (body : Block 16) (r : State) (fuel : Nat) (after : DenseClauses.State)
    (checked : Exec body r.core.core.store fuel after.store) :
    Exec (liftDense body) r.store fuel (r.withDense after).store :=
  liftCache_exec _ r _ _ (CacheMode.liftDense_exec _ r.core _ _ checked)

structure Data where
  literals : BitString
  owners : BitString
  slots : BitString
  modes : BitString
  assignment : BitString
  failed : BitString
  row : BitString
def State.data (r : State) : Data :=
  ⟨r.core.core.formula,r.core.matching,r.core.counter,r.core.target,r.assignment,r.failed,r.row⟩

inductive Index where
  | variableIndex | row | failed | auxiliary
def indexWord : Index → State → BitString
  | .variableIndex,r => r.variableIndex
  | .row,r => r.row
  | .failed,r => r.failed
  | .auxiliary,r => r.auxiliary
def indexRegister : Index → Fin 24
  | .variableIndex => 21
  | .row => 22
  | .failed => 20
  | .auxiliary => 23
def loadIndex (index : Index) : Block 24 := .action (.copy 15 (indexRegister index))
def indexLoaded (index : Index) (r : State) : State :=
  r.withDense {r.core.core with index := indexWord index r}
theorem loadIndex_exec (index : Index) (r : State) :
    Exec (loadIndex index) r.store 1 (indexLoaded index r).store := by
  cases index <;> exact .action _ _
def query (kind : CoefficientCache.Kind) (index : Index) : Block 24 :=
  .seq (loadIndex index) (liftCache (CoefficientCache.read kind))
def queried (kind : CoefficientCache.Kind) (index : Index) (r : State) : State :=
  (indexLoaded index r).withCore (CoefficientCache.result kind (indexLoaded index r).core)
def queryFuel (kind : CoefficientCache.Kind) (index : Index) (r : State) : Nat :=
  1 + CoefficientCache.fuel kind (indexLoaded index r).core
theorem query_exec (kind : CoefficientCache.Kind) (index : Index) (r : State) :
    Exec (query kind index) r.store (queryFuel kind index r) (queried kind index r).store :=
  Exec.seq (loadIndex_exec index r)
    (liftCache_exec _ (indexLoaded index r) _ _ (CoefficientCache.read_exec kind _))
theorem queried_data (kind : CoefficientCache.Kind) (index : Index) (r : State) :
    (queried kind index r).data = r.data := by
  cases kind <;> rfl
theorem queried_buffers (kind : CoefficientCache.Kind) (index : Index) (r : State) :
    (queried kind index r).count = r.count ∧ (queried kind index r).buffer = r.buffer := by
  cases kind <;> exact ⟨rfl,rfl⟩
theorem queried_indices (kind : CoefficientCache.Kind) (index : Index) (r : State) :
    (queried kind index r).variableIndex = r.variableIndex ∧
    (queried kind index r).auxiliary = r.auxiliary := ⟨rfl,rfl⟩
theorem queryFuel_bound (kind : CoefficientCache.Kind) (index : Index) (r : State) :
    queryFuel kind index r ≤
      755 * (CoefficientCache.table kind r.core).length + 83 * (indexWord index r).length + 1172 := by
  have cost := CoefficientCache.fuel_bound kind (indexLoaded index r).core
  have table : CoefficientCache.table kind (indexLoaded index r).core = CoefficientCache.table kind r.core := by
    cases kind <;> rfl
  rw [table] at cost
  change CoefficientCache.fuel kind (indexLoaded index r).core ≤
    755 * (CoefficientCache.table kind r.core).length + 83 * (indexWord index r).length + 1171 at cost
  unfold queryFuel
  omega
theorem queried_output_bound (kind : CoefficientCache.Kind) (index : Index) (r : State) :
    (queried kind index r).registers.output.length ≤
      756 * (CoefficientCache.table kind r.core).length + 84 * (indexWord index r).length + 1151 := by
  have bound := CoefficientCache.output_bound kind (indexLoaded index r).core
  have table : CoefficientCache.table kind (indexLoaded index r).core = CoefficientCache.table kind r.core := by
    cases kind <;> rfl
  rw [table] at bound
  exact bound
theorem query_canonical (kind : CoefficientCache.Kind) (index : Index) (r : State)
    (entries : MatchingTable.Entries) (i : Nat)
    (table : CoefficientCache.table kind r.core = MatchingTable.encode entries)
    (selected : indexWord index r = List.replicate i true) :
    (queried kind index r).registers.output = TableOwner.answer (MatchingTable.read entries i) := by
  apply CoefficientCache.canonical kind (indexLoaded index r).core i entries selected
  cases kind <;> exact table

end PNP.Concrete.NormalizerBlocks.Coefficient

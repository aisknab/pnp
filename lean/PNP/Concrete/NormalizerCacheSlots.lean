/-
Copyright (c) 2026 PNP Labs.

Construct all slot cells by indexing an already computed mode table with
the already computed owner list. Source coherence supplies the later
equality proof; the machine performs real reads and accepts no slot answers.
-/
import PNP.Concrete.NormalizerCacheCell

namespace PNP.Concrete.NormalizerBlocks.CacheSlots
open BitRegister
abbrev State := DenseClauses.State

def body : Block 16 := .seq DenseClauses.readEntry (.seq CacheCell.read CacheOwner.appendEntry)
def bodyResult (r : State) : State := CacheOwner.appended (CacheCell.result (DenseClauses.entryRead r))
def bodyFuel (r : State) : Nat :=
  DenseClauses.readFuel r + (CacheCell.fuel (DenseClauses.entryRead r) +
    CacheOwner.appendFuel (CacheCell.result (DenseClauses.entryRead r)))
theorem body_exec (r : State) : Exec body r.store (bodyFuel r) (bodyResult r).store :=
  Exec.seq (DenseClauses.readEntry_exec r)
    (Exec.seq (CacheCell.read_exec (DenseClauses.entryRead r)) (CacheOwner.appendEntry_exec _))
theorem body_fields (r : State) :
    (bodyResult r).formula = r.formula ∧
    (bodyResult r).remaining = UnseenData.next r.remaining ∧
    (bodyResult r).core.variables = r.core.variables := by
  have read := DenseClauses.read_fields r
  have cell := CacheCell.result_fields (DenseClauses.entryRead r)
  have append := CacheOwner.appended_fields (CacheCell.result (DenseClauses.entryRead r))
  exact ⟨append.1.trans (cell.1.trans read.2.2.1),
    append.2.1.trans (cell.2.1.trans read.2.1),
    append.2.2.trans (cell.2.2.2.1.trans read.2.2.2.1)⟩
def bodyBound : NatPolynomial := .linear 4201 5824
theorem bodyFuel_bound (r : State) (n : Nat) (remaining : r.remaining.length ≤ n)
    (formula : r.formula.length ≤ n) (_variables : r.core.variables.length ≤ n) :
    bodyFuel r ≤ bodyBound.eval n := by
  have read := DenseClauses.readFuel_bound r
  have index := DenseClauses.read_index_bound r
  have cell := CacheCell.fuel_bound (DenseClauses.entryRead r)
  have output := CacheCell.output_bound (DenseClauses.entryRead r)
  rw [(DenseClauses.read_fields r).2.2.1] at cell output
  have append := CacheOwner.appendFuel_bound (CacheCell.result (DenseClauses.entryRead r))
  change bodyFuel r ≤ 4201 * n + 5824
  unfold bodyFuel
  omega
def value (modes : MatchingTable.Entries) (owner : CNFLiteral) : Option Nat :=
  MatchingTable.read modes owner.variableIndex
theorem body_buffer (r : State) (first : CNFLiteral) (rest : List CNFLiteral)
    (modes : MatchingTable.Entries)
    (remaining : r.remaining = SearchVertices.encodeVertices (first :: rest))
    (modeRead : r.formula = MatchingTable.encode modes) :
    (bodyResult r).core.buffer =
      (DenseClauses.clauseBits (MatchingTable.entryClause (value modes first))).reverse ++ r.core.buffer := by
  have read := DenseClauses.read_canonical r first rest remaining
  have cell := CacheCell.canonical (DenseClauses.entryRead r) modes first.variableIndex
    ((DenseClauses.read_fields r).2.2.1.trans modeRead) read.1
  have append := CacheOwner.appended_buffer (CacheCell.result (DenseClauses.entryRead r)) _ cell
  rw [(CacheCell.result_fields (DenseClauses.entryRead r)).2.2.2.2,
    (DenseClauses.read_fields r).2.2.2.2] at append
  exact append
def operation : SelectedFold.Operation where
  body := body
  after := bodyResult
  cost := bodyFuel
  execution := body_exec
  remaining := fun r => (body_fields r).2.1
  fields := fun r => ⟨(body_fields r).1,(body_fields r).2.2⟩
  bound := bodyBound
  cost_bound := bodyFuel_bound
def call : Block 16 := SelectedFold.call operation
def called (r : State) : State := SelectedFold.called operation r
def callSteps (r : State) : Nat := SelectedFold.callSteps operation r
def callBound : NatPolynomial := SelectedFold.callBound operation
theorem call_exec (r : State) : Exec call r.store (callSteps r) (called r).store :=
  SelectedFold.call_exec operation r
theorem callSteps_bound (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    callSteps r ≤ callBound.eval n := SelectedFold.callSteps_bound operation r n bounded
def values (modes : MatchingTable.Entries) (owners : List CNFLiteral) : MatchingTable.Entries :=
  owners.map (value modes)
theorem prefix_values (modes : MatchingTable.Entries) (owners : List CNFLiteral) :
    SelectedFold.prefixBits (fun owner => DenseClauses.clauseBits (MatchingTable.entryClause (value modes owner))) owners =
      DenseClauses.prefixBits (MatchingTable.clauses (values modes owners)) := by
  induction owners with
  | nil => rfl
  | cons first rest ih =>
      simp only [SelectedFold.prefix_cons,values,List.map_cons,MatchingTable.clauses,
        DenseClauses.prefix_cons] at *
      rw [ih]
theorem called_canonical (r : State) (modes : MatchingTable.Entries) (owners : List CNFLiteral)
    (modeRead : r.formula = MatchingTable.encode modes)
    (ownerRead : r.remaining = SearchVertices.encodeVertices owners) :
    (called r).registers.output = MatchingTable.encode (values modes owners) := by
  have contract : SelectedFold.BodyOutput operation (MatchingTable.encode modes) r.core.variables
      (fun owner => DenseClauses.clauseBits (MatchingTable.entryClause (value modes owner))) := by
    intro state first rest table _variables remaining
    exact body_buffer state first rest modes remaining table
  have checked := SelectedFold.called_output operation _ _ _ contract owners r ownerRead modeRead rfl
  rw [prefix_values,DenseClauses.prefix_data] at checked
  exact checked

end PNP.Concrete.NormalizerBlocks.CacheSlots

/-
Copyright (c) 2026 PNP Labs.

Append one derived owner entry and traverse actual selected-variable bytes.
The output has exactly one optional owner cell per selection, including
missing-owner cases. Costs are independent of the accumulated table buffer.
-/
import PNP.Concrete.NormalizerCacheOwnerQuery

namespace PNP.Concrete.NormalizerBlocks.CacheOwner
open BitRegister Occurrence

def beginEntry : Block 16 :=
  .seq (.action (.push 11 false)) <| .seq (.action (.push 11 true)) <|
    .seq (.action (.clear 12)) (.action (.push 12 true))
def entryStarted (r : State) : State :=
  {r with core := {r.core with buffer := true :: false :: r.core.buffer, positive := [true]}}
theorem beginEntry_exec (r : State) : Exec beginEntry r.store 4 (entryStarted r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
def emitOwner : Block 16 := DenseClauses.liftCompact CompactClause.choose
def ownerEmitted (r : State) : State := r.withCompact (CompactClause.chosen r.core)
theorem emitOwner_exec (r : State) :
    Exec emitOwner r.store (CompactClause.chooseFuel r.core) (ownerEmitted r).store :=
  DenseClauses.liftCompact_exec _ r _ _ (CompactClause.choose_exec r.core)
def appendEntry : Block 16 := .seq beginEntry (.seq emitOwner DenseClauses.closeClause)
def appended (r : State) : State := DenseClauses.clauseClosed (ownerEmitted (entryStarted r))
def appendFuel (r : State) : Nat := 4 + (CompactClause.chooseFuel (entryStarted r).core + 2)
theorem appendEntry_exec (r : State) : Exec appendEntry r.store (appendFuel r) (appended r).store :=
  Exec.seq (beginEntry_exec r)
    (Exec.seq (emitOwner_exec (entryStarted r)) (DenseClauses.closeClause_exec _))
theorem appended_fields (r : State) :
    (appended r).formula = r.formula ∧ (appended r).remaining = r.remaining ∧
    (appended r).core.variables = r.core.variables :=
  ⟨rfl,rfl,(CompactClause.chosen_fields (entryStarted r).core).2.1⟩
theorem appendFuel_bound (r : State) : appendFuel r ≤ 4 * r.registers.output.length + 18 := by
  have checked := CompactClause.chooseFuel_bound (entryStarted r).core
  change CompactClause.chooseFuel (entryStarted r).core ≤ 4 * r.registers.output.length + 12 at checked
  unfold appendFuel
  omega
theorem entry_literal (owner : Option Nat) :
    CompactClause.literalOutput (owner.map (fun index => ⟨true,index⟩)) =
      CompactClause.bits (MatchingTable.entryClause owner) := by
  cases owner with
  | none => rfl
  | some index =>
      change NANDFrontend.literalBits true index = CompactClause.bits [⟨true,index⟩]
      rw [CompactClause.bits_cons]
      change NANDFrontend.literalBits true index = NANDFrontend.literalBits true index ++ []
      exact (List.append_nil _).symm
theorem appended_buffer (r : State) (owner : Option Nat)
    (found : r.registers.output = TableOwner.answer owner) :
    (appended r).core.buffer =
      (DenseClauses.clauseBits (MatchingTable.entryClause owner)).reverse ++ r.core.buffer := by
  have checked := CompactClause.chosen_buffer (entryStarted r).core true owner rfl found
  rw [entry_literal] at checked
  change false :: true :: (CompactClause.chosen (entryStarted r).core).buffer = _
  rw [checked, DenseClauses.clauseBits_reverse_append]
  rfl

def body : Block 16 := .seq DenseClauses.readEntry (.seq lookup appendEntry)
def bodyResult (r : State) : State := appended (looked (DenseClauses.entryRead r))
def bodyFuel (r : State) : Nat :=
  DenseClauses.readFuel r + (lookupFuel (DenseClauses.entryRead r) + appendFuel (looked (DenseClauses.entryRead r)))
theorem body_exec (r : State) : Exec body r.store (bodyFuel r) (bodyResult r).store :=
  Exec.seq (DenseClauses.readEntry_exec r)
    (Exec.seq (lookup_exec (DenseClauses.entryRead r)) (appendEntry_exec _))
theorem body_fields (r : State) :
    (bodyResult r).formula = r.formula ∧
    (bodyResult r).remaining = UnseenData.next r.remaining ∧
    (bodyResult r).core.variables = r.core.variables := by
  have read := DenseClauses.read_fields r
  have lookup := lookup_fields (DenseClauses.entryRead r)
  have append := appended_fields (looked (DenseClauses.entryRead r))
  exact ⟨append.1.trans (lookup.1.trans read.2.2.1),
    append.2.1.trans (lookup.2.1.trans read.2.1),
    append.2.2.trans (lookup.2.2.1.trans read.2.2.2.1)⟩
def bodyBound : NatPolynomial := .linear 135 211
theorem bodyFuel_bound (r : State) (bound : Nat)
    (remaining : r.remaining.length ≤ bound) (matching : r.formula.length ≤ bound)
    (clauses : r.core.variables.length ≤ bound) : bodyFuel r ≤ bodyBound.eval bound := by
  have read := DenseClauses.readFuel_bound r
  have index := DenseClauses.read_index_bound r
  have lookup := lookupFuel_bound (DenseClauses.entryRead r)
  have output := lookup_output_bound (DenseClauses.entryRead r)
  rw [(DenseClauses.read_fields r).2.2.1,(DenseClauses.read_fields r).2.2.2.1] at lookup output
  have append := appendFuel_bound (looked (DenseClauses.entryRead r))
  change bodyFuel r ≤ 135 * bound + 211
  unfold bodyFuel
  omega
theorem body_buffer (r : State) (first : CNFLiteral) (rest clauses : List CNFLiteral)
    (table : MatchingTable.Entries)
    (remaining : r.remaining = SearchVertices.encodeVertices (first :: rest))
    (selected : r.core.variables = SearchVertices.encodeVertices clauses)
    (matching : r.formula = MatchingTable.encode table) :
    (bodyResult r).core.buffer =
      (DenseClauses.clauseBits (MatchingTable.entryClause (value table clauses first.variableIndex))).reverse ++
        r.core.buffer := by
  have read := DenseClauses.read_canonical r first rest remaining
  have lookup := lookup_canonical (DenseClauses.entryRead r) first.variableIndex table clauses read.1
    ((DenseClauses.read_fields r).2.2.1.trans matching)
    ((DenseClauses.read_fields r).2.2.2.1.trans selected)
  have checked := appended_buffer (looked (DenseClauses.entryRead r)) _ lookup
  rw [(lookup_fields (DenseClauses.entryRead r)).2.2.2,(DenseClauses.read_fields r).2.2.2.2] at checked
  exact checked

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
theorem callSteps_bound (r : State) (bound : Nat) (bounded : r.store.Bounded bound) :
    callSteps r ≤ callBound.eval bound := SelectedFold.callSteps_bound operation r bound bounded
def values (table : MatchingTable.Entries) (clauses selected : List CNFLiteral) : MatchingTable.Entries :=
  selected.map (fun vertex => value table clauses vertex.variableIndex)
theorem prefix_values (table : MatchingTable.Entries) (clauses selected : List CNFLiteral) :
    SelectedFold.prefixBits
      (fun vertex => DenseClauses.clauseBits (MatchingTable.entryClause (value table clauses vertex.variableIndex))) selected =
      DenseClauses.prefixBits (MatchingTable.clauses (values table clauses selected)) := by
  induction selected with
  | nil => rfl
  | cons first rest ih =>
      simp only [SelectedFold.prefix_cons, values, List.map_cons, MatchingTable.clauses,
        DenseClauses.prefix_cons] at *
      rw [ih]
theorem called_canonical (r : State) (table : MatchingTable.Entries) (clauses selected : List CNFLiteral)
    (matching : r.formula = MatchingTable.encode table)
    (selectedClauses : r.core.variables = SearchVertices.encodeVertices clauses)
    (selectedVariables : r.remaining = SearchVertices.encodeVertices selected) :
    (called r).registers.output = MatchingTable.encode (values table clauses selected) := by
  have contract : SelectedFold.BodyOutput operation (MatchingTable.encode table)
      (SearchVertices.encodeVertices clauses)
      (fun vertex => DenseClauses.clauseBits (MatchingTable.entryClause (value table clauses vertex.variableIndex))) := by
    intro r first rest matching clauses remaining
    exact body_buffer r first rest _ table remaining clauses matching
  have checked := SelectedFold.called_output operation _ _ _ contract selected r
    selectedVariables matching selectedClauses
  rw [prefix_values, DenseClauses.prefix_data] at checked
  exact checked

end PNP.Concrete.NormalizerBlocks.CacheOwner

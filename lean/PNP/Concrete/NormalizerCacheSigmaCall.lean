/-
Copyright (c) 2026 PNP Labs.

Compute a candidate variable value by reading its actual cached owner,
slot and literal. Every lookup executes finite code. The dense formula,
owner and slot tables and caller buffer remain protected for later reads.
-/
import PNP.Concrete.NormalizerCacheSigmaRead

namespace PNP.Concrete.NormalizerBlocks.CacheSigma
open BitRegister Occurrence

def stashOwner : Block 19 := .seq (.action (.copy 18 8)) (.action (.pop 18))
def ownerStashed (r : State) : State := {r with target := r.registers.output.tail}
theorem stashOwner_exec (r : State) : Exec stashOwner r.store 2 (ownerStashed r).store :=
  Exec.seq (.action _ _) (.action _ _)
def readOwner : Block 19 := .seq (readTable false) stashOwner
def ownerRead (r : State) : State := ownerStashed (tableRead false r)
def ownerFuel (r : State) : Nat := readFuel false r + 2
theorem readOwner_exec (r : State) : Exec readOwner r.store (ownerFuel r) (ownerRead r).store :=
  Exec.seq (readTable_exec false r) (stashOwner_exec (tableRead false r))

def loadLiteral : Block 19 :=
  .seq (.action (.copy 15 18)) (.seq (.action (.copy 14 8)) (.action (.pop 14)))
def literalLoaded (r : State) : State :=
  r.withDense {r.core with index := r.target, remaining := r.registers.output.tail}
theorem loadLiteral_exec (r : State) : Exec loadLiteral r.store 3 (literalLoaded r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
def setup : Block 19 := .seq readOwner (.seq (readTable true) loadLiteral)
def ready (r : State) : State := literalLoaded (tableRead true (ownerRead r))
def setupFuel (r : State) : Nat := ownerFuel r + (readFuel true (ownerRead r) + 3)
theorem setup_exec (r : State) : Exec setup r.store (setupFuel r) (ready r).store :=
  Exec.seq (readOwner_exec r) (Exec.seq (readTable_exec true (ownerRead r))
    (loadLiteral_exec (tableRead true (ownerRead r))))
theorem ready_fields (r : State) :
    (ready r).core.formula = r.core.formula ∧
    (ready r).core.index = (tableRead false r).registers.output.tail ∧
    (ready r).core.remaining = (tableRead true (ownerRead r)).registers.output.tail ∧
    (ready r).core.core.variables = r.core.core.variables ∧
    (ready r).core.core.buffer = r.core.core.buffer ∧
    (ready r).matching = r.matching ∧ (ready r).counter = r.counter :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def read : Block 19 := .seq setup (CacheMode.liftDense CacheLiteral.read)
def result (r : State) : State := (ready r).withDense (CacheLiteral.result (ready r).core)
def fuel (r : State) : Nat := setupFuel r + CacheLiteral.fuel (ready r).core
theorem read_exec (r : State) : Exec read r.store (fuel r) (result r).store :=
  Exec.seq (setup_exec r) (CacheMode.liftDense_exec _ (ready r) _ _ (CacheLiteral.read_exec _))
theorem result_fields (r : State) :
    (result r).core.formula = r.core.formula ∧
    (result r).core.core.variables = r.core.core.variables ∧
    (result r).core.core.buffer = r.core.core.buffer ∧
    (result r).matching = r.matching ∧ (result r).counter = r.counter := by
  have fields := CacheLiteral.result_fields (ready r).core
  exact ⟨fields.1,fields.2.2.2.1,fields.2.2.2.2,rfl,rfl⟩
theorem result_sign_length (r : State) : (result r).registers.output.length = 1 :=
  CacheLiteral.result_sign_length (ready r).core

def InputsBounded (r : State) (n : Nat) : Prop :=
  r.core.formula.length ≤ n ∧ r.matching.length ≤ n ∧
    r.counter.length ≤ n ∧ r.core.index.length ≤ n
def querySize : NatPolynomial := .linear 840 1151
theorem ready_bounded (r : State) (n : Nat) (bounded : InputsBounded r n) :
    (ready r).core.formula.length ≤ querySize.eval n ∧
    (ready r).core.index.length ≤ querySize.eval n ∧
    (ready r).core.remaining.length ≤ querySize.eval n := by
  have owner := tableRead_output_bound false r
  have slot := tableRead_output_bound true (ownerRead r)
  have ownerTail := ParentQuery.input_tail_bound (tableRead false r).registers.output
  have slotTail := ParentQuery.input_tail_bound (tableRead true (ownerRead r)).registers.output
  change (tableRead false r).registers.output.length ≤
    756 * r.matching.length + 84 * r.core.index.length + 1151 at owner
  change (tableRead true (ownerRead r)).registers.output.length ≤
    756 * r.counter.length + 84 * r.core.index.length + 1151 at slot
  rw [(ready_fields r).1,(ready_fields r).2.1,(ready_fields r).2.2.1]
  change r.core.formula.length ≤ 840 * n + 1151 ∧
    (tableRead false r).registers.output.tail.length ≤ 840 * n + 1151 ∧
    (tableRead true (ownerRead r)).registers.output.tail.length ≤ 840 * n + 1151
  rcases bounded with ⟨hf,ho,hs,hi⟩
  exact ⟨by omega,by omega,by omega⟩
theorem setupFuel_bound (r : State) (n : Nat) (bounded : InputsBounded r n) :
    setupFuel r ≤ 1676 * n + 2347 := by
  have owner := readFuel_bound false r
  have slot := readFuel_bound true (ownerRead r)
  change readFuel false r ≤ 755 * r.matching.length + 83 * r.core.index.length + 1171 at owner
  change readFuel true (ownerRead r) ≤ 755 * r.counter.length + 83 * r.core.index.length + 1171 at slot
  rcases bounded with ⟨_,ho,hs,hi⟩
  unfold setupFuel ownerFuel
  omega
def bound : NatPolynomial := .add (.linear 1676 2347) (CacheLiteral.bound.substitute querySize)
theorem bound_eval (n : Nat) :
    bound.eval n = (1676 * n + 2347) + CacheLiteral.bound.eval (querySize.eval n) := by
  change (1676 * n + 2347) + (CacheLiteral.bound.substitute querySize).eval n = _
  rw [NatPolynomial.eval_substitute]
theorem fuel_bound (r : State) (n : Nat) (bounded : InputsBounded r n) : fuel r ≤ bound.eval n := by
  have setup := setupFuel_bound r n bounded
  have sizes := ready_bounded r n bounded
  have query := CacheLiteral.fuel_bound (ready r).core (querySize.eval n) sizes.1 sizes.2.1 sizes.2.2
  rw [bound_eval]
  exact Nat.add_le_add setup query

theorem canonical (r : State) (owners slots : MatchingTable.Entries) (formula : List (List CNFLiteral))
    (v owner : Nat) (leading : List CNFLiteral) (literal : CNFLiteral) (rest : List CNFLiteral)
    (ownerBytes : r.matching = MatchingTable.encode owners)
    (slotBytes : r.counter = MatchingTable.encode slots)
    (literalBytes : r.core.formula = GraphQuery.clauseData formula)
    (variableRead : r.core.index = List.replicate v true)
    (ownerValue : MatchingTable.read owners v = some owner)
    (slotValue : MatchingTable.read slots v = some leading.length)
    (literalValue : formula[owner]?.getD [] = leading ++ literal::rest) :
    (result r).registers.target = List.replicate literal.variableIndex true ∧
      (result r).registers.output = [literal.positive] := by
  have ho := tableRead_canonical false r v owners variableRead ownerBytes
  have hs := tableRead_canonical true (ownerRead r) v slots variableRead slotBytes
  rw [ownerValue] at ho
  rw [slotValue] at hs
  have ownerInput : (ready r).core.index = List.replicate owner true := by
    rw [(ready_fields r).2.1,ho]
    rfl
  have slotInput : (ready r).core.remaining = List.replicate leading.length true := by
    rw [(ready_fields r).2.2.1,hs]
    rfl
  exact CacheLiteral.canonical (ready r).core formula owner leading literal rest
    literalBytes ownerInput slotInput literalValue

end PNP.Concrete.NormalizerBlocks.CacheSigma

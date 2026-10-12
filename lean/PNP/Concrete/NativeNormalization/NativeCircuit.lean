import PNP.Concrete.NativeNormalization.NativeTseitin

namespace PNP.Concrete.NativeNormalization.NativeTseitin

open PNP PNP.Concrete PNP.DirectWire PNP.DirectWire.LockedNANDTrace

/-- A syntactic transformation: no gate evaluation or assignment search occurs here. -/
def formula {n : Nat} (C : Circuit n) : CNFFormula :=
  { variableCount := n + 2 + C.gateCount
    clauses := [unitClause n false, unitClause (n + 1) true] ++
      programClauses C.program ++
      [unitClause (n + 2 + C.outputGate.val) true] }

theorem formula_shape {n : Nat} (C : Circuit n) :
    (formula C).variableCount = n + 2 + C.gateCount ∧
    (formula C).clauses.length = 3 * C.gateCount + 3 ∧
    ∀ ls ∈ (formula C).clauses, ls.length = 3 ∧
      ∀ l ∈ ls, l.variableIndex < (formula C).variableCount := by
  obtain ⟨hp, hs⟩ := programClauses_shape C.program
  refine ⟨rfl, ?_, ?_⟩
  · simp [formula, hp]
  · intro ls hm
    simp only [formula, List.mem_append, List.mem_cons, List.mem_nil_iff,
      or_false] at hm
    rcases hm with ((rfl | rfl) | hm) | rfl
    · simp [unitClause, formula]
      omega
    · simp [unitClause, formula]
      omega
    · exact hs ls hm
    · simp [unitClause, formula]

theorem formula_holds_iff {n : Nat} (C : Circuit n) (v : Nat → Bool) :
    holds v (formula C).clauses ↔
      v n = false ∧ v (n + 1) = true ∧
      holds v (programClauses C.program) ∧
      v (n + 2 + C.outputGate.val) = true := by
  simp only [formula, holds_append]
  simp [holds, unit_iff, and_assoc]

def ofGlobal (n : Nat) (v : Nat → Bool) : BitString :=
  List.ofFn fun i : Fin n => v i.val

def readValues (a : BitString) (k : Nat) : Bool := (a[k]?).getD false

theorem ofGlobal_read (n : Nat) (a : BitString) (h : a.length = n) :
    ofGlobal n (readValues a) = a :=
  NativeSourceEquations.vector_list n a h

theorem satisfied_iff_holds (F : CNFFormula) (v : Nat → Bool)
    (bounds : ∀ ls ∈ F.clauses, ∀ l ∈ ls, l.variableIndex < F.variableCount) :
    F.Satisfied (ofGlobal F.variableCount v) ↔ holds v F.clauses := by
  have lit (ls : List CNFLiteral) (hls : ls ∈ F.clauses)
      (l : CNFLiteral) (hl : l ∈ ls) :
      LiteralSatisfied l (ofGlobal F.variableCount v) ↔
        v l.variableIndex = l.positive := by
    simp only [LiteralSatisfied, ofGlobal, CNFCore.assignmentAt_fn,
      dif_pos (bounds ls hls l hl), Option.some.injEq]
  constructor
  · intro h ls hls
    obtain ⟨l, hl, hs⟩ := (CNFCore.clauseSatisfied_iff _ _).mp
      ((CNFCore.clausesSatisfied_iff _ _).mp h.2 ls hls)
    exact ⟨l, hl, (lit ls hls l hl).mp hs⟩
  · intro h
    refine ⟨by simp [ofGlobal], (CNFCore.clausesSatisfied_iff _ _).mpr ?_⟩
    intro ls hls
    obtain ⟨l, hl, hs⟩ := h ls hls
    exact (CNFCore.clauseSatisfied_iff _ _).mpr ⟨l, hl, (lit ls hls l hl).mpr hs⟩

/-- A specification of semantic extension, not a polynomial-time gate evaluator. -/
def extendValues {n g : Nat} (input : Valuation n) (gates : Valuation g)
    (k : Nat) : Bool :=
  if h : k < n then input ⟨k, h⟩
  else if h1 : k = n then false
  else if h2 : k = n + 1 then true
  else if h : k < n + 2 + g then gates ⟨k - (n + 2), by omega⟩
  else false

theorem extend_input {n g : Nat} (input : Valuation n) (gates : Valuation g)
    (i : Fin n) : extendValues input gates i.val = input i := by
  simp [extendValues, i.isLt]

theorem extend_false {n g : Nat} (input : Valuation n) (gates : Valuation g) :
    extendValues input gates n = false := by
  simp [extendValues]

theorem extend_true {n g : Nat} (input : Valuation n) (gates : Valuation g) :
    extendValues input gates (n + 1) = true := by
  have h : ¬ n + 1 < n := by omega
  have unequal : n + 1 ≠ n := by omega
  unfold extendValues
  rw [dif_neg h, dif_neg unequal, dif_pos (rfl : n + 1 = n + 1)]

theorem extend_gate {n g : Nat} (input : Valuation n) (gates : Valuation g)
    (j : Fin g) : extendValues input gates (n + 2 + j.val) = gates j := by
  have h0 : ¬ n + 2 + j.val < n := by omega
  have h1 : n + 2 + j.val ≠ n := by omega
  have h2 : n + 2 + j.val ≠ n + 1 := by omega
  have h3 : n + 2 + j.val < n + 2 + g := by omega
  simp [extendValues, h0, h1, h2, h3]

def extendModel {n : Nat} (C : Circuit n) (input : Valuation n) : BitString :=
  ofGlobal (formula C).variableCount (extendValues input (C.program.eval input))

def projectInput {n : Nat} (_C : Circuit n) (a : BitString) : Valuation n :=
  fun i => readValues a i.val

/-- Every satisfying circuit input extends to a satisfying three-CNF assignment. -/
theorem extend_model {n : Nat} (C : Circuit n) (input : Valuation n)
    (ho : C.program.eval input C.outputGate = true) :
    (formula C).Satisfied (extendModel C input) := by
  apply (satisfied_iff_holds (formula C) _
    (fun ls hl => (formula_shape C).2.2 ls hl |>.2)).mpr
  rw [formula_holds_iff]
  refine ⟨extend_false _ _, extend_true _ _, ?_, ?_⟩
  · apply (program_iff C.program _ (extend_false _ _) (extend_true _ _)).mpr
    have hi : (fun i : Fin n => extendValues input (C.program.eval input) i.val) =
        input := funext (extend_input input (C.program.eval input))
    rw [hi]
    exact extend_gate input (C.program.eval input)
  · rw [extend_gate]
    exact ho

/-- Every satisfying three-CNF assignment projects to a satisfying circuit input. -/
theorem project_model {n : Nat} (C : Circuit n) (a : BitString)
    (h : (formula C).Satisfied a) :
    C.program.eval (projectInput C a) C.outputGate = true := by
  have ha : (formula C).Satisfied
      (ofGlobal (formula C).variableCount (readValues a)) := by
    rw [ofGlobal_read _ _ h.1]
    exact h
  have hc := (satisfied_iff_holds (formula C) (readValues a)
    (fun ls hl => (formula_shape C).2.2 ls hl |>.2)).mp ha
  obtain ⟨hf, ht, hp, ho⟩ := (formula_holds_iff C _).mp hc
  have hg := (program_iff C.program _ hf ht).mp hp C.outputGate
  exact hg.symm.trans ho

theorem circuit_satisfiable_iff {n : Nat} (C : Circuit n) :
    (formula C).Satisfiable ↔ C.Satisfiable := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨projectInput C a, project_model C a ha⟩
  · rintro ⟨input, ho⟩
    exact ⟨extendModel C input, extend_model C input ho⟩

/-- The existing arbitrary-CNF compiler handles empty clauses and invalid references. -/
def frontend (F : CNFFormula) : CNFFormula :=
  formula (CNFToNAND.compiledFormulaCircuit F)

def recoverOriginal (F : CNFFormula) (a : BitString) : BitString :=
  List.ofFn (projectInput (CNFToNAND.compiledFormulaCircuit F) a)

theorem frontend_satisfiable_iff (F : CNFFormula) :
    (frontend F).Satisfiable ↔ F.Satisfiable :=
  (circuit_satisfiable_iff _).trans (CNFToNAND.compiledFormulaCircuit_satisfiable_iff F)

theorem frontend_recovery (F : CNFFormula) (a : BitString)
    (h : (frontend F).Satisfied a) : F.Satisfied (recoverOriginal F a) :=
  (CNFToNAND.compiledFormulaCircuit_eval_eq_true_iff F _).mp
    (project_model _ a h)

theorem frontend_shape (F : CNFFormula) :
    ∀ ls ∈ (frontend F).clauses, ls.length = 3 ∧
      ∀ l ∈ ls, l.variableIndex < (frontend F).variableCount :=
  (formula_shape _).2.2


end PNP.Concrete.NativeNormalization.NativeTseitin

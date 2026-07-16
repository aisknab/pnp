/-
Copyright (c) 2026 PNP Labs.

External encoded-size accounting for the concrete Cook--Levin formula.

The polynomial in this file is fixed by one proof-bearing verifier and is
evaluated only at the external source-input length.  It bounds the actual
canonical unary-indexed CNF encoding already proved semantically correct by
the preceding Cook--Levin development.

This file does not implement the formula builder as a raw machine, does not
claim a construction-runtime bound, and does not package a polynomial
reduction or NP-completeness theorem.
-/

import PNP.Concrete.CookLevinRawTapeBridge

namespace PNP.Concrete

namespace CookLevin

/-! ### Exact canonical-encoding lengths -/

/-- One unary natural contributes its payload and one terminating token. -/
theorem encodeUnaryTokens_length (count : Nat) :
    (encodeUnaryTokens count).length = count + 1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change Nat.succ (encodeUnaryTokens count).length = Nat.succ count + 1
      rw [ih]

/-- Exact token cost of one unary-indexed literal. -/
def literalTokenCost (literal : CNFLiteral) : Nat :=
  literal.variableIndex + 2

/-- Exact token cost of one clause, including its separator and terminator. -/
def clauseTokenCost (clause : List CNFLiteral) : Nat :=
  2 + (clause.map literalTokenCost).sum

/-- Exact token cost of a finite clause list. -/
def clauseListTokenCost (clauses : List (List CNFLiteral)) : Nat :=
  (clauses.map clauseTokenCost).sum

theorem encodeLiteralTokens_length (literal : CNFLiteral) :
    (encodeLiteralTokens literal).length = literalTokenCost literal := by
  unfold encodeLiteralTokens literalTokenCost
  split <;> simp [encodeUnaryTokens_length] <;> omega

theorem encodeLiteralListTokens_length (clause : List CNFLiteral) :
    (encodeLiteralListTokens clause).length =
      (clause.map literalTokenCost).sum := by
  induction clause with
  | nil => rfl
  | cons literal rest ih =>
      change
        (encodeLiteralTokens literal ++
          encodeLiteralListTokens rest).length =
        literalTokenCost literal + (rest.map literalTokenCost).sum
      rw [List.length_append, encodeLiteralTokens_length, ih]

theorem encodeClauseTokens_length (clause : List CNFLiteral) :
    (encodeClauseTokens clause).length = clauseTokenCost clause := by
  unfold encodeClauseTokens clauseTokenCost
  rw [List.length_cons, List.length_append,
    encodeLiteralListTokens_length]
  simp
  omega

theorem encodeClauseListTokens_length
    (clauses : List (List CNFLiteral)) :
    (encodeClauseListTokens clauses).length = clauseListTokenCost clauses := by
  induction clauses with
  | nil => rfl
  | cons clause rest ih =>
      change
        (encodeClauseTokens clause ++ encodeClauseListTokens rest).length =
          clauseTokenCost clause + (rest.map clauseTokenCost).sum
      rw [List.length_append, encodeClauseTokens_length, ih]
      rfl

theorem encodeCNFTokens_length (formula : CNFFormula) :
    (encodeCNFTokens formula).length =
      (formula.variableCount + 1) +
        clauseListTokenCost formula.clauses + 1 := by
  unfold encodeCNFTokens
  rw [List.length_append, List.length_append, encodeUnaryTokens_length,
    encodeClauseListTokens_length]
  rfl

/-- Exact raw-bit length of the canonical formula encoding. -/
theorem encodeCNF_size_exact (formula : CNFFormula) :
    BitString.size (encodeCNF formula) =
      2 * ((formula.variableCount + 1) +
        clauseListTokenCost formula.clauses + 1) + 1 := by
  unfold BitString.size encodeCNF
  rw [List.length_append, encodeTokenPairs_length, encodeCNFTokens_length]
  rfl

/-! ### Generic scoped-formula size bounds -/

theorem literalTokenCost_le {literal : CNFLiteral}
    {declaredVariables variableBound : Nat}
    (hLiteral : literal.variableIndex < declaredVariables)
    (hVariables : declaredVariables ≤ variableBound) :
    literalTokenCost literal ≤ variableBound + 1 := by
  unfold literalTokenCost
  omega

theorem literalTokenCost_sum_le (clause : List CNFLiteral)
    {declaredVariables variableBound : Nat}
    (hScoped : ∀ literal, literal ∈ clause →
      literal.variableIndex < declaredVariables)
    (hVariables : declaredVariables ≤ variableBound) :
    (clause.map literalTokenCost).sum ≤
      clause.length * (variableBound + 1) := by
  induction clause with
  | nil => simp
  | cons literal rest ih =>
      have hLiteral : literalTokenCost literal ≤ variableBound + 1 :=
        literalTokenCost_le (hScoped literal (List.Mem.head rest)) hVariables
      have hRest : (rest.map literalTokenCost).sum ≤
          rest.length * (variableBound + 1) := by
        apply ih
        intro candidate hCandidate
        exact hScoped candidate (List.Mem.tail literal hCandidate)
      change
        literalTokenCost literal + (rest.map literalTokenCost).sum ≤
          Nat.succ rest.length * (variableBound + 1)
      simpa [Nat.succ_mul, Nat.add_comm] using
        (Nat.add_le_add hLiteral hRest)

theorem clauseTokenCost_le (clause : List CNFLiteral)
    {declaredVariables variableBound : Nat}
    (hScoped : ∀ literal, literal ∈ clause →
      literal.variableIndex < declaredVariables)
    (hVariables : declaredVariables ≤ variableBound)
    (hLength : clause.length ≤ variableBound + 4) :
    clauseTokenCost clause ≤
      2 + (variableBound + 4) * (variableBound + 1) := by
  unfold clauseTokenCost
  have hTokens := literalTokenCost_sum_le clause hScoped hVariables
  have hScaled : clause.length * (variableBound + 1) ≤
      (variableBound + 4) * (variableBound + 1) :=
    Nat.mul_le_mul_right (variableBound + 1) hLength
  exact Nat.add_le_add_left (Nat.le_trans hTokens hScaled) 2

theorem clauseListTokenCost_le_aux
    (clauses : List (List CNFLiteral))
    (declaredVariables variableBound : Nat)
    (hVariables : declaredVariables ≤ variableBound)
    (hScoped : ∀ clause, clause ∈ clauses →
      ∀ literal, literal ∈ clause →
        literal.variableIndex < declaredVariables)
    (hLengths : ∀ clause, clause ∈ clauses →
      clause.length ≤ variableBound + 4) :
    clauseListTokenCost clauses ≤
      clauses.length *
        (2 + (variableBound + 4) * (variableBound + 1)) := by
  unfold clauseListTokenCost
  induction clauses with
  | nil => simp
  | cons clause rest ih =>
      have hClause : clauseTokenCost clause ≤
          2 + (variableBound + 4) * (variableBound + 1) := by
        apply clauseTokenCost_le clause
        · intro literal hLiteral
          exact hScoped clause (List.Mem.head rest) literal hLiteral
        · exact hVariables
        · exact hLengths clause (List.Mem.head rest)
      have hRest : (rest.map clauseTokenCost).sum ≤
          rest.length *
            (2 + (variableBound + 4) * (variableBound + 1)) := by
        apply ih
        · intro restClause hRestClause literal hLiteral
          exact hScoped restClause (List.Mem.tail clause hRestClause)
            literal hLiteral
        · intro restClause hRestClause
          exact hLengths restClause (List.Mem.tail clause hRestClause)
      change
        clauseTokenCost clause + (rest.map clauseTokenCost).sum ≤
          Nat.succ rest.length *
            (2 + (variableBound + 4) * (variableBound + 1))
      simpa [Nat.succ_mul, Nat.add_comm] using
        (Nat.add_le_add hClause hRest)

theorem clauseListTokenCost_le (formula : CNFFormula)
    (variableBound : Nat)
    (hVariables : formula.variableCount ≤ variableBound)
    (hScoped : FormulaWellScoped formula)
    (hLengths : ∀ clause, clause ∈ formula.clauses →
      clause.length ≤ variableBound + 4) :
    clauseListTokenCost formula.clauses ≤
      formula.clauses.length *
        (2 + (variableBound + 4) * (variableBound + 1)) := by
  exact clauseListTokenCost_le_aux formula.clauses formula.variableCount
    variableBound hVariables hScoped hLengths

/-- A well-scoped formula with bounded clause count and clause width has the
advertised canonical unary-indexed output bound. -/
theorem encodeCNF_size_le (formula : CNFFormula)
    (variableBound clauseBound : Nat)
    (hVariables : formula.variableCount ≤ variableBound)
    (hClauses : formula.clauses.length ≤ clauseBound)
    (hScoped : FormulaWellScoped formula)
    (hLengths : ∀ clause, clause ∈ formula.clauses →
      clause.length ≤ variableBound + 4) :
    BitString.size (encodeCNF formula) ≤
      2 * ((variableBound + 1) +
        clauseBound * (2 + (variableBound + 4) * (variableBound + 1)) + 1) +
        1 := by
  rw [encodeCNF_size_exact]
  have hClauseTokens := clauseListTokenCost_le formula variableBound
    hVariables hScoped hLengths
  have hClauseScale : formula.clauses.length *
        (2 + (variableBound + 4) * (variableBound + 1)) ≤
      clauseBound *
        (2 + (variableBound + 4) * (variableBound + 1)) :=
    Nat.mul_le_mul_right
      (2 + (variableBound + 4) * (variableBound + 1)) hClauses
  have hHeader : formula.variableCount + 1 ≤ variableBound + 1 :=
    Nat.add_le_add_right hVariables 1
  have hTokens :
      (formula.variableCount + 1) +
          clauseListTokenCost formula.clauses + 1 ≤
        (variableBound + 1) +
          clauseBound *
            (2 + (variableBound + 4) * (variableBound + 1)) + 1 :=
    Nat.add_le_add_right
      (Nat.add_le_add hHeader
        (Nat.le_trans hClauseTokens hClauseScale)) 1
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hTokens) 1

/-! ### Local-program size discipline -/

namespace LocalConstraint

/-- The only size facts needed from a local constraint: exactly-one lists fit
inside the advertised variable bound, and implication premises have the
constant arity used by the concrete tableau emitter. -/
def SizeBounded {width : Nat} (variableBound : Nat) :
    LocalConstraint width → Prop
  | .require _ => True
  | .implication premises _ => premises.length ≤ variableBound + 3
  | .exactlyOne variables => variables.length ≤ variableBound

theorem pairCount_le_square (count : Nat) :
    pairCount count ≤ count * count := by
  induction count with
  | zero => exact Nat.le_refl 0
  | succ count ih =>
      unfold pairCount
      have added := Nat.add_le_add_left ih count
      calc
        count + pairCount count ≤ count + count * count := added
        _ ≤ Nat.succ count * Nat.succ count := by
          simp [Nat.succ_mul, Nat.mul_succ]
          omega

theorem clauseCount_le {width variableBound : Nat}
    (constraint : LocalConstraint width)
    (hBounded : SizeBounded variableBound constraint) :
    clauseCount constraint ≤ 1 + variableBound * variableBound := by
  cases constraint with
  | require literal =>
      exact Nat.le_add_right 1 (variableBound * variableBound)
  | implication premises conclusion =>
      exact Nat.le_add_right 1 (variableBound * variableBound)
  | exactlyOne variables =>
      change 1 + pairCount variables.length ≤
        1 + variableBound * variableBound
      apply Nat.add_le_add_left
      exact Nat.le_trans (pairCount_le_square variables.length)
        (Nat.mul_le_mul hBounded hBounded)

theorem excludeBoundedWithClauses_clause_length
    {width : Nat} (first : Fin width) (rest : List (Fin width))
    (clause : BoundedClause width)
    (hClause : clause ∈ excludeBoundedWithClauses first rest) :
    clause.length = 2 := by
  induction rest with
  | nil => cases hClause
  | cons next rest ih =>
      cases hClause with
      | head => rfl
      | tail _ hTail => exact ih hTail

theorem atMostOneBoundedClauses_clause_length
    {width : Nat} (variables : List (Fin width))
    (clause : BoundedClause width)
    (hClause : clause ∈ atMostOneBoundedClauses variables) :
    clause.length = 2 := by
  induction variables with
  | nil => cases hClause
  | cons first rest ih =>
      change clause ∈
        excludeBoundedWithClauses first rest ++
          atMostOneBoundedClauses rest at hClause
      rw [List.mem_append] at hClause
      cases hClause with
      | inl hFirst =>
          exact excludeBoundedWithClauses_clause_length first rest clause hFirst
      | inr hRest => exact ih hRest

theorem emitted_bounded_clause_length_le
    {width variableBound : Nat}
    (constraint : LocalConstraint width)
    (hBounded : SizeBounded variableBound constraint)
    (clause : BoundedClause width)
    (hClause : clause ∈ emit constraint) :
    clause.length ≤ variableBound + 4 := by
  cases constraint with
  | require literal =>
      change clause ∈ unitClauses literal at hClause
      simp [unitClauses] at hClause
      subst clause
      simp
  | implication premises conclusion =>
      change clause ∈ implicationClauses premises conclusion at hClause
      simp [implicationClauses] at hClause
      subst clause
      change premises.length ≤ variableBound + 3 at hBounded
      unfold implicationClause
      rw [List.length_append]
      change (BoundedClause.negated premises).length + 1 ≤
        variableBound + 4
      simp [BoundedClause.negated]
      omega
  | exactlyOne variables =>
      change clause ∈ exactlyOneBoundedClauses variables at hClause
      cases hClause with
      | head =>
          change (atLeastOneBoundedClause variables).length ≤
            variableBound + 4
          simpa [atLeastOneBoundedClause] using
            Nat.le_trans hBounded
              (Nat.le_add_right variableBound 4)
      | tail _ hTail =>
          rw [atMostOneBoundedClauses_clause_length variables clause hTail]
          omega

end LocalConstraint

namespace LocalProgram

def SizeBounded {width : Nat} (variableBound : Nat)
    (program : LocalProgram width) : Prop :=
  ∀ constraint, constraint ∈ program →
    LocalConstraint.SizeBounded variableBound constraint

theorem sizeBounded_append {width variableBound : Nat}
    (left right : LocalProgram width)
    (hLeft : SizeBounded variableBound left)
    (hRight : SizeBounded variableBound right) :
    SizeBounded variableBound (left ++ right) := by
  intro constraint hConstraint
  rw [List.mem_append] at hConstraint
  cases hConstraint with
  | inl hMem => exact hLeft constraint hMem
  | inr hMem => exact hRight constraint hMem

theorem clauseCount_le {width variableBound : Nat}
    (program : LocalProgram width)
    (hBounded : SizeBounded variableBound program) :
    clauseCount program ≤
      program.length * (1 + variableBound * variableBound) := by
  induction program with
  | nil => simp [clauseCount]
  | cons constraint rest ih =>
      have hConstraint := hBounded constraint (List.Mem.head rest)
      have hRest : SizeBounded variableBound rest := by
        intro candidate hCandidate
        exact hBounded candidate (List.Mem.tail constraint hCandidate)
      have hFirst := LocalConstraint.clauseCount_le constraint hConstraint
      have hTail := ih hRest
      change
        LocalConstraint.clauseCount constraint + clauseCount rest ≤
          Nat.succ rest.length * (1 + variableBound * variableBound)
      calc
        LocalConstraint.clauseCount constraint + clauseCount rest ≤
            (1 + variableBound * variableBound) +
              rest.length * (1 + variableBound * variableBound) :=
          Nat.add_le_add hFirst hTail
        _ = rest.length * (1 + variableBound * variableBound) +
              (1 + variableBound * variableBound) := by
          exact Nat.add_comm _ _
        _ = Nat.succ rest.length *
              (1 + variableBound * variableBound) := by
          rw [Nat.succ_mul]

theorem bounded_clause_length_le {width variableBound : Nat}
    (program : LocalProgram width)
    (hBounded : SizeBounded variableBound program)
    (clause : BoundedClause width)
    (hClause : clause ∈ emit program) :
    clause.length ≤ variableBound + 4 := by
  induction program with
  | nil => cases hClause
  | cons constraint rest ih =>
      change clause ∈ LocalConstraint.emit constraint ++ emit rest at hClause
      rw [List.mem_append] at hClause
      cases hClause with
      | inl hFirst =>
          exact LocalConstraint.emitted_bounded_clause_length_le constraint
            (hBounded constraint (List.Mem.head rest)) clause hFirst
      | inr hRest =>
          apply ih
          · intro candidate hCandidate
            exact hBounded candidate (List.Mem.tail constraint hCandidate)
          · exact hRest

theorem emitted_clause_length_le {width variableBound : Nat}
    (program : LocalProgram width)
    (hBounded : SizeBounded variableBound program)
    (clause : List CNFLiteral)
    (hClause : clause ∈ (toFormula program).clauses) :
    clause.length ≤ variableBound + 4 := by
  change clause ∈ BoundedClauses.emit (emit program) at hClause
  unfold BoundedClauses.emit at hClause
  rcases List.mem_map.mp hClause with
    ⟨boundedClause, hBoundedClause, hEqual⟩
  rw [← hEqual, BoundedClause.emit_length]
  exact bounded_clause_length_le program hBounded boundedClause hBoundedClause

end LocalProgram

namespace VariableLayout

theorem variableCount_eq_sum (layout : VariableLayout) :
    layout.variableCount =
      layout.symbolWidth + layout.headWidth + layout.stateWidth +
        layout.certificateBitWidth + layout.certificateLengthWidth := by
  simp [variableCount, certificateLengthBlock, certificateBitBlock, stateBlock,
    headBlock, symbolBlock, VariableBlock.endOffset]

theorem symbolWidth_le_variableCount (layout : VariableLayout) :
    layout.symbolWidth ≤ layout.variableCount := by
  rw [variableCount_eq_sum]
  omega

theorem headWidth_le_variableCount (layout : VariableLayout) :
    layout.headWidth ≤ layout.variableCount := by
  rw [variableCount_eq_sum]
  omega

theorem stateWidth_le_variableCount (layout : VariableLayout) :
    layout.stateWidth ≤ layout.variableCount := by
  rw [variableCount_eq_sum]
  omega

theorem certificateBitWidth_le_variableCount (layout : VariableLayout) :
    layout.certificateBitWidth ≤ layout.variableCount := by
  rw [variableCount_eq_sum]
  omega

theorem certificateLengthWidth_le_variableCount (layout : VariableLayout) :
    layout.certificateLengthWidth ≤ layout.variableCount := by
  rw [variableCount_eq_sum]
  omega

theorem three_le_variableCount (layout : VariableLayout) :
    3 ≤ layout.variableCount := by
  have hRows : 0 < layout.dimensions.timeCount :=
    layout.dimensions.timeCount_positive
  have hTape : 0 < layout.dimensions.tapeWidth layout.mode :=
    layout.dimensions.tapeWidth_positive layout.mode
  have hProduct : 0 <
      layout.dimensions.timeCount *
        layout.dimensions.tapeWidth layout.mode :=
    Nat.mul_pos hRows hTape
  have hThree : 3 ≤ layout.symbolWidth := by
    unfold symbolWidth
    exact Nat.le_mul_of_pos_left 3 hProduct
  exact Nat.le_trans hThree (symbolWidth_le_variableCount layout)

theorem tapeWidth_le_variableCount (layout : VariableLayout) :
    layout.dimensions.tapeWidth layout.mode ≤ layout.variableCount := by
  have hHead : layout.dimensions.tapeWidth layout.mode ≤ layout.headWidth := by
    unfold headWidth
    exact Nat.le_mul_of_pos_left _ layout.dimensions.timeCount_positive
  exact Nat.le_trans hHead (headWidth_le_variableCount layout)

theorem stateBound_le_variableCount (layout : VariableLayout) :
    layout.dimensions.stateBound ≤ layout.variableCount := by
  have hState : layout.dimensions.stateBound ≤ layout.stateWidth := by
    unfold stateWidth
    exact Nat.le_mul_of_pos_left _ layout.dimensions.timeCount_positive
  exact Nat.le_trans hState (stateWidth_le_variableCount layout)

end VariableLayout

/-! ### Constructive list-cardinality transport -/

theorem flatMap_length_eq_mul (items : List α) (mapping : α → List β)
    (width : Nat)
    (hWidth : ∀ item, item ∈ items → (mapping item).length = width) :
    (items.flatMap mapping).length = items.length * width := by
  induction items with
  | nil => simp
  | cons first rest ih =>
      change (mapping first ++ rest.flatMap mapping).length =
        Nat.succ rest.length * width
      rw [List.length_append, hWidth first (List.Mem.head rest)]
      rw [ih (fun item hItem =>
        hWidth item (List.Mem.tail first hItem))]
      rw [Nat.succ_mul]
      exact Nat.add_comm _ _

theorem flatMap_length_le_mul (items : List α) (mapping : α → List β)
    (width : Nat)
    (hWidth : ∀ item, item ∈ items → (mapping item).length ≤ width) :
    (items.flatMap mapping).length ≤ items.length * width := by
  induction items with
  | nil => simp
  | cons first rest ih =>
      change (mapping first ++ rest.flatMap mapping).length ≤
        Nat.succ rest.length * width
      rw [List.length_append]
      have hFirst := hWidth first (List.Mem.head rest)
      have hRest := ih (fun item hItem =>
        hWidth item (List.Mem.tail first hItem))
      calc
        (mapping first).length + (rest.flatMap mapping).length ≤
            width + rest.length * width := Nat.add_le_add hFirst hRest
        _ = rest.length * width + width := Nat.add_comm _ _
        _ = Nat.succ rest.length * width := by rw [Nat.succ_mul]

/-! ### Fixed-verifier external polynomials -/

/-- Maximum encoded verifier-input size as a polynomial in source length. -/
def formulaEncodedInputPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  encodedInputPolynomial (inputModeOfVerifier verifier.program.inputMode)
    verifier.certificateBound

/-- Uniform tableau fuel after substituting the encoded-input polynomial into
the compiled raw verifier's own time polynomial. -/
def formulaFuelPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  NatPolynomial.substitute
    (DecisionProgram.RawRefinement.compile verifier.program.decision).timeBound
    (formulaEncodedInputPolynomial verifier)

/-- Number of represented time rows. -/
def formulaTimeCountPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (formulaFuelPolynomial verifier) (.constant 1)

/-- Width of the complete symmetric tableau tape window. -/
def formulaTapeWidthPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  tapeWidthPolynomial (inputModeOfVerifier verifier.program.inputMode)
    verifier.certificateBound (formulaFuelPolynomial verifier)

/-- The compiled verifier has a fixed finite state ceiling. -/
def formulaStateCountPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .constant (machineStateBound
    (DecisionProgram.RawRefinement.compile verifier.program.decision).machine)

/-- Conservative bound for the five collision-free Boolean-variable blocks.
The final two summands cover paired certificate bits and unary length; they
remain harmless upper bounds in input-only mode. -/
def formulaVariableCountPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let time := formulaTimeCountPolynomial verifier
  let tape := formulaTapeWidthPolynomial verifier
  let states := formulaStateCountPolynomial verifier
  let certificate := verifier.certificateBound
  .add
    (.add
      (.add
        (.add
          (.mul (.mul (.constant 3) time) tape)
          (.mul time tape))
        (.mul time states))
      certificate)
    (.add certificate (.constant 1))

/-- Exact width of the five collision-free Boolean-variable blocks.  Unlike
`formulaVariableCountPolynomial`, this expression follows the verifier input
mode, so the certificate blocks contribute zero in input-only mode and their
exact two unary widths in paired mode. -/
def formulaWidthPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let time := formulaTimeCountPolynomial verifier
  let tape := formulaTapeWidthPolynomial verifier
  let states := formulaStateCountPolynomial verifier
  let common :=
    .add
      (.add
        (.mul (.mul (.constant 3) time) tape)
        (.mul time tape))
      (.mul time states)
  match verifier.program.inputMode with
  | .inputOnly => common
  | .paired =>
      .add common
        (.add verifier.certificateBound
          (.add verifier.certificateBound (.constant 1)))

/-- Constraint-family bound: row shape, control updates, untouched-cell
preservation, both initialization modes, and final acceptance. -/
def formulaConstraintCountPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let certificate := verifier.certificateBound
  let fuel := formulaFuelPolynomial verifier
  let time := formulaTimeCountPolynomial verifier
  let tape := formulaTapeWidthPolynomial verifier
  let states := formulaStateCountPolynomial verifier
  .add
    (.add
      (.add
        (.add
          (.mul time (.add tape (.constant 2)))
          (.mul (.constant 9) (.mul (.mul fuel tape) states)))
        (.mul (.constant 3) (.mul (.mul fuel tape) tape)))
      (.constant 4))
    (.mul (.constant 2)
      (.mul (.add certificate (.constant 1)) tape))

/-- Every concrete local constraint emits at most `1 + V^2` clauses. -/
def formulaClauseCountPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let constraints := formulaConstraintCountPolynomial verifier
  let variables := formulaVariableCountPolynomial verifier
  .mul constraints
    (.add (.constant 1) (.mul variables variables))

/-- Every emitted clause uses at most `V + 4` literals and each unary literal
uses at most `V + 1` tokens, in addition to separator and finish tokens. -/
def formulaClauseTokenPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let variables := formulaVariableCountPolynomial verifier
  .add (.constant 2)
    (.mul (.add variables (.constant 4))
      (.add variables (.constant 1)))

/-- Complete external bound for the canonical raw bitstring formula. -/
def encodedFormulaSizePolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let variables := formulaVariableCountPolynomial verifier
  let clauses := formulaClauseCountPolynomial verifier
  let clauseTokens := formulaClauseTokenPolynomial verifier
  .add
    (.mul (.constant 2)
      (.add
        (.add (.add variables (.constant 1))
          (.mul clauses clauseTokens))
        (.constant 1)))
    (.constant 1)

namespace VerifierTableauProblem

theorem formulaEncodedInputPolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (formulaEncodedInputPolynomial problem.verifier).eval
        (BitString.size problem.input) =
      problem.encodedInputLimit := by
  rfl

theorem formulaFuelPolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (formulaFuelPolynomial problem.verifier).eval
        (BitString.size problem.input) =
      problem.uniformFuel := by
  unfold formulaFuelPolynomial VerifierTableauProblem.uniformFuel
    VerifierTableauProblem.rawTimeBound
  rw [NatPolynomial.eval_substitute]
  rfl

theorem formulaTimeCountPolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (formulaTimeCountPolynomial problem.verifier).eval
        (BitString.size problem.input) =
      problem.dimensions.timeCount := by
  unfold formulaTimeCountPolynomial Dimensions.timeCount
  rw [NatPolynomial.eval_add, problem.formulaFuelPolynomial_eval]
  rfl

theorem formulaTapeWidthPolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (formulaTapeWidthPolynomial problem.verifier).eval
        (BitString.size problem.input) =
      problem.dimensions.tapeWidth problem.tableauInputMode := by
  unfold formulaTapeWidthPolynomial Dimensions.tapeWidth
  rw [eval_tapeWidthPolynomial,
    problem.formulaFuelPolynomial_eval,
    problem.dimensions_encodedInputLength,
    problem.dimensions_timeBound]
  rfl

theorem formulaStateCountPolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (formulaStateCountPolynomial problem.verifier).eval
        (BitString.size problem.input) =
      problem.dimensions.stateBound := by
  rfl

theorem formulaVariableCountPolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (formulaVariableCountPolynomial problem.verifier).eval
        (BitString.size problem.input) =
      (3 * problem.dimensions.timeCount) *
          (problem.dimensions.tapeWidth problem.tableauInputMode) +
        problem.dimensions.timeCount *
          (problem.dimensions.tapeWidth problem.tableauInputMode) +
        problem.dimensions.timeCount * problem.dimensions.stateBound +
        problem.certificateLimit + (problem.certificateLimit + 1) := by
  unfold formulaVariableCountPolynomial
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant]
  rw [problem.formulaTimeCountPolynomial_eval,
    problem.formulaTapeWidthPolynomial_eval,
    problem.formulaStateCountPolynomial_eval]
  rfl

/-- The mode-sensitive external polynomial evaluates to the actual layout
width, not merely an upper bound. -/
theorem formulaWidthPolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (formulaWidthPolynomial problem.verifier).eval
        (BitString.size problem.input) = problem.FormulaWidth := by
  cases hMode : problem.verifier.program.inputMode with
  | inputOnly =>
      simp [formulaWidthPolynomial, hMode,
        problem.formulaTimeCountPolynomial_eval,
        problem.formulaTapeWidthPolynomial_eval,
        problem.formulaStateCountPolynomial_eval, FormulaWidth,
        VerifierTableauProblem.layout, VariableLayout.variableCount_eq_sum,
        VariableLayout.symbolWidth, VariableLayout.headWidth,
        VariableLayout.stateWidth, VariableLayout.certificateBitWidth,
        VariableLayout.certificateLengthWidth,
        VerifierTableauProblem.tableauInputMode, inputModeOfVerifier,
        Nat.mul_comm, Nat.mul_left_comm] <;> omega
  | paired =>
      simp [formulaWidthPolynomial, hMode,
        problem.formulaTimeCountPolynomial_eval,
        problem.formulaTapeWidthPolynomial_eval,
        problem.formulaStateCountPolynomial_eval, FormulaWidth,
        VerifierTableauProblem.layout, VariableLayout.variableCount_eq_sum,
        VariableLayout.symbolWidth, VariableLayout.headWidth,
        VariableLayout.stateWidth, VariableLayout.certificateBitWidth,
        VariableLayout.certificateLengthWidth,
        VerifierTableauProblem.tableauInputMode, inputModeOfVerifier,
        VerifierTableauProblem.dimensions_certificateBound,
        VerifierTableauProblem.certificateLimit,
        Nat.mul_comm, Nat.mul_left_comm] <;> omega

theorem formulaConstraintCountPolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (formulaConstraintCountPolynomial problem.verifier).eval
        (BitString.size problem.input) =
      problem.dimensions.timeCount *
          (problem.dimensions.tapeWidth problem.tableauInputMode + 2) +
        9 * (problem.uniformFuel *
          problem.dimensions.tapeWidth problem.tableauInputMode *
          problem.dimensions.stateBound) +
        3 * (problem.uniformFuel *
          problem.dimensions.tapeWidth problem.tableauInputMode *
          problem.dimensions.tapeWidth problem.tableauInputMode) +
        4 +
        2 * ((problem.certificateLimit + 1) *
          problem.dimensions.tapeWidth problem.tableauInputMode) := by
  unfold formulaConstraintCountPolynomial
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant]
  rw [problem.formulaFuelPolynomial_eval,
    problem.formulaTimeCountPolynomial_eval,
    problem.formulaTapeWidthPolynomial_eval,
    problem.formulaStateCountPolynomial_eval]
  rfl

theorem formulaClauseCountPolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (formulaClauseCountPolynomial problem.verifier).eval
        (BitString.size problem.input) =
      (formulaConstraintCountPolynomial problem.verifier).eval
          (BitString.size problem.input) *
        (1 +
          (formulaVariableCountPolynomial problem.verifier).eval
              (BitString.size problem.input) *
            (formulaVariableCountPolynomial problem.verifier).eval
              (BitString.size problem.input)) := by
  rfl

theorem formulaClauseTokenPolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (formulaClauseTokenPolynomial problem.verifier).eval
        (BitString.size problem.input) =
      2 +
        ((formulaVariableCountPolynomial problem.verifier).eval
            (BitString.size problem.input) + 4) *
          ((formulaVariableCountPolynomial problem.verifier).eval
            (BitString.size problem.input) + 1) := by
  rfl

theorem encodedFormulaSizePolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (encodedFormulaSizePolynomial problem.verifier).eval
        (BitString.size problem.input) =
      2 *
          (((formulaVariableCountPolynomial problem.verifier).eval
                (BitString.size problem.input) + 1) +
            (formulaClauseCountPolynomial problem.verifier).eval
                (BitString.size problem.input) *
              (2 +
                ((formulaVariableCountPolynomial problem.verifier).eval
                    (BitString.size problem.input) + 4) *
                  ((formulaVariableCountPolynomial problem.verifier).eval
                    (BitString.size problem.input) + 1)) +
            1) +
        1 := by
  rfl

/-! ### Concrete constraint arities -/

theorem symbolVariables_length {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount)
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    (problem.symbolVariables time position).length = 3 := by
  simp [symbolVariables, tapeSymbols]

theorem headVariables_length {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    (problem.headVariables time).length =
      problem.dimensions.tapeWidth problem.tableauInputMode := by
  simp [headVariables, finiteIndices_length]

theorem stateVariables_length {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    (problem.stateVariables time).length =
      problem.dimensions.stateBound := by
  simp [stateVariables, finiteIndices_length]

theorem pairedLengthVariables_length {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) :
    (problem.pairedLengthVariables hMode).length =
      problem.certificateLimit + 1 := by
  simp [pairedLengthVariables, finiteIndices_length]

theorem symbolVariables_length_le_formulaWidth {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount)
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    (problem.symbolVariables time position).length ≤ problem.FormulaWidth := by
  rw [problem.symbolVariables_length time position]
  exact problem.layout.three_le_variableCount

theorem headVariables_length_le_formulaWidth {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    (problem.headVariables time).length ≤ problem.FormulaWidth := by
  rw [problem.headVariables_length time]
  exact problem.layout.tapeWidth_le_variableCount

theorem stateVariables_length_le_formulaWidth {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    (problem.stateVariables time).length ≤ problem.FormulaWidth := by
  rw [problem.stateVariables_length time]
  exact problem.layout.stateBound_le_variableCount

theorem pairedLengthVariables_length_le_formulaWidth {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) :
    (problem.pairedLengthVariables hMode).length ≤ problem.FormulaWidth := by
  rw [problem.pairedLengthVariables_length hMode]
  have hWidth := problem.layout.certificateLengthWidth_le_variableCount
  unfold VariableLayout.certificateLengthWidth at hWidth
  rw [problem.layout_mode, hMode] at hWidth
  exact hWidth

theorem formulaWidth_le_formulaVariableCountPolynomial {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.FormulaWidth ≤
      (formulaVariableCountPolynomial problem.verifier).eval
        (BitString.size problem.input) := by
  rw [problem.formulaVariableCountPolynomial_eval]
  change problem.layout.variableCount ≤ _
  rw [VariableLayout.variableCount_eq_sum]
  unfold VariableLayout.symbolWidth VariableLayout.headWidth
    VariableLayout.stateWidth VariableLayout.certificateBitWidth
    VariableLayout.certificateLengthWidth
  rw [problem.layout_mode]
  change
    problem.dimensions.timeCount *
          problem.dimensions.tapeWidth problem.tableauInputMode * 3 +
        problem.dimensions.timeCount *
          problem.dimensions.tapeWidth problem.tableauInputMode +
        problem.dimensions.timeCount * problem.dimensions.stateBound +
        (match problem.tableauInputMode with
         | .inputOnly => 0
         | .paired => problem.dimensions.certificateBound) +
        (match problem.tableauInputMode with
         | .inputOnly => 0
         | .paired => problem.dimensions.certificateBound + 1) ≤ _
  rw [problem.dimensions_certificateBound]
  cases problem.tableauInputMode <;>
    simp only [Nat.mul_comm, Nat.mul_left_comm] <;> omega

/-! ### Every concrete program constraint obeys the local size discipline -/

theorem symbolShapeRow_sizeBounded {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    LocalProgram.SizeBounded problem.FormulaWidth
      (problem.symbolShapeRow time) := by
  intro constraint hConstraint
  unfold symbolShapeRow at hConstraint
  rcases List.mem_map.mp hConstraint with
    ⟨position, _, hEqual⟩
  subst constraint
  change (problem.symbolVariables time position).length ≤
    problem.FormulaWidth
  exact problem.symbolVariables_length_le_formulaWidth time position

theorem rowShapeProgram_sizeBounded {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    LocalProgram.SizeBounded problem.FormulaWidth
      (problem.rowShapeProgram time) := by
  intro constraint hConstraint
  unfold rowShapeProgram at hConstraint
  rw [List.mem_append] at hConstraint
  cases hConstraint with
  | inl hSymbol =>
      exact problem.symbolShapeRow_sizeBounded time constraint hSymbol
  | inr hTail =>
      rcases List.mem_cons.mp hTail with hHead | hStateTail
      · subst constraint
        change (problem.headVariables time).length ≤ problem.FormulaWidth
        exact problem.headVariables_length_le_formulaWidth time
      · rcases List.mem_cons.mp hStateTail with hState | impossible
        · subst constraint
          change (problem.stateVariables time).length ≤ problem.FormulaWidth
          exact problem.stateVariables_length_le_formulaWidth time
        · cases impossible

theorem shapeProgram_sizeBounded {language : Language}
    (problem : VerifierTableauProblem language) :
    LocalProgram.SizeBounded problem.FormulaWidth problem.shapeProgram := by
  intro constraint hConstraint
  unfold shapeProgram at hConstraint
  rcases List.mem_flatMap.mp hConstraint with ⟨time, _, hAtTime⟩
  exact problem.rowShapeProgram_sizeBounded time constraint hAtTime

theorem controlConstraints_sizeBounded {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (state : Fin problem.dimensions.stateBound)
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol) :
    LocalProgram.SizeBounded problem.FormulaWidth
      (problem.controlConstraints step state position symbol) := by
  intro constraint hConstraint
  unfold controlConstraints at hConstraint
  dsimp only at hConstraint
  rcases List.mem_cons.mp hConstraint with hState | hTail
  · subst constraint
    change (problem.controlPremises step state position symbol).length ≤
      problem.FormulaWidth + 3
    simp [controlPremises]
  · rcases List.mem_cons.mp hTail with hHead | hSymbolTail
    · subst constraint
      change (problem.controlPremises step state position symbol).length ≤
        problem.FormulaWidth + 3
      simp [controlPremises]
    · rcases List.mem_cons.mp hSymbolTail with hSymbol | impossible
      · subst constraint
        change (problem.controlPremises step state position symbol).length ≤
          problem.FormulaWidth + 3
        simp [controlPremises]
      · cases impossible

theorem controlConstraintsAtPosition_sizeBounded {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    LocalProgram.SizeBounded problem.FormulaWidth
      (problem.controlConstraintsAtPosition step position) := by
  intro constraint hConstraint
  unfold controlConstraintsAtPosition at hConstraint
  rcases List.mem_flatMap.mp hConstraint with ⟨state, _, hAtState⟩
  rcases List.mem_flatMap.mp hAtState with ⟨symbol, _, hLocal⟩
  exact problem.controlConstraints_sizeBounded step state position symbol
    constraint hLocal

theorem controlTransitionProgram_sizeBounded {language : Language}
    (problem : VerifierTableauProblem language) :
    LocalProgram.SizeBounded problem.FormulaWidth
      problem.controlTransitionProgram := by
  intro constraint hConstraint
  unfold controlTransitionProgram at hConstraint
  rcases List.mem_flatMap.mp hConstraint with ⟨step, _, hAtStep⟩
  rcases List.mem_flatMap.mp hAtStep with ⟨position, _, hLocal⟩
  exact problem.controlConstraintsAtPosition_sizeBounded step position
    constraint hLocal

theorem preservationConstraints_sizeBounded {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (headPosition otherPosition : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    LocalProgram.SizeBounded problem.FormulaWidth
      (problem.preservationConstraints step headPosition otherPosition) := by
  intro constraint hConstraint
  unfold preservationConstraints at hConstraint
  split at hConstraint
  · cases hConstraint
  · rcases List.mem_map.mp hConstraint with ⟨symbol, _, hEqual⟩
    subst constraint
    change 2 ≤ problem.FormulaWidth + 3
    omega

theorem preservationAtHead_sizeBounded {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (headPosition : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    LocalProgram.SizeBounded problem.FormulaWidth
      (problem.preservationAtHead step headPosition) := by
  intro constraint hConstraint
  unfold preservationAtHead at hConstraint
  rcases List.mem_flatMap.mp hConstraint with
    ⟨otherPosition, _, hLocal⟩
  exact problem.preservationConstraints_sizeBounded step headPosition
    otherPosition constraint hLocal

theorem preservationProgram_sizeBounded {language : Language}
    (problem : VerifierTableauProblem language) :
    LocalProgram.SizeBounded problem.FormulaWidth
      problem.preservationProgram := by
  intro constraint hConstraint
  unfold preservationProgram at hConstraint
  rcases List.mem_flatMap.mp hConstraint with ⟨step, _, hAtStep⟩
  rcases List.mem_flatMap.mp hAtStep with
    ⟨headPosition, _, hLocal⟩
  exact problem.preservationAtHead_sizeBounded step headPosition
    constraint hLocal

theorem transitionProgram_sizeBounded {language : Language}
    (problem : VerifierTableauProblem language) :
    LocalProgram.SizeBounded problem.FormulaWidth problem.transitionProgram := by
  unfold transitionProgram
  exact LocalProgram.sizeBounded_append _ _
    problem.controlTransitionProgram_sizeBounded
    problem.preservationProgram_sizeBounded

theorem inputOnlyCellProgram_sizeBounded {language : Language}
    (problem : VerifierTableauProblem language)
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    LocalProgram.SizeBounded problem.FormulaWidth
      (problem.inputOnlyCellProgram position) := by
  unfold inputOnlyCellProgram
  generalize initialCellAt (inputOnlyInitialCells problem.input)
    problem.uniformFuel position.val = cell
  cases cell with
  | blank =>
      intro constraint hConstraint
      simp [fixedInitialCellConstraint] at hConstraint
      subst constraint
      trivial
  | fixed value =>
      intro constraint hConstraint
      simp [fixedInitialCellConstraint] at hConstraint
      subst constraint
      trivial
  | certificate index => exact Fin.elim0 index

theorem inputOnlyInitialSymbolsProgram_sizeBounded {language : Language}
    (problem : VerifierTableauProblem language) :
    LocalProgram.SizeBounded problem.FormulaWidth
      problem.inputOnlyInitialSymbolsProgram := by
  intro constraint hConstraint
  unfold inputOnlyInitialSymbolsProgram at hConstraint
  rcases List.mem_flatMap.mp hConstraint with ⟨position, _, hLocal⟩
  exact problem.inputOnlyCellProgram_sizeBounded position constraint hLocal

theorem pairedCellProgram_sizeBounded {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    LocalProgram.SizeBounded problem.FormulaWidth
      (problem.pairedCellProgram hMode length position) := by
  unfold pairedCellProgram
  dsimp only
  generalize initialCellAt
    (pairedInitialCells problem.input problem.certificateLimit length)
    problem.uniformFuel position.val = cell
  cases cell with
  | blank =>
      intro constraint hConstraint
      simp at hConstraint
      subst constraint
      change 1 ≤ problem.FormulaWidth + 3
      omega
  | fixed value =>
      intro constraint hConstraint
      simp at hConstraint
      subst constraint
      change 1 ≤ problem.FormulaWidth + 3
      omega
  | certificate index =>
      intro constraint hConstraint
      simp at hConstraint
      cases hConstraint with
      | inl hOne =>
          subst constraint
          change 2 ≤ problem.FormulaWidth + 3
          omega
      | inr hZero =>
          subst constraint
          change 2 ≤ problem.FormulaWidth + 3
          omega

theorem pairedCellsForLengthProgram_sizeBounded {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1)) :
    LocalProgram.SizeBounded problem.FormulaWidth
      (problem.pairedCellsForLengthProgram hMode length) := by
  intro constraint hConstraint
  unfold pairedCellsForLengthProgram at hConstraint
  rcases List.mem_flatMap.mp hConstraint with ⟨position, _, hLocal⟩
  exact problem.pairedCellProgram_sizeBounded hMode length position
    constraint hLocal

theorem pairedInitialSymbolsProgram_sizeBounded {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) :
    LocalProgram.SizeBounded problem.FormulaWidth
      (problem.pairedInitialSymbolsProgram hMode) := by
  intro constraint hConstraint
  unfold pairedInitialSymbolsProgram at hConstraint
  rcases List.mem_cons.mp hConstraint with hLength | hTail
  · subst constraint
    change (problem.pairedLengthVariables hMode).length ≤ problem.FormulaWidth
    exact problem.pairedLengthVariables_length_le_formulaWidth hMode
  · rcases List.mem_flatMap.mp hTail with ⟨length, _, hLocal⟩
    exact problem.pairedCellsForLengthProgram_sizeBounded hMode length
      constraint hLocal

theorem initialSymbolsProgram_sizeBounded {language : Language}
    (problem : VerifierTableauProblem language) :
    LocalProgram.SizeBounded problem.FormulaWidth
      problem.initialSymbolsProgram := by
  unfold initialSymbolsProgram
  split
  · exact problem.inputOnlyInitialSymbolsProgram_sizeBounded
  · exact problem.pairedInitialSymbolsProgram_sizeBounded
      (problem.tableauInputMode_of_paired ‹_›)

theorem initialProgram_sizeBounded {language : Language}
    (problem : VerifierTableauProblem language) :
    LocalProgram.SizeBounded problem.FormulaWidth problem.initialProgram := by
  intro constraint hConstraint
  unfold initialProgram at hConstraint
  rw [List.mem_append] at hConstraint
  cases hConstraint with
  | inl hPrefix =>
      rcases List.mem_cons.mp hPrefix with hState | hHeadTail
      · subst constraint
        trivial
      · rcases List.mem_cons.mp hHeadTail with hHead | impossible
        · subst constraint
          trivial
        · cases impossible
  | inr hSymbols =>
      exact problem.initialSymbolsProgram_sizeBounded constraint hSymbols

theorem acceptanceProgram_sizeBounded {language : Language}
    (problem : VerifierTableauProblem language) :
    LocalProgram.SizeBounded problem.FormulaWidth
      problem.acceptanceProgram := by
  intro constraint hConstraint
  unfold acceptanceProgram at hConstraint
  rcases List.mem_cons.mp hConstraint with hAccept | impossible
  · subst constraint
    trivial
  · cases impossible

theorem program_sizeBounded {language : Language}
    (problem : VerifierTableauProblem language) :
    LocalProgram.SizeBounded problem.FormulaWidth problem.program := by
  unfold program
  apply LocalProgram.sizeBounded_append
  · apply LocalProgram.sizeBounded_append
    · apply LocalProgram.sizeBounded_append
      · exact problem.shapeProgram_sizeBounded
      · exact problem.initialProgram_sizeBounded
    · exact problem.transitionProgram_sizeBounded
  · exact problem.acceptanceProgram_sizeBounded

/-! ### Exact and conservative program cardinalities -/

theorem symbolShapeRow_length {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    (problem.symbolShapeRow time).length =
      problem.dimensions.tapeWidth problem.tableauInputMode := by
  unfold symbolShapeRow
  rw [List.length_map, finiteIndices_length]

theorem rowShapeProgram_length {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    (problem.rowShapeProgram time).length =
      problem.dimensions.tapeWidth problem.tableauInputMode + 2 := by
  unfold rowShapeProgram
  rw [List.length_append, problem.symbolShapeRow_length time]
  rfl

theorem shapeProgram_length {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.shapeProgram.length =
      problem.dimensions.timeCount *
        (problem.dimensions.tapeWidth problem.tableauInputMode + 2) := by
  unfold shapeProgram
  rw [flatMap_length_eq_mul _ _
    (problem.dimensions.tapeWidth problem.tableauInputMode + 2)]
  · rw [finiteIndices_length]
  · intro time _
    exact problem.rowShapeProgram_length time

theorem controlConstraints_length {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (state : Fin problem.dimensions.stateBound)
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol) :
    (problem.controlConstraints step state position symbol).length = 3 := by
  unfold controlConstraints
  rfl

theorem controlConstraintsAtPosition_length {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    (problem.controlConstraintsAtPosition step position).length =
      problem.dimensions.stateBound * 9 := by
  unfold controlConstraintsAtPosition
  rw [flatMap_length_eq_mul _ _ 9]
  · rw [finiteIndices_length]
  · intro state _
    rw [flatMap_length_eq_mul _ _ 3]
    · rfl
    · intro symbol _
      exact problem.controlConstraints_length step state position symbol

theorem controlTransitionProgram_length {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.controlTransitionProgram.length =
      problem.uniformFuel *
        (problem.dimensions.tapeWidth problem.tableauInputMode *
          (problem.dimensions.stateBound * 9)) := by
  unfold controlTransitionProgram
  rw [flatMap_length_eq_mul _ _
    (problem.dimensions.tapeWidth problem.tableauInputMode *
      (problem.dimensions.stateBound * 9))]
  · rw [finiteIndices_length]
  · intro step _
    rw [flatMap_length_eq_mul _ _ (problem.dimensions.stateBound * 9)]
    · rw [finiteIndices_length]
    · intro position _
      exact problem.controlConstraintsAtPosition_length step position

theorem preservationConstraints_length_le {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (headPosition otherPosition : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    (problem.preservationConstraints step headPosition otherPosition).length ≤
      3 := by
  unfold preservationConstraints
  split
  · exact Nat.zero_le 3
  · simp [tapeSymbols]

theorem preservationAtHead_length_le {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (headPosition : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    (problem.preservationAtHead step headPosition).length ≤
      problem.dimensions.tapeWidth problem.tableauInputMode * 3 := by
  unfold preservationAtHead
  apply Nat.le_trans
    (flatMap_length_le_mul _ _ 3 (fun otherPosition _ =>
      problem.preservationConstraints_length_le step headPosition
        otherPosition))
  rw [finiteIndices_length]
  exact Nat.le_refl _

theorem preservationProgram_length_le {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.preservationProgram.length ≤
      3 * (problem.uniformFuel *
        problem.dimensions.tapeWidth problem.tableauInputMode *
        problem.dimensions.tapeWidth problem.tableauInputMode) := by
  unfold preservationProgram
  have hSteps := flatMap_length_le_mul
    (finiteIndices problem.uniformFuel)
    (fun step =>
      (finiteIndices
        (problem.dimensions.tapeWidth problem.tableauInputMode)).flatMap
          fun headPosition => problem.preservationAtHead step headPosition)
    (problem.dimensions.tapeWidth problem.tableauInputMode *
      (problem.dimensions.tapeWidth problem.tableauInputMode * 3))
    (fun step _ => by
      apply Nat.le_trans
        (flatMap_length_le_mul _ _
          (problem.dimensions.tapeWidth problem.tableauInputMode * 3)
          (fun headPosition _ =>
            problem.preservationAtHead_length_le step headPosition))
      rw [finiteIndices_length]
      exact Nat.le_refl _)
  rw [finiteIndices_length] at hSteps
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hSteps

theorem transitionProgram_length_le {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.transitionProgram.length ≤
      9 * (problem.uniformFuel *
        problem.dimensions.tapeWidth problem.tableauInputMode *
        problem.dimensions.stateBound) +
      3 * (problem.uniformFuel *
        problem.dimensions.tapeWidth problem.tableauInputMode *
        problem.dimensions.tapeWidth problem.tableauInputMode) := by
  unfold transitionProgram
  rw [List.length_append, problem.controlTransitionProgram_length]
  have hPreservation := problem.preservationProgram_length_le
  have hControl :
      problem.uniformFuel *
          (problem.dimensions.tapeWidth problem.tableauInputMode *
            (problem.dimensions.stateBound * 9)) =
        9 * (problem.uniformFuel *
          problem.dimensions.tapeWidth problem.tableauInputMode *
          problem.dimensions.stateBound) := by
    ac_rfl
  rw [hControl]
  exact Nat.add_le_add_left hPreservation _

theorem inputOnlyCellProgram_length {language : Language}
    (problem : VerifierTableauProblem language)
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    (problem.inputOnlyCellProgram position).length = 1 := by
  unfold inputOnlyCellProgram
  generalize initialCellAt (inputOnlyInitialCells problem.input)
    problem.uniformFuel position.val = cell
  cases cell with
  | blank => rfl
  | fixed value => rfl
  | certificate index => exact Fin.elim0 index

theorem inputOnlyInitialSymbolsProgram_length {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.inputOnlyInitialSymbolsProgram.length =
      problem.dimensions.tapeWidth problem.tableauInputMode := by
  unfold inputOnlyInitialSymbolsProgram
  rw [flatMap_length_eq_mul _ _ 1]
  · rw [finiteIndices_length, Nat.mul_one]
  · intro position _
    exact problem.inputOnlyCellProgram_length position

theorem pairedCellProgram_length_le {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    (problem.pairedCellProgram hMode length position).length ≤ 2 := by
  unfold pairedCellProgram
  dsimp only
  generalize initialCellAt
    (pairedInitialCells problem.input problem.certificateLimit length)
    problem.uniformFuel position.val = cell
  cases cell <;> simp

theorem pairedCellsForLengthProgram_length_le {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1)) :
    (problem.pairedCellsForLengthProgram hMode length).length ≤
      problem.dimensions.tapeWidth problem.tableauInputMode * 2 := by
  unfold pairedCellsForLengthProgram
  apply Nat.le_trans
    (flatMap_length_le_mul _ _ 2 (fun position _ =>
      problem.pairedCellProgram_length_le hMode length position))
  rw [finiteIndices_length]
  exact Nat.le_refl _

theorem pairedInitialSymbolsProgram_length_le {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) :
    (problem.pairedInitialSymbolsProgram hMode).length ≤
      1 + (problem.certificateLimit + 1) *
        (problem.dimensions.tapeWidth problem.tableauInputMode * 2) := by
  unfold pairedInitialSymbolsProgram
  change Nat.succ
      ((finiteIndices (problem.certificateLimit + 1)).flatMap
        (fun length => problem.pairedCellsForLengthProgram hMode length)).length ≤
    _
  have hLengths := flatMap_length_le_mul
    (finiteIndices (problem.certificateLimit + 1))
    (fun length => problem.pairedCellsForLengthProgram hMode length)
    (problem.dimensions.tapeWidth problem.tableauInputMode * 2)
    (fun length _ =>
      problem.pairedCellsForLengthProgram_length_le hMode length)
  rw [finiteIndices_length] at hLengths
  omega

theorem initialSymbolsProgram_length_le {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.initialSymbolsProgram.length ≤
      1 + 2 * ((problem.certificateLimit + 1) *
        problem.dimensions.tapeWidth problem.tableauInputMode) := by
  unfold initialSymbolsProgram
  split
  · rw [problem.inputOnlyInitialSymbolsProgram_length]
    have hPositive : 0 < 2 * (problem.certificateLimit + 1) := by omega
    have hScaled := Nat.le_mul_of_pos_left
      (problem.dimensions.tapeWidth problem.tableauInputMode) hPositive
    have hEqual :
        (2 * (problem.certificateLimit + 1)) *
            problem.dimensions.tapeWidth problem.tableauInputMode =
          2 * ((problem.certificateLimit + 1) *
            problem.dimensions.tapeWidth problem.tableauInputMode) := by
      ac_rfl
    rw [hEqual] at hScaled
    omega
  · have hPaired := problem.pairedInitialSymbolsProgram_length_le
      (problem.tableauInputMode_of_paired ‹_›)
    have hEqual :
        1 + (problem.certificateLimit + 1) *
            (problem.dimensions.tapeWidth problem.tableauInputMode * 2) =
          1 + 2 * ((problem.certificateLimit + 1) *
            problem.dimensions.tapeWidth problem.tableauInputMode) := by
      congr 1
      ac_rfl
    rw [← hEqual]
    exact hPaired

theorem initialProgram_length_le {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.initialProgram.length ≤
      3 + 2 * ((problem.certificateLimit + 1) *
        problem.dimensions.tapeWidth problem.tableauInputMode) := by
  unfold initialProgram
  rw [List.length_append]
  change 2 + problem.initialSymbolsProgram.length ≤
    3 + 2 * ((problem.certificateLimit + 1) *
      problem.dimensions.tapeWidth problem.tableauInputMode)
  have hSymbols := problem.initialSymbolsProgram_length_le
  omega

theorem acceptanceProgram_length {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.acceptanceProgram.length = 1 := by
  rfl

theorem program_length_le_formulaConstraintCountPolynomial
    {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.program.length ≤
      (formulaConstraintCountPolynomial problem.verifier).eval
        (BitString.size problem.input) := by
  rw [problem.formulaConstraintCountPolynomial_eval]
  unfold program
  simp only [List.length_append]
  rw [problem.shapeProgram_length, problem.acceptanceProgram_length]
  have hInitial := problem.initialProgram_length_le
  have hTransition := problem.transitionProgram_length_le
  omega

/-! ### External clause and raw-output bounds -/

theorem formula_clauseCount_le_formulaClauseCountPolynomial
    {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formula.clauses.length ≤
      (formulaClauseCountPolynomial problem.verifier).eval
        (BitString.size problem.input) := by
  rw [problem.formula_clauseCount,
    problem.formulaClauseCountPolynomial_eval]
  have hLocal := LocalProgram.clauseCount_le problem.program
    problem.program_sizeBounded
  have hProgram := problem.program_length_le_formulaConstraintCountPolynomial
  have hVariables := problem.formulaWidth_le_formulaVariableCountPolynomial
  have hSquare := Nat.mul_le_mul hVariables hVariables
  have hFactor := Nat.add_le_add_left hSquare 1
  exact Nat.le_trans hLocal (Nat.mul_le_mul hProgram hFactor)

theorem formula_clause_length_le {language : Language}
    (problem : VerifierTableauProblem language)
    (clause : List CNFLiteral)
    (hClause : clause ∈ problem.formula.clauses) :
    clause.length ≤
      (formulaVariableCountPolynomial problem.verifier).eval
          (BitString.size problem.input) + 4 := by
  have hLocal := LocalProgram.emitted_clause_length_le problem.program
    problem.program_sizeBounded clause hClause
  have hVariables := problem.formulaWidth_le_formulaVariableCountPolynomial
  exact Nat.le_trans hLocal (Nat.add_le_add_right hVariables 4)

/-- The actual answer-independent Cook--Levin formula has a uniform canonical
raw-bit size polynomial in the external source-input length. -/
theorem encodedFormula_size_le {language : Language}
    (problem : VerifierTableauProblem language) :
    BitString.size problem.encodedFormula ≤
      (encodedFormulaSizePolynomial problem.verifier).eval
        (BitString.size problem.input) := by
  rw [problem.encodedFormulaSizePolynomial_eval]
  unfold encodedFormula
  apply encodeCNF_size_le problem.formula
    ((formulaVariableCountPolynomial problem.verifier).eval
      (BitString.size problem.input))
    ((formulaClauseCountPolynomial problem.verifier).eval
      (BitString.size problem.input))
  · exact problem.formulaWidth_le_formulaVariableCountPolynomial
  · exact problem.formula_clauseCount_le_formulaClauseCountPolynomial
  · exact problem.formula_wellScoped
  · intro clause hClause
    exact problem.formula_clause_length_le clause hClause

end VerifierTableauProblem

end CookLevin

end PNP.Concrete

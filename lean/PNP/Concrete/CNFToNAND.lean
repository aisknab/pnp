/-
Copyright (c) 2026 PNP Labs.

A universal semantic compiler from the concrete CNF language to the strict
version-zero NAND-circuit language.  The construction is deliberately
answer-independent: it traverses syntax, constructs an intrinsically
topological NAND program, and only then reifies that program to raw bytes.
-/

import PNP.Concrete.CNF
import PNP.Concrete.LockedNANDReduction
import PNP.NANDComposition

namespace PNP
namespace Concrete
namespace CNFToNAND

open DirectWire
open DirectWire.LockedNANDTrace

/-! ## A finite Boolean expression used only as the compiler specification -/

private inductive BoolExpression (inputs : Nat) where
  | input (index : Fin inputs)
  | constant (value : Bool)
  | neg (body : BoolExpression inputs)
  | conj (left right : BoolExpression inputs)
  | disj (left right : BoolExpression inputs)

private def BoolExpression.eval {inputs : Nat} :
    BoolExpression inputs → Valuation inputs → Bool
  | .input index, valuation => valuation index
  | .constant value, _ => value
  | .neg body, valuation => !(body.eval valuation)
  | .conj left right, valuation =>
      left.eval valuation && right.eval valuation
  | .disj left right, valuation =>
      left.eval valuation || right.eval valuation

private def BoolExpression.gateCost {inputs : Nat} :
    BoolExpression inputs → Nat
  | .input _ => 0
  | .constant _ => 0
  | .neg body => body.gateCost + 1
  | .conj left right => left.gateCost + right.gateCost + 2
  | .disj left right => left.gateCost + right.gateCost + 3

private def literalExpression (inputs : Nat)
    (literal : CNFLiteral) : BoolExpression inputs :=
  if valid : literal.variableIndex < inputs then
    let source : BoolExpression inputs :=
      .input ⟨literal.variableIndex, valid⟩
    if literal.positive then source else .neg source
  else
    .constant false

private def clauseExpression (inputs : Nat) :
    List CNFLiteral → BoolExpression inputs
  | [] => .constant false
  | literal :: rest =>
      .disj (literalExpression inputs literal)
        (clauseExpression inputs rest)

private def clausesExpression (inputs : Nat) :
    List (List CNFLiteral) → BoolExpression inputs
  | [] => .constant true
  | clause :: rest =>
      .conj (clauseExpression inputs clause)
        (clausesExpression inputs rest)

private def formulaExpression (formula : CNFFormula) :
    BoolExpression formula.variableCount :=
  clausesExpression formula.variableCount formula.clauses

/-! ## Intrinsically topological compilation -/

private structure CompiledExpression (inputs : Nat) where
  gateCount : Nat
  program : Program inputs gateCount
  output : Source inputs gateCount

private def CompiledExpression.value {inputs : Nat}
    (compiled : CompiledExpression inputs) (input : Valuation inputs) : Bool :=
  compiled.output.eval input (compiled.program.eval input)

private def identityBinding {inputs gates : Nat} :
    Fin inputs → Source inputs gates :=
  fun index => .input index

private structure PairedCompilation (inputs : Nat) where
  gateCount : Nat
  program : Program inputs gateCount
  left : Source inputs gateCount
  right : Source inputs gateCount

private def pairCompilations {inputs : Nat}
    (left right : CompiledExpression inputs) : PairedCompilation inputs :=
  { gateCount := left.gateCount + right.gateCount
    program :=
      left.program.appendSubstituted
        (identityBinding (gates := left.gateCount)) right.program
    left := left.output.weakenGates right.gateCount
    right :=
      right.output.substituteInputs
        (identityBinding (gates := left.gateCount)) }

private theorem pairCompilations_left_value {inputs : Nat}
    (left right : CompiledExpression inputs) (input : Valuation inputs) :
    (pairCompilations left right).left.eval input
        ((pairCompilations left right).program.eval input) =
      left.value input := by
  unfold pairCompilations CompiledExpression.value
  rw [Source.eval_weakenGates]
  apply left.output.eval_congr
  · intro index
    rfl
  · intro gate
    exact Program.eval_appendSubstituted_prefix
      left.program (identityBinding (gates := left.gateCount))
      right.program input gate

private theorem pairCompilations_right_value {inputs : Nat}
    (left right : CompiledExpression inputs) (input : Valuation inputs) :
    (pairCompilations left right).right.eval input
        ((pairCompilations left right).program.eval input) =
      right.value input := by
  unfold pairCompilations CompiledExpression.value
  rw [Source.eval_substituteInputs]
  apply right.output.eval_congr
  · intro index
    rfl
  · intro gate
    exact Program.eval_appendSubstituted_suffix
      left.program (identityBinding (gates := left.gateCount))
      right.program input gate

private def CompiledExpression.negate {inputs : Nat}
    (compiled : CompiledExpression inputs) : CompiledExpression inputs :=
  { gateCount := compiled.gateCount + 1
    program :=
      .snoc compiled.program
        { left := compiled.output
          right := compiled.output }
    output := .gate (Fin.last compiled.gateCount) }

private theorem CompiledExpression.negate_value {inputs : Nat}
    (compiled : CompiledExpression inputs) (input : Valuation inputs) :
    compiled.negate.value input = !(compiled.value input) := by
  change
    (Program.snoc compiled.program
        { left := compiled.output, right := compiled.output }).eval
      input (Fin.last compiled.gateCount) =
        !(compiled.output.eval input (compiled.program.eval input))
  rw [Program.eval_snoc_last]
  change boolNand
      (compiled.output.eval input (compiled.program.eval input))
      (compiled.output.eval input (compiled.program.eval input)) =
    !(compiled.output.eval input (compiled.program.eval input))
  cases compiled.output.eval input (compiled.program.eval input) <;> rfl

private def PairedCompilation.nand {inputs : Nat}
    (paired : PairedCompilation inputs) : CompiledExpression inputs :=
  { gateCount := paired.gateCount + 1
    program :=
      .snoc paired.program
        { left := paired.left
          right := paired.right }
    output := .gate (Fin.last paired.gateCount) }

private theorem PairedCompilation.nand_value {inputs : Nat}
    (paired : PairedCompilation inputs) (input : Valuation inputs) :
    paired.nand.value input =
      boolNand
        (paired.left.eval input (paired.program.eval input))
        (paired.right.eval input (paired.program.eval input)) := by
  change
    (Program.snoc paired.program
        { left := paired.left, right := paired.right }).eval
      input (Fin.last paired.gateCount) =
        boolNand
          (paired.left.eval input (paired.program.eval input))
          (paired.right.eval input (paired.program.eval input))
  rw [Program.eval_snoc_last]
  rfl

private def compileExpression {inputs : Nat} :
    BoolExpression inputs → CompiledExpression inputs
  | .input index =>
      { gateCount := 0
        program := .empty
        output := .input index }
  | .constant value =>
      { gateCount := 0
        program := .empty
        output := .constant value }
  | .neg body =>
      (compileExpression body).negate
  | .conj left right =>
      (pairCompilations
        (compileExpression left) (compileExpression right)).nand.negate
  | .disj left right =>
      (pairCompilations
        (compileExpression left).negate
        (compileExpression right).negate).nand

private theorem compileExpression_gateCount {inputs : Nat}
    (expression : BoolExpression inputs) :
    (compileExpression expression).gateCount = expression.gateCost := by
  induction expression with
  | input index => rfl
  | constant value => rfl
  | neg body ih =>
      simp [compileExpression, CompiledExpression.negate,
        BoolExpression.gateCost, ih]
  | conj left right leftIH rightIH =>
      simp [compileExpression, CompiledExpression.negate,
        PairedCompilation.nand, pairCompilations,
        BoolExpression.gateCost, leftIH, rightIH] <;> omega
  | disj left right leftIH rightIH =>
      simp [compileExpression, CompiledExpression.negate,
        PairedCompilation.nand, pairCompilations,
        BoolExpression.gateCost, leftIH, rightIH] <;> omega

private theorem compileExpression_value {inputs : Nat}
    (expression : BoolExpression inputs) (input : Valuation inputs) :
    (compileExpression expression).value input = expression.eval input := by
  induction expression with
  | input index =>
      rfl
  | constant value =>
      rfl
  | neg body ih =>
      rw [compileExpression, CompiledExpression.negate_value, ih]
      simp [BoolExpression.eval]
  | conj left right leftIH rightIH =>
      rw [compileExpression, CompiledExpression.negate_value,
        PairedCompilation.nand_value,
        pairCompilations_left_value, pairCompilations_right_value,
        leftIH, rightIH]
      simp [BoolExpression.eval, boolNand]
  | disj left right leftIH rightIH =>
      rw [compileExpression, PairedCompilation.nand_value,
        pairCompilations_left_value, pairCompilations_right_value,
        CompiledExpression.negate_value, CompiledExpression.negate_value,
        leftIH, rightIH]
      simp [BoolExpression.eval, boolNand]

/-! ## Final-gate normalization -/

private def CompiledExpression.toCircuit {inputs : Nat}
    (compiled : CompiledExpression inputs) : Circuit inputs :=
  match compiled.output with
  | .gate index =>
      { gateCount := compiled.gateCount
        program := compiled.program
        outputGate := index }
  | .input index =>
      let first : Program inputs (compiled.gateCount + 1) :=
        .snoc compiled.program
          { left := .input index
            right := .constant true }
      let second : Program inputs ((compiled.gateCount + 1) + 1) :=
        .snoc first
          { left := .gate (Fin.last compiled.gateCount)
            right := .gate (Fin.last compiled.gateCount) }
      { gateCount := (compiled.gateCount + 1) + 1
        program := second
        outputGate := Fin.last (compiled.gateCount + 1) }
  | .constant false =>
      { gateCount := compiled.gateCount + 1
        program :=
          .snoc compiled.program
            { left := .constant true
              right := .constant true }
        outputGate := Fin.last compiled.gateCount }
  | .constant true =>
      { gateCount := compiled.gateCount + 1
        program :=
          .snoc compiled.program
            { left := .constant false
              right := .constant false }
        outputGate := Fin.last compiled.gateCount }

private theorem CompiledExpression.toCircuit_value {inputs : Nat}
    (compiled : CompiledExpression inputs) (input : Valuation inputs) :
    compiled.toCircuit.program.eval input compiled.toCircuit.outputGate =
      compiled.value input := by
  cases output : compiled.output with
  | gate index =>
      unfold CompiledExpression.toCircuit CompiledExpression.value
      rw [output]
      rfl
  | input index =>
      unfold CompiledExpression.toCircuit CompiledExpression.value
      rw [output]
      simp only [Program.eval_snoc_last, Gate.eval, Source.eval]
      change boolNand (boolNand (input index) true)
          (boolNand (input index) true) = input index
      cases input index <;> rfl
  | constant value =>
      cases value with
      | false =>
          unfold CompiledExpression.toCircuit CompiledExpression.value
          rw [output]
          simp [Program.eval_snoc_last,
            Gate.eval, Source.eval, boolNand]
      | true =>
          unfold CompiledExpression.toCircuit CompiledExpression.value
          rw [output]
          simp [Program.eval_snoc_last,
            Gate.eval, Source.eval, boolNand]

/-! ## Agreement with the concrete CNF semantics -/

private theorem assignmentAt_eq_getElem?
    (assignment : BitString) (index : Nat) :
    assignmentAt assignment index = assignment[index]? := by
  induction assignment generalizing index with
  | nil =>
      simp [assignmentAt]
  | cons value rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          simpa [assignmentAt] using ih index

private theorem assignmentAt_ofFn {inputs : Nat}
    (input : Valuation inputs) (index : Nat) :
    assignmentAt (List.ofFn input) index =
      if valid : index < inputs then
        some (input ⟨index, valid⟩)
      else
        none := by
  rw [assignmentAt_eq_getElem?, List.getElem?_ofFn]

private theorem literalExpression_eval (inputs : Nat)
    (literal : CNFLiteral) (input : Valuation inputs) :
    (literalExpression inputs literal).eval input =
      checkLiteral literal (List.ofFn input) := by
  unfold literalExpression checkLiteral
  rw [assignmentAt_ofFn]
  split
  · rename_i valid
    cases positive : literal.positive <;>
      cases value : input ⟨literal.variableIndex, valid⟩ <;>
      simp [BoolExpression.eval, boolEqual] <;> assumption
  · simp [BoolExpression.eval]

private theorem clauseExpression_eval (inputs : Nat)
    (clause : List CNFLiteral) (input : Valuation inputs) :
    (clauseExpression inputs clause).eval input =
      checkClause clause (List.ofFn input) := by
  induction clause with
  | nil => rfl
  | cons literal rest ih =>
      simp [clauseExpression, BoolExpression.eval,
        literalExpression_eval, checkClause, ih]

private theorem clausesExpression_eval (inputs : Nat)
    (clauses : List (List CNFLiteral)) (input : Valuation inputs) :
    (clausesExpression inputs clauses).eval input =
      checkClauses clauses (List.ofFn input) := by
  induction clauses with
  | nil => rfl
  | cons clause rest ih =>
      simp [clausesExpression, BoolExpression.eval,
        clauseExpression_eval, checkClauses, ih]

private theorem formulaExpression_eval (formula : CNFFormula)
    (input : Valuation formula.variableCount) :
    (formulaExpression formula).eval input =
      checkCNF formula (List.ofFn input) := by
  unfold formulaExpression checkCNF
  have width :
      natEqual (List.ofFn input).length formula.variableCount = true := by
    apply (natEqual_eq_true_iff _ _).mpr
    simp
  rw [width]
  simp [clausesExpression_eval]

private theorem list_ofFn_bounded_get_eq
    (assignment : BitString) (width : Nat)
    (lengthEqual : assignment.length = width) :
    List.ofFn
        (fun index : Fin width =>
          assignment.get
            ⟨index.val, by omega⟩) =
      assignment := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_ofFn]
  by_cases within : index < width
  · have assignmentWithin : index < assignment.length := by
      omega
    simp [within, assignmentWithin]
  · have assignmentOutside : ¬ index < assignment.length := by
      omega
    simp [within, assignmentOutside]

/-! ## Public compiler interface -/

/-- Total number of literal occurrences in a decoded CNF formula. -/
def literalCount (formula : CNFFormula) : Nat :=
  (formula.clauses.map List.length).sum

/-- Number of in-range negative literal occurrences.  Out-of-range literals
are semantically false in the concrete CNF language and are not counted as
negation gates. -/
def validNegativeLiteralCount (formula : CNFFormula) : Nat :=
  (formula.clauses.map fun clause =>
    (clause.filter fun literal =>
      !literal.positive && literal.variableIndex < formula.variableCount).length).sum

private def clausesMass (clauses : List (List CNFLiteral)) : Nat :=
  clauses.length + (clauses.map List.length).sum

private theorem clausesMass_cons (clause : List CNFLiteral)
    (clauses : List (List CNFLiteral)) :
    clausesMass (clause :: clauses) =
      clause.length + clausesMass clauses + 1 := by
  simp [clausesMass]
  omega

/-- Every clause or literal introduced by the strict recursive grammar
consumes a token.  Keeping the three mutually recursive parser states in one
induction avoids any trusted parser-size oracle. -/
private theorem decodeFormulaBodies_mass_bound (tokens : List CNFToken) :
    (∀ clauses,
        decodeFormulaClauses tokens = some clauses →
          clausesMass clauses ≤ tokens.length) ∧
    (∀ clause clauses,
        decodeFormulaClause tokens = some (clause, clauses) →
          clause.length + clausesMass clauses ≤ tokens.length) ∧
    (∀ positive start clause clauses,
        decodeFormulaLiteral positive start tokens =
            some (clause, clauses) →
          clause.length + clausesMass clauses ≤ tokens.length + 1) := by
  induction tokens with
  | nil =>
      constructor
      · intro clauses decoded
        change none = some clauses at decoded
        cases decoded
      · constructor
        · intro clause clauses decoded
          change none = some (clause, clauses) at decoded
          cases decoded
        · intro positive start clause clauses decoded
          change none = some (clause, clauses) at decoded
          cases decoded
  | cons token rest ih =>
      rcases ih with ⟨clausesIH, clauseIH, literalIH⟩
      constructor
      · intro clauses decoded
        cases token with
        | f =>
            change none = some clauses at decoded
            cases decoded
        | t =>
            change none = some clauses at decoded
            cases decoded
        | sep =>
            change
              (match decodeFormulaClause rest with
                | none => none
                | some (clause, suffix) =>
                    some (clause :: suffix)) =
                some clauses at decoded
            cases clauseCase : decodeFormulaClause rest with
            | none =>
                rw [clauseCase] at decoded
                cases decoded
            | some result =>
                rcases result with ⟨clause, suffix⟩
                rw [clauseCase] at decoded
                have equal : clause :: suffix = clauses :=
                  Option.some.inj decoded
                cases equal
                have bound := clauseIH clause suffix clauseCase
                rw [clausesMass_cons]
                simp only [List.length_cons]
                omega
        | finish =>
            cases rest with
            | nil =>
                change some [] = some clauses at decoded
                have equal : [] = clauses := Option.some.inj decoded
                cases equal
                simp [clausesMass]
            | cons next suffix =>
                change none = some clauses at decoded
                cases decoded
      · constructor
        · intro clause clauses decoded
          cases token with
          | f =>
              change decodeFormulaLiteral false 0 rest =
                  some (clause, clauses) at decoded
              have bound := literalIH false 0 clause clauses decoded
              simpa only [List.length_cons] using bound
          | t =>
              change decodeFormulaLiteral true 0 rest =
                  some (clause, clauses) at decoded
              have bound := literalIH true 0 clause clauses decoded
              simpa only [List.length_cons] using bound
          | sep =>
              change none = some (clause, clauses) at decoded
              cases decoded
          | finish =>
              change
                (match decodeFormulaClauses rest with
                  | none => none
                  | some suffix => some ([], suffix)) =
                    some (clause, clauses) at decoded
              cases clausesCase : decodeFormulaClauses rest with
              | none =>
                  rw [clausesCase] at decoded
                  cases decoded
              | some suffix =>
                  rw [clausesCase] at decoded
                  have equal : ([], suffix) = (clause, clauses) :=
                    Option.some.inj decoded
                  have bound := clausesIH suffix clausesCase
                  cases equal
                  simp only [List.length_nil, Nat.zero_add,
                    List.length_cons]
                  omega
        · intro positive start clause clauses decoded
          cases token with
          | f =>
              change
                (match decodeFormulaClause rest with
                  | none => none
                  | some (tail, suffix) =>
                      some
                        ({ positive := positive,
                           variableIndex := start } :: tail, suffix)) =
                    some (clause, clauses) at decoded
              cases clauseCase : decodeFormulaClause rest with
              | none =>
                  rw [clauseCase] at decoded
                  cases decoded
              | some result =>
                  rcases result with ⟨tail, suffix⟩
                  rw [clauseCase] at decoded
                  have equal :
                      ({ positive := positive,
                         variableIndex := start } :: tail, suffix) =
                        (clause, clauses) :=
                    Option.some.inj decoded
                  have bound := clauseIH tail suffix clauseCase
                  cases equal
                  simp only [List.length_cons]
                  omega
          | t =>
              change decodeFormulaLiteral positive (start + 1) rest =
                  some (clause, clauses) at decoded
              have bound :=
                literalIH positive (start + 1) clause clauses decoded
              simp only [List.length_cons]
              omega
          | sep =>
              change none = some (clause, clauses) at decoded
              cases decoded
          | finish =>
              change none = some (clause, clauses) at decoded
              cases decoded

private theorem decodeFormulaHeader_mass_bound
    (start : Nat) (tokens : List CNFToken) (formula : CNFFormula)
    (decoded : decodeFormulaHeader start tokens = some formula) :
    formula.variableCount + clausesMass formula.clauses ≤
      start + tokens.length := by
  induction tokens generalizing start formula with
  | nil =>
      change none = some formula at decoded
      cases decoded
  | cons token rest ih =>
      cases token with
      | f =>
          change
            (match decodeFormulaClauses rest with
              | none => none
              | some clauses =>
                  some
                    ({ variableCount := start,
                       clauses := clauses } : CNFFormula)) =
                some formula at decoded
          cases clausesCase : decodeFormulaClauses rest with
          | none =>
              rw [clausesCase] at decoded
              cases decoded
          | some clauses =>
              rw [clausesCase] at decoded
              have equal :
                  ({ variableCount := start,
                     clauses := clauses } : CNFFormula) = formula :=
                Option.some.inj decoded
              cases equal
              have bound :=
                (decodeFormulaBodies_mass_bound rest).1 clauses clausesCase
              simp only [List.length_cons]
              omega
      | t =>
          change decodeFormulaHeader (start + 1) rest =
              some formula at decoded
          have bound := ih (start + 1) formula decoded
          simp only [List.length_cons]
          omega
      | sep =>
          change none = some formula at decoded
          cases decoded
      | finish =>
          change none = some formula at decoded
          cases decoded

private theorem decodedFormula_structural_size_le
    (bits : BitString) (formula : CNFFormula)
    (decoded : decodeEncodedCNF bits = some formula) :
    formula.variableCount + literalCount formula +
        formula.clauses.length ≤ bits.length := by
  unfold decodeEncodedCNF at decoded
  cases tokenCase : decodeFormulaTokenPairs bits with
  | none =>
      rw [tokenCase] at decoded
      cases decoded
  | some tokens =>
      rw [tokenCase] at decoded
      unfold decodeCNFTokens at decoded
      have mass :=
        decodeFormulaHeader_mass_bound 0 tokens formula decoded
      have lengthEqual :=
        decodeFormulaTokenPairs_length bits tokens tokenCase
      unfold clausesMass at mass
      unfold literalCount
      rw [Nat.zero_add] at mass
      rw [lengthEqual]
      omega

/-! Accepted source encodings are canonical, not aliases for a second byte
representation of the same formula. -/

private theorem decodeFormulaBodies_reencode (tokens : List CNFToken) :
    (∀ clauses,
        decodeFormulaClauses tokens = some clauses →
          tokens =
            encodeClauseListTokens clauses ++ [.finish]) ∧
    (∀ clause clauses,
        decodeFormulaClause tokens = some (clause, clauses) →
          tokens =
            encodeLiteralListTokens clause ++
              [.finish] ++
              encodeClauseListTokens clauses ++ [.finish]) ∧
    (∀ positive start clause clauses,
        decodeFormulaLiteral positive start tokens =
            some (clause, clauses) →
          ∃ index tail,
            clause =
              { positive := positive,
                variableIndex := index } :: tail ∧
            start ≤ index ∧
            tokens =
              encodeUnaryTokens (index - start) ++
                encodeLiteralListTokens tail ++
                [.finish] ++
                encodeClauseListTokens clauses ++ [.finish]) := by
  induction tokens with
  | nil =>
      constructor
      · intro clauses decoded
        change none = some clauses at decoded
        cases decoded
      · constructor
        · intro clause clauses decoded
          change none = some (clause, clauses) at decoded
          cases decoded
        · intro positive start clause clauses decoded
          change none = some (clause, clauses) at decoded
          cases decoded
  | cons token rest ih =>
      rcases ih with ⟨clausesIH, clauseIH, literalIH⟩
      constructor
      · intro clauses decoded
        cases token with
        | f =>
            change none = some clauses at decoded
            cases decoded
        | t =>
            change none = some clauses at decoded
            cases decoded
        | sep =>
            change
              (match decodeFormulaClause rest with
                | none => none
                | some (clause, suffix) =>
                    some (clause :: suffix)) =
                some clauses at decoded
            cases clauseCase : decodeFormulaClause rest with
            | none =>
                rw [clauseCase] at decoded
                cases decoded
            | some result =>
                rcases result with ⟨clause, suffix⟩
                rw [clauseCase] at decoded
                have equal : clause :: suffix = clauses :=
                  Option.some.inj decoded
                have restBytes :=
                  clauseIH clause suffix clauseCase
                cases equal
                rw [restBytes]
                simp [encodeClauseListTokens, encodeClauseTokens,
                  List.append_assoc]
        | finish =>
            cases rest with
            | nil =>
                change some [] = some clauses at decoded
                have equal : [] = clauses := Option.some.inj decoded
                cases equal
                rfl
            | cons next suffix =>
                change none = some clauses at decoded
                cases decoded
      · constructor
        · intro clause clauses decoded
          cases token with
          | f =>
              change decodeFormulaLiteral false 0 rest =
                  some (clause, clauses) at decoded
              rcases literalIH false 0 clause clauses decoded with
                ⟨index, tail, clauseEqual, _, restBytes⟩
              cases clauseEqual
              rw [restBytes]
              simp [encodeLiteralListTokens, encodeLiteralTokens,
                List.append_assoc]
          | t =>
              change decodeFormulaLiteral true 0 rest =
                  some (clause, clauses) at decoded
              rcases literalIH true 0 clause clauses decoded with
                ⟨index, tail, clauseEqual, _, restBytes⟩
              cases clauseEqual
              rw [restBytes]
              simp [encodeLiteralListTokens, encodeLiteralTokens,
                List.append_assoc]
          | sep =>
              change none = some (clause, clauses) at decoded
              cases decoded
          | finish =>
              change
                (match decodeFormulaClauses rest with
                  | none => none
                  | some suffix => some ([], suffix)) =
                    some (clause, clauses) at decoded
              cases clausesCase : decodeFormulaClauses rest with
              | none =>
                  rw [clausesCase] at decoded
                  cases decoded
              | some suffix =>
                  rw [clausesCase] at decoded
                  have equal : ([], suffix) = (clause, clauses) :=
                    Option.some.inj decoded
                  have restBytes := clausesIH suffix clausesCase
                  cases equal
                  rw [restBytes]
                  simp [encodeLiteralListTokens]
        · intro positive start clause clauses decoded
          cases token with
          | f =>
              change
                (match decodeFormulaClause rest with
                  | none => none
                  | some (tail, suffix) =>
                      some
                        ({ positive := positive,
                           variableIndex := start } :: tail, suffix)) =
                    some (clause, clauses) at decoded
              cases clauseCase : decodeFormulaClause rest with
              | none =>
                  rw [clauseCase] at decoded
                  cases decoded
              | some result =>
                  rcases result with ⟨tail, suffix⟩
                  rw [clauseCase] at decoded
                  have equal :
                      ({ positive := positive,
                         variableIndex := start } :: tail, suffix) =
                        (clause, clauses) :=
                    Option.some.inj decoded
                  have restBytes :=
                    clauseIH tail suffix clauseCase
                  cases equal
                  refine ⟨start, tail, rfl, Nat.le_refl start, ?_⟩
                  rw [restBytes]
                  simp [encodeUnaryTokens, List.append_assoc]
          | t =>
              change decodeFormulaLiteral positive (start + 1) rest =
                  some (clause, clauses) at decoded
              rcases literalIH positive (start + 1) clause clauses decoded with
                ⟨index, tail, clauseEqual, indexBound, restBytes⟩
              refine ⟨index, tail, clauseEqual, by omega, ?_⟩
              rw [restBytes]
              have difference :
                  index - start = (index - (start + 1)) + 1 := by
                omega
              rw [difference]
              rfl
          | sep =>
              change none = some (clause, clauses) at decoded
              cases decoded
          | finish =>
              change none = some (clause, clauses) at decoded
              cases decoded

private theorem decodeFormulaHeader_reencode
    (start : Nat) (tokens : List CNFToken) (formula : CNFFormula)
    (decoded : decodeFormulaHeader start tokens = some formula) :
    ∃ count,
      formula.variableCount = start + count ∧
      tokens =
        encodeUnaryTokens count ++
          encodeClauseListTokens formula.clauses ++ [.finish] := by
  induction tokens generalizing start formula with
  | nil =>
      change none = some formula at decoded
      cases decoded
  | cons token rest ih =>
      cases token with
      | f =>
          change
            (match decodeFormulaClauses rest with
              | none => none
              | some clauses =>
                  some
                    ({ variableCount := start,
                       clauses := clauses } : CNFFormula)) =
                some formula at decoded
          cases clausesCase : decodeFormulaClauses rest with
          | none =>
              rw [clausesCase] at decoded
              cases decoded
          | some clauses =>
              rw [clausesCase] at decoded
              have equal :
                  ({ variableCount := start,
                     clauses := clauses } : CNFFormula) = formula :=
                Option.some.inj decoded
              have restBytes :=
                (decodeFormulaBodies_reencode rest).1 clauses clausesCase
              cases equal
              refine ⟨0, rfl, ?_⟩
              rw [restBytes]
              rfl
      | t =>
          change decodeFormulaHeader (start + 1) rest =
              some formula at decoded
          rcases ih (start + 1) formula decoded with
            ⟨count, width, restBytes⟩
          refine ⟨count + 1, by omega, ?_⟩
          rw [restBytes]
          rfl
      | sep =>
          change none = some formula at decoded
          cases decoded
      | finish =>
          change none = some formula at decoded
          cases decoded

private theorem decodeCNFTokens_reencode
    (tokens : List CNFToken) (formula : CNFFormula)
    (decoded : decodeCNFTokens tokens = some formula) :
    tokens = encodeCNFTokens formula := by
  unfold decodeCNFTokens at decoded
  rcases decodeFormulaHeader_reencode 0 tokens formula decoded with
    ⟨count, width, bytes⟩
  have countEqual : count = formula.variableCount := by
    omega
  cases countEqual
  simpa [encodeCNFTokens] using bytes

private theorem token_bits_ofBits (first second : Bool) :
    (CNFToken.ofBits first second).bits = [first, second] := by
  cases first <;> cases second <;> rfl

private theorem decodeFormulaTokenPairs_reencode
    (bits : BitString) (tokens : List CNFToken)
    (decoded : decodeFormulaTokenPairs bits = some tokens) :
    bits = encodeTokenPairs tokens ++ [false] := by
  induction tokens generalizing bits with
  | nil =>
      cases bits with
      | nil =>
          change none = some [] at decoded
          cases decoded
      | cons first tail =>
          cases tail with
          | nil =>
              cases first with
              | false => rfl
              | true =>
                  change none = some [] at decoded
                  cases decoded
          | cons second rest =>
              simp only [decodeFormulaTokenPairs] at decoded
              cases restCase : decodeFormulaTokenPairs rest with
              | none =>
                  rw [restCase] at decoded
                  cases decoded
              | some decodedTokens =>
                  rw [restCase] at decoded
                  have impossible :
                      CNFToken.ofBits first second :: decodedTokens = [] :=
                    Option.some.inj decoded
                  cases impossible
  | cons token tokens ih =>
      cases bits with
      | nil =>
          change none = some (token :: tokens) at decoded
          cases decoded
      | cons first tail =>
          cases tail with
          | nil =>
              cases first with
              | false =>
                  change some [] = some (token :: tokens) at decoded
                  have impossible : [] = token :: tokens :=
                    Option.some.inj decoded
                  cases impossible
              | true =>
                  change none = some (token :: tokens) at decoded
                  cases decoded
          | cons second rest =>
              simp only [decodeFormulaTokenPairs] at decoded
              cases restCase : decodeFormulaTokenPairs rest with
              | none =>
                  rw [restCase] at decoded
                  cases decoded
              | some decodedTokens =>
                  rw [restCase] at decoded
                  have equal :
                      CNFToken.ofBits first second :: decodedTokens =
                        token :: tokens :=
                    Option.some.inj decoded
                  have headEqual :
                      CNFToken.ofBits first second = token :=
                    (List.cons.inj equal).1
                  have tailEqual : decodedTokens = tokens :=
                    (List.cons.inj equal).2
                  cases tailEqual
                  have restBytes := ih rest restCase
                  rw [restBytes]
                  rw [encodeTokenPairs,
                    BitString.append_assoc_constructive,
                    ← headEqual, token_bits_ofBits]
                  rfl

/-- Every accepted formula byte string is the unique canonical encoding of
the formula returned by the strict decoder. -/
theorem encodeCNF_of_decodeEncodedCNF
    (bits : BitString) (formula : CNFFormula)
    (decoded : decodeEncodedCNF bits = some formula) :
    encodeCNF formula = bits := by
  unfold decodeEncodedCNF at decoded
  cases tokenCase : decodeFormulaTokenPairs bits with
  | none =>
      rw [tokenCase] at decoded
      cases decoded
  | some tokens =>
      rw [tokenCase] at decoded
      have tokenBytes :=
        decodeCNFTokens_reencode tokens formula decoded
      have bitBytes :=
        decodeFormulaTokenPairs_reencode bits tokens tokenCase
      rw [bitBytes, tokenBytes]
      rfl

private theorem literalExpression_gateCost (inputs : Nat)
    (literal : CNFLiteral) :
    (literalExpression inputs literal).gateCost =
      if !literal.positive && literal.variableIndex < inputs then 1 else 0 := by
  unfold literalExpression
  by_cases valid : literal.variableIndex < inputs
  · simp [valid]
    cases literal.positive <;> rfl
  · simp [valid, BoolExpression.gateCost]

private theorem clauseExpression_gateCost (inputs : Nat)
    (clause : List CNFLiteral) :
    (clauseExpression inputs clause).gateCost =
      (clause.filter fun literal =>
        !literal.positive && literal.variableIndex < inputs).length +
        3 * clause.length := by
  induction clause with
  | nil => rfl
  | cons literal rest ih =>
      cases condition :
          (!literal.positive &&
            decide (literal.variableIndex < inputs)) <;>
        simp [clauseExpression, BoolExpression.gateCost,
          literalExpression_gateCost,
          condition, ih] <;> omega

private theorem clausesExpression_gateCost (inputs : Nat)
    (clauses : List (List CNFLiteral)) :
    (clausesExpression inputs clauses).gateCost =
      (clauses.map fun clause =>
        (clause.filter fun literal =>
          !literal.positive && literal.variableIndex < inputs).length).sum +
        3 * (clauses.map List.length).sum +
        2 * clauses.length := by
  induction clauses with
  | nil => rfl
  | cons clause rest ih =>
      rw [clausesExpression]
      simp only [BoolExpression.gateCost, List.map_cons, List.sum_cons,
        List.length_cons, clauseExpression_gateCost, ih]
      omega

/-- The intrinsically topological circuit produced for one decoded formula. -/
def compiledFormulaCircuit (formula : CNFFormula) :
    Circuit formula.variableCount :=
  (compileExpression (formulaExpression formula)).toCircuit

/-- Reify the typed compiler result to the strict raw circuit boundary. -/
def compileFormula (formula : CNFFormula) : LockedNAND.RawCircuit :=
  LockedNAND.RawCircuit.ofCircuit (compiledFormulaCircuit formula)

/-! ## Pure postfix compilation plan

The semantic compiler above is intrinsically typed.  The following plan is
the same construction expressed as three finite actions over an untyped
gate accumulator and source stack.  It is suitable for later realization by
a fixed machine: source actions only push data, while each `negate` or
`nand` action emits exactly one gate at the current accumulator length.
-/

inductive CompilationAction where
  | push (source : LockedNAND.RawSource)
  | negate
  | nand
deriving BEq, DecidableEq, Repr

structure CompilationState where
  gates : List LockedNAND.RawGate
  stack : List LockedNAND.RawSource
deriving BEq, DecidableEq, Repr

private def CompilationState.emitNand
    (state : CompilationState)
    (left right : LockedNAND.RawSource)
    (rest : List LockedNAND.RawSource) : CompilationState :=
  let output := LockedNAND.RawSource.gate state.gates.length
  { gates := state.gates ++ [{ left := left, right := right }]
    stack := output :: rest }

/-- One fail-closed postfix action.  `nand` pops the right operand first,
then the left operand, preserving the typed compiler's gate orientation. -/
def CompilationAction.step
    (action : CompilationAction)
    (state : CompilationState) : Option CompilationState :=
  match action with
  | .push source =>
      some { state with stack := source :: state.stack }
  | .negate =>
      match state.stack with
      | source :: rest =>
          some (state.emitNand source source rest)
      | [] => none
  | .nand =>
      match state.stack with
      | right :: left :: rest =>
          some (state.emitNand left right rest)
      | _ => none

/-- Execute a finite postfix plan without any host-side lookup. -/
def runCompilationPlan :
    List CompilationAction → CompilationState →
      Option CompilationState
  | [], state => some state
  | action :: rest, state =>
      match action.step state with
      | none => none
      | some next => runCompilationPlan rest next

private theorem runCompilationPlan_append
    (first second : List CompilationAction)
    (state : CompilationState) :
    runCompilationPlan (first ++ second) state =
      match runCompilationPlan first state with
      | none => none
      | some middle => runCompilationPlan second middle := by
  induction first generalizing state with
  | nil =>
      rfl
  | cons action rest ih =>
      simp only [List.cons_append, runCompilationPlan]
      cases stepped : action.step state with
      | none => rfl
      | some next => exact ih next

/-- Literal actions.  Both polarities of an out-of-range literal compile to
false; only an in-range negative occurrence emits a literal-negation gate. -/
def literalPlan (inputs : Nat)
    (literal : CNFLiteral) : List CompilationAction :=
  if literal.variableIndex < inputs then
    [.push (.input literal.variableIndex)] ++
      if literal.positive then [] else [.negate]
  else
    [.push (.constant false)]

/-- Out-of-range literals of either polarity compile to the same false
source, matching the fail-closed CNF semantics. -/
theorem literalPlan_of_out_of_range
    (inputs : Nat) (literal : CNFLiteral)
    (outOfRange : inputs ≤ literal.variableIndex) :
    literalPlan inputs literal =
      [.push (.constant false)] := by
  have invalid : ¬ literal.variableIndex < inputs :=
    Nat.not_lt.mpr outOfRange
  simp [literalPlan, invalid]

/-- Right-recursive disjunction plan.  Its order is literal, literal
negation for the NAND encoding of OR, recursive tail, tail negation, NAND. -/
def clausePlan (inputs : Nat) :
    List CNFLiteral → List CompilationAction
  | [] => [.push (.constant false)]
  | literal :: rest =>
      literalPlan inputs literal ++ [.negate] ++
        clausePlan inputs rest ++ [.negate, .nand]

@[simp] theorem clausePlan_empty (inputs : Nat) :
    clausePlan inputs [] =
      [.push (.constant false)] := rfl

theorem clausePlan_cons
    (inputs : Nat) (literal : CNFLiteral)
    (rest : List CNFLiteral) :
    clausePlan inputs (literal :: rest) =
      literalPlan inputs literal ++ [.negate] ++
        clausePlan inputs rest ++ [.negate, .nand] := rfl

/-- Right-recursive conjunction plan.  Each clause/tail pair emits NAND and
then a self-NAND, exactly matching the current compiler's AND encoding. -/
def clausesPlan (inputs : Nat) :
    List (List CNFLiteral) → List CompilationAction
  | [] => [.push (.constant true)]
  | clause :: rest =>
      clausePlan inputs clause ++ clausesPlan inputs rest ++
        [.nand, .negate]

@[simp] theorem clausesPlan_empty (inputs : Nat) :
    clausesPlan inputs [] =
      [.push (.constant true)] := rfl

theorem clausesPlan_cons
    (inputs : Nat) (clause : List CNFLiteral)
    (rest : List (List CNFLiteral)) :
    clausesPlan inputs (clause :: rest) =
      clausePlan inputs clause ++ clausesPlan inputs rest ++
        [.nand, .negate] := rfl

/-- Complete action list for one decoded formula. -/
def formulaPlan (formula : CNFFormula) : List CompilationAction :=
  clausesPlan formula.variableCount formula.clauses

@[simp] theorem formulaPlan_empty (inputs : Nat) :
    formulaPlan { variableCount := inputs, clauses := [] } =
      [.push (.constant true)] := rfl

@[simp] theorem formulaPlan_single_empty_clause (inputs : Nat) :
    formulaPlan { variableCount := inputs, clauses := [[]] } =
      [ .push (.constant false)
      , .push (.constant true)
      , .nand
      , .negate ] := rfl

private theorem literalPlan_length
    (inputs : Nat) (literal : CNFLiteral) :
    (literalPlan inputs literal).length =
      1 +
        (if !literal.positive &&
            literal.variableIndex < inputs then 1 else 0) := by
  unfold literalPlan
  by_cases valid : literal.variableIndex < inputs
  · cases literal.positive <;> simp [valid]
  · simp [valid]

private theorem clausePlan_length
    (inputs : Nat) (clause : List CNFLiteral) :
    (clausePlan inputs clause).length =
      (clause.filter fun literal =>
        !literal.positive &&
          literal.variableIndex < inputs).length +
        4 * clause.length + 1 := by
  induction clause with
  | nil => rfl
  | cons literal rest ih =>
      rw [clausePlan_cons]
      cases polarity : literal.positive <;>
        by_cases valid : literal.variableIndex < inputs <;>
          simp [literalPlan_length, ih, polarity, valid] <;> omega

private theorem clausesPlan_length
    (inputs : Nat) (clauses : List (List CNFLiteral)) :
    (clausesPlan inputs clauses).length =
      (clauses.map fun clause =>
        (clause.filter fun literal =>
          !literal.positive &&
            literal.variableIndex < inputs).length).sum +
        4 * (clauses.map List.length).sum +
        3 * clauses.length + 1 := by
  induction clauses with
  | nil => rfl
  | cons clause rest ih =>
      rw [clausesPlan_cons]
      simp only [List.length_append, List.length_cons,
        List.length_nil, clausePlan_length, ih,
        List.map_cons, List.sum_cons]
      omega

/-- Exact size of the machine-friendly postfix schedule.  The constant
`1` is its terminal Boolean source; every other action is forced by a
literal polarity or one of the fixed recursive NAND wrappers. -/
theorem formulaPlan_length_exact (formula : CNFFormula) :
    (formulaPlan formula).length =
      validNegativeLiteralCount formula +
        4 * literalCount formula +
        3 * formula.clauses.length + 1 := by
  unfold formulaPlan validNegativeLiteralCount literalCount
  exact clausesPlan_length formula.variableCount formula.clauses

private theorem validNegativeLiteralCount_le_literalCount
    (formula : CNFFormula) :
    validNegativeLiteralCount formula ≤ literalCount formula := by
  unfold validNegativeLiteralCount literalCount
  induction formula.clauses with
  | nil => exact Nat.le_refl 0
  | cons clause rest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (List.length_filter_le _ _) ih

/-- Linear structural upper bound for the postfix schedule. -/
theorem formulaPlan_length_le (formula : CNFFormula) :
    (formulaPlan formula).length ≤
      5 * literalCount formula +
        3 * formula.clauses.length + 1 := by
  rw [formulaPlan_length_exact]
  have negativeBound :=
    validNegativeLiteralCount_le_literalCount formula
  omega

/-- A decoded source word bounds the complete postfix schedule linearly. -/
theorem formulaPlan_length_le_encoded_bits
    (bits : BitString) (formula : CNFFormula)
    (decoded : decodeEncodedCNF bits = some formula) :
    (formulaPlan formula).length ≤ 5 * bits.length + 1 := by
  have planBound := formulaPlan_length_le formula
  have structural :=
    decodedFormula_structural_size_le bits formula decoded
  omega

/-- Normalize the single postfix result to a mandatory gate output using the
same legacy cases as `CompiledExpression.toCircuit`. -/
def finalizeCompilation (inputs : Nat)
    (state : CompilationState) :
    Option LockedNAND.RawCircuit :=
  match state.stack with
  | [output] =>
      match output with
      | .gate index =>
          some
            { inputCount := inputs
              gates := state.gates
              output := .gate index }
      | .input index =>
          let first := state.gates.length
          some
            { inputCount := inputs
              gates := state.gates ++
                [ { left := .input index, right := .constant true }
                , { left := .gate first, right := .gate first } ]
              output := .gate (first + 1) }
      | .constant false =>
          let first := state.gates.length
          some
            { inputCount := inputs
              gates := state.gates ++
                [{ left := .constant true, right := .constant true }]
              output := .gate first }
      | .constant true =>
          let first := state.gates.length
          some
            { inputCount := inputs
              gates := state.gates ++
                [{ left := .constant false, right := .constant false }]
              output := .gate first }
  | _ => none

/-- Pure plan execution from the empty accumulator. -/
def executeFormulaPlan
    (formula : CNFFormula) : Option LockedNAND.RawCircuit :=
  match runCompilationPlan (formulaPlan formula)
      { gates := [], stack := [] } with
  | none => none
  | some state => finalizeCompilation formula.variableCount state

/-- Exact byte emitter induced by the pure plan; malformed internal stack
states fail closed to the empty word. -/
def emitFormulaPlan (formula : CNFFormula) : BitString :=
  match executeFormulaPlan formula with
  | none => []
  | some circuit => LockedNAND.encodeCircuit circuit

private def expressionPlan {inputs : Nat} :
    BoolExpression inputs → List CompilationAction
  | .input index => [.push (.input index.val)]
  | .constant value => [.push (.constant value)]
  | .neg body => expressionPlan body ++ [.negate]
  | .conj left right =>
      expressionPlan left ++ expressionPlan right ++
        [.nand, .negate]
  | .disj left right =>
      expressionPlan left ++ [.negate] ++
        expressionPlan right ++ [.negate, .nand]

private theorem literalPlan_eq_expressionPlan
    (inputs : Nat) (literal : CNFLiteral) :
    literalPlan inputs literal =
      expressionPlan (literalExpression inputs literal) := by
  unfold literalPlan literalExpression
  split
  · rename_i valid
    cases literal.positive <;> rfl
  · rfl

private theorem clausePlan_eq_expressionPlan
    (inputs : Nat) (clause : List CNFLiteral) :
    clausePlan inputs clause =
      expressionPlan (clauseExpression inputs clause) := by
  induction clause with
  | nil =>
      rfl
  | cons literal rest ih =>
      simp only [clausePlan, clauseExpression, expressionPlan,
        literalPlan_eq_expressionPlan, ih, List.append_assoc]

private theorem clausesPlan_eq_expressionPlan
    (inputs : Nat) (clauses : List (List CNFLiteral)) :
    clausesPlan inputs clauses =
      expressionPlan (clausesExpression inputs clauses) := by
  induction clauses with
  | nil =>
      rfl
  | cons clause rest ih =>
      simp only [clausesPlan, clausesExpression, expressionPlan,
        clausePlan_eq_expressionPlan, ih, List.append_assoc]

private def shiftRawSource (offset : Nat) :
    LockedNAND.RawSource → LockedNAND.RawSource
  | .input index => .input index
  | .constant value => .constant value
  | .gate index => .gate (offset + index)

private def shiftRawGate (offset : Nat)
    (gate : LockedNAND.RawGate) : LockedNAND.RawGate :=
  { left := shiftRawSource offset gate.left
    right := shiftRawSource offset gate.right }

private def shiftRawGates (offset : Nat)
    (gates : List LockedNAND.RawGate) :
    List LockedNAND.RawGate :=
  gates.map (shiftRawGate offset)

private theorem shiftRawSource_zero
    (source : LockedNAND.RawSource) :
    shiftRawSource 0 source = source := by
  cases source <;> simp [shiftRawSource]

private theorem shiftRawSource_add
    (first second : Nat) (source : LockedNAND.RawSource) :
    shiftRawSource first (shiftRawSource second source) =
      shiftRawSource (first + second) source := by
  cases source <;> simp [shiftRawSource, Nat.add_assoc]

private theorem shiftRawGate_add
    (first second : Nat) (gate : LockedNAND.RawGate) :
    shiftRawGate first (shiftRawGate second gate) =
      shiftRawGate (first + second) gate := by
  cases gate
  simp [shiftRawGate, shiftRawSource_add]

private theorem shiftRawGates_add
    (first second : Nat) (gates : List LockedNAND.RawGate) :
    shiftRawGates first (shiftRawGates second gates) =
      shiftRawGates (first + second) gates := by
  simp [shiftRawGates, List.map_map, shiftRawGate_add]

private theorem shiftRawGates_append
    (offset : Nat) (first second : List LockedNAND.RawGate) :
    shiftRawGates offset (first ++ second) =
      shiftRawGates offset first ++ shiftRawGates offset second := by
  simp [shiftRawGates]

private theorem shiftRawGates_singleton
    (offset : Nat) (gate : LockedNAND.RawGate) :
    shiftRawGates offset [gate] = [shiftRawGate offset gate] := rfl

private theorem shiftRawGate_zero
    (gate : LockedNAND.RawGate) :
    shiftRawGate 0 gate = gate := by
  cases gate
  simp [shiftRawGate, shiftRawSource_zero]

private theorem shiftRawGates_zero
    (gates : List LockedNAND.RawGate) :
    shiftRawGates 0 gates = gates := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      change shiftRawGate 0 gate :: shiftRawGates 0 rest =
        gate :: rest
      rw [shiftRawGate_zero, ih]

private theorem shiftRawGates_length
    (offset : Nat) (gates : List LockedNAND.RawGate) :
    (shiftRawGates offset gates).length = gates.length := by
  simp [shiftRawGates]

private theorem rawProgramGates_length_plan
    {inputs gates : Nat} (program : Program inputs gates) :
    (LockedNAND.rawProgramGates program).length = gates := by
  induction program with
  | empty => rfl
  | @snoc gates initial gate ih =>
      simp [LockedNAND.rawProgramGates, ih]

private theorem rawSource_ofSource_weakenGates
    {inputs gates : Nat} (source : Source inputs gates)
    (extra : Nat) :
    LockedNAND.RawSource.ofSource (source.weakenGates extra) =
      LockedNAND.RawSource.ofSource source := by
  cases source <;> rfl

private theorem rawSource_ofSource_substitute_identity
    {inputs prefixGates suffixGates : Nat}
    (source : Source inputs suffixGates) :
    LockedNAND.RawSource.ofSource
        (source.substituteInputs
          (identityBinding (inputs := inputs)
            (gates := prefixGates))) =
      shiftRawSource prefixGates
        (LockedNAND.RawSource.ofSource source) := by
  cases source with
  | input index =>
      change LockedNAND.RawSource.input index.val =
        LockedNAND.RawSource.input index.val
      rfl
  | constant value =>
      rfl
  | gate index =>
      rfl

private theorem rawGate_ofGate_substitute_identity
    {inputs prefixGates suffixGates : Nat}
    (gate : Gate inputs suffixGates) :
    LockedNAND.RawGate.ofGate
        (gate.substituteInputs
          (identityBinding (inputs := inputs)
            (gates := prefixGates))) =
      shiftRawGate prefixGates
        (LockedNAND.RawGate.ofGate gate) := by
  cases gate with
  | mk left right =>
      simp [Gate.substituteInputs, LockedNAND.RawGate.ofGate,
        shiftRawGate, rawSource_ofSource_substitute_identity]

private theorem rawProgramGates_appendSubstituted_identity
    {inputs prefixGates suffixGates : Nat}
    (initialProgram : Program inputs prefixGates)
    (suffix : Program inputs suffixGates) :
    LockedNAND.rawProgramGates
        (initialProgram.appendSubstituted
          (identityBinding (inputs := inputs)
            (gates := prefixGates)) suffix) =
      LockedNAND.rawProgramGates initialProgram ++
        shiftRawGates prefixGates
          (LockedNAND.rawProgramGates suffix) := by
  induction suffix with
  | empty =>
      simp [Program.appendSubstituted, LockedNAND.rawProgramGates,
        shiftRawGates]
  | @snoc gates initial gate ih =>
      simp [Program.appendSubstituted,
        LockedNAND.rawProgramGates, ih,
        shiftRawGates,
        rawGate_ofGate_substitute_identity, List.append_assoc]

private def appendCompiledState {inputs : Nat}
    (compiled : CompiledExpression inputs)
    (state : CompilationState) : CompilationState :=
  { gates :=
      state.gates ++
        shiftRawGates state.gates.length
          (LockedNAND.rawProgramGates compiled.program)
    stack :=
      shiftRawSource state.gates.length
        (LockedNAND.RawSource.ofSource compiled.output) ::
          state.stack }

private theorem run_negate_appendCompiledState
    {inputs : Nat} (compiled : CompiledExpression inputs)
    (state : CompilationState) :
    runCompilationPlan [.negate]
        (appendCompiledState compiled state) =
      some (appendCompiledState compiled.negate state) := by
  simp [runCompilationPlan, CompilationAction.step,
    CompilationState.emitNand, appendCompiledState,
    CompiledExpression.negate, LockedNAND.rawProgramGates,
    LockedNAND.RawGate.ofGate,
    LockedNAND.RawSource.ofSource,
    shiftRawGates, shiftRawSource,
    rawProgramGates_length_plan]
  cases compiled.output <;> rfl

private theorem pairCompilations_rawProgram
    {inputs : Nat} (left right : CompiledExpression inputs) :
    LockedNAND.rawProgramGates
        (pairCompilations left right).program =
      LockedNAND.rawProgramGates left.program ++
        shiftRawGates left.gateCount
          (LockedNAND.rawProgramGates right.program) := by
  exact rawProgramGates_appendSubstituted_identity
    left.program right.program

private theorem pairCompilations_gateCount
    {inputs : Nat} (left right : CompiledExpression inputs) :
    (pairCompilations left right).gateCount =
      left.gateCount + right.gateCount := rfl

private theorem pairCompilations_rawLeft
    {inputs : Nat} (left right : CompiledExpression inputs) :
    LockedNAND.RawSource.ofSource
        (pairCompilations left right).left =
      LockedNAND.RawSource.ofSource left.output := by
  simp [pairCompilations, rawSource_ofSource_weakenGates]

private theorem pairCompilations_rawRight
    {inputs : Nat} (left right : CompiledExpression inputs) :
    LockedNAND.RawSource.ofSource
        (pairCompilations left right).right =
      shiftRawSource left.gateCount
        (LockedNAND.RawSource.ofSource right.output) := by
  exact rawSource_ofSource_substitute_identity right.output

private theorem run_nand_appendCompiledStates
    {inputs : Nat} (left right : CompiledExpression inputs)
    (state : CompilationState) :
    runCompilationPlan [.nand]
        (appendCompiledState right
          (appendCompiledState left state)) =
      some
        (appendCompiledState
          (pairCompilations left right).nand state) := by
  simp only [runCompilationPlan, CompilationAction.step,
    CompilationState.emitNand, appendCompiledState,
    PairedCompilation.nand, LockedNAND.rawProgramGates,
    LockedNAND.RawGate.ofGate]
  rw [pairCompilations_rawProgram,
    pairCompilations_rawLeft, pairCompilations_rawRight]
  simp [shiftRawGates_append, shiftRawGates_add,
    shiftRawSource_add, shiftRawGates_length,
    rawProgramGates_length_plan,
    LockedNAND.RawSource.ofSource,
    shiftRawGates_singleton, shiftRawGate,
    pairCompilations_gateCount]
  rfl

private theorem run_nand_negate_appendCompiledStates
    {inputs : Nat} (left right : CompiledExpression inputs)
    (state : CompilationState) :
    runCompilationPlan [.nand, .negate]
        (appendCompiledState right
          (appendCompiledState left state)) =
      some
        (appendCompiledState
          (pairCompilations left right).nand.negate state) := by
  calc
    _ =
        match
          runCompilationPlan [.nand]
            (appendCompiledState right
              (appendCompiledState left state)) with
        | none => none
        | some middle =>
            runCompilationPlan [.negate] middle := by
              exact runCompilationPlan_append
                [.nand] [.negate]
                (appendCompiledState right
                  (appendCompiledState left state))
    _ = _ := by
      simpa only [run_nand_appendCompiledStates] using
        run_negate_appendCompiledState
          (pairCompilations left right).nand state

private theorem run_negate_nand_appendCompiledStates
    {inputs : Nat} (left right : CompiledExpression inputs)
    (state : CompilationState) :
    runCompilationPlan [.negate, .nand]
        (appendCompiledState right
          (appendCompiledState left state)) =
      some
        (appendCompiledState
          (pairCompilations left right.negate).nand state) := by
  calc
    _ =
        match
          runCompilationPlan [.negate]
            (appendCompiledState right
              (appendCompiledState left state)) with
        | none => none
        | some middle =>
            runCompilationPlan [.nand] middle := by
              exact runCompilationPlan_append
                [.negate] [.nand]
                (appendCompiledState right
                  (appendCompiledState left state))
    _ = _ := by
      simpa only [run_negate_appendCompiledState] using
        run_nand_appendCompiledStates left right.negate state

private theorem run_expressionPlan
    {inputs : Nat} (expression : BoolExpression inputs)
    (state : CompilationState) :
    runCompilationPlan (expressionPlan expression) state =
      some
        (appendCompiledState
          (compileExpression expression) state) := by
  induction expression generalizing state with
  | input index =>
      simp [expressionPlan, runCompilationPlan,
        CompilationAction.step, appendCompiledState,
        compileExpression, shiftRawGates, shiftRawSource,
        LockedNAND.rawProgramGates,
        LockedNAND.RawSource.ofSource]
  | constant value =>
      simp [expressionPlan, runCompilationPlan,
        CompilationAction.step, appendCompiledState,
        compileExpression, shiftRawGates, shiftRawSource,
        LockedNAND.rawProgramGates,
        LockedNAND.RawSource.ofSource]
  | neg body ih =>
      rw [expressionPlan, runCompilationPlan_append, ih]
      exact run_negate_appendCompiledState
        (compileExpression body) state
  | conj left right leftIH rightIH =>
      simp only [expressionPlan, List.append_assoc,
        runCompilationPlan_append, leftIH, rightIH]
      simpa [compileExpression] using
        run_nand_negate_appendCompiledStates
          (compileExpression left) (compileExpression right) state
  | disj left right leftIH rightIH =>
      simp only [expressionPlan, List.append_assoc,
        runCompilationPlan_append, leftIH,
        run_negate_appendCompiledState, rightIH]
      simpa [compileExpression] using
        run_negate_nand_appendCompiledStates
          (compileExpression left).negate
          (compileExpression right) state

private theorem finalize_appendCompiledState
    {inputs : Nat} (compiled : CompiledExpression inputs) :
    finalizeCompilation inputs
        (appendCompiledState compiled
          { gates := [], stack := [] }) =
      some
        (LockedNAND.RawCircuit.ofCircuit compiled.toCircuit) := by
  cases compiled with
  | mk gateCount program output =>
      cases output with
      | input index =>
          simp [appendCompiledState, finalizeCompilation,
            CompiledExpression.toCircuit,
            shiftRawGates_zero, shiftRawSource,
            LockedNAND.RawCircuit.ofCircuit,
            LockedNAND.rawProgramGates,
            LockedNAND.RawSource.ofSource,
            LockedNAND.RawGate.ofGate,
            rawProgramGates_length_plan]
      | gate index =>
          simp [appendCompiledState, finalizeCompilation,
            CompiledExpression.toCircuit,
            shiftRawGates_zero, shiftRawSource_zero,
            LockedNAND.RawCircuit.ofCircuit,
            LockedNAND.RawSource.ofSource]
      | constant value =>
          cases value <;>
            simp [appendCompiledState, finalizeCompilation,
              CompiledExpression.toCircuit,
              shiftRawGates_zero, shiftRawSource,
              LockedNAND.RawCircuit.ofCircuit,
              LockedNAND.rawProgramGates,
              LockedNAND.RawSource.ofSource,
              LockedNAND.RawGate.ofGate,
              rawProgramGates_length_plan]

/-- The pure postfix plan produces exactly the existing intrinsically typed
compiler result, including all recursive gate indices and finalization
cases. -/
theorem executeFormulaPlan_exact (formula : CNFFormula) :
    executeFormulaPlan formula = some (compileFormula formula) := by
  unfold executeFormulaPlan formulaPlan
  rw [clausesPlan_eq_expressionPlan]
  change
    (match
        runCompilationPlan
          (expressionPlan (formulaExpression formula))
          { gates := [], stack := [] } with
      | none => none
      | some state =>
          finalizeCompilation formula.variableCount state) =
      some (compileFormula formula)
  rw [run_expressionPlan]
  simpa [compileFormula, compiledFormulaCircuit] using
    finalize_appendCompiledState
      (compileExpression (formulaExpression formula))

/-- Exact byte-level bridge required by the concrete reduction. -/
theorem emitFormulaPlan_exact (formula : CNFFormula) :
    emitFormulaPlan formula =
      LockedNAND.encodeCircuit (compileFormula formula) := by
  rw [emitFormulaPlan, executeFormulaPlan_exact]

/-- The empty conjunction is true and is normalized to one `false NAND
false` gate. -/
@[simp] theorem executeFormulaPlan_empty_formula (inputs : Nat) :
    executeFormulaPlan
        { variableCount := inputs, clauses := [] } =
      some
        { inputCount := inputs
          gates :=
            [{ left := .constant false
               right := .constant false }]
          output := .gate 0 } := rfl

/-- A formula containing one empty clause is false.  Its exact two gates
preserve the compiler's NAND-then-self-NAND ordering. -/
@[simp] theorem executeFormulaPlan_single_empty_clause
    (inputs : Nat) :
    executeFormulaPlan
        { variableCount := inputs, clauses := [[]] } =
      some
        { inputCount := inputs
          gates :=
            [ { left := .constant false
                right := .constant true }
            , { left := .gate 0
                right := .gate 0 } ]
          output := .gate 1 } := rfl

theorem compileFormula_inputCount (formula : CNFFormula) :
    (compileFormula formula).inputCount = formula.variableCount := rfl

theorem compileFormula_output_is_gate (formula : CNFFormula) :
    ∃ index, (compileFormula formula).output = .gate index := by
  exact ⟨(compiledFormulaCircuit formula).outputGate.val, rfl⟩

private theorem rawProgramGates_length {inputs gates : Nat}
    (program : Program inputs gates) :
    (LockedNAND.rawProgramGates program).length = gates := by
  induction program with
  | empty => rfl
  | @snoc gates initial gate ih =>
      simp [LockedNAND.rawProgramGates, ih]

private theorem rawSource_wellFormed_ofSource
    {inputs gates : Nat} (source : Source inputs gates) :
    (LockedNAND.RawSource.ofSource source).wellFormed inputs gates = true := by
  cases source with
  | input index =>
      simp [LockedNAND.RawSource.ofSource,
        LockedNAND.RawSource.wellFormed, index.isLt]
  | constant value =>
      rfl
  | gate index =>
      simp [LockedNAND.RawSource.ofSource,
        LockedNAND.RawSource.wellFormed, index.isLt]

private theorem rawGate_wellFormed_ofGate
    {inputs gates : Nat} (gate : Gate inputs gates) :
    (LockedNAND.RawGate.ofGate gate).wellFormed inputs gates = true := by
  cases gate with
  | mk left right =>
      simp [LockedNAND.RawGate.ofGate, LockedNAND.RawGate.wellFormed,
        rawSource_wellFormed_ofSource]

private theorem rawGatesWellFormed_append
    (inputs prior : Nat) (first second : List LockedNAND.RawGate) :
    LockedNAND.rawGatesWellFormed inputs prior (first ++ second) =
      (LockedNAND.rawGatesWellFormed inputs prior first &&
        LockedNAND.rawGatesWellFormed inputs (prior + first.length) second) := by
  induction first generalizing prior with
  | nil =>
      simp [LockedNAND.rawGatesWellFormed]
  | cons gate rest ih =>
      simp only [List.cons_append, LockedNAND.rawGatesWellFormed,
        List.length_cons]
      rw [ih]
      have shifted :
          prior + 1 + rest.length = prior + Nat.succ rest.length := by
        omega
      rw [shifted]
      cases gate.wellFormed inputs prior <;>
        cases LockedNAND.rawGatesWellFormed inputs (prior + 1) rest <;>
        rfl

private theorem rawGatesWellFormed_rawProgramGates
    {inputs gates : Nat} (program : Program inputs gates) :
    LockedNAND.rawGatesWellFormed inputs 0
        (LockedNAND.rawProgramGates program) = true := by
  induction program with
  | empty => rfl
  | @snoc gates initial gate ih =>
      rw [LockedNAND.rawProgramGates, rawGatesWellFormed_append]
      rw [ih, rawProgramGates_length]
      simp [LockedNAND.rawGatesWellFormed,
        rawGate_wellFormed_ofGate]

private theorem rawCircuit_ofCircuit_wellFormed
    {inputs : Nat} (circuit : Circuit inputs) :
    (LockedNAND.RawCircuit.ofCircuit circuit).wellFormed = true := by
  cases circuit with
  | mk gates program outputGate =>
      simp [LockedNAND.RawCircuit.ofCircuit,
        LockedNAND.RawCircuit.wellFormed,
        rawGatesWellFormed_rawProgramGates,
        rawProgramGates_length,
        LockedNAND.RawSource.wellFormed,
        outputGate.isLt]

theorem compileFormula_wellFormed (formula : CNFFormula) :
    (compileFormula formula).wellFormed = true :=
  rawCircuit_ofCircuit_wellFormed (compiledFormulaCircuit formula)

theorem decodeValidCircuit_encode_compileFormula (formula : CNFFormula) :
    LockedNAND.decodeValidCircuit
        (LockedNAND.encodeCircuit (compileFormula formula)) =
      some (compileFormula formula) := by
  exact LockedNAND.decodeValidCircuit_encodeCircuit
    (compileFormula formula) (compileFormula_wellFormed formula)

theorem compiledFormulaCircuit_eval_eq_true_iff
    (formula : CNFFormula)
    (input : Valuation formula.variableCount) :
    (compiledFormulaCircuit formula).program.eval input
        (compiledFormulaCircuit formula).outputGate = true ↔
      formula.Satisfied (List.ofFn input) := by
  rw [compiledFormulaCircuit,
    CompiledExpression.toCircuit_value,
    compileExpression_value,
    formulaExpression_eval,
    checkCNF_eq_true_iff]

theorem compiledFormulaCircuit_satisfiable_iff (formula : CNFFormula) :
    (compiledFormulaCircuit formula).Satisfiable ↔
      formula.Satisfiable := by
  constructor
  · rintro ⟨input, outputTrue⟩
    exact ⟨List.ofFn input,
      (compiledFormulaCircuit_eval_eq_true_iff formula input).mp outputTrue⟩
  · rintro ⟨assignment, satisfied⟩
    let input : Valuation formula.variableCount :=
      fun index =>
        assignment.get
          ⟨index.val, by
            rw [satisfied.left]
            exact index.isLt⟩
    have assignmentCanonical :
        List.ofFn input = assignment := by
      exact list_ofFn_bounded_get_eq assignment formula.variableCount
        satisfied.left
    refine ⟨input,
      (compiledFormulaCircuit_eval_eq_true_iff formula input).mpr ?_⟩
    rw [assignmentCanonical]
    exact satisfied

theorem compileFormula_satisfiable_iff (formula : CNFFormula) :
    (compileFormula formula).Satisfiable ↔ formula.Satisfiable := by
  unfold compileFormula LockedNAND.RawCircuit.Satisfiable
  rw [LockedNAND.RawCircuit.elaborate_ofCircuit]
  exact compiledFormulaCircuit_satisfiable_iff formula

theorem formula_satisfiable_iff_encoded_compileFormula
    (formula : CNFFormula) :
    formula.Satisfiable ↔
      LockedNAND.EncodedNANDSAT
        (LockedNAND.encodeCircuit (compileFormula formula)) := by
  unfold compileFormula
  rw [LockedNAND.EncodedNANDSAT,
    LockedNAND.decodeElaboratedCircuit_encodeCircuit_ofCircuit]
  exact (compiledFormulaCircuit_satisfiable_iff formula).symm

private theorem compileExpression_formula_output
    (formula : CNFFormula) :
    match formula.clauses with
    | [] =>
        (compileExpression (formulaExpression formula)).output =
          .constant true
    | _ :: _ =>
        ∃ index,
          (compileExpression (formulaExpression formula)).output = .gate index := by
  cases formula with
  | mk inputs clauses =>
      cases clauses with
      | nil => rfl
      | cons clause rest =>
          simp [formulaExpression, clausesExpression,
            compileExpression, CompiledExpression.negate,
            PairedCompilation.nand]

private theorem CompiledExpression.toCircuit_negate_gateCount
    {inputs : Nat} (compiled : CompiledExpression inputs) :
    compiled.negate.toCircuit.gateCount = compiled.gateCount + 1 := by
  rfl

private theorem compiledFormulaCircuit_gateCount (formula : CNFFormula) :
    (compiledFormulaCircuit formula).gateCount =
      validNegativeLiteralCount formula +
        3 * literalCount formula +
        2 * formula.clauses.length +
        (if formula.clauses.isEmpty then 1 else 0) := by
  have expressionCost :=
    clausesExpression_gateCost formula.variableCount formula.clauses
  have compiledCost :=
    compileExpression_gateCount (formulaExpression formula)
  cases formula with
  | mk inputs clauses =>
      cases clauses with
      | nil =>
          simp [compiledFormulaCircuit, formulaExpression,
            clausesExpression, compileExpression,
            CompiledExpression.toCircuit,
            validNegativeLiteralCount, literalCount]
      | cons clause rest =>
          change
            ((pairCompilations
                (compileExpression (clauseExpression inputs clause))
                (compileExpression
                  (clausesExpression inputs rest))).nand.negate.toCircuit).gateCount =
              validNegativeLiteralCount
                  { variableCount := inputs, clauses := clause :: rest } +
                3 * literalCount
                  { variableCount := inputs, clauses := clause :: rest } +
                2 * (clause :: rest).length +
                (if (clause :: rest).isEmpty then 1 else 0)
          rw [CompiledExpression.toCircuit_negate_gateCount]
          change
            (compileExpression
                ((clauseExpression inputs clause).conj
                  (clausesExpression inputs rest))).gateCount =
              validNegativeLiteralCount
                  { variableCount := inputs, clauses := clause :: rest } +
                3 * literalCount
                  { variableCount := inputs, clauses := clause :: rest } +
                2 * (clause :: rest).length +
                (if (clause :: rest).isEmpty then 1 else 0)
          rw [compileExpression_gateCount]
          change
            (clausesExpression inputs (clause :: rest)).gateCost =
              validNegativeLiteralCount
                  { variableCount := inputs, clauses := clause :: rest } +
                3 * literalCount
                  { variableCount := inputs, clauses := clause :: rest } +
                2 * (clause :: rest).length +
                (if (clause :: rest).isEmpty then 1 else 0)
          rw [clausesExpression_gateCost]
          simp [validNegativeLiteralCount, literalCount]

theorem compileFormula_gateCount_exact (formula : CNFFormula) :
    (compileFormula formula).gates.length =
      validNegativeLiteralCount formula +
        3 * literalCount formula +
        2 * formula.clauses.length +
        (if formula.clauses.isEmpty then 1 else 0) := by
  unfold compileFormula LockedNAND.RawCircuit.ofCircuit
  rw [rawProgramGates_length, compiledFormulaCircuit_gateCount]

/-- The action executor succeeds with the exact compiler circuit and hence
inherits its closed gate-count formula. -/
theorem executeFormulaPlan_gateCount_exact (formula : CNFFormula) :
    ∃ circuit,
      executeFormulaPlan formula = some circuit ∧
        circuit.gates.length =
          validNegativeLiteralCount formula +
            3 * literalCount formula +
            2 * formula.clauses.length +
            (if formula.clauses.isEmpty then 1 else 0) := by
  exact
    ⟨compileFormula formula, executeFormulaPlan_exact formula,
      compileFormula_gateCount_exact formula⟩

theorem compileFormula_gateCount_le (formula : CNFFormula) :
    (compileFormula formula).gates.length ≤
      4 * literalCount formula + 2 * formula.clauses.length + 1 := by
  rw [compileFormula_gateCount_exact]
  unfold validNegativeLiteralCount literalCount
  have filtered :
      (formula.clauses.map fun clause =>
        (clause.filter fun literal =>
          !literal.positive &&
            literal.variableIndex < formula.variableCount).length).sum ≤
        (formula.clauses.map List.length).sum := by
    induction formula.clauses with
    | nil => exact Nat.le_refl 0
    | cons clause rest ih =>
        simp only [List.map_cons, List.sum_cons]
        exact Nat.add_le_add (List.length_filter_le _ _) ih
  have finalGate :
      (if formula.clauses.isEmpty then 1 else 0) ≤ 1 := by
    split <;> omega
  omega

/-! ## Exact-byte polynomial size accounting -/

private theorem encodeNatTokens_length (value : Nat) :
    (LockedNAND.encodeNatTokens value).length = value + 1 := by
  induction value with
  | zero => rfl
  | succ value ih =>
      simp [LockedNAND.encodeNatTokens, ih]

private theorem encodeGateListTokens_append
    (first second : List LockedNAND.RawGate) :
    LockedNAND.encodeGateListTokens (first ++ second) =
      LockedNAND.encodeGateListTokens first ++
        LockedNAND.encodeGateListTokens second := by
  induction first with
  | nil => rfl
  | cons gate rest ih =>
      simp [LockedNAND.encodeGateListTokens, ih, List.append_assoc]

private theorem encodeSourceTokens_ofSource_length_le
    {inputs gates : Nat} (source : Source inputs gates) :
    (LockedNAND.encodeSourceTokens
        (LockedNAND.RawSource.ofSource source)).length ≤
      inputs + gates + 1 := by
  cases source with
  | input index =>
      simp [LockedNAND.RawSource.ofSource,
        LockedNAND.encodeSourceTokens, encodeNatTokens_length]
      omega
  | constant value =>
      cases value <;>
        simp [LockedNAND.RawSource.ofSource,
          LockedNAND.encodeSourceTokens]
  | gate index =>
      simp [LockedNAND.RawSource.ofSource,
        LockedNAND.encodeSourceTokens, encodeNatTokens_length]
      omega

private theorem encodeGateTokens_ofGate_length_le
    {inputs gates : Nat} (gate : Gate inputs gates) :
    (LockedNAND.encodeGateTokens
        (LockedNAND.RawGate.ofGate gate)).length ≤
      2 * (inputs + gates + 1) + 1 := by
  cases gate with
  | mk left right =>
      simp only [LockedNAND.encodeGateTokens,
        LockedNAND.RawGate.ofGate, List.length_append,
        List.length_cons, List.length_nil]
      have leftBound := encodeSourceTokens_ofSource_length_le left
      have rightBound := encodeSourceTokens_ofSource_length_le right
      omega

private theorem encodeGateListTokens_rawProgramGates_length_le
    {inputs gates : Nat} (program : Program inputs gates) :
    (LockedNAND.encodeGateListTokens
        (LockedNAND.rawProgramGates program)).length ≤
      gates * (2 * (inputs + gates + 1) + 1) := by
  induction program with
  | empty =>
      simp [LockedNAND.rawProgramGates,
        LockedNAND.encodeGateListTokens]
  | @snoc gates earlier gate ih =>
      rw [LockedNAND.rawProgramGates,
        encodeGateListTokens_append]
      simp only [List.length_append,
        LockedNAND.encodeGateListTokens, List.append_nil]
      let factor := 2 * (inputs + (gates + 1) + 1) + 1
      have earlierFactor :
          2 * (inputs + gates + 1) + 1 ≤ factor := by
        dsimp [factor]
        omega
      have earlierBound :
          (LockedNAND.encodeGateListTokens
              (LockedNAND.rawProgramGates earlier)).length ≤
            gates * factor :=
        Nat.le_trans ih (Nat.mul_le_mul_left gates earlierFactor)
      have gateBound :
          (LockedNAND.encodeGateTokens
              (LockedNAND.RawGate.ofGate gate)).length ≤ factor := by
        exact Nat.le_trans
          (encodeGateTokens_ofGate_length_le gate) earlierFactor
      have combined := Nat.add_le_add earlierBound gateBound
      change
        (LockedNAND.encodeGateListTokens
              (LockedNAND.rawProgramGates earlier)).length +
            (LockedNAND.encodeGateTokens
              (LockedNAND.RawGate.ofGate gate)).length ≤
          (gates + 1) * factor
      rw [Nat.add_mul]
      simpa using combined

private theorem encodeCircuit_ofCircuit_length_le
    {inputs : Nat} (circuit : Circuit inputs) :
    (LockedNAND.encodeCircuit
        (LockedNAND.RawCircuit.ofCircuit circuit)).length ≤
      4 *
        (inputs + circuit.gateCount + 6 +
          circuit.gateCount *
            (2 * (inputs + circuit.gateCount + 1) + 1) +
          (inputs + circuit.gateCount + 1)) := by
  cases circuit with
  | mk gates program outputGate =>
      rw [LockedNAND.encodeCircuit, LockedNAND.encodeTokens_length]
      have gateBound :=
        encodeGateListTokens_rawProgramGates_length_le program
      have outputBound :
          (LockedNAND.encodeSourceTokens
              (.gate outputGate.val)).length ≤
            inputs + gates + 1 := by
        simpa [LockedNAND.RawSource.ofSource] using
          (encodeSourceTokens_ofSource_length_le
            (Source.gate outputGate))
      apply Nat.mul_le_mul_left 4
      simp only [LockedNAND.RawCircuit.ofCircuit,
        LockedNAND.encodeCircuitTokens, List.length_cons,
        List.length_append, List.length_nil,
        encodeNatTokens_length, rawProgramGates_length]
      omega

/-- A monotone quadratic bound for the exact strict-v0 NAND bytes.  With
`s = n + 1`, its literal value is
`4 * ((5*s) * (15*s) + 19*s)`. -/
def cnfToNANDOutputSizePolynomial : NatPolynomial :=
  let shifted : NatPolynomial :=
    .add .variable (.constant 1)
  .mul (.constant 4)
    (.add
      (.mul
        (.mul (.constant 5) shifted)
        (.mul (.constant 15) shifted))
      (.mul (.constant 19) shifted))

theorem cnfToNANDOutputSizePolynomial_eval (bitLength : Nat) :
    cnfToNANDOutputSizePolynomial.eval bitLength =
      4 *
        ((5 * (bitLength + 1)) * (15 * (bitLength + 1)) +
          19 * (bitLength + 1)) := by
  rfl

private theorem compiledFormulaCircuit_gateCount_le_input
    (bits : BitString) (formula : CNFFormula)
    (decoded : decodeEncodedCNF bits = some formula) :
    (compiledFormulaCircuit formula).gateCount ≤
      5 * (bits.length + 1) := by
  have structural :=
    decodedFormula_structural_size_le bits formula decoded
  have rawBound := compileFormula_gateCount_le formula
  have lengthEqual :
      (compileFormula formula).gates.length =
        (compiledFormulaCircuit formula).gateCount := by
    unfold compileFormula LockedNAND.RawCircuit.ofCircuit
    exact rawProgramGates_length (compiledFormulaCircuit formula).program
  rw [lengthEqual] at rawBound
  omega

/-- Total strict source transformation.  Malformed CNF bytes fail closed to
the empty word. -/
def compileEncodedCNFToNAND (bits : BitString) : BitString :=
  match decodeEncodedCNF bits with
  | none => []
  | some formula =>
      LockedNAND.encodeCircuit (compileFormula formula)

theorem compileEncodedCNFToNAND_of_decoded
    (bits : BitString) (formula : CNFFormula)
    (decoded : decodeEncodedCNF bits = some formula) :
    compileEncodedCNFToNAND bits =
      LockedNAND.encodeCircuit (compileFormula formula) := by
  simp [compileEncodedCNFToNAND, decoded]

/-- On a successfully decoded source word, the pure action emitter is
byte-for-byte the total concrete CNF-to-NAND transformation. -/
theorem emitFormulaPlan_eq_compileEncodedCNFToNAND_of_decoded
    (bits : BitString) (formula : CNFFormula)
    (decoded : decodeEncodedCNF bits = some formula) :
    emitFormulaPlan formula =
      compileEncodedCNFToNAND bits := by
  rw [emitFormulaPlan_exact,
    compileEncodedCNFToNAND_of_decoded bits formula decoded]

theorem compileEncodedCNFToNAND_of_malformed
    (bits : BitString)
    (malformed : decodeEncodedCNF bits = none) :
    compileEncodedCNFToNAND bits = [] := by
  simp [compileEncodedCNFToNAND, malformed]

theorem compileEncodedCNFToNAND_size_le (bits : BitString) :
    BitString.size (compileEncodedCNFToNAND bits) ≤
      cnfToNANDOutputSizePolynomial.eval (BitString.size bits) := by
  unfold BitString.size
  cases decoded : decodeEncodedCNF bits with
  | none =>
      simp [compileEncodedCNFToNAND, decoded]
  | some formula =>
      rw [compileEncodedCNFToNAND_of_decoded bits formula decoded]
      let shifted := bits.length + 1
      let gates := (compiledFormulaCircuit formula).gateCount
      have shiftedPositive : 1 ≤ shifted := by
        dsimp [shifted]
        omega
      have inputsBound : formula.variableCount ≤ shifted := by
        have structural :=
          decodedFormula_structural_size_le bits formula decoded
        dsimp [shifted]
        omega
      have gatesBound : gates ≤ 5 * shifted := by
        dsimp [gates]
        exact compiledFormulaCircuit_gateCount_le_input
          bits formula decoded
      have sourceBound :
          formula.variableCount + gates + 1 ≤ 7 * shifted := by
        omega
      have gateFactorBound :
          2 * (formula.variableCount + gates + 1) + 1 ≤
            15 * shifted := by
        omega
      have productBound :
          gates *
              (2 * (formula.variableCount + gates + 1) + 1) ≤
            (5 * shifted) * (15 * shifted) :=
        Nat.mul_le_mul gatesBound gateFactorBound
      have headerBound :
          formula.variableCount + gates + 6 +
              (formula.variableCount + gates + 1) ≤
            19 * shifted := by
        omega
      have totalBound :
          formula.variableCount + gates + 6 +
                gates *
                  (2 * (formula.variableCount + gates + 1) + 1) +
              (formula.variableCount + gates + 1) ≤
            (5 * shifted) * (15 * shifted) +
              19 * shifted := by
        omega
      have serialized :=
        encodeCircuit_ofCircuit_length_le
          (compiledFormulaCircuit formula)
      rw [cnfToNANDOutputSizePolynomial_eval]
      exact Nat.le_trans serialized
        (Nat.mul_le_mul_left 4 totalBound)

theorem empty_not_encodedNANDSAT :
    ¬ LockedNAND.EncodedNANDSAT [] := by
  simp [LockedNAND.EncodedNANDSAT,
    LockedNAND.decodeElaboratedCircuit,
    LockedNAND.decodeCircuit,
    LockedNAND.decodeTokens,
    LockedNAND.decodeCircuitTokens]

theorem compileEncodedCNFToNAND_correct (bits : BitString) :
    CNFSAT bits ↔
      LockedNAND.EncodedNANDSAT (compileEncodedCNFToNAND bits) := by
  cases decoded : decodeEncodedCNF bits with
  | none =>
      simp [CNFSAT, decoded,
        compileEncodedCNFToNAND_of_malformed bits decoded,
        empty_not_encodedNANDSAT]
  | some formula =>
      rw [compileEncodedCNFToNAND_of_decoded bits formula decoded]
      constructor
      · rintro ⟨decodedFormula, decodedFormulaEq, satisfiable⟩
        have equal : decodedFormula = formula := by
          exact Option.some.inj (decodedFormulaEq.symm.trans decoded)
        cases equal
        exact
          (formula_satisfiable_iff_encoded_compileFormula formula).mp
            satisfiable
      · intro encodedSatisfiable
        exact ⟨formula, decoded,
          (formula_satisfiable_iff_encoded_compileFormula formula).mpr
            encodedSatisfiable⟩

/-- Pure semantic composition with the already-proved locked-NAND instance
builder.  No finite-machine runtime claim is made here. -/
def buildLockedNANDFromCNF (bits : BitString) : BitString :=
  LockedNAND.buildLockedNANDInstance (compileEncodedCNFToNAND bits)

theorem buildLockedNANDFromCNF_correct (bits : BitString) :
    CNFSAT bits ↔
      LockedNAND.EncodedLockedNANDThreshold
        (buildLockedNANDFromCNF bits) := by
  rw [compileEncodedCNFToNAND_correct]
  exact LockedNAND.buildLockedNANDInstance_correct
    (compileEncodedCNFToNAND bits)

end CNFToNAND
end Concrete
end PNP

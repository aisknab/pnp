/-
Copyright (c) 2026 PNP Labs.

An executable, canonical encoding of finite CNF formulae and assignments.

The four two-bit tokens deliberately use the whole two-bit alphabet:
`F = 00`, `T = 11`, `Sep = 01`, and `Finish = 10`.  Formula encodings carry
one additional zero pad bit, so formula strings are odd and assignment
certificates are even.  The checker below parses both strings independently;
it does not rely on a Lean function hidden inside a machine program.
-/

import PNP.Concrete.Complexity

namespace PNP.Concrete

/-- The complete two-bit token alphabet used by the concrete CNF codec. -/
inductive CNFToken where
  | f
  | t
  | sep
  | finish
deriving BEq, DecidableEq, Repr

namespace CNFToken

/-- The exact two-bit representation of one token. -/
def bits : CNFToken → BitString
  | .f => [false, false]
  | .t => [true, true]
  | .sep => [false, true]
  | .finish => [true, false]

/-- Decode the complete two-bit alphabet. -/
def ofBits : Bool → Bool → CNFToken
  | false, false => .f
  | true, true => .t
  | false, true => .sep
  | true, false => .finish

theorem ofBits_bits (token : CNFToken) :
    ofBits token.bits.head! token.bits.tail.head! = token := by
  cases token <;> rfl

end CNFToken

/-- Flatten a token list into its exact two-bit representation. -/
def encodeTokenPairs : List CNFToken → BitString
  | [] => []
  | token :: rest => token.bits ++ encodeTokenPairs rest

/-- Decode a string made from complete two-bit tokens; an odd tail is
rejected. -/
def decodeTokenPairs : BitString → Option (List CNFToken)
  | [] => some []
  | first :: second :: rest =>
      match decodeTokenPairs rest with
      | none => none
      | some tokens => some (CNFToken.ofBits first second :: tokens)
  | [_] => none

theorem decodeTokenPairs_cons_bits (token : CNFToken) (tokens : List CNFToken) :
    decodeTokenPairs (token.bits ++ encodeTokenPairs tokens) =
      match decodeTokenPairs (encodeTokenPairs tokens) with
      | none => none
      | some decoded => some (token :: decoded) := by
  cases token <;> rfl

/-- Token encoding and token decoding are exact inverses on canonical input. -/
theorem decodeTokenPairs_canonical (tokens : List CNFToken) :
    decodeTokenPairs (encodeTokenPairs tokens) = some tokens := by
  induction tokens with
  | nil => rfl
  | cons token rest ih =>
      change decodeTokenPairs (token.bits ++ encodeTokenPairs rest) =
        some (token :: rest)
      rw [decodeTokenPairs_cons_bits]
      rw [ih]

/-- A literal names a zero-based variable and records whether that variable
must be true (`positive = true`) or false. -/
structure CNFLiteral where
  positive : Bool
  variableIndex : Nat
deriving BEq, DecidableEq, Repr

/-- A finite CNF formula with an explicit assignment width.  A literal whose
index is outside that width simply cannot be satisfied. -/
structure CNFFormula where
  variableCount : Nat
  clauses : List (List CNFLiteral)
deriving BEq, DecidableEq, Repr

/-- Read one zero-based assignment position without silently inventing a
value for an out-of-range literal. -/
def assignmentAt : BitString → Nat → Option Bool
  | [], _ => none
  | value :: _, 0 => some value
  | _ :: rest, index + 1 => assignmentAt rest index

/-- Propositional semantics of a literal, independent of the Boolean
checker. -/
def LiteralSatisfied (literal : CNFLiteral) (assignment : BitString) : Prop :=
  assignmentAt assignment literal.variableIndex = some literal.positive

/-- Propositional semantics of a disjunctive clause. -/
def ClauseSatisfied : List CNFLiteral → BitString → Prop
  | [], _ => False
  | literal :: rest, assignment =>
      LiteralSatisfied literal assignment ∨ ClauseSatisfied rest assignment

/-- Propositional semantics of a conjunction of clauses. -/
def ClausesSatisfied : List (List CNFLiteral) → BitString → Prop
  | [], _ => True
  | clause :: rest, assignment =>
      ClauseSatisfied clause assignment ∧ ClausesSatisfied rest assignment

/-- Standard finite CNF satisfaction, including the declared assignment
width. -/
def CNFFormula.Satisfied (formula : CNFFormula) (assignment : BitString) : Prop :=
  assignment.length = formula.variableCount ∧
    ClausesSatisfied formula.clauses assignment

/-- Constructive Boolean equality, kept local so the reflection proof does
not depend on simplifier-oriented equality lemmas. -/
def boolEqual : Bool → Bool → Bool
  | false, false => true
  | false, true => false
  | true, false => false
  | true, true => true

/-- Constructive natural equality used by the formula checker. -/
def natEqual : Nat → Nat → Bool
  | 0, 0 => true
  | 0, _ + 1 => false
  | _ + 1, 0 => false
  | left + 1, right + 1 => natEqual left right

/-- Executable literal checker. -/
def checkLiteral (literal : CNFLiteral) (assignment : BitString) : Bool :=
  match assignmentAt assignment literal.variableIndex with
  | none => false
  | some value => boolEqual value literal.positive

/-- Executable disjunction checker. -/
def checkClause : List CNFLiteral → BitString → Bool
  | [], _ => false
  | literal :: rest, assignment =>
      checkLiteral literal assignment || checkClause rest assignment

/-- Executable conjunction checker. -/
def checkClauses : List (List CNFLiteral) → BitString → Bool
  | [], _ => true
  | clause :: rest, assignment =>
      checkClause clause assignment && checkClauses rest assignment

/-- Executable CNF semantics on already-decoded data. -/
def checkCNF (formula : CNFFormula) (assignment : BitString) : Bool :=
  natEqual assignment.length formula.variableCount &&
    checkClauses formula.clauses assignment

theorem boolEqual_eq_true_iff (left right : Bool) :
    boolEqual left right = true ↔ left = right := by
  cases left <;> cases right
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · constructor
    · intro impossible
      exact Bool.noConfusion impossible
    · intro impossible
      exact Bool.noConfusion impossible
  · constructor
    · intro impossible
      exact Bool.noConfusion impossible
    · intro impossible
      exact Bool.noConfusion impossible
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem natEqual_eq_true_iff (left right : Nat) :
    natEqual left right = true ↔ left = right := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
      | succ right =>
          constructor
          · intro impossible
            exact Bool.noConfusion impossible
          · intro impossible
            exact Nat.noConfusion impossible
  | succ left ih =>
      cases right with
      | zero =>
          constructor
          · intro impossible
            exact Bool.noConfusion impossible
          · intro impossible
            exact Nat.noConfusion impossible
      | succ right =>
          change natEqual left right = true ↔ Nat.succ left = Nat.succ right
          constructor
          · intro equal
            exact congrArg Nat.succ ((ih right).mp equal)
          · intro equal
            exact (ih right).mpr (Nat.succ.inj equal)

theorem checkLiteral_eq_true_iff (literal : CNFLiteral)
    (assignment : BitString) :
    checkLiteral literal assignment = true ↔
      LiteralSatisfied literal assignment := by
  unfold checkLiteral LiteralSatisfied
  cases found : assignmentAt assignment literal.variableIndex with
  | none =>
      constructor
      · intro impossible
        exact Bool.noConfusion impossible
      · intro impossible
        cases impossible
  | some value =>
      change boolEqual value literal.positive = true ↔
        some value = some literal.positive
      constructor
      · intro equal
        exact congrArg some ((boolEqual_eq_true_iff value literal.positive).mp equal)
      · intro equal
        exact (boolEqual_eq_true_iff value literal.positive).mpr
          (Option.some.inj equal)

theorem checkClause_eq_true_iff (clause : List CNFLiteral)
    (assignment : BitString) :
    checkClause clause assignment = true ↔ ClauseSatisfied clause assignment := by
  induction clause with
  | nil =>
      constructor
      · intro impossible
        exact Bool.noConfusion impossible
      · intro impossible
        exact False.elim impossible
  | cons literal rest ih =>
      change (checkLiteral literal assignment || checkClause rest assignment) = true ↔
        LiteralSatisfied literal assignment ∨ ClauseSatisfied rest assignment
      cases literalCheck : checkLiteral literal assignment with
      | false =>
          change checkClause rest assignment = true ↔
            LiteralSatisfied literal assignment ∨ ClauseSatisfied rest assignment
          constructor
          · intro restTrue
            exact Or.inr ((ih).mp restTrue)
          · intro disjunction
            cases disjunction with
            | inl literalTrue =>
                have contradiction :=
                  (checkLiteral_eq_true_iff literal assignment).mpr literalTrue
                rw [literalCheck] at contradiction
                exact Bool.noConfusion contradiction
            | inr restTrue => exact ih.mpr restTrue
      | true =>
          constructor
          · intro _
            exact Or.inl ((checkLiteral_eq_true_iff literal assignment).mp literalCheck)
          · intro _
            rfl

theorem checkClauses_eq_true_iff (clauses : List (List CNFLiteral))
    (assignment : BitString) :
    checkClauses clauses assignment = true ↔
      ClausesSatisfied clauses assignment := by
  induction clauses with
  | nil =>
      constructor
      · intro _
        exact True.intro
      · intro _
        rfl
  | cons clause rest ih =>
      change (checkClause clause assignment && checkClauses rest assignment) = true ↔
        ClauseSatisfied clause assignment ∧ ClausesSatisfied rest assignment
      cases clauseCheck : checkClause clause assignment with
      | false =>
          constructor
          · intro impossible
            exact Bool.noConfusion impossible
          · intro conjunction
            have contradiction :=
              (checkClause_eq_true_iff clause assignment).mpr conjunction.left
            rw [clauseCheck] at contradiction
            exact Bool.noConfusion contradiction
      | true =>
          change checkClauses rest assignment = true ↔
            ClauseSatisfied clause assignment ∧ ClausesSatisfied rest assignment
          constructor
          · intro restTrue
            exact ⟨(checkClause_eq_true_iff clause assignment).mp clauseCheck,
              ih.mp restTrue⟩
          · intro conjunction
            exact ih.mpr conjunction.right

/-- The executable checker on decoded data exactly reflects the independent
propositional semantics. -/
theorem checkCNF_eq_true_iff (formula : CNFFormula) (assignment : BitString) :
    checkCNF formula assignment = true ↔ formula.Satisfied assignment := by
  unfold checkCNF CNFFormula.Satisfied
  cases widthCheck : natEqual assignment.length formula.variableCount with
  | false =>
      constructor
      · intro impossible
        exact Bool.noConfusion impossible
      · intro conjunction
        have contradiction :=
          (natEqual_eq_true_iff assignment.length formula.variableCount).mpr
            conjunction.left
        rw [widthCheck] at contradiction
        exact Bool.noConfusion contradiction
  | true =>
      change checkClauses formula.clauses assignment = true ↔
        assignment.length = formula.variableCount ∧
          ClausesSatisfied formula.clauses assignment
      constructor
      · intro clausesTrue
        exact ⟨(natEqual_eq_true_iff assignment.length formula.variableCount).mp
            widthCheck,
          (checkClauses_eq_true_iff formula.clauses assignment).mp clausesTrue⟩
      · intro conjunction
        exact (checkClauses_eq_true_iff formula.clauses assignment).mpr
          conjunction.right

/-! ### Canonical token encoding -/

/-- Unary natural encoding inside the token grammar: `T^n F`. -/
def encodeUnaryTokens : Nat → List CNFToken
  | 0 => [.f]
  | count + 1 => .t :: encodeUnaryTokens count

/-- Encode a literal as its sign token followed by its unary zero-based
variable index. -/
def encodeLiteralTokens (literal : CNFLiteral) : List CNFToken :=
  (if literal.positive then .t else .f) :: encodeUnaryTokens literal.variableIndex

/-- Concatenate the token encodings of all literals in one clause. -/
def encodeLiteralListTokens : List CNFLiteral → List CNFToken
  | [] => []
  | literal :: rest => encodeLiteralTokens literal ++ encodeLiteralListTokens rest

/-- Encode one clause, including its leading separator and terminal finish
token. -/
def encodeClauseTokens (clause : List CNFLiteral) : List CNFToken :=
  .sep :: (encodeLiteralListTokens clause ++ [.finish])

/-- Concatenate all encoded clauses. -/
def encodeClauseListTokens : List (List CNFLiteral) → List CNFToken
  | [] => []
  | clause :: rest => encodeClauseTokens clause ++ encodeClauseListTokens rest

/-- Canonical token representation of a formula: a unary assignment width,
all clauses, and one final finish token. -/
def encodeCNFTokens (formula : CNFFormula) : List CNFToken :=
  encodeUnaryTokens formula.variableCount ++
    encodeClauseListTokens formula.clauses ++ [.finish]

/-- Descriptive alias used by the work-tape compiler layer. -/
def encodeFormulaTokens (formula : CNFFormula) : List CNFToken :=
  encodeCNFTokens formula

/-- Canonical raw formula encoding.  The final zero pad makes every encoded
formula odd-length and keeps it disjoint from assignment certificates. -/
def encodeCNF (formula : CNFFormula) : BitString :=
  encodeTokenPairs (encodeCNFTokens formula) ++ [false]

/-- Descriptive alias for the canonical raw formula encoding. -/
def encodeFormula (formula : CNFFormula) : BitString := encodeCNF formula

/-- Convert one assignment value to its canonical token. -/
def assignmentToken : Bool → CNFToken
  | false => .f
  | true => .t

/-- Canonical assignment token representation: one F/T token per value and
one final finish token. -/
def encodeAssignmentTokens : BitString → List CNFToken
  | [] => [.finish]
  | value :: rest => assignmentToken value :: encodeAssignmentTokens rest

/-- Canonical even-length assignment certificate. -/
def encodeAssignmentCertificate (assignment : BitString) : BitString :=
  encodeTokenPairs (encodeAssignmentTokens assignment)

/-! ### Strict decoders -/

/- Decode the clause suffix of the formula grammar.  These three mutually
recursive states consume at least one token on every call. -/
mutual
  def decodeFormulaClauses : List CNFToken → Option (List (List CNFLiteral))
    | [] => none
    | token :: rest =>
        match token with
        | .f => none
        | .t => none
        | .sep =>
            match decodeFormulaClause rest with
            | none => none
            | some (clause, clauses) => some (clause :: clauses)
        | .finish =>
            match rest with
            | [] => some []
            | _ :: _ => none

  def decodeFormulaClause :
      List CNFToken → Option (List CNFLiteral × List (List CNFLiteral))
    | [] => none
    | token :: rest =>
        match token with
        | .f => decodeFormulaLiteral false 0 rest
        | .t => decodeFormulaLiteral true 0 rest
        | .sep => none
        | .finish =>
            match decodeFormulaClauses rest with
            | none => none
            | some clauses => some ([], clauses)

  def decodeFormulaLiteral (positive : Bool) (variableIndex : Nat) :
      List CNFToken → Option (List CNFLiteral × List (List CNFLiteral))
    | [] => none
    | token :: rest =>
        match token with
        | .f =>
            match decodeFormulaClause rest with
            | none => none
            | some (clause, clauses) =>
                some
                  ({ positive := positive, variableIndex := variableIndex } :: clause,
                    clauses)
        | .t => decodeFormulaLiteral positive (variableIndex + 1) rest
        | .sep => none
        | .finish => none
end

/-- Decode the initial unary variable count and then the strict clause
grammar. -/
def decodeFormulaHeader : Nat → List CNFToken → Option CNFFormula
  | _, [] => none
  | count, token :: rest =>
      match token with
      | .f =>
          match decodeFormulaClauses rest with
          | none => none
          | some clauses => some { variableCount := count, clauses := clauses }
      | .t => decodeFormulaHeader (count + 1) rest
      | .sep => none
      | .finish => none

/-- Decode a complete canonical formula token stream. -/
def decodeCNFTokens (tokens : List CNFToken) : Option CNFFormula :=
  decodeFormulaHeader 0 tokens

/-- Decode pairs ending in exactly one zero formula pad. -/
def decodeFormulaTokenPairs : BitString → Option (List CNFToken)
  | [] => none
  | first :: tail =>
      match tail with
      | [] =>
          match first with
          | false => some []
          | true => none
      | second :: rest =>
          match decodeFormulaTokenPairs rest with
          | none => none
          | some tokens => some (CNFToken.ofBits first second :: tokens)

/-- Strict whole-string formula decoder. -/
def decodeEncodedCNF (bits : BitString) : Option CNFFormula :=
  match decodeFormulaTokenPairs bits with
  | none => none
  | some tokens => decodeCNFTokens tokens

/-- Descriptive alias for the strict whole-string formula decoder. -/
def decodeFormula (bits : BitString) : Option CNFFormula := decodeEncodedCNF bits

/-- Strict assignment-token decoder. -/
def decodeAssignmentTokens : List CNFToken → Option BitString
  | [] => none
  | token :: rest =>
      match token with
      | .f =>
          match decodeAssignmentTokens rest with
          | none => none
          | some assignment => some (false :: assignment)
      | .t =>
          match decodeAssignmentTokens rest with
          | none => none
          | some assignment => some (true :: assignment)
      | .sep => none
      | .finish =>
          match rest with
          | [] => some []
          | _ :: _ => none

/-- Strict whole-string assignment-certificate decoder. -/
def decodeAssignmentCertificate (certificate : BitString) : Option BitString :=
  match decodeTokenPairs certificate with
  | none => none
  | some tokens => decodeAssignmentTokens tokens

theorem decodeFormulaTokenPairs_cons_bits (token : CNFToken)
    (tokens : List CNFToken) :
    decodeFormulaTokenPairs
        (token.bits ++ (encodeTokenPairs tokens ++ [false])) =
      match decodeFormulaTokenPairs (encodeTokenPairs tokens ++ [false]) with
      | none => none
      | some decoded => some (token :: decoded) := by
  cases token <;> rfl

theorem decodeFormulaTokenPairs_canonical (tokens : List CNFToken) :
    decodeFormulaTokenPairs (encodeTokenPairs tokens ++ [false]) = some tokens := by
  induction tokens with
  | nil => rfl
  | cons token rest ih =>
      change decodeFormulaTokenPairs
          ((token.bits ++ encodeTokenPairs rest) ++ [false]) =
        some (token :: rest)
      rw [BitString.append_assoc_constructive]
      rw [decodeFormulaTokenPairs_cons_bits]
      rw [ih]

theorem decodeAssignmentTokens_canonical (assignment : BitString) :
    decodeAssignmentTokens (encodeAssignmentTokens assignment) = some assignment := by
  induction assignment with
  | nil => rfl
  | cons value rest ih =>
      cases value with
      | false =>
          change (match decodeAssignmentTokens (encodeAssignmentTokens rest) with
            | none => none
            | some decodedAssignment => some (false :: decodedAssignment)) =
              some (false :: rest)
          rw [ih]
      | true =>
          change (match decodeAssignmentTokens (encodeAssignmentTokens rest) with
            | none => none
            | some decodedAssignment => some (true :: decodedAssignment)) =
              some (true :: rest)
          rw [ih]

/-- Every accepted assignment token stream is already the unique canonical
encoding of the assignment it decodes to. -/
theorem encodeAssignmentTokens_of_decode (tokens : List CNFToken)
    (assignment : BitString)
    (decoded : decodeAssignmentTokens tokens = some assignment) :
    encodeAssignmentTokens assignment = tokens := by
  induction tokens generalizing assignment with
  | nil =>
      change none = some assignment at decoded
      cases decoded
  | cons token rest ih =>
      cases token with
      | f =>
          change (match decodeAssignmentTokens rest with
            | none => none
            | some decodedAssignment => some (false :: decodedAssignment)) =
              some assignment at decoded
          cases restCase : decodeAssignmentTokens rest with
          | none =>
              rw [restCase] at decoded
              cases decoded
          | some decodedAssignment =>
              rw [restCase] at decoded
              have assignmentEqual : false :: decodedAssignment = assignment :=
                Option.some.inj decoded
              cases assignmentEqual
              change CNFToken.f :: encodeAssignmentTokens decodedAssignment =
                CNFToken.f :: rest
              exact congrArg (List.cons CNFToken.f)
                (ih decodedAssignment restCase)
      | t =>
          change (match decodeAssignmentTokens rest with
            | none => none
            | some decodedAssignment => some (true :: decodedAssignment)) =
              some assignment at decoded
          cases restCase : decodeAssignmentTokens rest with
          | none =>
              rw [restCase] at decoded
              cases decoded
          | some decodedAssignment =>
              rw [restCase] at decoded
              have assignmentEqual : true :: decodedAssignment = assignment :=
                Option.some.inj decoded
              cases assignmentEqual
              change CNFToken.t :: encodeAssignmentTokens decodedAssignment =
                CNFToken.t :: rest
              exact congrArg (List.cons CNFToken.t)
                (ih decodedAssignment restCase)
      | sep =>
          change none = some assignment at decoded
          cases decoded
      | finish =>
          cases rest with
          | nil =>
              change some [] = some assignment at decoded
              have assignmentEmpty : [] = assignment := Option.some.inj decoded
              cases assignmentEmpty
              rfl
          | cons next suffix =>
              change none = some assignment at decoded
              cases decoded

/-- Canonical assignment certificates round-trip exactly. -/
theorem decodeAssignmentCertificate_canonical (assignment : BitString) :
    decodeAssignmentCertificate (encodeAssignmentCertificate assignment) =
      some assignment := by
  unfold decodeAssignmentCertificate encodeAssignmentCertificate
  rw [decodeTokenPairs_canonical]
  exact decodeAssignmentTokens_canonical assignment

/-! ### Canonical formula round trip -/

theorem token_append_assoc_constructive (left middle right : List CNFToken) :
    (left ++ middle) ++ right = left ++ (middle ++ right) := by
  induction left with
  | nil => rfl
  | cons token rest ih => exact congrArg (List.cons token) ih

theorem token_append_nil_constructive (tokens : List CNFToken) :
    tokens ++ [] = tokens := by
  induction tokens with
  | nil => rfl
  | cons token rest ih => exact congrArg (List.cons token) ih

theorem nat_add_succ_shift (left right : Nat) :
    (left + 1) + right = left + (right + 1) := by
  induction right with
  | zero =>
      rw [Nat.add_zero]
  | succ right ih =>
      change Nat.succ ((left + 1) + right) =
        Nat.succ (left + (right + 1))
      exact congrArg Nat.succ ih

theorem decodeFormulaLiteral_unary (positive : Bool) (start count : Nat)
    (suffix : List CNFToken) :
    decodeFormulaLiteral positive start (encodeUnaryTokens count ++ suffix) =
      match decodeFormulaClause suffix with
      | none => none
      | some (clause, clauses) =>
          some ({ positive := positive, variableIndex := start + count } :: clause,
            clauses) := by
  induction count generalizing start with
  | zero =>
      change (match decodeFormulaClause suffix with
        | none => none
        | some (clause, clauses) =>
            some (({ positive := positive, variableIndex := start } : CNFLiteral) :: clause,
              clauses)) =
        match decodeFormulaClause suffix with
        | none => none
        | some (clause, clauses) =>
            some (({ positive := positive, variableIndex := start + 0 } : CNFLiteral) :: clause,
              clauses)
      rw [Nat.add_zero]
  | succ count ih =>
      change decodeFormulaLiteral positive (start + 1)
          (encodeUnaryTokens count ++ suffix) =
        match decodeFormulaClause suffix with
        | none => none
        | some (clause, clauses) =>
            some ({ positive := positive, variableIndex := start + (count + 1) } ::
              clause, clauses)
      rw [ih]
      rw [nat_add_succ_shift]

theorem decodeFormulaClauses_canonical (clauses : List (List CNFLiteral)) :
    decodeFormulaClauses (encodeClauseListTokens clauses ++ [.finish]) =
      some clauses := by
  induction clauses with
  | nil => rfl
  | cons clause rest restIH =>
      have clauseDecoded :
          decodeFormulaClause
              (encodeLiteralListTokens clause ++
                (.finish :: (encodeClauseListTokens rest ++ [.finish]))) =
            some (clause, rest) := by
        induction clause with
        | nil =>
            change (match decodeFormulaClauses
                (encodeClauseListTokens rest ++ [.finish]) with
              | none => none
              | some decodedClauses => some ([], decodedClauses)) =
                some ([], rest)
            rw [restIH]
        | cons literal tail tailIH =>
            change decodeFormulaClause
                ((encodeLiteralTokens literal ++ encodeLiteralListTokens tail) ++
                  (.finish :: (encodeClauseListTokens rest ++ [.finish]))) =
              some (literal :: tail, rest)
            rw [token_append_assoc_constructive]
            unfold encodeLiteralTokens
            cases literal with
            | mk positive variableIndex =>
              cases positive with
              | false =>
                change decodeFormulaLiteral false 0
                    (encodeUnaryTokens variableIndex ++
                      (encodeLiteralListTokens tail ++
                        (.finish :: (encodeClauseListTokens rest ++ [.finish])))) =
                  some ({ positive := false, variableIndex := variableIndex } :: tail,
                    rest)
                rw [decodeFormulaLiteral_unary]
                rw [tailIH]
                change some
                    ({ positive := false, variableIndex := 0 + variableIndex } :: tail,
                      rest) =
                  some ({ positive := false, variableIndex := variableIndex } :: tail,
                    rest)
                rw [Nat.zero_add]
              | true =>
                change decodeFormulaLiteral true 0
                    (encodeUnaryTokens variableIndex ++
                      (encodeLiteralListTokens tail ++
                        (.finish :: (encodeClauseListTokens rest ++ [.finish])))) =
                  some ({ positive := true, variableIndex := variableIndex } :: tail,
                    rest)
                rw [decodeFormulaLiteral_unary]
                rw [tailIH]
                change some
                    ({ positive := true, variableIndex := 0 + variableIndex } :: tail,
                      rest) =
                  some ({ positive := true, variableIndex := variableIndex } :: tail,
                    rest)
                rw [Nat.zero_add]
      change decodeFormulaClauses
          ((encodeClauseTokens clause ++ encodeClauseListTokens rest) ++ [.finish]) =
        some (clause :: rest)
      rw [token_append_assoc_constructive]
      change (match decodeFormulaClause
          ((encodeLiteralListTokens clause ++ [.finish]) ++
            (encodeClauseListTokens rest ++ [.finish])) with
        | none => none
        | some (decodedClause, decodedClauses) =>
            some (decodedClause :: decodedClauses)) = some (clause :: rest)
      rw [token_append_assoc_constructive]
      exact congrArg (fun result =>
        match result with
        | none => none
        | some (decodedClause, decodedClauses) =>
            some (decodedClause :: decodedClauses)) clauseDecoded

theorem decodeFormulaHeader_unary (start count : Nat)
    (clauses : List (List CNFLiteral)) :
    decodeFormulaHeader start
        (encodeUnaryTokens count ++ encodeClauseListTokens clauses ++ [.finish]) =
      some { variableCount := start + count, clauses := clauses } := by
  induction count generalizing start with
  | zero =>
      change (match decodeFormulaClauses
          (encodeClauseListTokens clauses ++ [.finish]) with
        | none => none
        | some decodedClauses =>
            some ({ variableCount := start, clauses := decodedClauses } : CNFFormula)) =
          some ({ variableCount := start + 0, clauses := clauses } : CNFFormula)
      rw [decodeFormulaClauses_canonical]
      rw [Nat.add_zero]
  | succ count ih =>
      change decodeFormulaHeader (start + 1)
          (encodeUnaryTokens count ++ encodeClauseListTokens clauses ++ [.finish]) =
        some { variableCount := start + (count + 1), clauses := clauses }
      rw [ih]
      rw [nat_add_succ_shift]

/-- Canonical formula token streams round-trip exactly. -/
theorem decodeCNFTokens_canonical (formula : CNFFormula) :
    decodeCNFTokens (encodeCNFTokens formula) = some formula := by
  unfold decodeCNFTokens encodeCNFTokens
  rw [decodeFormulaHeader_unary]
  cases formula with
  | mk variableCount clauses =>
      change some
          ({ variableCount := 0 + variableCount, clauses := clauses } : CNFFormula) =
        some ({ variableCount := variableCount, clauses := clauses } : CNFFormula)
      rw [Nat.zero_add]

/-- Canonical raw formula strings round-trip exactly. -/
theorem decodeEncodedCNF_canonical (formula : CNFFormula) :
    decodeEncodedCNF (encodeCNF formula) = some formula := by
  unfold decodeEncodedCNF encodeCNF
  rw [decodeFormulaTokenPairs_canonical]
  exact decodeCNFTokens_canonical formula

/-! ### Encoded checker and SAT language -/

/-- Parse a raw formula and a raw assignment certificate and check them.  Any
malformed component fails closed. -/
def checkEncodedCertificate (encodedFormula certificate : BitString) : Bool :=
  match decodeEncodedCNF encodedFormula with
  | none => false
  | some formula =>
      match decodeAssignmentCertificate certificate with
      | none => false
      | some assignment => checkCNF formula assignment

/-- Existential semantics of one already-decoded formula. -/
def CNFFormula.Satisfiable (formula : CNFFormula) : Prop :=
  ∃ assignment, formula.Satisfied assignment

/-- The concrete language of strictly encoded satisfiable CNF formulae. -/
def CNFSAT : Language := fun encodedFormula =>
  ∃ formula,
    decodeEncodedCNF encodedFormula = some formula ∧ formula.Satisfiable

/-- The raw checker reflects the independently stated propositional
semantics, including both strict decoders. -/
theorem checkEncodedCertificate_eq_true_iff
    (encodedFormula certificate : BitString) :
    checkEncodedCertificate encodedFormula certificate = true ↔
      ∃ formula assignment,
        decodeEncodedCNF encodedFormula = some formula ∧
          decodeAssignmentCertificate certificate = some assignment ∧
          formula.Satisfied assignment := by
  unfold checkEncodedCertificate
  cases formulaCase : decodeEncodedCNF encodedFormula with
  | none =>
      constructor
      · intro impossible
        exact Bool.noConfusion impossible
      · intro existsDecoded
        rcases existsDecoded with ⟨formula, assignment, decodedFormula,
          decodedAssignment, satisfied⟩
        cases decodedFormula
  | some formula =>
      cases assignmentCase : decodeAssignmentCertificate certificate with
      | none =>
          constructor
          · intro impossible
            exact Bool.noConfusion impossible
          · intro existsDecoded
            rcases existsDecoded with ⟨decodedFormula, assignment, formulaEqual,
              assignmentEqual, satisfied⟩
            cases assignmentEqual
      | some assignment =>
          constructor
          · intro checked
            exact ⟨formula, assignment, rfl, rfl,
              (checkCNF_eq_true_iff formula assignment).mp checked⟩
          · intro existsDecoded
            rcases existsDecoded with ⟨decodedFormula, decodedAssignment,
              formulaEqual, assignmentEqual, satisfied⟩
            have formulasEqual : formula = decodedFormula :=
              Option.some.inj formulaEqual
            have assignmentsEqual : assignment = decodedAssignment :=
              Option.some.inj assignmentEqual
            cases formulasEqual
            cases assignmentsEqual
            exact (checkCNF_eq_true_iff formula assignment).mpr satisfied

theorem checkEncodedCertificate_canonical_eq_true_iff
    (formula : CNFFormula) (assignment : BitString) :
    checkEncodedCertificate (encodeCNF formula)
        (encodeAssignmentCertificate assignment) = true ↔
      formula.Satisfied assignment := by
  constructor
  · intro checked
    have existsDecoded :=
      (checkEncodedCertificate_eq_true_iff (encodeCNF formula)
        (encodeAssignmentCertificate assignment)).mp checked
    rcases existsDecoded with ⟨decodedFormula, decodedAssignment, formulaEqual,
      assignmentEqual, satisfied⟩
    have formulasEqual : decodedFormula = formula :=
      Option.some.inj (formulaEqual.symm.trans (decodeEncodedCNF_canonical formula))
    have assignmentsEqual : decodedAssignment = assignment :=
      Option.some.inj
        (assignmentEqual.symm.trans
          (decodeAssignmentCertificate_canonical assignment))
    cases formulasEqual
    cases assignmentsEqual
    exact satisfied
  · intro satisfied
    exact (checkEncodedCertificate_eq_true_iff (encodeCNF formula)
      (encodeAssignmentCertificate assignment)).mpr
        ⟨formula, assignment, decodeEncodedCNF_canonical formula,
          decodeAssignmentCertificate_canonical assignment, satisfied⟩

theorem cnfSAT_iff_encoded_certificate (encodedFormula : BitString) :
    CNFSAT encodedFormula ↔
      ∃ certificate, checkEncodedCertificate encodedFormula certificate = true := by
  constructor
  · intro satisfiable
    rcases satisfiable with ⟨formula, decoded, assignment, satisfied⟩
    refine ⟨encodeAssignmentCertificate assignment, ?_⟩
    exact (checkEncodedCertificate_eq_true_iff encodedFormula
      (encodeAssignmentCertificate assignment)).mpr
        ⟨formula, assignment, decoded,
          decodeAssignmentCertificate_canonical assignment, satisfied⟩
  · intro acceptedCertificate
    rcases acceptedCertificate with ⟨certificate, accepted⟩
    have reflected :=
      (checkEncodedCertificate_eq_true_iff encodedFormula certificate).mp accepted
    rcases reflected with ⟨formula, assignment, decodedFormula, decodedAssignment,
      satisfied⟩
    exact ⟨formula, decodedFormula, assignment, satisfied⟩

/-! ### Certificate-size accounting -/

theorem token_bits_length (token : CNFToken) : token.bits.length = 2 := by
  cases token <;> rfl

theorem token_length_append_constructive (left right : List CNFToken) :
    (left ++ right).length = left.length + right.length := by
  induction left with
  | nil => exact (Nat.zero_add right.length).symm
  | cons token rest ih =>
      change Nat.succ (rest ++ right).length = Nat.succ rest.length + right.length
      rw [Nat.succ_add]
      exact congrArg Nat.succ ih

theorem encodeTokenPairs_length (tokens : List CNFToken) :
    (encodeTokenPairs tokens).length = 2 * tokens.length := by
  induction tokens with
  | nil => rfl
  | cons token rest ih =>
      change (token.bits ++ encodeTokenPairs rest).length =
        2 * Nat.succ rest.length
      rw [BitString.length_append_constructive]
      rw [token_bits_length]
      rw [ih]
      change 2 + 2 * rest.length = 2 * rest.length + 2
      exact (Nat.add_comm (2 * rest.length) 2).symm

theorem encodeAssignmentTokens_length (assignment : BitString) :
    (encodeAssignmentTokens assignment).length = assignment.length + 1 := by
  induction assignment with
  | nil => rfl
  | cons value rest ih =>
      change Nat.succ (encodeAssignmentTokens rest).length =
        Nat.succ rest.length + 1
      rw [ih]

theorem encodeAssignmentCertificate_size (assignment : BitString) :
    BitString.size (encodeAssignmentCertificate assignment) =
      2 * (assignment.length + 1) := by
  unfold BitString.size encodeAssignmentCertificate
  rw [encodeTokenPairs_length]
  rw [encodeAssignmentTokens_length]

theorem decodeFormulaHeader_variable_succ_le (start : Nat)
    (tokens : List CNFToken) (formula : CNFFormula)
    (decoded : decodeFormulaHeader start tokens = some formula) :
    formula.variableCount + 1 ≤ start + tokens.length := by
  induction tokens generalizing start formula with
  | nil =>
      change none = some formula at decoded
      cases decoded
  | cons token rest ih =>
      cases token with
      | f =>
          change (match decodeFormulaClauses rest with
            | none => none
            | some clauses =>
                some ({ variableCount := start, clauses := clauses } : CNFFormula)) =
              some formula at decoded
          cases clausesCase : decodeFormulaClauses rest with
          | none =>
              rw [clausesCase] at decoded
              cases decoded
          | some clauses =>
              rw [clausesCase] at decoded
              have formulaEqual :
                  ({ variableCount := start, clauses := clauses } : CNFFormula) =
                    formula := Option.some.inj decoded
              cases formulaEqual
              change start + 1 ≤ start + Nat.succ rest.length
              exact Nat.add_le_add_left
                (Nat.succ_le_succ (Nat.zero_le rest.length)) start
      | t =>
          change decodeFormulaHeader (start + 1) rest = some formula at decoded
          have bound := ih (start + 1) formula decoded
          change formula.variableCount + 1 ≤ start + Nat.succ rest.length
          have rightEqual : (start + 1) + rest.length =
              start + Nat.succ rest.length := nat_add_succ_shift start rest.length
          exact rightEqual ▸ bound
      | sep =>
          change none = some formula at decoded
          cases decoded
      | finish =>
          change none = some formula at decoded
          cases decoded

theorem decodeCNFTokens_variable_succ_le (tokens : List CNFToken)
    (formula : CNFFormula) (decoded : decodeCNFTokens tokens = some formula) :
    formula.variableCount + 1 ≤ tokens.length := by
  unfold decodeCNFTokens at decoded
  have bound := decodeFormulaHeader_variable_succ_le 0 tokens formula decoded
  rw [Nat.zero_add] at bound
  exact bound

theorem decodeFormulaTokenPairs_length (bits : BitString)
    (tokens : List CNFToken)
    (decoded : decodeFormulaTokenPairs bits = some tokens) :
    bits.length = 2 * tokens.length + 1 := by
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
                  have impossible : [] = token :: tokens := Option.some.inj decoded
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
                  have tokensEqual :
                      CNFToken.ofBits first second :: decodedTokens = token :: tokens :=
                    Option.some.inj decoded
                  have tailsEqual : decodedTokens = tokens :=
                    congrArg List.tail tokensEqual
                  cases tailsEqual
                  have restLength := ih rest restCase
                  change Nat.succ (Nat.succ rest.length) =
                    2 * Nat.succ tokens.length + 1
                  rw [restLength]
                  change Nat.succ (Nat.succ (2 * tokens.length + 1)) =
                    2 * tokens.length + 2 + 1
                  rfl

/-- The canonical assignment induced by any satisfying decoded formula is no
longer than that raw formula input itself. -/
theorem encodedCNF_assignment_certificate_size_le
    (encodedFormula : BitString) (formula : CNFFormula)
    (assignment : BitString)
    (decoded : decodeEncodedCNF encodedFormula = some formula)
    (satisfied : formula.Satisfied assignment) :
    BitString.size (encodeAssignmentCertificate assignment) ≤
      BitString.size encodedFormula := by
  unfold decodeEncodedCNF at decoded
  cases tokenCase : decodeFormulaTokenPairs encodedFormula with
  | none =>
      rw [tokenCase] at decoded
      cases decoded
  | some tokens =>
      rw [tokenCase] at decoded
      have headerBound := decodeCNFTokens_variable_succ_le tokens formula decoded
      have inputLength :=
        decodeFormulaTokenPairs_length encodedFormula tokens tokenCase
      rw [encodeAssignmentCertificate_size]
      rw [satisfied.left]
      unfold BitString.size
      rw [inputLength]
      exact Nat.le_trans (Nat.mul_le_mul_left 2 headerBound)
        (Nat.le_add_right (2 * tokens.length) 1)

/-- The explicit certificate polynomial used by the concrete CNF verifier. -/
def cnfCertificateBound : NatPolynomial := NatPolynomial.linear 2 2

theorem encodedCNF_assignment_certificate_size_le_bound
    (encodedFormula : BitString) (formula : CNFFormula)
    (assignment : BitString)
    (decoded : decodeEncodedCNF encodedFormula = some formula)
    (satisfied : formula.Satisfied assignment) :
    BitString.size (encodeAssignmentCertificate assignment) ≤
      cnfCertificateBound.eval (BitString.size encodedFormula) := by
  have certificateLeInput := encodedCNF_assignment_certificate_size_le
    encodedFormula formula assignment decoded satisfied
  change BitString.size (encodeAssignmentCertificate assignment) ≤
    2 * BitString.size encodedFormula + 2
  exact Nat.le_trans certificateLeInput
    (Nat.le_trans
      (Nat.le_mul_of_pos_left (BitString.size encodedFormula)
        (Nat.zero_lt_succ 1))
      (Nat.le_add_right (2 * BitString.size encodedFormula) 2))

/-- Exact bounded-certificate characterization of the concrete CNF language. -/
theorem cnfSAT_iff_bounded_encoded_certificate (encodedFormula : BitString) :
    CNFSAT encodedFormula ↔
      ∃ certificate,
        BitString.size certificate ≤
            cnfCertificateBound.eval (BitString.size encodedFormula) ∧
          checkEncodedCertificate encodedFormula certificate = true := by
  constructor
  · intro satisfiable
    rcases satisfiable with ⟨formula, decoded, assignment, satisfied⟩
    refine ⟨encodeAssignmentCertificate assignment, ?_, ?_⟩
    · exact encodedCNF_assignment_certificate_size_le_bound
        encodedFormula formula assignment decoded satisfied
    · exact (checkEncodedCertificate_eq_true_iff encodedFormula
        (encodeAssignmentCertificate assignment)).mpr
          ⟨formula, assignment, decoded,
            decodeAssignmentCertificate_canonical assignment, satisfied⟩
  · intro acceptedCertificate
    rcases acceptedCertificate with ⟨certificate, certificateSize, accepted⟩
    have reflected :=
      (checkEncodedCertificate_eq_true_iff encodedFormula certificate).mp accepted
    rcases reflected with ⟨formula, assignment, decodedFormula, decodedAssignment,
      satisfied⟩
    exact ⟨formula, decodedFormula, assignment, satisfied⟩

end PNP.Concrete

/-
Copyright (c) 2026 PNP Labs.

Finite, width-indexed CNF emitters for the concrete Cook--Levin route.

Every source literal carries a `Fin width` variable, so emitted clauses are
in range by construction.  The compiler below reflects unit constraints,
finite implications, and pairwise exactly-one constraints into the concrete
`CNFFormula` semantics.  Exact clause counts are computed by the same
structural recursion as emission.

This file does not assemble a machine tableau formula, encode a reduction,
or claim NP-hardness.
-/

import PNP.Concrete.CookLevinVerifierTableau

namespace PNP.Concrete

namespace CookLevin

/-! ### Exact assignment lookup inside a declared width -/

theorem assignmentAt_exists_of_lt (assignment : BitString) (index : Nat)
    (hIndex : index < assignment.length) :
    ∃ value, assignmentAt assignment index = some value := by
  induction assignment generalizing index with
  | nil => cases hIndex
  | cons first rest ih =>
      cases index with
      | zero => exact ⟨first, rfl⟩
      | succ index =>
          exact ih index ((Nat.succ_lt_succ_iff).mp hIndex)

/-- Materialize exactly `width` Boolean values from a total, answer-independent
index function. -/
def assignmentOf : (width : Nat) → (Nat → Bool) → BitString
  | 0, _ => []
  | width + 1, value =>
      value 0 :: assignmentOf width (fun index => value (index + 1))

theorem assignmentOf_length (width : Nat) (value : Nat → Bool) :
    (assignmentOf width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih =>
      change Nat.succ
          (assignmentOf width (fun index => value (index + 1))).length =
        Nat.succ width
      exact congrArg Nat.succ (ih (fun index => value (index + 1)))

theorem assignmentAt_assignmentOf (width : Nat) (value : Nat → Bool)
    (index : Nat) (hIndex : index < width) :
    assignmentAt (assignmentOf width value) index = some (value index) := by
  induction width generalizing value index with
  | zero => cases hIndex
  | succ width ih =>
      cases index with
      | zero => rfl
      | succ index =>
          change assignmentAt
              (assignmentOf width (fun next => value (next + 1))) index =
            some (value (index + 1))
          exact ih (fun next => value (next + 1)) index
            ((Nat.succ_lt_succ_iff).mp hIndex)

/-! ### Width-indexed literals and their literal compiler -/

/-- A Boolean literal whose variable is constructively inside one declared
assignment width. -/
structure BoundedLiteral (width : Nat) where
  positive : Bool
  index : Fin width
deriving DecidableEq, Repr

namespace BoundedLiteral

def emit {width : Nat} (literal : BoundedLiteral width) : CNFLiteral :=
  { positive := literal.positive, variableIndex := literal.index.val }

def Holds {width : Nat} (literal : BoundedLiteral width)
    (assignment : BitString) : Prop :=
  assignmentAt assignment literal.index.val = some literal.positive

def negate {width : Nat} (literal : BoundedLiteral width) :
    BoundedLiteral width :=
  { positive := !literal.positive, index := literal.index }

theorem emit_variable_lt {width : Nat} (literal : BoundedLiteral width) :
    literal.emit.variableIndex < width :=
  literal.index.isLt

theorem emit_satisfied_iff {width : Nat} (literal : BoundedLiteral width)
    (assignment : BitString) :
    LiteralSatisfied literal.emit assignment ↔ literal.Holds assignment :=
  Iff.rfl

theorem negate_holds_iff_not {width : Nat}
    (literal : BoundedLiteral width) (assignment : BitString)
    (hLength : assignment.length = width) :
    literal.negate.Holds assignment ↔ ¬ literal.Holds assignment := by
  have hIndex : literal.index.val < assignment.length := by
    exact hLength.symm ▸ literal.index.isLt
  rcases assignmentAt_exists_of_lt assignment literal.index.val hIndex with
    ⟨value, hValue⟩
  cases literal with
  | mk positive index =>
      change
        assignmentAt assignment index.val = some (!positive) ↔
          ¬ assignmentAt assignment index.val = some positive
      cases positive <;> cases value
      · constructor
        · intro hTrue hFalse
          have impossible : (false : Bool) = true :=
            Option.some.inj (hFalse.symm.trans hTrue)
          exact Bool.noConfusion impossible
        · intro hNot
          exact False.elim (hNot hValue)
      · constructor
        · intro hTrue hFalse
          have impossible : (false : Bool) = true :=
            Option.some.inj (hFalse.symm.trans hTrue)
          exact Bool.noConfusion impossible
        · intro _
          exact hValue
      · constructor
        · intro hFalse hTrue
          have impossible : (true : Bool) = false :=
            Option.some.inj (hTrue.symm.trans hFalse)
          exact Bool.noConfusion impossible
        · intro _
          exact hValue
      · constructor
        · intro hFalse hTrue
          have impossible : (true : Bool) = false :=
            Option.some.inj (hTrue.symm.trans hFalse)
          exact Bool.noConfusion impossible
        · intro hNot
          exact False.elim (hNot hValue)

theorem holds_or_negate_holds {width : Nat}
    (literal : BoundedLiteral width) (assignment : BitString)
    (hLength : assignment.length = width) :
    literal.Holds assignment ∨ literal.negate.Holds assignment := by
  have hIndex : literal.index.val < assignment.length :=
    hLength.symm ▸ literal.index.isLt
  rcases assignmentAt_exists_of_lt assignment literal.index.val hIndex with
    ⟨value, hValue⟩
  cases literal with
  | mk positive index =>
      change
        assignmentAt assignment index.val = some positive ∨
          assignmentAt assignment index.val = some (!positive)
      cases positive <;> cases value
      · exact Or.inl hValue
      · exact Or.inr hValue
      · exact Or.inr hValue
      · exact Or.inl hValue

end BoundedLiteral

abbrev BoundedClause (width : Nat) := List (BoundedLiteral width)

abbrev BoundedClauses (width : Nat) := List (BoundedClause width)

namespace BoundedClause

def emit {width : Nat} (clause : BoundedClause width) :
    List CNFLiteral :=
  clause.map BoundedLiteral.emit

def Holds {width : Nat} : BoundedClause width → BitString → Prop
  | [], _ => False
  | literal :: rest, assignment =>
      literal.Holds assignment ∨ Holds rest assignment

def AllHold {width : Nat} : BoundedClause width → BitString → Prop
  | [], _ => True
  | literal :: rest, assignment =>
      literal.Holds assignment ∧ AllHold rest assignment

def negated {width : Nat} (clause : BoundedClause width) :
    BoundedClause width :=
  clause.map BoundedLiteral.negate

theorem emit_length {width : Nat} (clause : BoundedClause width) :
    (emit clause).length = clause.length := by
  induction clause with
  | nil => rfl
  | cons literal rest ih =>
      change Nat.succ (emit rest).length = Nat.succ rest.length
      exact congrArg Nat.succ ih

theorem emitted_variable_lt {width : Nat} (clause : BoundedClause width)
    (literal : CNFLiteral) (hLiteral : literal ∈ emit clause) :
    literal.variableIndex < width := by
  induction clause with
  | nil => cases hLiteral
  | cons first rest ih =>
      cases hLiteral with
      | head => exact first.emit_variable_lt
      | tail _ hTail => exact ih hTail

theorem emit_satisfied_iff {width : Nat} (clause : BoundedClause width)
    (assignment : BitString) :
    ClauseSatisfied (emit clause) assignment ↔ Holds clause assignment := by
  induction clause with
  | nil => exact Iff.rfl
  | cons literal rest ih =>
      change
        (literal.Holds assignment ∨ ClauseSatisfied (emit rest) assignment) ↔
          (literal.Holds assignment ∨ Holds rest assignment)
      constructor
      · intro satisfied
        cases satisfied with
        | inl hLiteral => exact Or.inl hLiteral
        | inr hRest => exact Or.inr (ih.mp hRest)
      · intro satisfied
        cases satisfied with
        | inl hLiteral => exact Or.inl hLiteral
        | inr hRest => exact Or.inr (ih.mpr hRest)

theorem holds_append {width : Nat} (left right : BoundedClause width)
    (assignment : BitString) :
    Holds (left ++ right) assignment ↔
      Holds left assignment ∨ Holds right assignment := by
  induction left with
  | nil =>
      constructor
      · intro hRight
        exact Or.inr hRight
      · intro disjunction
        cases disjunction with
        | inl impossible => exact False.elim impossible
        | inr hRight => exact hRight
  | cons literal rest ih =>
      change
        (literal.Holds assignment ∨ Holds (rest ++ right) assignment) ↔
          (literal.Holds assignment ∨ Holds rest assignment) ∨
            Holds right assignment
      constructor
      · intro disjunction
        cases disjunction with
        | inl hLiteral => exact Or.inl (Or.inl hLiteral)
        | inr hTail =>
            cases ih.mp hTail with
            | inl hRest => exact Or.inl (Or.inr hRest)
            | inr hRight => exact Or.inr hRight
      · intro disjunction
        cases disjunction with
        | inl hLeft =>
            cases hLeft with
            | inl hLiteral => exact Or.inl hLiteral
            | inr hRest => exact Or.inr (ih.mpr (Or.inl hRest))
        | inr hRight => exact Or.inr (ih.mpr (Or.inr hRight))

theorem singleton_holds_iff {width : Nat} (literal : BoundedLiteral width)
    (assignment : BitString) :
    Holds ([literal] : BoundedClause width) assignment ↔
      literal.Holds assignment := by
  constructor
  · intro satisfied
    cases satisfied with
    | inl hLiteral => exact hLiteral
    | inr impossible => exact False.elim impossible
  · intro hLiteral
    exact Or.inl hLiteral

theorem negated_holds_iff_not_allHold {width : Nat}
    (clause : BoundedClause width) (assignment : BitString)
    (hLength : assignment.length = width) :
    Holds (negated clause) assignment ↔ ¬ AllHold clause assignment := by
  induction clause with
  | nil =>
      constructor
      · intro impossible
        exact False.elim impossible
      · intro notTrue
        exact False.elim (notTrue True.intro)
  | cons literal rest ih =>
      change
        (literal.negate.Holds assignment ∨ Holds (negated rest) assignment) ↔
          ¬ (literal.Holds assignment ∧ AllHold rest assignment)
      constructor
      · intro disjunction conjunction
        cases disjunction with
        | inl hNegated =>
            exact (BoundedLiteral.negate_holds_iff_not literal assignment
              hLength).mp hNegated conjunction.left
        | inr hRest => exact ih.mp hRest conjunction.right
      · intro notAll
        cases BoundedLiteral.holds_or_negate_holds literal assignment hLength with
        | inl hLiteral =>
            exact Or.inr (ih.mpr (fun hRest =>
              notAll ⟨hLiteral, hRest⟩))
        | inr hNegated => exact Or.inl hNegated

theorem allHold_or_negated_holds {width : Nat}
    (clause : BoundedClause width) (assignment : BitString)
    (hLength : assignment.length = width) :
    AllHold clause assignment ∨ Holds (negated clause) assignment := by
  induction clause with
  | nil => exact Or.inl True.intro
  | cons literal rest ih =>
      cases BoundedLiteral.holds_or_negate_holds literal assignment hLength with
      | inr hNegated => exact Or.inr (Or.inl hNegated)
      | inl hLiteral =>
          cases ih with
          | inl hRest => exact Or.inl ⟨hLiteral, hRest⟩
          | inr hRest => exact Or.inr (Or.inr hRest)

end BoundedClause

namespace BoundedClauses

def emit {width : Nat} (clauses : BoundedClauses width) :
    List (List CNFLiteral) :=
  clauses.map BoundedClause.emit

def Holds {width : Nat} : BoundedClauses width → BitString → Prop
  | [], _ => True
  | clause :: rest, assignment =>
      clause.Holds assignment ∧ Holds rest assignment

theorem emit_length {width : Nat} (clauses : BoundedClauses width) :
    (emit clauses).length = clauses.length := by
  induction clauses with
  | nil => rfl
  | cons clause rest ih =>
      change Nat.succ (emit rest).length = Nat.succ rest.length
      exact congrArg Nat.succ ih

theorem emitted_variable_lt {width : Nat} (clauses : BoundedClauses width)
    (clause : List CNFLiteral) (hClause : clause ∈ emit clauses)
    (literal : CNFLiteral) (hLiteral : literal ∈ clause) :
    literal.variableIndex < width := by
  induction clauses with
  | nil => cases hClause
  | cons first rest ih =>
      cases hClause with
      | head => exact BoundedClause.emitted_variable_lt first literal hLiteral
      | tail _ hTail => exact ih hTail

theorem emit_satisfied_iff {width : Nat} (clauses : BoundedClauses width)
    (assignment : BitString) :
    ClausesSatisfied (emit clauses) assignment ↔ Holds clauses assignment := by
  induction clauses with
  | nil => exact Iff.rfl
  | cons clause rest ih =>
      change
        (ClauseSatisfied (BoundedClause.emit clause) assignment ∧
          ClausesSatisfied (emit rest) assignment) ↔
        (BoundedClause.Holds clause assignment ∧ Holds rest assignment)
      constructor
      · intro satisfied
        exact ⟨(BoundedClause.emit_satisfied_iff clause assignment).mp
          satisfied.left, ih.mp satisfied.right⟩
      · intro satisfied
        exact ⟨(BoundedClause.emit_satisfied_iff clause assignment).mpr
          satisfied.left, ih.mpr satisfied.right⟩

theorem holds_append {width : Nat} (left right : BoundedClauses width)
    (assignment : BitString) :
    Holds (left ++ right) assignment ↔
      Holds left assignment ∧ Holds right assignment := by
  induction left with
  | nil =>
      constructor
      · intro hRight
        exact ⟨True.intro, hRight⟩
      · intro conjunction
        exact conjunction.right
  | cons clause rest ih =>
      change
        (BoundedClause.Holds clause assignment ∧
          Holds (rest ++ right) assignment) ↔
          (BoundedClause.Holds clause assignment ∧ Holds rest assignment) ∧
            Holds right assignment
      constructor
      · intro conjunction
        have tail := ih.mp conjunction.right
        exact ⟨⟨conjunction.left, tail.left⟩, tail.right⟩
      · intro conjunction
        exact ⟨conjunction.left.left,
          ih.mpr ⟨conjunction.left.right, conjunction.right⟩⟩

theorem length_append {width : Nat} (left right : BoundedClauses width) :
    (left ++ right).length = left.length + right.length := by
  induction left with
  | nil => exact (Nat.zero_add right.length).symm
  | cons clause rest ih =>
      change Nat.succ (rest ++ right).length =
        Nat.succ rest.length + right.length
      rw [Nat.succ_add]
      exact congrArg Nat.succ ih

end BoundedClauses

/-! ### Unit and implication emitters -/

def unitClauses {width : Nat} (literal : BoundedLiteral width) :
    BoundedClauses width :=
  [[literal]]

def implicationClause {width : Nat} (premises : BoundedClause width)
    (conclusion : BoundedLiteral width) : BoundedClause width :=
  BoundedClause.negated premises ++ [conclusion]

def implicationClauses {width : Nat} (premises : BoundedClause width)
    (conclusion : BoundedLiteral width) : BoundedClauses width :=
  [implicationClause premises conclusion]

theorem unitClauses_holds_iff {width : Nat}
    (literal : BoundedLiteral width) (assignment : BitString) :
    BoundedClauses.Holds (unitClauses literal) assignment ↔
      literal.Holds assignment := by
  constructor
  · intro satisfied
    exact (BoundedClause.singleton_holds_iff literal assignment).mp
      satisfied.left
  · intro hLiteral
    exact ⟨(BoundedClause.singleton_holds_iff literal assignment).mpr hLiteral,
      True.intro⟩

theorem implicationClauses_holds_iff {width : Nat}
    (premises : BoundedClause width) (conclusion : BoundedLiteral width)
    (assignment : BitString) (hLength : assignment.length = width) :
    BoundedClauses.Holds (implicationClauses premises conclusion) assignment ↔
      (BoundedClause.AllHold premises assignment →
        conclusion.Holds assignment) := by
  have clauseSplit := BoundedClause.holds_append
    (BoundedClause.negated premises)
    ([conclusion] : BoundedClause width) assignment
  constructor
  · intro satisfied hPremises
    have clauseHolds := satisfied.left
    cases clauseSplit.mp clauseHolds with
    | inl hNegated =>
        exact False.elim
          ((BoundedClause.negated_holds_iff_not_allHold premises assignment
            hLength).mp hNegated hPremises)
    | inr hConclusion =>
        exact (BoundedClause.singleton_holds_iff conclusion assignment).mp
          hConclusion
  · intro implication
    refine ⟨?_, True.intro⟩
    apply clauseSplit.mpr
    cases BoundedClause.allHold_or_negated_holds premises assignment hLength with
    | inl hPremises =>
        exact Or.inr
          ((BoundedClause.singleton_holds_iff conclusion assignment).mpr
            (implication hPremises))
    | inr hNegated => exact Or.inl hNegated

/-! ### Pairwise exactly-one emitter -/

def trueLiteral {width : Nat} (index : Fin width) :
    BoundedLiteral width :=
  { positive := true, index := index }

def falseLiteral {width : Nat} (index : Fin width) :
    BoundedLiteral width :=
  { positive := false, index := index }

def atLeastOneBoundedClause {width : Nat} (variables : List (Fin width)) :
    BoundedClause width :=
  variables.map trueLiteral

def excludeBoundedPairClause {width : Nat} (left right : Fin width) :
    BoundedClause width :=
  [falseLiteral left, falseLiteral right]

def excludeBoundedWithClauses {width : Nat} (first : Fin width) :
    List (Fin width) → BoundedClauses width
  | [] => []
  | next :: rest =>
      excludeBoundedPairClause first next ::
        excludeBoundedWithClauses first rest

def atMostOneBoundedClauses {width : Nat} :
    List (Fin width) → BoundedClauses width
  | [] => []
  | first :: rest =>
      excludeBoundedWithClauses first rest ++
        atMostOneBoundedClauses rest

def exactlyOneBoundedClauses {width : Nat} (variables : List (Fin width)) :
    BoundedClauses width :=
  atLeastOneBoundedClause variables :: atMostOneBoundedClauses variables

def AnyTrue {width : Nat} (variables : List (Fin width))
    (assignment : BitString) : Prop :=
  ∃ index, index ∈ variables ∧
    (trueLiteral index).Holds assignment

def AtMostOneTrue {width : Nat} : List (Fin width) → BitString → Prop
  | [], _ => True
  | first :: rest, assignment =>
      (∀ next, next ∈ rest →
        ¬ ((trueLiteral first).Holds assignment ∧
          (trueLiteral next).Holds assignment)) ∧
        AtMostOneTrue rest assignment

def ExactlyOneTrue {width : Nat} (variables : List (Fin width))
    (assignment : BitString) : Prop :=
  AnyTrue variables assignment ∧ AtMostOneTrue variables assignment

theorem falseLiteral_eq_negate_trueLiteral {width : Nat}
    (index : Fin width) :
    falseLiteral index = (trueLiteral index).negate := rfl

theorem atLeastOneBoundedClause_holds_iff {width : Nat}
    (variables : List (Fin width)) (assignment : BitString) :
    BoundedClause.Holds (atLeastOneBoundedClause variables) assignment ↔
      AnyTrue variables assignment := by
  induction variables with
  | nil =>
      constructor
      · intro impossible
        exact False.elim impossible
      · intro witness
        rcases witness with ⟨index, hMem, _⟩
        cases hMem
  | cons first rest ih =>
      change
        ((trueLiteral first).Holds assignment ∨
          BoundedClause.Holds (atLeastOneBoundedClause rest) assignment) ↔
        ∃ index, index ∈ first :: rest ∧
          (trueLiteral index).Holds assignment
      constructor
      · intro disjunction
        cases disjunction with
        | inl hFirst => exact ⟨first, List.Mem.head rest, hFirst⟩
        | inr hRest =>
            rcases ih.mp hRest with ⟨index, hMem, hValue⟩
            exact ⟨index, List.Mem.tail first hMem, hValue⟩
      · intro witness
        rcases witness with ⟨index, hMem, hValue⟩
        cases hMem with
        | head => exact Or.inl hValue
        | tail _ hTail => exact Or.inr (ih.mpr ⟨index, hTail, hValue⟩)

theorem excludeBoundedPairClause_holds_iff {width : Nat}
    (left right : Fin width) (assignment : BitString)
    (hLength : assignment.length = width) :
    BoundedClause.Holds (excludeBoundedPairClause left right) assignment ↔
      ¬ ((trueLiteral left).Holds assignment ∧
        (trueLiteral right).Holds assignment) := by
  constructor
  · intro satisfied bothTrue
    cases satisfied with
    | inl hLeftFalse =>
        rw [falseLiteral_eq_negate_trueLiteral] at hLeftFalse
        exact (BoundedLiteral.negate_holds_iff_not
          (trueLiteral left) assignment hLength).mp hLeftFalse bothTrue.left
    | inr tail =>
        cases tail with
        | inl hRightFalse =>
            rw [falseLiteral_eq_negate_trueLiteral] at hRightFalse
            exact (BoundedLiteral.negate_holds_iff_not
              (trueLiteral right) assignment hLength).mp hRightFalse
                bothTrue.right
        | inr impossible => exact False.elim impossible
  · intro notBoth
    cases BoundedLiteral.holds_or_negate_holds
        (trueLiteral left) assignment hLength with
    | inr hLeftFalse =>
        exact Or.inl (falseLiteral_eq_negate_trueLiteral left ▸ hLeftFalse)
    | inl hLeftTrue =>
        cases BoundedLiteral.holds_or_negate_holds
            (trueLiteral right) assignment hLength with
        | inr hRightFalse =>
            exact Or.inr (Or.inl
              (falseLiteral_eq_negate_trueLiteral right ▸ hRightFalse))
        | inl hRightTrue =>
            exact False.elim (notBoth ⟨hLeftTrue, hRightTrue⟩)

theorem excludeBoundedWithClauses_holds_iff {width : Nat}
    (first : Fin width) (rest : List (Fin width))
    (assignment : BitString) (hLength : assignment.length = width) :
    BoundedClauses.Holds (excludeBoundedWithClauses first rest) assignment ↔
      ∀ next, next ∈ rest →
        ¬ ((trueLiteral first).Holds assignment ∧
          (trueLiteral next).Holds assignment) := by
  induction rest with
  | nil =>
      constructor
      · intro _ next hMem
        cases hMem
      · intro _
        exact True.intro
  | cons next rest ih =>
      change
        (BoundedClause.Holds (excludeBoundedPairClause first next) assignment ∧
          BoundedClauses.Holds (excludeBoundedWithClauses first rest)
            assignment) ↔
        ∀ candidate, candidate ∈ next :: rest →
          ¬ ((trueLiteral first).Holds assignment ∧
            (trueLiteral candidate).Holds assignment)
      constructor
      · intro conjunction candidate hMem
        cases hMem with
        | head =>
            exact (excludeBoundedPairClause_holds_iff first next assignment
              hLength).mp conjunction.left
        | tail _ hTail => exact ih.mp conjunction.right candidate hTail
      · intro allPairs
        exact ⟨(excludeBoundedPairClause_holds_iff first next assignment
            hLength).mpr (allPairs next (List.Mem.head rest)),
          ih.mpr (fun candidate hMem =>
            allPairs candidate (List.Mem.tail next hMem))⟩

theorem atMostOneBoundedClauses_holds_iff {width : Nat}
    (variables : List (Fin width)) (assignment : BitString)
    (hLength : assignment.length = width) :
    BoundedClauses.Holds (atMostOneBoundedClauses variables) assignment ↔
      AtMostOneTrue variables assignment := by
  induction variables with
  | nil => exact Iff.rfl
  | cons first rest ih =>
      change
        BoundedClauses.Holds
          (excludeBoundedWithClauses first rest ++
            atMostOneBoundedClauses rest) assignment ↔
        ((∀ next, next ∈ rest →
          ¬ ((trueLiteral first).Holds assignment ∧
            (trueLiteral next).Holds assignment)) ∧
          AtMostOneTrue rest assignment)
      constructor
      · intro satisfied
        have split := (BoundedClauses.holds_append
          (excludeBoundedWithClauses first rest)
          (atMostOneBoundedClauses rest) assignment).mp satisfied
        exact ⟨(excludeBoundedWithClauses_holds_iff first rest assignment
            hLength).mp split.left,
          ih.mp split.right⟩
      · intro semantic
        apply (BoundedClauses.holds_append
          (excludeBoundedWithClauses first rest)
          (atMostOneBoundedClauses rest) assignment).mpr
        exact ⟨(excludeBoundedWithClauses_holds_iff first rest assignment
            hLength).mpr semantic.left,
          ih.mpr semantic.right⟩

theorem exactlyOneBoundedClauses_holds_iff {width : Nat}
    (variables : List (Fin width)) (assignment : BitString)
    (hLength : assignment.length = width) :
    BoundedClauses.Holds (exactlyOneBoundedClauses variables) assignment ↔
      ExactlyOneTrue variables assignment := by
  change
    (BoundedClause.Holds (atLeastOneBoundedClause variables) assignment ∧
      BoundedClauses.Holds (atMostOneBoundedClauses variables) assignment) ↔
    (AnyTrue variables assignment ∧ AtMostOneTrue variables assignment)
  constructor
  · intro satisfied
    exact ⟨(atLeastOneBoundedClause_holds_iff variables assignment).mp
        satisfied.left,
      (atMostOneBoundedClauses_holds_iff variables assignment hLength).mp
        satisfied.right⟩
  · intro semantic
    exact ⟨(atLeastOneBoundedClause_holds_iff variables assignment).mpr
        semantic.left,
      (atMostOneBoundedClauses_holds_iff variables assignment hLength).mpr
        semantic.right⟩

/-! ### Finite local-constraint syntax and compiler -/

inductive LocalConstraint (width : Nat) where
  | require (literal : BoundedLiteral width)
  | implication (premises : BoundedClause width)
      (conclusion : BoundedLiteral width)
  | exactlyOne (variables : List (Fin width))
deriving Repr

namespace LocalConstraint

def emit {width : Nat} : LocalConstraint width → BoundedClauses width
  | .require literal => unitClauses literal
  | .implication premises conclusion => implicationClauses premises conclusion
  | .exactlyOne variables => exactlyOneBoundedClauses variables

def Holds {width : Nat} : LocalConstraint width → BitString → Prop
  | .require literal, assignment => literal.Holds assignment
  | .implication premises conclusion, assignment =>
      BoundedClause.AllHold premises assignment → conclusion.Holds assignment
  | .exactlyOne variables, assignment => ExactlyOneTrue variables assignment

def pairCount : Nat → Nat
  | 0 => 0
  | count + 1 => count + pairCount count

def clauseCount {width : Nat} : LocalConstraint width → Nat
  | .require _ => 1
  | .implication _ _ => 1
  | .exactlyOne variables => 1 + pairCount variables.length

theorem excludeBoundedWithClauses_length {width : Nat}
    (first : Fin width) (rest : List (Fin width)) :
    (excludeBoundedWithClauses first rest).length = rest.length := by
  induction rest with
  | nil => rfl
  | cons next rest ih =>
      change Nat.succ (excludeBoundedWithClauses first rest).length =
        Nat.succ rest.length
      exact congrArg Nat.succ ih

theorem atMostOneBoundedClauses_length {width : Nat}
    (variables : List (Fin width)) :
    (atMostOneBoundedClauses variables).length =
      pairCount variables.length := by
  induction variables with
  | nil => rfl
  | cons first rest ih =>
      change
        (excludeBoundedWithClauses first rest ++
          atMostOneBoundedClauses rest).length =
        rest.length + pairCount rest.length
      calc
        (excludeBoundedWithClauses first rest ++
            atMostOneBoundedClauses rest).length =
            (excludeBoundedWithClauses first rest).length +
              (atMostOneBoundedClauses rest).length :=
          BoundedClauses.length_append _ _
        _ = rest.length + (atMostOneBoundedClauses rest).length :=
          congrArg (fun count => count +
            (atMostOneBoundedClauses rest).length)
              (excludeBoundedWithClauses_length first rest)
        _ = rest.length + pairCount rest.length :=
          congrArg (Nat.add rest.length) ih

theorem exactlyOneBoundedClauses_length {width : Nat}
    (variables : List (Fin width)) :
    (exactlyOneBoundedClauses variables).length =
      1 + pairCount variables.length := by
  change Nat.succ (atMostOneBoundedClauses variables).length =
    1 + pairCount variables.length
  rw [atMostOneBoundedClauses_length, Nat.one_add]

theorem emit_length {width : Nat} (constraint : LocalConstraint width) :
    (emit constraint).length = clauseCount constraint := by
  cases constraint with
  | require literal => rfl
  | implication premises conclusion => rfl
  | exactlyOne variables => exact exactlyOneBoundedClauses_length variables

theorem emit_holds_iff {width : Nat} (constraint : LocalConstraint width)
    (assignment : BitString) (hLength : assignment.length = width) :
    BoundedClauses.Holds (emit constraint) assignment ↔
      Holds constraint assignment := by
  cases constraint with
  | require literal => exact unitClauses_holds_iff literal assignment
  | implication premises conclusion =>
      exact implicationClauses_holds_iff premises conclusion assignment hLength
  | exactlyOne variables =>
      exact exactlyOneBoundedClauses_holds_iff variables assignment hLength

end LocalConstraint

abbrev LocalProgram (width : Nat) := List (LocalConstraint width)

namespace LocalProgram

def emit {width : Nat} : LocalProgram width → BoundedClauses width
  | [] => []
  | constraint :: rest => LocalConstraint.emit constraint ++ emit rest

def Holds {width : Nat} : LocalProgram width → BitString → Prop
  | [], _ => True
  | constraint :: rest, assignment =>
      LocalConstraint.Holds constraint assignment ∧ Holds rest assignment

def clauseCount {width : Nat} : LocalProgram width → Nat
  | [] => 0
  | constraint :: rest =>
      LocalConstraint.clauseCount constraint + clauseCount rest

def toFormula {width : Nat} (program : LocalProgram width) : CNFFormula :=
  { variableCount := width, clauses := BoundedClauses.emit (emit program) }

theorem emit_length {width : Nat} (program : LocalProgram width) :
    (emit program).length = clauseCount program := by
  induction program with
  | nil => rfl
  | cons constraint rest ih =>
      change
        (LocalConstraint.emit constraint ++ emit rest).length =
          LocalConstraint.clauseCount constraint + clauseCount rest
      calc
        (LocalConstraint.emit constraint ++ emit rest).length =
            (LocalConstraint.emit constraint).length +
              (emit rest).length :=
          BoundedClauses.length_append _ _
        _ = LocalConstraint.clauseCount constraint +
              (emit rest).length :=
          congrArg (fun count => count + (emit rest).length)
            (LocalConstraint.emit_length constraint)
        _ = LocalConstraint.clauseCount constraint + clauseCount rest :=
          congrArg (Nat.add (LocalConstraint.clauseCount constraint)) ih

theorem emitted_clause_count {width : Nat} (program : LocalProgram width) :
    (toFormula program).clauses.length = clauseCount program := by
  unfold toFormula
  rw [BoundedClauses.emit_length, emit_length]

theorem emit_holds_iff {width : Nat} (program : LocalProgram width)
    (assignment : BitString) (hLength : assignment.length = width) :
    BoundedClauses.Holds (emit program) assignment ↔
      Holds program assignment := by
  induction program with
  | nil => exact Iff.rfl
  | cons constraint rest ih =>
      change
        BoundedClauses.Holds
          (LocalConstraint.emit constraint ++ emit rest) assignment ↔
          (LocalConstraint.Holds constraint assignment ∧
            Holds rest assignment)
      constructor
      · intro satisfied
        have split := (BoundedClauses.holds_append
          (LocalConstraint.emit constraint) (emit rest) assignment).mp satisfied
        exact ⟨(LocalConstraint.emit_holds_iff constraint assignment hLength).mp
            split.left,
          ih.mp split.right⟩
      · intro semantic
        apply (BoundedClauses.holds_append
          (LocalConstraint.emit constraint) (emit rest) assignment).mpr
        exact ⟨(LocalConstraint.emit_holds_iff constraint assignment hLength).mpr
            semantic.left,
          ih.mpr semantic.right⟩

theorem toFormula_satisfied_iff {width : Nat} (program : LocalProgram width)
    (assignment : BitString) :
    (toFormula program).Satisfied assignment ↔
      assignment.length = width ∧ Holds program assignment := by
  unfold CNFFormula.Satisfied toFormula
  constructor
  · intro satisfied
    exact ⟨satisfied.left,
      (emit_holds_iff program assignment satisfied.left).mp
        ((BoundedClauses.emit_satisfied_iff (emit program) assignment).mp
          satisfied.right)⟩
  · intro semantic
    exact ⟨semantic.left,
      (BoundedClauses.emit_satisfied_iff (emit program) assignment).mpr
        ((emit_holds_iff program assignment semantic.left).mpr
          semantic.right)⟩

theorem toFormula_satisfiable_iff {width : Nat}
    (program : LocalProgram width) :
    (toFormula program).Satisfiable ↔
      ∃ assignment, assignment.length = width ∧ Holds program assignment := by
  constructor
  · intro satisfiable
    rcases satisfiable with ⟨assignment, hSatisfied⟩
    exact ⟨assignment,
      (toFormula_satisfied_iff program assignment).mp hSatisfied⟩
  · intro witness
    rcases witness with ⟨assignment, hAssignment⟩
    exact ⟨assignment,
      (toFormula_satisfied_iff program assignment).mpr hAssignment⟩

end LocalProgram

/-- Every emitted literal index is strictly below the formula's declared
variable count. -/
def FormulaWellScoped (formula : CNFFormula) : Prop :=
  ∀ clause, clause ∈ formula.clauses →
    ∀ literal, literal ∈ clause →
      literal.variableIndex < formula.variableCount

theorem localProgram_formula_wellScoped {width : Nat}
    (program : LocalProgram width) :
    FormulaWellScoped (LocalProgram.toFormula program) := by
  intro clause hClause literal hLiteral
  exact BoundedClauses.emitted_variable_lt
    (LocalProgram.emit program) clause hClause literal hLiteral

end CookLevin

end PNP.Concrete

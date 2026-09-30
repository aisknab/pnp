import PNP.NANDNormalizationAbstractValue

set_option autoImplicit false

/-!
Proof-side symbolic NAND expressions. The relation identifies only structural
commutation, recursively; it is not Boolean-function equivalence. Literal
constant identities are performed by the constructor. Expanded terms are proof
objects, not a claimed polynomial executable representation.
-/

namespace PNP.DirectWire.NormalizationTerm

inductive Term where
  | constant (bit : Bool)
  | input (index : Nat)
  | node (left right : Term)
  deriving DecidableEq, Repr

/-- Unordered structural equality, without arbitrary Boolean simplification. -/
def Related : Term → Term → Prop
  | .constant left, .constant right => left = right
  | .input left, .input right => left = right
  | .node left right, .node otherLeft otherRight =>
      (Related left otherLeft ∧ Related right otherRight) ∨
        (Related left otherRight ∧ Related right otherLeft)
  | _, _ => False

namespace Related

theorem refl (term : Term) : Related term term := by
  induction term with
  | constant bit => rfl
  | input index => rfl
  | node left right ihLeft ihRight => exact Or.inl ⟨ihLeft, ihRight⟩

theorem symm {left right : Term} (related : Related left right) : Related right left := by
  induction left generalizing right with
  | constant bit =>
      cases right with
      | constant other => exact Eq.symm related
      | input index => exact False.elim related
      | node a b => exact False.elim related
  | input index =>
      cases right with
      | constant bit => exact False.elim related
      | input other => exact Eq.symm related
      | node a b => exact False.elim related
  | node childLeft childRight ihLeft ihRight =>
      cases right with
      | constant bit => exact False.elim related
      | input index => exact False.elim related
      | node a b =>
          rcases related with ⟨la, rb⟩ | ⟨lb, ra⟩
          · exact Or.inl ⟨ihLeft la, ihRight rb⟩
          · exact Or.inr ⟨ihRight ra, ihLeft lb⟩

theorem trans {first middle last : Term}
    (one : Related first middle) (two : Related middle last) : Related first last := by
  induction first generalizing middle last with
  | constant bit =>
      cases middle with
      | constant other =>
          cases last with
          | constant final => exact Eq.trans one two
          | input index => exact False.elim two
          | node a b => exact False.elim two
      | input index => exact False.elim one
      | node a b => exact False.elim one
  | input index =>
      cases middle with
      | constant bit => exact False.elim one
      | input other =>
          cases last with
          | constant bit => exact False.elim two
          | input final => exact Eq.trans one two
          | node a b => exact False.elim two
      | node a b => exact False.elim one
  | node left right ihLeft ihRight =>
      cases middle with
      | constant bit => exact False.elim one
      | input index => exact False.elim one
      | node ml mr =>
          cases last with
          | constant bit => exact False.elim two
          | input index => exact False.elim two
          | node ll lr =>
              rcases one with ⟨leftMiddle, rightMiddle⟩ | ⟨leftMiddle, rightMiddle⟩
              · rcases two with ⟨middleLeft, middleRight⟩ | ⟨middleLeft, middleRight⟩
                · exact Or.inl ⟨ihLeft leftMiddle middleLeft, ihRight rightMiddle middleRight⟩
                · exact Or.inr ⟨ihLeft leftMiddle middleLeft, ihRight rightMiddle middleRight⟩
              · rcases two with ⟨middleLeft, middleRight⟩ | ⟨middleLeft, middleRight⟩
                · exact Or.inr ⟨ihLeft leftMiddle middleRight, ihRight rightMiddle middleLeft⟩
                · exact Or.inl ⟨ihLeft leftMiddle middleRight, ihRight rightMiddle middleLeft⟩

theorem constant_left {term : Term} {bit : Bool} (related : Related (.constant bit) term) :
    term = .constant bit := by
  cases term with
  | constant other => exact congrArg Term.constant (Eq.symm related)
  | input index => exact False.elim related
  | node left right => exact False.elim related

theorem constant_iff {left right : Term} (related : Related left right) (bit : Bool) :
    left = .constant bit ↔ right = .constant bit := by
  constructor
  · intro same
    rw [same] at related
    exact constant_left related
  · intro same
    have reversed := symm related
    rw [same] at reversed
    exact constant_left reversed

end Related

/-- Exactly the literal constant compiler's identities; otherwise retain the node. -/
def nand (left right : Term) : Term :=
  if left = .constant false ∨ right = .constant false then .constant true
  else if left = .constant true ∧ right = .constant true then .constant false
  else .node left right

theorem nand_false_left (right : Term) : nand (.constant false) right = .constant true := by
  unfold nand
  rw [if_pos (Or.inl rfl)]

theorem nand_false_right (left : Term) : nand left (.constant false) = .constant true := by
  unfold nand
  rw [if_pos (Or.inr rfl)]

theorem nand_true_true : nand (.constant true) (.constant true) = .constant false := by
  simp only [nand, Term.constant.injEq, Bool.true_eq_false, or_self, if_false,
    and_self, if_true]

theorem nand_comm (left right : Term) : Related (nand left right) (nand right left) := by
  unfold nand
  by_cases oneFalse : left = .constant false ∨ right = .constant false
  · rw [if_pos oneFalse, if_pos oneFalse.symm]
    exact Related.refl _
  · have otherNotFalse : ¬(right = .constant false ∨ left = .constant false) :=
      fun swapped => oneFalse swapped.symm
    rw [if_neg oneFalse, if_neg otherNotFalse]
    by_cases bothTrue : left = .constant true ∧ right = .constant true
    · rw [if_pos bothTrue, if_pos bothTrue.symm]
      exact Related.refl _
    · have otherNotTrue : ¬(right = .constant true ∧ left = .constant true) :=
        fun swapped => bothTrue swapped.symm
      rw [if_neg bothTrue, if_neg otherNotTrue]
      exact Or.inr ⟨Related.refl left, Related.refl right⟩

theorem nand_congr {left right otherLeft otherRight : Term}
    (leftRelated : Related left otherLeft) (rightRelated : Related right otherRight) :
    Related (nand left right) (nand otherLeft otherRight) := by
  have leftFalse := Related.constant_iff leftRelated false
  have rightFalse := Related.constant_iff rightRelated false
  have leftTrue := Related.constant_iff leftRelated true
  have rightTrue := Related.constant_iff rightRelated true
  unfold nand
  by_cases oneFalse : left = .constant false ∨ right = .constant false
  · have otherFalse : otherLeft = .constant false ∨ otherRight = .constant false := by
      rcases oneFalse with left | right
      · exact Or.inl (leftFalse.mp left)
      · exact Or.inr (rightFalse.mp right)
    rw [if_pos oneFalse, if_pos otherFalse]
    exact Related.refl _
  · have otherNotFalse : ¬(otherLeft = .constant false ∨ otherRight = .constant false) := by
      intro someFalse
      rcases someFalse with left | right
      · exact oneFalse (Or.inl (leftFalse.mpr left))
      · exact oneFalse (Or.inr (rightFalse.mpr right))
    rw [if_neg oneFalse, if_neg otherNotFalse]
    by_cases bothTrue : left = .constant true ∧ right = .constant true
    · rw [if_pos bothTrue, if_pos ⟨leftTrue.mp bothTrue.1, rightTrue.mp bothTrue.2⟩]
      exact Related.refl _
    · have otherNotTrue : ¬(otherLeft = .constant true ∧ otherRight = .constant true) := by
        intro other
        exact bothTrue ⟨leftTrue.mpr other.1, rightTrue.mpr other.2⟩
      rw [if_neg bothTrue, if_neg otherNotTrue]
      exact Or.inl ⟨leftRelated, rightRelated⟩

/-- Interpretation into Booleans is a consequence, not the definition of Related. -/
def value (valuation : Nat → Bool) : Term → Bool
  | .constant bit => bit
  | .input index => valuation index
  | .node left right => boolNand (value valuation left) (value valuation right)

theorem related_value {left right : Term} (related : Related left right)
    (valuation : Nat → Bool) : value valuation left = value valuation right := by
  induction left generalizing right with
  | constant bit =>
      cases right with
      | constant other => exact related
      | input index => exact False.elim related
      | node a b => exact False.elim related
  | input index =>
      cases right with
      | constant bit => exact False.elim related
      | input other => exact congrArg valuation related
      | node a b => exact False.elim related
  | node childLeft childRight ihLeft ihRight =>
      cases right with
      | constant bit => exact False.elim related
      | input index => exact False.elim related
      | node a b =>
          change boolNand (value valuation childLeft) (value valuation childRight) =
            boolNand (value valuation a) (value valuation b)
          rcases related with ⟨la, rb⟩ | ⟨lb, ra⟩
          · rw [ihLeft la, ihRight rb]
          · rw [ihLeft lb, ihRight ra]
            cases value valuation a <;> cases value valuation b <;> rfl

/-- A finite structural check for small probes; no polynomial tree-size claim. -/
def relatedCheck : Term → Term → Bool
  | .constant left, .constant right => left == right
  | .input left, .input right => left == right
  | .node left right, .node otherLeft otherRight =>
      (relatedCheck left otherLeft && relatedCheck right otherRight) ||
        (relatedCheck left otherRight && relatedCheck right otherLeft)
  | _, _ => false

theorem relatedCheck_iff (left right : Term) :
    relatedCheck left right = true ↔ Related left right := by
  induction left generalizing right with
  | constant bit =>
      cases right <;> simp only [relatedCheck, Related, beq_iff_eq, Bool.false_eq_true]
  | input index =>
      cases right <;> simp only [relatedCheck, Related, beq_iff_eq, Bool.false_eq_true]
  | node childLeft childRight ihLeft ihRight =>
      cases right <;> simp only [relatedCheck, Related, Bool.false_eq_true,
        Bool.or_eq_true, Bool.and_eq_true, ihLeft, ihRight]

theorem nand_value (left right : Term) (valuation : Nat → Bool) :
    value valuation (nand left right) = boolNand (value valuation left) (value valuation right) := by
  unfold nand
  split
  next oneFalse =>
    rcases oneFalse with leftAt | rightAt
    · rw [leftAt]
      cases value valuation right <;> rfl
    · rw [rightAt]
      cases value valuation left <;> rfl
  next neitherFalse =>
    split
    next bothTrue => rw [bothTrue.1, bothTrue.2]; rfl
    next neitherTrue => rfl

end PNP.DirectWire.NormalizationTerm

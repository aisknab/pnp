import PNP.NANDDemandForest

set_option autoImplicit false
set_option Elab.async false

/-! Read-once semantics for the actual raw demand expansion. The structural
hypotheses are explicit; no correctness certificate or size bound is supplied. -/

namespace PNP.DirectWire.ReadOnceTerm
open NormalizationTerm (Term value)
open DemandForest (constants expression expand extendInput)

variable {inputs gates : Nat}

def variables : Term → List Nat
  | .constant _ => []
  | .input index => [index]
  | .node left right => variables left ++ variables right

/-- The occurrence list uses exactly the already verified forest weighting. -/
theorem variables_weight (weights : Nat → Nat) (term : Term) :
    DemandForest.variableWeight weights term = ((variables term).map weights).sum := by
  induction term with
  | constant bit => rfl
  | input index =>
      simp only [DemandForest.variableWeight,variables,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,Nat.add_zero]
  | node left right ihLeft ihRight =>
      simp only [DemandForest.variableWeight,variables,List.map_append,List.sum_append,
        ihLeft,ihRight]

theorem value_congr (term : Term) (left right : Nat → Bool)
    (agree : ∀ index, index ∈ variables term → left index = right index) :
    value left term = value right term := by
  induction term with
  | constant bit => rfl
  | input index => exact agree index List.mem_cons_self
  | node first second ihFirst ihSecond =>
      change boolNand (value left first) (value left second) =
        boolNand (value right first) (value right second)
      rw [ihFirst (fun index member => agree index (List.mem_append_left _ member)),
        ihSecond (fun index member => agree index (List.mem_append_right _ member))]

private def splice (indices : List Nat) (left right : Nat → Bool) : Nat → Bool :=
  fun index => if index ∈ indices then left index else right index

private theorem splice_left (term : Term) (left right : Nat → Bool) :
    value (splice (variables term) left right) term = value left term := by
  apply value_congr
  intro index member
  exact if_pos member

private theorem splice_right (first second : Term) (left right : Nat → Bool)
    (separate : ∀ a ∈ variables first, ∀ b ∈ variables second, a ≠ b) :
    value (splice (variables first) left right) second = value right second := by
  apply value_congr
  intro index member
  apply if_neg
  intro also
  exact separate index also index member rfl

private theorem constants_split (left right : Term)
    (empty : constants (.node left right) = 0) :
    constants left = 0 ∧ constants right = 0 := by
  change constants left + constants right = 0 at empty
  constructor <;> omega

/-- Both Boolean values are constructively attainable on a constant-free,
distinct-leaf raw term. This is not true for arbitrary expanded circuits. -/
theorem attains (term : Term) (empty : constants term = 0)
    (distinct : (variables term).Nodup) (bit : Bool) :
    ∃ input : Nat → Bool, value input term = bit := by
  induction term generalizing bit with
  | constant fixed => cases empty
  | input index => exact ⟨fun _ => bit,rfl⟩
  | node left right ihLeft ihRight =>
      obtain ⟨noLeft,noRight⟩ := constants_split left right empty
      obtain ⟨leftDistinct,rightDistinct,separate⟩ := List.nodup_append.mp distinct
      obtain ⟨leftInput,leftValue⟩ := ihLeft noLeft leftDistinct (!bit)
      obtain ⟨rightInput,rightValue⟩ := ihRight noRight rightDistinct true
      refine ⟨splice (variables left) leftInput rightInput,?_⟩
      change boolNand (value _ left) (value _ right) = bit
      rw [splice_left,splice_right left right leftInput rightInput separate,leftValue,rightValue]
      cases bit <;> rfl

private theorem nand_right_true_ne (left right : Bool) (different : left ≠ right) :
    boolNand left true ≠ boolNand right true := by
  cases left <;> cases right
  · exact False.elim (different rfl)
  · decide
  · decide
  · exact False.elim (different rfl)

private theorem nand_left_true_ne (left right : Bool) (different : left ≠ right) :
    boolNand true left ≠ boolNand true right := by
  cases left <;> cases right
  · exact False.elim (different rfl)
  · decide
  · decide
  · exact False.elim (different rfl)

/-- Every mentioned input has a witness pair differing only at that input. -/
theorem essential_witness (term : Term) (empty : constants term = 0)
    (distinct : (variables term).Nodup) (index : Nat) (member : index ∈ variables term) :
    ∃ left right : Nat → Bool,
      (∀ other, other ≠ index → left other = right other) ∧ value left term ≠ value right term := by
  induction term generalizing index with
  | constant bit => cases empty
  | input actual =>
      have same : index = actual := List.mem_singleton.mp member
      subst index
      refine ⟨fun _ => false,fun other => if other = actual then true else false,?_,?_⟩
      · intro other different
        simp only [if_neg different]
      · change false ≠ if actual = actual then true else false
        rw [if_pos rfl]
        decide
  | node first second ihFirst ihSecond =>
      obtain ⟨noFirst,noSecond⟩ := constants_split first second empty
      obtain ⟨firstDistinct,secondDistinct,separate⟩ := List.nodup_append.mp distinct
      rcases List.mem_append.mp member with inFirst | inSecond
      · obtain ⟨left,right,agree,changed⟩ := ihFirst noFirst firstDistinct index inFirst
        obtain ⟨fixed,fixedValue⟩ := attains second noSecond secondDistinct true
        refine ⟨splice (variables first) left fixed,splice (variables first) right fixed,?_,?_⟩
        · intro other different
          by_cases within : other ∈ variables first
          · simp only [splice,if_pos within]
            exact agree other different
          · simp only [splice,if_neg within]
        · change boolNand (value _ first) (value _ second) ≠
            boolNand (value _ first) (value _ second)
          rw [splice_left,splice_left,
            splice_right first second left fixed separate,
            splice_right first second right fixed separate,fixedValue]
          exact nand_right_true_ne _ _ changed
      · obtain ⟨left,right,agree,changed⟩ := ihSecond noSecond secondDistinct index inSecond
        obtain ⟨fixed,fixedValue⟩ := attains first noFirst firstDistinct true
        refine ⟨splice (variables first) fixed left,splice (variables first) fixed right,?_,?_⟩
        · intro other different
          by_cases within : other ∈ variables first
          · simp only [splice,if_pos within]
          · simp only [splice,if_neg within]
            exact agree other different
        · change boolNand (value _ first) (value _ second) ≠
            boolNand (value _ first) (value _ second)
          rw [splice_left,splice_left,
            splice_right first second fixed left separate,
            splice_right first second fixed right separate,fixedValue]
          exact nand_left_true_ne _ _ changed

/-- Essential inputs must occur, even without the read-once hypotheses. -/
theorem essential_mem (term : Term) (index : Nat)
    (essential : ∃ left right : Nat → Bool,
      (∀ other, other ≠ index → left other = right other) ∧ value left term ≠ value right term) :
    index ∈ variables term := by
  by_cases member : index ∈ variables term
  · exact member
  · obtain ⟨left,right,agree,changed⟩ := essential
    apply False.elim
    apply changed
    apply value_congr
    intro other within
    apply agree other
    intro same
    subst other
    exact member within

private theorem read_range (source : Source inputs gates) (terms : Fin gates → Term)
    (within : ∀ gate index, index ∈ variables (terms gate) → index < inputs) :
    ∀ index, index ∈ variables
      (NormalizationTerm.read source (fun input => .input input.val) terms) → index < inputs := by
  intro index member
  cases source with
  | input actual =>
      have same : index = actual.val := List.mem_singleton.mp member
      rw [same]
      exact actual.isLt
  | constant bit => cases member
  | gate gate => exact within gate index member

private theorem expand_range (program : Program inputs gates) :
    ∀ gate index, index ∈ variables (expand program gate) → index < inputs := by
  induction program with
  | empty => intro gate; exact Fin.elim0 gate
  | @snoc size initial gate ih =>
      intro demanded index member
      rcases CausalBound.index_cases demanded with ⟨earlier,rfl⟩ | rfl
      · rw [DemandForest.expand_earlier] at member
        exact ih earlier index member
      · rw [DemandForest.expand_last] at member
        rcases List.mem_append.mp member with inLeft | inRight
        · exact read_range gate.left (expand initial) ih index inLeft
        · exact read_range gate.right (expand initial) ih index inRight

/-- All natural-number leaves came from actual finite circuit inputs. -/
theorem expression_variables_lt (program : Program inputs gates) (source : Source inputs gates)
    (index : Nat) (member : index ∈ variables (expression program source)) : index < inputs :=
  read_range source (expand program) (expand_range program) index member

/-- Restricting a witness to the actual input width preserves its value. -/
theorem expression_natural_sound (program : Program inputs gates) (source : Source inputs gates)
    (input : Nat → Bool) :
    value input (expression program source) =
      source.eval (fun index => input index.val) (program.eval (fun index => input index.val)) := by
  have same : value input (expression program source) =
      value (extendInput (fun index : Fin inputs => input index.val)) (expression program source) := by
    apply value_congr
    intro index member
    have bound := expression_variables_lt program source index member
    exact (DemandForest.extendInput_at (fun index : Fin inputs => input index.val)
      (⟨index,bound⟩ : Fin inputs)).symm
  exact same.trans (DemandForest.expression_sound program source _)

theorem expression_attains (program : Program inputs gates) (source : Source inputs gates)
    (empty : constants (expression program source) = 0)
    (distinct : (variables (expression program source)).Nodup) (bit : Bool) :
    ∃ input : Valuation inputs, source.eval input (program.eval input) = bit := by
  obtain ⟨input,attained⟩ := attains (expression program source) empty distinct bit
  refine ⟨fun index => input index.val,?_⟩
  rw [← expression_natural_sound program source input]
  exact attained

theorem expression_essential (program : Program inputs gates) (source : Source inputs gates)
    (empty : constants (expression program source) = 0)
    (distinct : (variables (expression program source)).Nodup)
    (index : Fin inputs) (member : index.val ∈ variables (expression program source)) :
    EssentialInputBound.Essential (fun input => source.eval input (program.eval input)) index := by
  obtain ⟨left,right,agree,changed⟩ :=
    essential_witness (expression program source) empty distinct index.val member
  refine ⟨fun other => left other.val,fun other => right other.val,?_,?_⟩
  · intro other different
    apply agree other.val
    intro same
    exact different (Fin.ext same)
  · intro equal
    apply changed
    exact (expression_natural_sound program source left).trans
      (equal.trans (expression_natural_sound program source right).symm)

/-- For a read-once expansion, syntactic occurrence and actual finite-input
essentiality coincide. The hypotheses must still be derived for each circuit. -/
theorem expression_essential_iff (program : Program inputs gates) (source : Source inputs gates)
    (empty : constants (expression program source) = 0)
    (distinct : (variables (expression program source)).Nodup) (index : Fin inputs) :
    EssentialInputBound.Essential (fun input => source.eval input (program.eval input)) index ↔
      index.val ∈ variables (expression program source) := by
  constructor
  · intro essential
    apply essential_mem (expression program source) index.val
    obtain ⟨left,right,agree,changed⟩ := essential
    refine ⟨extendInput left,extendInput right,?_,?_⟩
    · intro other different
      unfold extendInput
      by_cases bound : other < inputs
      · rw [dif_pos bound,dif_pos bound]
        apply agree ⟨other,bound⟩
        intro same
        exact different (congrArg Fin.val same)
      · rw [dif_neg bound,dif_neg bound]
    · rw [DemandForest.expression_sound,DemandForest.expression_sound]
      exact changed
  · exact expression_essential program source empty distinct index

end PNP.DirectWire.ReadOnceTerm

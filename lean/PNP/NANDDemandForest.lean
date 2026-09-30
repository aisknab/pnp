import PNP.NANDDemandDeficit
import PNP.NANDNormalizationTermTransport

set_option autoImplicit false
set_option Elab.async false

/-! Unsimplified, source-derived demand forests. Raw nodes preserve the
information that the literal normalizer intentionally removes. Expansion is a
proof-side representation and has no claimed general polynomial-size bound. -/

namespace PNP.DirectWire.DemandForest
open EssentialInputBound DemandDeficit
open NormalizationTerm (Term read value)
open NormalizationAbstractValue (extend extend_earlier extend_last)

variable {inputs gates : Nat}

/-- Interpret natural-number term inputs using the actual finite valuation. -/
def extendInput (input : Valuation inputs) : Nat → Bool :=
  fun index => if bound : index < inputs then input ⟨index,bound⟩ else false

theorem extendInput_at (input : Valuation inputs) (index : Fin inputs) :
    extendInput input index.val = input index := by
  unfold extendInput
  rw [dif_pos index.isLt]

/-- No constant folding or semantic quotient occurs in this expansion. -/
def expand : {gates : Nat} → Program inputs gates → Fin gates → Term
  | _,.empty => Fin.elim0
  | _,.snoc initial gate =>
      extend (expand initial)
        (.node (read gate.left (fun index => .input index.val) (expand initial))
          (read gate.right (fun index => .input index.val) (expand initial)))

def expression (program : Program inputs gates) (source : Source inputs gates) : Term :=
  read source (fun index => .input index.val) (expand program)

theorem expand_earlier (program : Program inputs gates) (gate : Gate inputs gates)
    (index : Fin gates) :
    expand (.snoc program gate) index.castSucc = expand program index :=
  extend_earlier _ _ _

theorem expand_last (program : Program inputs gates) (gate : Gate inputs gates) :
    expand (.snoc program gate) (Fin.last gates) =
      .node (expression program gate.left) (expression program gate.right) :=
  extend_last _ _

private theorem read_sound (source : Source inputs gates) (input : Nat → Bool)
    (terms : Fin gates → Term) (computed : Valuation gates)
    (sound : ∀ index, value input (terms index) = computed index) :
    value input (read source (fun index => .input index.val) terms) =
      source.eval (fun index => input index.val) computed := by
  cases source with
  | input index => rfl
  | constant bit => rfl
  | gate index => exact sound index

private theorem expand_sound (program : Program inputs gates) (input : Nat → Bool) :
    ∀ index, value input (expand program index) =
      program.eval (fun index => input index.val) index := by
  induction program with
  | empty => intro index; exact Fin.elim0 index
  | @snoc size initial gate ih =>
      intro index
      rcases CausalBound.index_cases index with ⟨earlier,rfl⟩ | rfl
      · rw [expand_earlier,Program.eval_snoc_castSucc]
        exact ih earlier
      · rw [expand_last,Program.eval_snoc_last]
        change boolNand (value input (expression initial gate.left))
          (value input (expression initial gate.right)) =
            boolNand (gate.left.eval (fun index => input index.val)
              (initial.eval (fun index => input index.val)))
              (gate.right.eval (fun index => input index.val)
                (initial.eval (fun index => input index.val)))
        unfold expression
        rw [read_sound _ _ _ _ ih,read_sound _ _ _ _ ih]

/-- Every raw expanded source has exactly its actual circuit behaviour. -/
theorem expression_sound (program : Program inputs gates) (source : Source inputs gates)
    (input : Valuation inputs) :
    value (extendInput input) (expression program source) =
      source.eval input (program.eval input) := by
  have same : (fun index : Fin inputs => extendInput input index.val) = input :=
    funext (extendInput_at input)
  have sound := read_sound source (extendInput input) (expand program)
    (program.eval (fun index => extendInput input index.val)) (expand_sound program (extendInput input))
  rw [same] at sound
  exact sound

def nodes : Term → Nat
  | .constant _ => 0
  | .input _ => 0
  | .node left right => nodes left + nodes right + 1

def constants : Term → Nat
  | .constant _ => 1
  | .input _ => 0
  | .node left right => constants left + constants right

/-- Arbitrary weights retain the multiplicity of every primary input. -/
def variableWeight (weights : Nat → Nat) : Term → Nat
  | .constant _ => 0
  | .input index => weights index
  | .node left right => variableWeight weights left + variableWeight weights right

private def weightedSum {alpha : Type} (weight : alpha → Nat) : List alpha → Nat
  | [] => 0
  | head :: tail => weight head + weightedSum weight tail

def weightTotal (weight : Term → Nat) (program : Program inputs gates)
    (demand : List (Source inputs gates)) : Nat :=
  weightedSum (fun source => weight (expression program source)) demand

def inputWeight (weights : Nat → Nat) (demand : List (Fin inputs)) : Nat :=
  weightedSum (fun index => weights index.val) demand

private theorem weighted_append {alpha : Type} (weight : alpha → Nat) (left right : List alpha) :
    weightedSum weight (left ++ right) = weightedSum weight left + weightedSum weight right := by
  induction left with
  | nil => exact (Nat.zero_add _).symm
  | cons head tail ih =>
      simp only [List.cons_append,weightedSum,ih,Nat.add_assoc]

private theorem weighted_congr {alpha : Type} (left right : alpha → Nat) (items : List alpha)
    (same : ∀ item, left item = right item) : weightedSum left items = weightedSum right items := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp only [weightedSum,same,ih]

private theorem weighted_zero {alpha : Type} (items : List alpha) :
    weightedSum (fun _ => 0) items = 0 := by
  induction items with
  | nil => rfl
  | cons head tail ih => simpa only [weightedSum,Nat.zero_add] using ih

private theorem filter_weight {alpha beta : Type} (f : alpha → Option beta)
    (weight : beta → Nat) (missing : Nat) (items : List alpha) :
    weightedSum (fun item => (f item).elim missing weight) items =
      weightedSum weight (items.filterMap f) + discarded f items * missing := by
  induction items with
  | nil => simp only [weightedSum,List.filterMap_nil,discarded,Nat.zero_mul]
  | cons head tail ih =>
      simp only [Option.elim] at ih
      cases found : f head with
      | none =>
          simp only [weightedSum,List.filterMap_cons,discarded,found,Option.elim,
            Nat.add_mul,Nat.one_mul]
          omega
      | some kept =>
          simp only [weightedSum,List.filterMap_cons,discarded,found,Option.elim]
          omega

private theorem previous_none (source : Source inputs (gates + 1))
    (missing : previous? source = none) : source = .gate (Fin.last gates) := by
  cases source with
  | input index => cases missing
  | constant value => cases missing
  | gate index =>
      simp only [previous?] at missing
      split at missing
      · cases missing
      · rename_i absent
        congr 1
        apply Fin.ext
        have upper := index.isLt
        change index.val = gates
        omega

private theorem expression_previous (initial : Program inputs gates) (gate : Gate inputs gates)
    (source : Source inputs (gates + 1)) (prior : Source inputs gates)
    (found : previous? source = some prior) :
    expression (.snoc initial gate) source = expression initial prior := by
  cases source with
  | input index => cases found; rfl
  | constant bit => cases found; rfl
  | gate index =>
      simp only [previous?] at found
      split at found
      · rename_i before
        cases found
        have same : index = (⟨index.val,before⟩ : Fin gates).castSucc := Fin.ext rfl
        exact (congrArg (expand (.snoc initial gate)) same).trans (expand_earlier initial gate _)
      · cases found

/-- Each demanded use duplicates the whole last-gate term. This is why
physical sharing cannot be treated as a free single input in a formula count. -/
theorem weightTotal_step (weight : Term → Nat) (initial : Program inputs gates)
    (gate : Gate inputs gates) (demand : List (Source inputs (gates + 1))) :
    weightTotal weight (.snoc initial gate) demand =
      weightTotal weight initial (demand.filterMap previous?) +
        lastUses demand * weight (.node (expression initial gate.left) (expression initial gate.right)) := by
  have pointwise : ∀ source : Source inputs (gates + 1),
      weight (expression (.snoc initial gate) source) =
        (previous? source).elim
          (weight (.node (expression initial gate.left) (expression initial gate.right)))
          (fun prior => weight (expression initial prior)) := by
    intro source
    cases found : previous? source with
    | some prior => rw [expression_previous initial gate source prior found]; rfl
    | none =>
        have same := previous_none source found
        subst source
        change weight (expand (.snoc initial gate) (Fin.last gates)) = _
        rw [expand_last]
        rfl
  unfold weightTotal
  rw [weighted_congr _ _ demand pointwise]
  exact filter_weight previous? _ _ demand

private theorem zero_step (weight : Term → Nat) (cost : Nat)
    (branch : ∀ left right, weight (.node left right) = weight left + weight right + cost)
    (initial : Program inputs gates) (gate : Gate inputs gates)
    (demand : List (Source inputs (gates + 1)))
    (zero : (tally (.snoc initial gate) demand).total = 0) :
    weightTotal weight (.snoc initial gate) demand =
      weightTotal weight initial (rewind gate demand) + cost := by
  obtain ⟨used,once,_⟩ := zero_loss_last initial gate demand zero
  have step := weightTotal_step weight initial gate demand
  rw [once,Nat.one_mul,branch] at step
  have previous : weightTotal weight initial (rewind gate demand) =
      weightTotal weight initial (demand.filterMap previous?) +
        weight (expression initial gate.left) + weight (expression initial gate.right) := by
    simp only [weightTotal,rewind,if_pos used,weighted_append,weightedSum]
    omega
  omega

private theorem empty_input_weight (weight : Term → Nat)
    (noConstant : ∀ bit, weight (.constant bit) = 0) (demand : List (Source inputs 0)) :
    weightTotal weight .empty demand =
      weightedSum (fun index : Fin inputs => weight (.input index.val)) (demand.filterMap input?) := by
  induction demand with
  | nil => rfl
  | cons source tail ih =>
      cases source with
      | input index =>
          change weight (.input index.val) + weightTotal weight .empty tail = _
          simp only [List.filterMap_cons,input?]
          change weight (.input index.val) + weightTotal weight .empty tail =
            weight (.input index.val) + weightedSum _ _
          rw [ih]
      | constant bit =>
          change weight (.constant bit) + weightTotal weight .empty tail = _
          rw [noConstant,Nat.zero_add]
          exact ih
      | gate index => exact Fin.elim0 index

private theorem empty_constants (demand : List (Source inputs 0)) :
    weightTotal constants .empty demand = discarded input? demand := by
  induction demand with
  | nil => rfl
  | cons source tail ih =>
      cases source with
      | input index =>
          change 0 + weightTotal constants .empty tail = discarded input? tail
          rw [Nat.zero_add]
          exact ih
      | constant bit =>
          change 1 + weightTotal constants .empty tail = discarded input? tail + 1
          omega
      | gate index => exact Fin.elim0 index

/-- Zero physical loss makes expanded and physical NAND counts coincide. -/
theorem zero_loss_nodes (program : Program inputs gates) (demand : List (Source inputs gates))
    (zero : (tally program demand).total = 0) : weightTotal nodes program demand = gates := by
  induction program with
  | empty =>
      rw [empty_input_weight nodes (fun _ => rfl)]
      exact weighted_zero _
  | @snoc size initial gate ih =>
      have prior := (zero_loss_last initial gate demand zero).2.2
      rw [zero_step nodes 1 (fun _ _ => rfl) initial gate demand zero,
        ih (rewind gate demand) prior]

theorem zero_loss_constants (program : Program inputs gates) (demand : List (Source inputs gates))
    (zero : (tally program demand).total = 0) : weightTotal constants program demand = 0 := by
  induction program with
  | empty =>
      rw [empty_constants]
      change 0 + 0 + discarded input? demand = 0 at zero
      omega
  | @snoc size initial gate ih =>
      have prior := (zero_loss_last initial gate demand zero).2.2
      rw [zero_step constants 0 (fun _ _ => rfl) initial gate demand zero,
        ih (rewind gate demand) prior]

/-- Equality for every weighting preserves the complete input multiplicities,
including repeated primaries. It is stronger than comparing only leaf totals. -/
theorem zero_loss_inputs (weights : Nat → Nat) (program : Program inputs gates)
    (demand : List (Source inputs gates)) (zero : (tally program demand).total = 0) :
    weightTotal (variableWeight weights) program demand = inputWeight weights (required program demand) := by
  induction program with
  | empty => exact empty_input_weight (variableWeight weights) (fun _ => rfl) demand
  | @snoc size initial gate ih =>
      have prior := (zero_loss_last initial gate demand zero).2.2
      rw [zero_step (variableWeight weights) 0 (fun _ _ => rfl) initial gate demand zero,
        ih (rewind gate demand) prior]
      simp only [required,Nat.add_zero]

end PNP.DirectWire.DemandForest

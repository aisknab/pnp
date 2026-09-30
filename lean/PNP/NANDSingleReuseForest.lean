import PNP.NANDReadOnceTerm

set_option autoImplicit false
set_option Elab.async false

/-! A source-derived factorization at the unique reused gate. The fresh primary
label is outside the real input width. Substitution recovers each actual output;
a weighted identity retains the distinction between shared subtrees and inputs. -/

namespace PNP.DirectWire.SingleReuseForest
open NormalizationTerm (Term read value)
open NormalizationAbstractValue (extend extend_earlier extend_last)
open DemandForest (expression expand constants variableWeight inputWeight)
open EssentialInputBound (previous? rewind required)
open DemandDeficit (tally lastUses)

variable {inputs gates : Nat}

def replaceInput (marker : Nat) (replacement : Term) : Term → Term
  | .constant bit => .constant bit
  | .input index => if index = marker then replacement else .input index
  | .node left right => .node (replaceInput marker replacement left) (replaceInput marker replacement right)

theorem replaceInput_value (marker : Nat) (replacement term : Term) (input : Nat → Bool) :
    value input (replaceInput marker replacement term) =
      value (fun index => if index = marker then value input replacement else input index) term := by
  induction term with
  | constant bit => rfl
  | input index =>
      by_cases same : index = marker
      · simp only [replaceInput,value,if_pos same]
      · simp only [replaceInput,value,if_neg same]
  | node left right ihLeft ihRight =>
      simp only [replaceInput,value,ihLeft,ihRight]

/-- Stop just the indicated physical gate; all other nodes remain raw NANDs. -/
def cutExpand (cut : Nat) : {gates : Nat} → Program inputs gates → Fin gates → Term
  | _,.empty => Fin.elim0
  | size + 1,.snoc initial gate =>
      extend (cutExpand cut initial)
        (if size = cut then .input inputs else
          .node (read gate.left (fun index => .input index.val) (cutExpand cut initial))
            (read gate.right (fun index => .input index.val) (cutExpand cut initial)))

def cutExpression (cut : Nat) (program : Program inputs gates) (source : Source inputs gates) : Term :=
  read source (fun index => .input index.val) (cutExpand cut program)

private theorem cut_earlier (cut : Nat) (initial : Program inputs gates) (gate : Gate inputs gates)
    (index : Fin gates) :
    cutExpand cut (.snoc initial gate) index.castSucc = cutExpand cut initial index :=
  extend_earlier _ _ _

private theorem cut_last (cut : Nat) (initial : Program inputs gates) (gate : Gate inputs gates) :
    cutExpand cut (.snoc initial gate) (Fin.last gates) =
      if gates = cut then .input inputs else
        .node (cutExpression cut initial gate.left) (cutExpression cut initial gate.right) :=
  extend_last _ _

private theorem read_replace (replacement : Term) (source : Source inputs gates)
    (terms : Fin gates → Term) :
    replaceInput inputs replacement (read source (fun index => .input index.val) terms) =
      read source (fun index => .input index.val) (fun gate => replaceInput inputs replacement (terms gate)) := by
  cases source with
  | input index =>
      change (if index.val = inputs then replacement else .input index.val) = .input index.val
      exact if_neg (Nat.ne_of_lt index.isLt)
  | constant bit => rfl
  | gate index => rfl

private theorem read_congr (source : Source inputs gates) (left right : Fin gates → Term)
    (same : ∀ index, left index = right index) :
    read source (fun index => .input index.val) left =
      read source (fun index => .input index.val) right := by
  cases source with
  | input index => rfl
  | constant bit => rfl
  | gate index => exact same index

private theorem expand_factor (program : Program inputs gates) (cut : Nat) (replacement : Term)
    (atCut : ∀ index : Fin gates, index.val = cut → expand program index = replacement) :
    ∀ index, replaceInput inputs replacement (cutExpand cut program index) = expand program index := by
  induction program with
  | empty => intro index; exact Fin.elim0 index
  | @snoc size initial gate ih =>
      have prior : ∀ index, replaceInput inputs replacement (cutExpand cut initial index) =
          expand initial index := ih (by
        intro index same
        have checked := atCut index.castSucc same
        rw [DemandForest.expand_earlier] at checked
        exact checked)
      intro index
      rcases CausalBound.index_cases index with ⟨earlier,rfl⟩ | rfl
      · rw [cut_earlier,DemandForest.expand_earlier]
        exact prior earlier
      · rw [cut_last]
        by_cases selected : size = cut
        · rw [if_pos selected]
          change (if inputs = inputs then replacement else .input inputs) = _
          rw [if_pos rfl]
          exact (atCut (Fin.last size) selected).symm
        · rw [if_neg selected,DemandForest.expand_last]
          change Term.node
            (replaceInput inputs replacement (read gate.left (fun index => .input index.val) _))
            (replaceInput inputs replacement (read gate.right (fun index => .input index.val) _)) = _
          rw [read_replace,read_replace,
            read_congr gate.left _ _ prior,read_congr gate.right _ _ prior]
          rfl

/-- Substitution recovers each actual source, not merely an aggregate count. -/
theorem cutExpression_factorization (program : Program inputs gates) (cut : Fin gates)
    (source : Source inputs gates) :
    replaceInput inputs (expand program cut) (cutExpression cut.val program source) =
      expression program source := by
  unfold cutExpression expression
  rw [read_replace]
  apply read_congr
  apply expand_factor
  intro index same
  exact congrArg (expand program) (Fin.ext same)

/-- The factored output has exactly the physical circuit semantics after the
fresh label receives the value of the selected physical gate. -/
theorem cutExpression_semantics (program : Program inputs gates) (cut : Fin gates)
    (source : Source inputs gates) (input : Valuation inputs) :
    value (fun index => if index = inputs then program.eval input cut else DemandForest.extendInput input index)
      (cutExpression cut.val program source) = source.eval input (program.eval input) := by
  have sharedValue : value (DemandForest.extendInput input) (expand program cut) =
      program.eval input cut := DemandForest.expression_sound program (.gate cut) input
  have result := replaceInput_value inputs (expand program cut)
    (cutExpression cut.val program source) (DemandForest.extendInput input)
  rw [cutExpression_factorization,DemandForest.expression_sound,sharedValue] at result
  exact result.symm

private theorem expand_before (program : Program inputs gates) (cut : Nat) (outside : gates ≤ cut) :
    ∀ index, cutExpand cut program index = expand program index := by
  induction program with
  | empty => intro index; exact Fin.elim0 index
  | @snoc size initial gate ih =>
      have before : size ≤ cut := by omega
      have different : size ≠ cut := by omega
      intro index
      rcases CausalBound.index_cases index with ⟨earlier,rfl⟩ | rfl
      · rw [cut_earlier,DemandForest.expand_earlier]
        exact ih before earlier
      · rw [cut_last,if_neg different,DemandForest.expand_last]
        unfold cutExpression expression
        rw [read_congr gate.left _ _ (ih before),read_congr gate.right _ _ (ih before)]

private theorem expression_before (program : Program inputs gates) (cut : Nat)
    (outside : gates ≤ cut) (source : Source inputs gates) :
    cutExpression cut program source = expression program source :=
  read_congr source _ _ (expand_before program cut outside)

def cutWeightTotal (weight : Term → Nat) (cut : Nat) (program : Program inputs gates)
    (demand : List (Source inputs gates)) : Nat :=
  (demand.map (fun source => weight (cutExpression cut program source))).sum

private theorem weightTotal_sum (weight : Term → Nat) (program : Program inputs gates)
    (demand : List (Source inputs gates)) :
    DemandForest.weightTotal weight program demand =
      (demand.map (fun source => weight (expression program source))).sum := by
  induction demand with
  | nil => rfl
  | cons head tail ih =>
      change weight (expression program head) + DemandForest.weightTotal weight program tail = _
      simp only [List.map_cons,List.sum_cons,ih]

private theorem cut_total_before (weight : Term → Nat) (program : Program inputs gates)
    (cut : Nat) (outside : gates ≤ cut) (demand : List (Source inputs gates)) :
    cutWeightTotal weight cut program demand = DemandForest.weightTotal weight program demand := by
  rw [weightTotal_sum]
  unfold cutWeightTotal
  congr 2
  funext source
  rw [expression_before program cut outside]

private theorem previous_none (source : Source inputs (gates + 1))
    (missing : previous? source = none) : source = .gate (Fin.last gates) := by
  cases source with
  | input index => cases missing
  | constant bit => cases missing
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

private theorem cut_previous (cut : Nat) (initial : Program inputs gates) (gate : Gate inputs gates)
    (source : Source inputs (gates + 1)) (prior : Source inputs gates)
    (found : previous? source = some prior) :
    cutExpression cut (.snoc initial gate) source = cutExpression cut initial prior := by
  cases source with
  | input index => cases found; rfl
  | constant bit => cases found; rfl
  | gate index =>
      simp only [previous?] at found
      split at found
      · rename_i before
        cases found
        have same : index = (⟨index.val,before⟩ : Fin gates).castSucc := Fin.ext rfl
        exact (congrArg (cutExpand cut (.snoc initial gate)) same).trans (cut_earlier cut initial gate _)
      · cases found

private theorem filter_sum {alpha beta : Type} (f : alpha → Option beta)
    (weight : beta → Nat) (missing : Nat) (items : List alpha) :
    (items.map (fun item => (f item).elim missing weight)).sum =
      ((items.filterMap f).map weight).sum + DemandDeficit.discarded f items * missing := by
  induction items with
  | nil =>
      simp only [List.map_nil,List.sum_nil,List.filterMap_nil,DemandDeficit.discarded,Nat.zero_mul,Nat.add_zero]
  | cons head tail ih =>
      simp only [Option.elim] at ih
      cases found : f head with
      | none =>
          simp only [List.map_cons,List.sum_cons,List.filterMap_cons,DemandDeficit.discarded,
            found,Option.elim,Nat.add_mul,Nat.one_mul]
          omega
      | some kept =>
          simp only [List.map_cons,List.sum_cons,List.filterMap_cons,DemandDeficit.discarded,
            found,Option.elim]
          omega

private theorem cut_total_step (weight : Term → Nat) (cut : Nat) (initial : Program inputs gates)
    (gate : Gate inputs gates) (demand : List (Source inputs (gates + 1))) :
    cutWeightTotal weight cut (.snoc initial gate) demand =
      cutWeightTotal weight cut initial (demand.filterMap previous?) +
        lastUses demand * weight
          (if gates = cut then .input inputs else
            .node (cutExpression cut initial gate.left) (cutExpression cut initial gate.right)) := by
  have pointwise : (fun source : Source inputs (gates + 1) =>
      weight (cutExpression cut (.snoc initial gate) source)) =
      (fun source => (previous? source).elim
        (weight (if gates = cut then .input inputs else
          .node (cutExpression cut initial gate.left) (cutExpression cut initial gate.right)))
        (fun prior => weight (cutExpression cut initial prior))) := by
    funext source
    cases found : previous? source with
    | some prior => rw [cut_previous cut initial gate source prior found]; rfl
    | none =>
        have same := previous_none source found
        subst source
        change weight (cutExpand cut (.snoc initial gate) (Fin.last gates)) = _
        rw [cut_last]
        rfl
  unfold cutWeightTotal
  rw [pointwise]
  exact filter_sum previous? _ _ demand

private theorem cut_rewind (weight : Term → Nat)
    (additive : ∀ left right, weight (.node left right) = weight left + weight right)
    (cut : Nat) (different : gates ≠ cut) (initial : Program inputs gates) (gate : Gate inputs gates)
    (demand : List (Source inputs (gates + 1))) (used : Source.gate (Fin.last gates) ∈ demand)
    (once : lastUses demand = 1) :
    cutWeightTotal weight cut (.snoc initial gate) demand =
      cutWeightTotal weight cut initial (rewind gate demand) := by
  rw [cut_total_step,if_neg different,once,Nat.one_mul,additive]
  simp only [rewind,if_pos used,cutWeightTotal,List.map_append,List.sum_append,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

private theorem cut_at_reuse (weight : Term → Nat)
    (additive : ∀ left right, weight (.node left right) = weight left + weight right)
    (initial : Program inputs gates) (gate : Gate inputs gates)
    (demand : List (Source inputs (gates + 1))) (used : Source.gate (Fin.last gates) ∈ demand)
    (twice : lastUses demand = 2) :
    cutWeightTotal weight gates (.snoc initial gate) demand +
      weight (expand (.snoc initial gate) (Fin.last gates)) =
        DemandForest.weightTotal weight initial (rewind gate demand) + 2 * weight (.input inputs) := by
  rw [cut_total_step,if_pos rfl,twice,cut_total_before weight initial gates (Nat.le_refl _),
    DemandForest.expand_last,additive]
  simp only [weightTotal_sum,rewind,if_pos used,List.map_append,List.sum_append,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

/-- Actual demand multiplicity at each physical gate during the backward scan. -/
def usesAt : {gates : Nat} → Program inputs gates →
    List (Source inputs gates) → Fin gates → Nat
  | _,.empty,_ => Fin.elim0
  | _,.snoc initial gate,demand =>
      extend (usesAt initial (rewind gate demand)) (lastUses demand)

private theorem uses_earlier (initial : Program inputs gates) (gate : Gate inputs gates)
    (demand : List (Source inputs (gates + 1))) (index : Fin gates) :
    usesAt (.snoc initial gate) demand index.castSucc = usesAt initial (rewind gate demand) index :=
  extend_earlier _ _ _

private theorem uses_last (initial : Program inputs gates) (gate : Gate inputs gates)
    (demand : List (Source inputs (gates + 1))) :
    usesAt (.snoc initial gate) demand (Fin.last gates) = lastUses demand :=
  extend_last _ _

theorem zero_loss_uses (program : Program inputs gates) (demand : List (Source inputs gates))
    (zero : (tally program demand).total = 0) :
    ∀ index, usesAt program demand index = 1 := by
  induction program with
  | empty => intro index; exact Fin.elim0 index
  | @snoc size initial gate ih =>
      obtain ⟨_,once,prior⟩ := DemandDeficit.zero_loss_last initial gate demand zero
      intro index
      rcases CausalBound.index_cases index with ⟨earlier,rfl⟩ | rfl
      · rw [uses_earlier]
        exact ih (rewind gate demand) prior earlier
      · rw [uses_last]
        exact once

theorem expanded_gate_node (program : Program inputs gates) (index : Fin gates) :
    ∃ left right, expand program index = .node left right := by
  induction program with
  | empty => exact Fin.elim0 index
  | @snoc size initial gate ih =>
      rcases CausalBound.index_cases index with ⟨earlier,rfl⟩ | rfl
      · rw [DemandForest.expand_earlier]
        exact ih earlier
      · exact ⟨expression initial gate.left,expression initial gate.right,DemandForest.expand_last _ _⟩

/-- With one repeated physical gate use and no other physical losses, the
source itself supplies a unique cut. Every output remains separately available
through cutExpression; aggregate weights preserve all real-input multiplicities. -/
theorem one_reuse_decomposition (program : Program inputs gates) (demand : List (Source inputs gates))
    (noUnused : (tally program demand).unusedGates = 0)
    (oneReuse : (tally program demand).repeatedGateUses = 1)
    (noConstants : (tally program demand).constantDemands = 0) :
    ∃ cut : Fin gates,
      usesAt program demand cut = 2 ∧
      (∀ other, other ≠ cut → usesAt program demand other = 1) ∧
      cutWeightTotal constants cut.val program demand + constants (expand program cut) = 0 ∧
      (∀ weights : Nat → Nat,
        cutWeightTotal (variableWeight weights) cut.val program demand +
          variableWeight weights (expand program cut) =
            inputWeight weights (required program demand) + 2 * weights inputs) := by
  induction program with
  | empty => cases oneReuse
  | @snoc size initial gate ih =>
      by_cases used : Source.gate (Fin.last size) ∈ demand
      · have positive := DemandDeficit.lastUses_positive demand used
        simp only [tally,if_pos used] at noUnused oneReuse noConstants
        by_cases twice : lastUses demand = 2
        · have priorZero : (tally initial (rewind gate demand)).total = 0 := by
            unfold DemandDeficit.Ledger.total
            omega
          refine ⟨Fin.last size,?_,?_,?_,?_⟩
          · rw [uses_last]
            exact twice
          · intro other different
            rcases CausalBound.index_cases other with ⟨earlier,rfl⟩ | rfl
            · rw [uses_earlier]
              exact zero_loss_uses initial (rewind gate demand) priorZero earlier
            · exact False.elim (different rfl)
          · simp only [Fin.val_last]
            rw [cut_at_reuse constants (fun _ _ => rfl) initial gate demand used twice,
              DemandForest.zero_loss_constants initial (rewind gate demand) priorZero]
            rfl
          · intro weights
            simp only [Fin.val_last]
            rw [cut_at_reuse (variableWeight weights) (fun _ _ => rfl) initial gate demand used twice,
              DemandForest.zero_loss_inputs weights initial (rewind gate demand) priorZero]
            rfl
        · have once : lastUses demand = 1 := by omega
          have priorReuse : (tally initial (rewind gate demand)).repeatedGateUses = 1 := by omega
          obtain ⟨cut,atCut,others,noLiteral,weightsAt⟩ :=
            ih (rewind gate demand) noUnused priorReuse noConstants
          have different : size ≠ cut.val := Nat.ne_of_gt cut.isLt
          refine ⟨cut.castSucc,?_,?_,?_,?_⟩
          · rw [uses_earlier]
            exact atCut
          · intro other notCut
            rcases CausalBound.index_cases other with ⟨earlier,rfl⟩ | rfl
            · rw [uses_earlier]
              apply others earlier
              intro same
              exact notCut (congrArg Fin.castSucc same)
            · rw [uses_last]
              exact once
          · rw [DemandForest.expand_earlier]
            change cutWeightTotal constants cut.val (.snoc initial gate) demand +
              constants (expand initial cut) = 0
            rw [cut_rewind constants (fun _ _ => rfl) cut.val different initial gate demand used once]
            exact noLiteral
          · intro weights
            rw [DemandForest.expand_earlier]
            change cutWeightTotal (variableWeight weights) cut.val (.snoc initial gate) demand +
              variableWeight weights (expand initial cut) =
                inputWeight weights (required initial (rewind gate demand)) + 2 * weights inputs
            rw [cut_rewind (variableWeight weights) (fun _ _ => rfl)
              cut.val different initial gate demand used once]
            exact weightsAt weights
      · simp only [tally,if_neg used] at noUnused
        exfalso
        omega


/-- The occurrence list retains output order and multiplicity, including the
fresh label. It is not a set of inputs or a supplied dependency table. -/
def cutVariables (cut : Nat) (program : Program inputs gates)
    (demand : List (Source inputs gates)) : List Nat :=
  demand.flatMap (fun source => ReadOnceTerm.variables (cutExpression cut program source))

theorem cutVariables_weight (weights : Nat → Nat) (cut : Nat) (program : Program inputs gates)
    (demand : List (Source inputs gates)) :
    cutWeightTotal (variableWeight weights) cut program demand =
      ((cutVariables cut program demand).map weights).sum := by
  induction demand with
  | nil => rfl
  | cons head tail ih =>
      change variableWeight weights (cutExpression cut program head) +
        cutWeightTotal (variableWeight weights) cut program tail = _
      rw [ReadOnceTerm.variables_weight,ih]
      simp only [cutVariables,List.flatMap_cons,List.map_append,List.sum_append]

private def pointWeight (needle : Nat) : Nat → Nat :=
  fun index => if index = needle then 1 else 0

private theorem point_sum (needle : Nat) (items : List Nat) :
    (items.map (pointWeight needle)).sum = items.count needle := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [List.map_cons,List.sum_cons,ih]
      by_cases same : head = needle
      · have atHead : pointWeight needle head = 1 := if_pos same
        rw [atHead,same,List.count_cons_self]
        omega
      · have atHead : pointWeight needle head = 0 := if_neg same
        rw [atHead,List.count_cons_of_ne same,Nat.zero_add]

private theorem input_point_sum (needle : Nat) (items : List (Fin inputs)) :
    inputWeight (pointWeight needle) items = (items.map Fin.val).count needle := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      change pointWeight needle head.val + inputWeight (pointWeight needle) tail = _
      rw [ih,List.map_cons]
      by_cases same : head.val = needle
      · have atHead : pointWeight needle head.val = 1 := if_pos same
        rw [atHead,same,List.count_cons_self]
        omega
      · have atHead : pointWeight needle head.val = 0 := if_neg same
        rw [atHead,List.count_cons_of_ne same,Nat.zero_add]

private theorem nodup_input_values (items : List (Fin inputs)) (distinct : items.Nodup) :
    (items.map Fin.val).Nodup := by
  induction items with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
      obtain ⟨absent,prior⟩ := List.nodup_cons.mp distinct
      change (head.val :: tail.map Fin.val).Nodup
      apply List.nodup_cons.mpr
      refine ⟨?_,ih prior⟩
      intro member
      obtain ⟨other,within,same⟩ := List.mem_map.mp member
      have equal : other = head := Fin.ext same
      exact absent (equal ▸ within)

/-- The arbitrary-weight identity gives an exact equation for each primary
occurrence, with precisely two extra occurrences of the fresh cut label. -/
theorem occurrence_accounting (program : Program inputs gates) (demand : List (Source inputs gates))
    (cut : Fin gates)
    (weightsAt : ∀ weights : Nat → Nat,
      cutWeightTotal (variableWeight weights) cut.val program demand +
        variableWeight weights (expand program cut) =
          inputWeight weights (required program demand) + 2 * weights inputs)
    (index : Nat) :
    (cutVariables cut.val program demand).count index +
      (ReadOnceTerm.variables (expand program cut)).count index =
        ((required program demand).map Fin.val).count index + if inputs = index then 2 else 0 := by
  have counted := weightsAt (pointWeight index)
  rw [cutVariables_weight,ReadOnceTerm.variables_weight,point_sum,point_sum,input_point_sum] at counted
  by_cases same : inputs = index
  · simpa only [pointWeight,if_pos same] using counted
  · simpa only [pointWeight,if_neg same,Nat.mul_zero] using counted

private theorem leaf_accounting (term : Term) :
    (ReadOnceTerm.variables term).length + constants term = DemandForest.nodes term + 1 := by
  induction term with
  | constant bit => rfl
  | input index => rfl
  | node left right ihLeft ihRight =>
      simp only [ReadOnceTerm.variables,List.length_append,constants,DemandForest.nodes]
      omega

/-- A physical gate whose raw expansion is constant-free and read-once
essentially depends on at least two distinct real circuit inputs. -/
theorem shared_two_essential (program : Program inputs gates) (cut : Fin gates)
    (noConstant : constants (expand program cut) = 0)
    (distinct : (ReadOnceTerm.variables (expand program cut)).Nodup) :
    ∃ left right : Fin inputs, left ≠ right ∧
      EssentialInputBound.Essential (fun input => program.eval input cut) left ∧
      EssentialInputBound.Essential (fun input => program.eval input cut) right := by
  have leaves := leaf_accounting (expand program cut)
  have positive : 0 < DemandForest.nodes (expand program cut) := by
    obtain ⟨left,right,same⟩ := expanded_gate_node program cut
    rw [same]
    change 0 < DemandForest.nodes left + DemandForest.nodes right + 1
    omega
  have lower : 2 ≤ (ReadOnceTerm.variables (expand program cut)).length := by omega
  cases terms : ReadOnceTerm.variables (expand program cut) with
  | nil =>
      rw [terms] at lower
      change 2 ≤ 0 at lower
      exfalso
      omega
  | cons first tail =>
      cases tail with
      | nil =>
          rw [terms] at lower
          change 2 ≤ 1 at lower
          exfalso
          omega
      | cons second rest =>
          have firstMember : first ∈ ReadOnceTerm.variables (expand program cut) := by
            rw [terms]
            exact List.mem_cons_self
          have secondMember : second ∈ ReadOnceTerm.variables (expand program cut) := by
            rw [terms]
            exact List.mem_cons_of_mem first List.mem_cons_self
          have different : first ≠ second := by
            rw [terms] at distinct
            have absent := (List.nodup_cons.mp distinct).1
            intro same
            exact absent (same ▸ List.mem_cons_self)
          let left : Fin inputs :=
            ⟨first,ReadOnceTerm.expression_variables_lt program (.gate cut) first firstMember⟩
          let right : Fin inputs :=
            ⟨second,ReadOnceTerm.expression_variables_lt program (.gate cut) second secondMember⟩
          refine ⟨left,right,?_,?_,?_⟩
          · intro equal
            exact different (congrArg Fin.val equal)
          · exact ReadOnceTerm.expression_essential program (.gate cut) noConstant distinct left firstMember
          · exact ReadOnceTerm.expression_essential program (.gate cut) noConstant distinct right secondMember

/-- Derive the fresh-label count, shared read-once structure, real-input
separation and two essential inputs from actual demand multiplicities. -/
theorem one_reuse_semantic (program : Program inputs gates) (demand : List (Source inputs gates))
    (noUnused : (tally program demand).unusedGates = 0)
    (oneReuse : (tally program demand).repeatedGateUses = 1)
    (noConstants : (tally program demand).constantDemands = 0)
    (distinct : (required program demand).Nodup) :
    ∃ cut : Fin gates,
      usesAt program demand cut = 2 ∧
      (∀ other, other ≠ cut → usesAt program demand other = 1) ∧
      cutWeightTotal constants cut.val program demand = 0 ∧
      constants (expand program cut) = 0 ∧
      (ReadOnceTerm.variables (expand program cut)).Nodup ∧
      (cutVariables cut.val program demand).count inputs = 2 ∧
      (∀ index, index ≠ inputs →
        (cutVariables cut.val program demand).count index +
          (ReadOnceTerm.variables (expand program cut)).count index ≤ 1) ∧
      (∃ left right : Fin inputs, left ≠ right ∧
        EssentialInputBound.Essential (fun input => program.eval input cut) left ∧
        EssentialInputBound.Essential (fun input => program.eval input cut) right) := by
  obtain ⟨cut,atCut,others,noLiteral,weightsAt⟩ :=
    one_reuse_decomposition program demand noUnused oneReuse noConstants
  have cutConstant : cutWeightTotal constants cut.val program demand = 0 := by omega
  have sharedConstant : constants (expand program cut) = 0 := by omega
  have valuesDistinct := nodup_input_values (required program demand) distinct
  have requiredMarker : ((required program demand).map Fin.val).count inputs = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro member
    obtain ⟨index,_,same⟩ := List.mem_map.mp member
    exact (Nat.ne_of_lt index.isLt) same
  have sharedMarker : (ReadOnceTerm.variables (expand program cut)).count inputs = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro member
    have tooLarge := ReadOnceTerm.expression_variables_lt program (.gate cut) inputs member
    exact Nat.lt_irrefl inputs tooLarge
  have counted := occurrence_accounting program demand cut weightsAt
  have markerCount : (cutVariables cut.val program demand).count inputs = 2 := by
    have atMarker := counted inputs
    rw [if_pos rfl,requiredMarker,sharedMarker] at atMarker
    omega
  have separated : ∀ index, index ≠ inputs →
      (cutVariables cut.val program demand).count index +
        (ReadOnceTerm.variables (expand program cut)).count index ≤ 1 := by
    intro index different
    have count := counted index
    rw [if_neg different.symm,Nat.add_zero] at count
    have upper := List.nodup_iff_count.mp valuesDistinct index
    omega
  have sharedDistinct : (ReadOnceTerm.variables (expand program cut)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro index
    by_cases isMarker : index = inputs
    · rw [isMarker,sharedMarker]
      exact Nat.zero_le _
    · have bound := separated index isMarker
      omega
  exact ⟨cut,atCut,others,cutConstant,sharedConstant,sharedDistinct,markerCount,separated,
    shared_two_essential program cut sharedConstant sharedDistinct⟩

end PNP.DirectWire.SingleReuseForest

import PNP.NANDEssentialInputBound

set_option autoImplicit false
set_option Elab.async false

/-! Exact physical backward-demand accounting. Gate sharing and repeated
primary inputs consume distinct parts of a finite loss budget. No semantic
enumeration, read-once premise or supplied minimality certificate is used. -/

namespace PNP.DirectWire.DemandDeficit
open EssentialInputBound

variable {inputs gates : Nat}

/-- Number of entries discarded by an option-valued map. -/
def discarded {alpha beta : Type} (f : alpha → Option beta) : List alpha → Nat
  | [] => 0
  | head :: tail => match f head with
    | none => discarded f tail + 1
    | some _ => discarded f tail

theorem filter_accounting {alpha beta : Type} (f : alpha → Option beta)
    (items : List alpha) :
    (items.filterMap f).length + discarded f items = items.length := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      cases found : f head with
      | none =>
          simp only [List.filterMap_cons,discarded,found,List.length_cons]
          omega
      | some kept =>
          simp only [List.filterMap_cons,discarded,found,List.length_cons]
          omega

private theorem discarded_positive {alpha beta : Type} (f : alpha → Option beta)
    (items : List alpha) (item : alpha) (member : item ∈ items) (missing : f item = none) :
    0 < discarded f items := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with same | later
      · subst head
        simp only [discarded,missing]
        omega
      · have positive := ih later
        cases found : f head with
        | none => simp only [discarded,found]; omega
        | some kept => simp only [discarded,found]; exact positive

private theorem discarded_zero {alpha beta : Type} (f : alpha → Option beta)
    (items : List alpha) (kept : ∀ item, item ∈ items → f item ≠ none) :
    discarded f items = 0 := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      cases found : f head with
      | none => exact False.elim (kept head List.mem_cons_self found)
      | some value =>
          simp only [discarded,found]
          exact ih (fun item member => kept item (List.mem_cons_of_mem head member))

private theorem previous_last :
    previous? (.gate (Fin.last gates) : Source inputs (gates + 1)) = none := by
  simp only [previous?,Fin.val_last,Nat.lt_irrefl,dif_neg,not_false_eq_true]

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

/-- Multiplicity of the final gate in the current demand, before merging uses. -/
def lastUses (demand : List (Source inputs (gates + 1))) : Nat :=
  discarded previous? demand

theorem lastUses_positive (demand : List (Source inputs (gates + 1)))
    (used : Source.gate (Fin.last gates) ∈ demand) : 0 < lastUses demand :=
  discarded_positive previous? demand (.gate (Fin.last gates)) used previous_last

theorem lastUses_zero (demand : List (Source inputs (gates + 1)))
    (unused : Source.gate (Fin.last gates) ∉ demand) : lastUses demand = 0 := by
  apply discarded_zero
  intro source member missing
  exact unused ((previous_none source missing) ▸ member)

/-- A used gate loses one unit per merged extra demand; an unused gate loses one. -/
def stepLoss (demand : List (Source inputs (gates + 1))) : Nat :=
  if Source.gate (Fin.last gates) ∈ demand then lastUses demand - 1 else 1

theorem rewind_accounting (gate : Gate inputs gates)
    (demand : List (Source inputs (gates + 1))) :
    (rewind gate demand).length + stepLoss demand = demand.length + 1 := by
  have count := filter_accounting previous? demand
  change (demand.filterMap previous?).length + lastUses demand = demand.length at count
  by_cases used : Source.gate (Fin.last gates) ∈ demand
  · have positive := lastUses_positive demand used
    simp only [rewind,stepLoss,if_pos used,List.length_append,List.length_cons,List.length_nil]
    omega
  · have zero := lastUses_zero demand used
    simp only [rewind,stepLoss,if_neg used]
    omega

/-- Separate physical losses; the fields are computed, never supplied. -/
structure Ledger where
  unusedGates : Nat
  repeatedGateUses : Nat
  constantDemands : Nat
  deriving DecidableEq, Repr

def Ledger.total (ledger : Ledger) : Nat :=
  ledger.unusedGates + ledger.repeatedGateUses + ledger.constantDemands

/-- Traverse every physical gate backwards, retaining the three distinct losses. -/
def tally : {gates : Nat} → Program inputs gates → List (Source inputs gates) → Ledger
  | _,.empty,demand => ⟨0,0,discarded input? demand⟩
  | _,.snoc initial gate,demand =>
      let prior := tally initial (rewind gate demand)
      if Source.gate (Fin.last _) ∈ demand then
        {prior with repeatedGateUses := prior.repeatedGateUses + (lastUses demand - 1)}
      else {prior with unusedGates := prior.unusedGates + 1}

theorem tally_step (initial : Program inputs gates) (gate : Gate inputs gates)
    (demand : List (Source inputs (gates + 1))) :
    (tally (.snoc initial gate) demand).total =
      (tally initial (rewind gate demand)).total + stepLoss demand := by
  by_cases used : Source.gate (Fin.last gates) ∈ demand
  · simp only [tally,stepLoss,if_pos used,Ledger.total]
    omega
  · simp only [tally,stepLoss,if_neg used,Ledger.total]
    omega

/-- Exact identity, not merely a fan-in inequality. -/
theorem accounting (program : Program inputs gates) (demand : List (Source inputs gates)) :
    (required program demand).length + (tally program demand).total = demand.length + gates := by
  induction program with
  | empty =>
      have count := filter_accounting input? demand
      change (demand.filterMap input?).length + (0 + 0 + discarded input? demand) = demand.length + 0
      omega
  | @snoc size initial gate ih =>
      have prior := ih (rewind gate demand)
      have step := rewind_accounting gate demand
      change (required initial (rewind gate demand)).length +
        (tally (.snoc initial gate) demand).total = demand.length + (size + 1)
      rw [tally_step]
      omega

theorem zero_loss_last (initial : Program inputs gates) (gate : Gate inputs gates)
    (demand : List (Source inputs (gates + 1)))
    (zero : (tally (.snoc initial gate) demand).total = 0) :
    Source.gate (Fin.last gates) ∈ demand ∧ lastUses demand = 1 ∧
      (tally initial (rewind gate demand)).total = 0 := by
  have step := tally_step initial gate demand
  by_cases used : Source.gate (Fin.last gates) ∈ demand
  · have positive := lastUses_positive demand used
    simp only [stepLoss,if_pos used] at step
    exact ⟨used,by omega,by omega⟩
  · simp only [stepLoss,if_neg used] at step
    exfalso
    omega

theorem one_loss_last (initial : Program inputs gates) (gate : Gate inputs gates)
    (demand : List (Source inputs (gates + 1)))
    (small : (tally (.snoc initial gate) demand).total ≤ 1) :
    (tally initial (rewind gate demand)).total ≤ 1 ∧
      (Source.gate (Fin.last gates) ∈ demand → lastUses demand ≤ 2) ∧
      (Source.gate (Fin.last gates) ∉ demand →
        (tally initial (rewind gate demand)).total = 0) := by
  have step := tally_step initial gate demand
  by_cases used : Source.gate (Fin.last gates) ∈ demand
  · have positive := lastUses_positive demand used
    simp only [stepLoss,if_pos used] at step
    exact ⟨by omega,fun _ => by omega,fun absent => False.elim (absent used)⟩
  · simp only [stepLoss,if_neg used] at step
    exact ⟨by omega,fun present => False.elim (used present),fun _ => by omega⟩

/-- Every input is essential to at least one of the actual demanded outputs. -/
def JointEssential (program : Program inputs gates) (demand : List (Source inputs gates)) : Prop :=
  ∀ index, ∃ source, source ∈ demand ∧
    Essential (fun input => source.eval input (program.eval input)) index

theorem essential_demand_mem (program : Program inputs gates) (demand : List (Source inputs gates))
    (source : Source inputs gates) (member : source ∈ demand) (index : Fin inputs)
    (essential : Essential (fun input => source.eval input (program.eval input)) index) :
    index ∈ required program demand := by
  by_cases present : index ∈ required program demand
  · exact present
  · obtain ⟨left,right,agree,changed⟩ := essential
    have same := required_sound program demand left right (by
      intro other inRequired
      apply agree other
      intro equal
      subst other
      exact present inRequired) source member
    exact False.elim (changed same)

private theorem ofFn_distinct {alpha : Type} {width : Nat}
    (value : Fin width → alpha) (injective : Function.Injective value) :
    (List.ofFn value).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro left right lb rb less same
  have l : left < width := by simpa only [List.length_ofFn] using lb
  have r : right < width := by simpa only [List.length_ofFn] using rb
  have equal : value ⟨left,l⟩ = value ⟨right,r⟩ := by
    simpa only [List.getElem_ofFn] using same
  have indices : left = right := congrArg Fin.val (injective equal)
  omega

private theorem nodup_length_le_subset {alpha : Type} {left right : List alpha}
    (distinct : left.Nodup) (included : ∀ item, item ∈ left → item ∈ right) :
    left.length ≤ right.length := by
  induction left generalizing right with
  | nil => exact Nat.zero_le _
  | cons head tail ih =>
      obtain ⟨before,after,rfl⟩ := List.append_of_mem (included head List.mem_cons_self)
      obtain ⟨headAbsent,tailDistinct⟩ := List.nodup_cons.mp distinct
      have tailIncluded : ∀ item, item ∈ tail → item ∈ before ++ after := by
        intro item member
        rcases List.mem_append.mp (included item (List.mem_cons_of_mem head member)) with first | rest
        · exact List.mem_append_left _ first
        · rcases List.mem_cons.mp rest with same | last
          · subst item
            exact False.elim (headAbsent member)
          · exact List.mem_append_right _ last
      have smaller := ih tailDistinct tailIncluded
      simp only [List.length_cons,List.length_append] at smaller ⊢
      omega

theorem joint_required_length (program : Program inputs gates) (demand : List (Source inputs gates))
    (essential : JointEssential program demand) : inputs ≤ (required program demand).length := by
  have distinct := ofFn_distinct (id : Fin inputs → Fin inputs) (fun _ _ same => same)
  have included : ∀ index, index ∈ List.ofFn (id : Fin inputs → Fin inputs) →
      index ∈ required program demand := by
    intro index _
    obtain ⟨source,member,changes⟩ := essential index
    exact essential_demand_mem program demand source member index changes
  have bound := nodup_length_le_subset distinct included
  simpa only [List.length_ofFn] using bound

/-- Occurrences beyond the input universe. Under JointEssential these are
exactly the excess repeated primary demands; without that premise no such
interpretation is asserted. -/
def inputExcess (program : Program inputs gates) (demand : List (Source inputs gates)) : Nat :=
  (required program demand).length - inputs

/-- Essentiality exposes a fourth loss term, distinct from internal gate reuse. -/
theorem joint_accounting (program : Program inputs gates) (demand : List (Source inputs gates))
    (essential : JointEssential program demand) :
    inputs + (tally program demand).total + inputExcess program demand = demand.length + gates := by
  have exactCount := accounting program demand
  have covered := joint_required_length program demand essential
  unfold inputExcess
  omega

theorem one_defect_budget (program : Program inputs gates) (demand : List (Source inputs gates))
    (essential : JointEssential program demand) (small : demand.length + gates ≤ inputs + 1) :
    (tally program demand).total + inputExcess program demand ≤ 1 := by
  have exactCount := joint_accounting program demand essential
  omega

/-- Every possible one-unit loss is explicit. This classifies a count budget;
it does not yet establish a semantic forest or the joint minimum theorem. -/
theorem one_defect_classification (program : Program inputs gates) (demand : List (Source inputs gates))
    (essential : JointEssential program demand) (small : demand.length + gates ≤ inputs + 1) :
    let ledger := tally program demand
    let extra := inputExcess program demand
    (ledger.unusedGates = 0 ∧ ledger.repeatedGateUses = 0 ∧ ledger.constantDemands = 0 ∧ extra = 0) ∨
    (ledger.unusedGates = 1 ∧ ledger.repeatedGateUses = 0 ∧ ledger.constantDemands = 0 ∧ extra = 0) ∨
    (ledger.unusedGates = 0 ∧ ledger.repeatedGateUses = 1 ∧ ledger.constantDemands = 0 ∧ extra = 0) ∨
    (ledger.unusedGates = 0 ∧ ledger.repeatedGateUses = 0 ∧ ledger.constantDemands = 1 ∧ extra = 0) ∨
    (ledger.unusedGates = 0 ∧ ledger.repeatedGateUses = 0 ∧ ledger.constantDemands = 0 ∧ extra = 1) := by
  have bound := one_defect_budget program demand essential small
  unfold Ledger.total at bound
  dsimp only
  by_cases unused : (tally program demand).unusedGates = 0
  · by_cases reused : (tally program demand).repeatedGateUses = 0
    · by_cases constant : (tally program demand).constantDemands = 0
      · by_cases extra : inputExcess program demand = 0
        · exact Or.inl ⟨unused,reused,constant,extra⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨unused,reused,constant,by omega⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨unused,reused,by omega,by omega⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨unused,by omega,by omega,by omega⟩))
  · exact Or.inr (Or.inl ⟨by omega,by omega,by omega,by omega⟩)

end PNP.DirectWire.DemandDeficit

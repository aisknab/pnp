import PNP.NANDEssentialInputBound

set_option autoImplicit false
set_option Elab.async false

/-! Equality in the physical fan-in demand bound forces an input symmetry.
The argument allows arbitrary sharing, constants and multiple demanded wires.
It does not assume a read-once representation or execute semantic enumeration. -/

namespace PNP.DirectWire.TightDemandSymmetry
open EssentialInputBound

variable {inputs gates : Nat}

/-- Exchange two primary inputs, leaving every other input unchanged. -/
def inputSwap (left right : Fin inputs) (input : Valuation inputs) : Valuation inputs :=
  fun index => if index = left then input right else if index = right then input left else input index

theorem inputSwap_left (left right : Fin inputs) (input : Valuation inputs) :
    inputSwap left right input left = input right := by
  unfold inputSwap
  exact if_pos rfl

theorem inputSwap_right (left right : Fin inputs) (input : Valuation inputs)
    (different : left ≠ right) : inputSwap left right input right = input left := by
  unfold inputSwap
  rw [if_neg (Ne.symm different),if_pos rfl]

theorem inputSwap_other (left right : Fin inputs) (input : Valuation inputs)
    (index : Fin inputs) (notLeft : index ≠ left) (notRight : index ≠ right) :
    inputSwap left right input index = input index := by
  simp only [inputSwap,if_neg notLeft,if_neg notRight]

theorem inputSwap_comm (left right : Fin inputs) (input : Valuation inputs) :
    inputSwap left right input = inputSwap right left input := by
  by_cases same : left = right
  · subst right
    rfl
  · funext index
    by_cases first : index = left
    · subst index
      rw [inputSwap_left,inputSwap_right _ _ _ (Ne.symm same)]
    · by_cases second : index = right
      · subst index
        rw [inputSwap_right _ _ _ same,inputSwap_left]
      · rw [inputSwap_other _ _ _ _ first second,inputSwap_other _ _ _ _ second first]

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

private theorem previous_eval (initial : Program inputs gates) (gate : Gate inputs gates)
    (source : Source inputs (gates + 1)) (prior : Source inputs gates)
    (found : previous? source = some prior) (input : Valuation inputs) :
    source.eval input ((initial.snoc gate).eval input) =
      prior.eval input (initial.eval input) := by
  cases source with
  | input index => cases found; rfl
  | constant value => cases found; rfl
  | gate index =>
      simp only [previous?] at found
      split at found
      · rename_i before
        cases found
        have same : index = (⟨index.val,before⟩ : Fin gates).castSucc := Fin.ext rfl
        exact (congrArg ((initial.snoc gate).eval input) same).trans
          (Program.eval_snoc_castSucc initial gate input _)
      · cases found

/-- Agreement on the entire rewound interface propagates through the last gate. -/
theorem rewind_agreement (initial : Program inputs gates) (gate : Gate inputs gates)
    (demand : List (Source inputs (gates + 1))) (left right : Valuation inputs)
    (agree : ∀ source, source ∈ rewind gate demand →
      source.eval left (initial.eval left) = source.eval right (initial.eval right)) :
    ∀ source, source ∈ demand →
      source.eval left ((initial.snoc gate).eval left) =
        source.eval right ((initial.snoc gate).eval right) := by
  intro source member
  cases found : previous? source with
  | some prior =>
      have kept : prior ∈ demand.filterMap previous? :=
        List.mem_filterMap.mpr ⟨source,member,found⟩
      have rewound : prior ∈ rewind gate demand := by
        unfold rewind
        split
        · exact List.mem_append_left _ kept
        · exact kept
      exact (previous_eval initial gate source prior found left).trans
        ((agree prior rewound).trans (previous_eval initial gate source prior found right).symm)
  | none =>
      have last := previous_none source found
      subst source
      have lhs : gate.left ∈ rewind gate demand := by
        simp only [rewind,if_pos member]
        exact List.mem_append_right _ List.mem_cons_self
      have rhs : gate.right ∈ rewind gate demand := by
        simp only [rewind,if_pos member]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
      change (initial.snoc gate).eval left (Fin.last gates) =
        (initial.snoc gate).eval right (Fin.last gates)
      rw [Program.eval_snoc_last,Program.eval_snoc_last]
      unfold Gate.eval
      rw [agree _ lhs,agree _ rhs]

private theorem filterMap_full {alpha beta : Type} (f : alpha → Option beta)
    (xs : List alpha) (full : (xs.filterMap f).length = xs.length) :
    ∀ item, item ∈ xs → ∃ kept, f item = some kept := by
  induction xs with
  | nil => intro item member; cases member
  | cons head tail ih =>
      cases found : f head with
      | none =>
          have bound := List.length_filterMap_le f tail
          rw [List.filterMap_cons,found] at full
          change (tail.filterMap f).length = tail.length + 1 at full
          exfalso
          omega
      | some kept =>
          have tailFull : (tail.filterMap f).length = tail.length := by
            rw [List.filterMap_cons,found] at full
            exact Nat.succ.inj full
          intro item member
          rcases List.mem_cons.mp member with same | later
          · subst item
            exact ⟨kept,found⟩
          · exact ih tailFull item later

private theorem input_found (source : Source inputs 0) (index : Fin inputs)
    (found : input? source = some index) : source = .input index := by
  cases source with
  | input old => cases found; rfl
  | constant bit => cases found
  | gate old => exact Fin.elim0 old

private theorem one_gate_symmetry (gate : Gate inputs 0)
    (demand : List (Source inputs 1))
    (distinct : (required (.snoc .empty gate) demand).Nodup)
    (tight : (required (.snoc .empty gate) demand).length = demand.length + 1) :
    ∃ left right : Fin inputs, left ≠ right ∧
      ∀ input source, source ∈ demand →
        source.eval input ((Program.snoc .empty gate).eval input) =
          source.eval (inputSwap left right input)
            ((Program.snoc .empty gate).eval (inputSwap left right input)) := by
  have used : Source.gate (Fin.last 0) ∈ demand := by
    by_cases member : Source.gate (Fin.last 0) ∈ demand
    · exact member
    · have upper := List.length_filterMap_le input? (demand.filterMap previous?)
      have prior := List.length_filterMap_le previous? demand
      simp only [required,rewind,if_neg member] at tight
      omega
  have full : ((rewind gate demand).filterMap input?).length = (rewind gate demand).length := by
    have upper := rewind_length gate demand
    have lower := List.length_filterMap_le input? (rewind gate demand)
    change ((rewind gate demand).filterMap input?).length = demand.length + 1 at tight
    omega
  have lhs : gate.left ∈ rewind gate demand := by
    simp only [rewind,if_pos used]
    exact List.mem_append_right _ List.mem_cons_self
  have rhs : gate.right ∈ rewind gate demand := by
    simp only [rewind,if_pos used]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨left,leftFound⟩ := filterMap_full input? (rewind gate demand) full gate.left lhs
  obtain ⟨right,rightFound⟩ := filterMap_full input? (rewind gate demand) full gate.right rhs
  have leftSource := input_found gate.left left leftFound
  have rightSource := input_found gate.right right rightFound
  have shape : required (.snoc .empty gate) demand =
      ((demand.filterMap previous?).filterMap input?) ++ [left,right] := by
    simp only [required,rewind,if_pos used,List.filterMap_append,List.filterMap_cons,
      leftFound,rightFound,List.filterMap_nil]
  rw [shape] at distinct
  have parts := List.nodup_append.mp distinct
  have different : left ≠ right := by
    intro same
    apply (List.nodup_cons.mp parts.2.1).1
    rw [same]
    exact List.mem_cons_self
  refine ⟨left,right,different,?_⟩
  intro input source member
  cases source with
  | constant bit => rfl
  | input index =>
      have kept : index ∈ (demand.filterMap previous?).filterMap input? :=
        List.mem_filterMap.mpr ⟨.input index,
          List.mem_filterMap.mpr ⟨.input index,member,rfl⟩,rfl⟩
      have notLeft := parts.2.2 index kept left List.mem_cons_self
      have notRight := parts.2.2 index kept right (List.mem_cons_of_mem _ List.mem_cons_self)
      exact (inputSwap_other left right input index notLeft notRight).symm
  | gate index =>
      have last : index = Fin.last 0 := by
        apply Fin.ext
        have upper := index.isLt
        change index.val = 0
        omega
      change (Program.snoc .empty gate).eval input index =
        (Program.snoc .empty gate).eval (inputSwap left right input) index
      rw [last,Program.eval_snoc_last,Program.eval_snoc_last]
      unfold Gate.eval
      rw [leftSource,rightSource]
      change boolNand (input left) (input right) =
        boolNand (inputSwap left right input left) (inputSwap left right input right)
      rw [inputSwap_left,inputSwap_right _ _ _ different]
      cases input left <;> cases input right <;> rfl

/-- Saturating the distinct backward-demand bound forces a common symmetry
of every demanded output, even for programs with arbitrary sharing. -/
theorem maximal_nodup_symmetry (program : Program inputs gates)
    (demand : List (Source inputs gates)) (positive : 0 < gates)
    (distinct : (required program demand).Nodup)
    (tight : (required program demand).length = demand.length + gates) :
    ∃ left right : Fin inputs, left ≠ right ∧
      ∀ input source, source ∈ demand →
        source.eval input (program.eval input) =
          source.eval (inputSwap left right input) (program.eval (inputSwap left right input)) := by
  induction program with
  | empty => exfalso; omega
  | @snoc size initial gate ih =>
      cases size with
      | zero =>
          cases initial
          exact one_gate_symmetry gate demand distinct tight
      | succ size =>
          have earlierTight : (required initial (rewind gate demand)).length =
              (rewind gate demand).length + (size + 1) := by
            have earlier := required_length initial (rewind gate demand)
            have step := rewind_length gate demand
            change (required initial (rewind gate demand)).length =
              demand.length + (size + 1 + 1) at tight
            omega
          obtain ⟨left,right,different,earlier⟩ :=
            ih (rewind gate demand) (Nat.zero_lt_succ size) distinct earlierTight
          refine ⟨left,right,different,?_⟩
          intro input
          exact rewind_agreement initial gate demand input (inputSwap left right input) (earlier input)

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

private theorem cover_perm {alpha : Type} {left right : List alpha}
    (distinct : left.Nodup) (included : ∀ item, item ∈ left → item ∈ right)
    (short : right.length ≤ left.length) : right.Perm left := by
  induction left generalizing right with
  | nil =>
      have empty : right = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero short)
      rw [empty]
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
      have tailShort : (before ++ after).length ≤ tail.length := by
        simp only [List.length_append,List.length_cons] at short ⊢
        omega
      exact List.perm_middle.trans ((ih tailDistinct tailIncluded tailShort).cons head)

/-- At the sharp all-essential-input bound, the structural premises above
follow from essentiality itself rather than from a supplied read-once witness. -/
theorem essential_tight_symmetry (program : Program inputs gates) (source : Source inputs gates)
    (positive : 0 < gates)
    (essential : ∀ index, Essential (fun input => source.eval input (program.eval input)) index)
    (size : inputs = gates + 1) :
    ∃ left right : Fin inputs, left ≠ right ∧
      ∀ input, source.eval input (program.eval input) =
        source.eval (inputSwap left right input) (program.eval (inputSwap left right input)) := by
  have distinct := ofFn_distinct (id : Fin inputs → Fin inputs) (fun _ _ same => same)
  have included : ∀ index, index ∈ List.ofFn (id : Fin inputs → Fin inputs) →
      index ∈ required program [source] := fun index _ => essential_mem program source index (essential index)
  have short : (required program [source]).length ≤ (List.ofFn (id : Fin inputs → Fin inputs)).length := by
    have upper := required_length program [source]
    simp only [List.length_ofFn,List.length_cons,List.length_nil] at upper ⊢
    omega
  have permutation := cover_perm distinct included short
  have requiredDistinct := permutation.symm.nodup distinct
  have requiredLength := permutation.length_eq
  simp only [List.length_ofFn] at requiredLength
  have tight : (required program [source]).length = [source].length + gates := by
    simp only [List.length_cons,List.length_nil]
    omega
  obtain ⟨left,right,different,preserved⟩ :=
    maximal_nodup_symmetry program [source] positive requiredDistinct tight
  exact ⟨left,right,different,fun input => preserved input source List.mem_cons_self⟩

end PNP.DirectWire.TightDemandSymmetry

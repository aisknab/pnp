/-
Copyright (c) 2026 PNP Labs.

Literal source incidence and retained-origin identity for the existing NAND
constant compiler. Every original gate either has its exact ordered translated
sources at one retained position, or is eliminated by the actual literal
constant rule. Retained aliases are injective; input aliases cannot occur.

These are the compiler facts needed for a source-derived cut comparison.
No boundary bijection, independent-cut theorem, full normalization comparison,
manuscript profile transport or polynomial execution theorem is asserted here.
-/

import PNP.NANDPhysicalGateProvenance

set_option autoImplicit false

namespace PNP.DirectWire.ConstantSourceIncidence

def pairMap {alpha beta : Type} (mapping : alpha → beta) (pair : alpha × alpha) :
    beta × beta := (mapping pair.1, mapping pair.2)

private def extend {width : Nat} {alpha : Type}
    (earlier : Fin width → alpha) (last : alpha) (index : Fin (width + 1)) : alpha :=
  if within : index.val < width then earlier ⟨index.val, within⟩ else last

private theorem extend_earlier {width : Nat} {alpha : Type}
    (earlier : Fin width → alpha) (last : alpha) (index : Fin width) :
    extend earlier last index.castSucc = earlier index := by
  change (if within : index.val < width then earlier ⟨index.val, within⟩ else last) = earlier index
  rw [dif_pos index.isLt]

private theorem extend_last {width : Nat} {alpha : Type}
    (earlier : Fin width → alpha) (last : alpha) :
    extend earlier last (Fin.last width) = last := by
  change (if within : width < width then earlier ⟨width, within⟩ else last) = last
  rw [dif_neg (Nat.lt_irrefl width)]

private theorem index_cases {width : Nat} (index : Fin (width + 1)) :
    (∃ earlier : Fin width, index = earlier.castSucc) ∨ index = Fin.last width := by
  if within : index.val < width then
    exact Or.inl ⟨⟨index.val, within⟩, Fin.ext rfl⟩
  else
    right
    apply Fin.ext
    have bound := index.isLt
    change index.val = width
    omega

private theorem sources_earlier {inputs gates : Nat} (program : Program inputs gates)
    (gate : Gate inputs gates) (index : Fin gates) :
    (program.snoc gate).terminalGateSources index.castSucc =
      pairMap (fun source => source.weakenGates 1) (program.terminalGateSources index) := by
  change (if within : index.val < gates then
      let pair := program.terminalGateSources ⟨index.val, within⟩
      (pair.1.weakenGates 1, pair.2.weakenGates 1)
    else (gate.left.weakenGates 1, gate.right.weakenGates 1)) = _
  rw [dif_pos index.isLt]
  rfl

private theorem sources_last {inputs gates : Nat} (program : Program inputs gates)
    (gate : Gate inputs gates) :
    (program.snoc gate).terminalGateSources (Fin.last gates) =
      (gate.left.weakenGates 1, gate.right.weakenGates 1) := by
  change (if within : gates < gates then
      let pair := program.terminalGateSources ⟨gates, within⟩
      (pair.1.weakenGates 1, pair.2.weakenGates 1)
    else (gate.left.weakenGates 1, gate.right.weakenGates 1)) = _
  rw [dif_neg (Nat.lt_irrefl gates)]

private theorem rename_append {inputs fromGates toGates : Nat}
    (alias : Fin fromGates → Source inputs toGates) (source : Source inputs fromGates) :
    (source.weakenGates 1).propagationRename
        (extend (fun index => (alias index).weakenGates 1) (.gate (Fin.last toGates))) =
      (source.propagationRename alias).weakenGates 1 := by
  cases source with
  | input _ => rfl
  | constant _ => rfl
  | gate index =>
      change extend (fun index => (alias index).weakenGates 1)
        (.gate (Fin.last toGates)) index.castSucc = (alias index).weakenGates 1
      rw [extend_earlier]

private theorem rename_eliminate {inputs fromGates toGates : Nat}
    (alias : Fin fromGates → Source inputs toGates) (value : Bool) (source : Source inputs fromGates) :
    (source.weakenGates 1).propagationRename (extend alias (.constant value)) =
      source.propagationRename alias := by
  cases source with
  | input _ => rfl
  | constant _ => rfl
  | gate index =>
      change extend alias (.constant value) index.castSucc = alias index
      rw [extend_earlier]

private theorem constant_value_weaken {inputs gates : Nat} (left right : Source inputs gates) :
    constantGateValue (Gate.mk (left.weakenGates 1) (right.weakenGates 1)) =
      constantGateValue (Gate.mk left right) := by
  cases left with
  | input index =>
      cases right with
      | input other => rfl
      | gate other => rfl
      | constant value => cases value <;> rfl
  | gate index =>
      cases right with
      | input other => rfl
      | gate other => rfl
      | constant value => cases value <;> rfl
  | constant value =>
      cases right with
      | input index => cases value <;> rfl
      | gate index => cases value <;> rfl
      | constant other => cases value <;> cases other <;> rfl

/-- What the actual compiler promises about one original physical gate. -/
def Describes {inputs gates : Nat} (retained : Program inputs gates)
    (pair : Source inputs gates × Source inputs gates) (alias : Source inputs gates) : Prop :=
  match alias with
  | .input _ => False
  | .constant value => constantGateValue ⟨pair.1, pair.2⟩ = some value
  | .gate position => pair = retained.terminalGateSources position

def Coherent {inputs fromGates toGates : Nat} (original : Program inputs fromGates)
    (retained : Program inputs toGates) (alias : Fin fromGates → Source inputs toGates) : Prop :=
  ∀ index, Describes retained
    (pairMap (Source.propagationRename alias) (original.terminalGateSources index)) (alias index)

private theorem describes_weaken {inputs gates : Nat} (retained : Program inputs gates)
    (next : Gate inputs gates) (pair : Source inputs gates × Source inputs gates) (alias : Source inputs gates)
    (described : Describes retained pair alias) :
    Describes (retained.snoc next) (pairMap (fun source => source.weakenGates 1) pair)
      (alias.weakenGates 1) := by
  cases alias with
  | input index => exact described
  | constant value =>
      change constantGateValue ⟨pair.1.weakenGates 1, pair.2.weakenGates 1⟩ = some value
      rw [constant_value_weaken]
      exact described
  | gate position =>
      change pairMap (fun source => source.weakenGates 1) pair =
        (retained.snoc next).terminalGateSources position.castSucc
      rw [sources_earlier]
      exact congrArg (pairMap (fun source => source.weakenGates 1)) described

private theorem append_coherent {inputs fromGates toGates : Nat}
    (original : Program inputs fromGates) (retained : Program inputs toGates)
    (alias : Fin fromGates → Source inputs toGates) (gate : Gate inputs fromGates)
    (coherent : Coherent original retained alias) :
    Coherent (original.snoc gate)
      (retained.snoc ⟨gate.left.propagationRename alias, gate.right.propagationRename alias⟩)
      (extend (fun index => (alias index).weakenGates 1) (.gate (Fin.last toGates))) := by
  intro index
  rcases index_cases index with ⟨earlier, rfl⟩ | rfl
  · rw [sources_earlier, extend_earlier]
    change Describes _
      (((original.terminalGateSources earlier).1.weakenGates 1).propagationRename _,
        ((original.terminalGateSources earlier).2.weakenGates 1).propagationRename _)
      ((alias earlier).weakenGates 1)
    rw [rename_append, rename_append]
    exact describes_weaken retained _ _ _ (coherent earlier)
  · rw [sources_last, extend_last]
    change ((gate.left.weakenGates 1).propagationRename _, (gate.right.weakenGates 1).propagationRename _) =
      (retained.snoc ⟨gate.left.propagationRename alias, gate.right.propagationRename alias⟩).terminalGateSources
        (Fin.last toGates)
    rw [sources_last, rename_append, rename_append]

private theorem eliminate_coherent {inputs fromGates toGates : Nat}
    (original : Program inputs fromGates) (retained : Program inputs toGates)
    (alias : Fin fromGates → Source inputs toGates) (gate : Gate inputs fromGates) (value : Bool)
    (coherent : Coherent original retained alias)
    (folded : constantGateValue ⟨gate.left.propagationRename alias, gate.right.propagationRename alias⟩ = some value) :
    Coherent (original.snoc gate) retained (extend alias (.constant value)) := by
  intro index
  rcases index_cases index with ⟨earlier, rfl⟩ | rfl
  · rw [sources_earlier, extend_earlier]
    change Describes retained
      (((original.terminalGateSources earlier).1.weakenGates 1).propagationRename _,
        ((original.terminalGateSources earlier).2.weakenGates 1).propagationRename _) (alias earlier)
    rw [rename_eliminate, rename_eliminate]
    exact coherent earlier
  · rw [sources_last, extend_last]
    change constantGateValue ⟨(gate.left.weakenGates 1).propagationRename _,
      (gate.right.weakenGates 1).propagationRename _⟩ = some value
    rw [rename_eliminate, rename_eliminate]
    exact folded

theorem actual_sources {inputs gates : Nat} (program : Program inputs gates) :
    Coherent program (compileNANDConstantPropagation program).program (compileNANDConstantPropagation program).alias := by
  induction program with
  | empty => intro index; exact Fin.elim0 index
  | snoc initial gate ih =>
      simp only [compileNANDConstantPropagation]
      split
      · exact append_coherent initial _ _ gate ih
      · rename_i value checked
        exact eliminate_coherent initial _ _ gate value ih checked

theorem retained_sources {inputs gates : Nat} (program : Program inputs gates) (index : Fin gates)
    (position : Fin (compileNANDConstantPropagation program).gateCount)
    (found : (compileNANDConstantPropagation program).alias index = .gate position) :
    pairMap (Source.propagationRename (compileNANDConstantPropagation program).alias)
        (program.terminalGateSources index) =
      (compileNANDConstantPropagation program).program.terminalGateSources position := by
  have described := actual_sources program index
  change Describes _ _ _ at described
  rw [found] at described
  exact described

theorem folded_sources {inputs gates : Nat} (program : Program inputs gates) (index : Fin gates) (value : Bool)
    (found : (compileNANDConstantPropagation program).alias index = .constant value) :
    constantGateValue ⟨((program.terminalGateSources index).1).propagationRename (compileNANDConstantPropagation program).alias,
      ((program.terminalGateSources index).2).propagationRename (compileNANDConstantPropagation program).alias⟩ = some value := by
  have described := actual_sources program index
  change Describes _ _ _ at described
  rw [found] at described
  exact described

theorem alias_not_input {inputs gates : Nat} (program : Program inputs gates)
    (index : Fin gates) (input : Fin inputs) :
    (compileNANDConstantPropagation program).alias index ≠ .input input := by
  intro found
  have described := actual_sources program index
  change Describes _ _ _ at described
  rw [found] at described
  exact described

def UniqueGates {inputs fromGates toGates : Nat} (alias : Fin fromGates → Source inputs toGates) : Prop :=
  ∀ left right position, alias left = .gate position → alias right = .gate position → left = right

private theorem weaken_gate {inputs gates : Nat} (source : Source inputs gates) (target : Fin (gates + 1))
    (equal : source.weakenGates 1 = .gate target) :
    ∃ position, source = .gate position ∧ position.castSucc = target := by
  cases source with
  | input index => cases equal
  | constant value => cases equal
  | gate position => exact ⟨position, rfl, Source.gate.inj equal⟩

private theorem weaken_ne_last {inputs gates : Nat} (source : Source inputs gates) :
    source.weakenGates 1 ≠ .gate (Fin.last gates) := by
  intro equal
  obtain ⟨position, _, last⟩ := weaken_gate source (Fin.last gates) equal
  have same := congrArg Fin.val last
  have bound := position.isLt
  change position.val = gates at same
  omega

private theorem append_unique {inputs fromGates toGates : Nat} (alias : Fin fromGates → Source inputs toGates)
    (unique : UniqueGates alias) :
    UniqueGates (extend (fun index => (alias index).weakenGates 1) (.gate (Fin.last toGates))) := by
  intro left right position leftAt rightAt
  rcases index_cases left with ⟨oldLeft, rfl⟩ | rfl
  · rcases index_cases right with ⟨oldRight, rfl⟩ | rfl
    · rw [extend_earlier] at leftAt rightAt
      obtain ⟨leftPosition, leftAlias, leftMapped⟩ := weaken_gate (alias oldLeft) position leftAt
      obtain ⟨rightPosition, rightAlias, rightMapped⟩ := weaken_gate (alias oldRight) position rightAt
      have values := congrArg (fun index : Fin (toGates + 1) => index.val) (leftMapped.trans rightMapped.symm)
      have same : leftPosition = rightPosition := Fin.ext values
      have origins := unique oldLeft oldRight leftPosition leftAlias (rightAlias.trans (congrArg Source.gate same.symm))
      exact congrArg Fin.castSucc origins
    · rw [extend_earlier] at leftAt
      rw [extend_last] at rightAt
      exact False.elim (weaken_ne_last (alias oldLeft)
        (leftAt.trans (congrArg Source.gate (Source.gate.inj rightAt).symm)))
  · rcases index_cases right with ⟨oldRight, rfl⟩ | rfl
    · rw [extend_last] at leftAt
      rw [extend_earlier] at rightAt
      exact False.elim (weaken_ne_last (alias oldRight)
        (rightAt.trans (congrArg Source.gate (Source.gate.inj leftAt).symm)))
    · rfl

private theorem eliminate_unique {inputs fromGates toGates : Nat} (alias : Fin fromGates → Source inputs toGates)
    (value : Bool) (unique : UniqueGates alias) : UniqueGates (extend alias (.constant value)) := by
  intro left right position leftAt rightAt
  rcases index_cases left with ⟨oldLeft, rfl⟩ | rfl
  · rcases index_cases right with ⟨oldRight, rfl⟩ | rfl
    · rw [extend_earlier] at leftAt rightAt
      exact congrArg Fin.castSucc (unique oldLeft oldRight position leftAt rightAt)
    · rw [extend_last] at rightAt
      cases rightAt
  · rw [extend_last] at leftAt
    cases leftAt

theorem actual_gate_alias_injective {inputs gates : Nat} (program : Program inputs gates) :
    UniqueGates (compileNANDConstantPropagation program).alias := by
  induction program with
  | empty => intro left; exact Fin.elim0 left
  | snoc initial gate ih =>
      simp only [compileNANDConstantPropagation]
      split
      · exact append_unique _ ih
      · exact eliminate_unique _ _ ih

theorem origin_inverse {inputs gates : Nat} (program : Program inputs gates)
    (index : Fin gates) (position : Fin (compileNANDConstantPropagation program).gateCount)
    (found : (compileNANDConstantPropagation program).alias index = .gate position) :
    PhysicalGateProvenance.constantOrigin program position = index :=
  actual_gate_alias_injective program (PhysicalGateProvenance.constantOrigin program position) index position
    (PhysicalGateProvenance.constantOrigin_alias program position) found

theorem origin_sources {inputs gates : Nat} (program : Program inputs gates)
    (position : Fin (compileNANDConstantPropagation program).gateCount) :
    pairMap (Source.propagationRename (compileNANDConstantPropagation program).alias)
        (program.terminalGateSources (PhysicalGateProvenance.constantOrigin program position)) =
      (compileNANDConstantPropagation program).program.terminalGateSources position :=
  retained_sources program _ position (PhysicalGateProvenance.constantOrigin_alias program position)

/-- No caller-supplied partition: every origin is actually retained once or folded. -/
theorem alias_cases {inputs gates : Nat} (program : Program inputs gates) (index : Fin gates) :
    (∃ position, (compileNANDConstantPropagation program).alias index = .gate position ∧
      PhysicalGateProvenance.constantOrigin program position = index) ∨
    (∃ value, (compileNANDConstantPropagation program).alias index = .constant value) := by
  cases found : (compileNANDConstantPropagation program).alias index with
  | input input => exact False.elim (alias_not_input program index input found)
  | constant value => exact Or.inr ⟨value, rfl⟩
  | gate position => exact Or.inl ⟨position, rfl, origin_inverse program index position found⟩

theorem output_sources {inputs outputs : Nat} (current : Implementation inputs outputs) (output : Fin outputs) :
    (constantPropagationImplementation current).candidate.directWireWord.source output =
      (current.candidate.directWireWord.source output).propagationRename
        (compileNANDConstantPropagation current.candidate.program).alias :=
  Candidate.ofDirectWireWord_pointwise _ _ output

end PNP.DirectWire.ConstantSourceIncidence

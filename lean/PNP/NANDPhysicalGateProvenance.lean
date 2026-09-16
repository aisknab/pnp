/-
Copyright (c) 2026 PNP Labs.

Recover the original gate coordinates retained by the actual physical
normalization passes. This is a provenance prerequisite, not yet a complete
history ownership ledger or any new PCCMin/ZeroSlack claim.
-/

import PNP.PCCMinPhysicalNormalizationClosure

namespace PNP.DirectWire.PhysicalGateProvenance

private theorem castSucc_injective {width : Nat} {a b : Fin width}
    (same : a.castSucc = b.castSucc) : a = b :=
  Fin.ext (congrArg (fun index : Fin (width + 1) => index.val) same)

private theorem lift_nodup {width : Nat} (items : List (Fin width))
    (distinct : items.Nodup) : (items.map Fin.castSucc).Nodup := by
  induction items with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
      obtain ⟨absent, tailDistinct⟩ := List.nodup_cons.mp distinct
      apply List.nodup_cons.mpr
      refine ⟨?_, ih tailDistinct⟩
      intro member
      obtain ⟨previous, present, same⟩ := List.mem_map.mp member
      exact absent (castSucc_injective same ▸ present)

private theorem append_last_nodup {width : Nat} (items : List (Fin width))
    (distinct : items.Nodup) :
    (items.map Fin.castSucc ++ [Fin.last width]).Nodup := by
  induction items with
  | nil =>
      exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | cons head tail ih =>
      obtain ⟨absent, tailDistinct⟩ := List.nodup_cons.mp distinct
      apply List.nodup_cons.mpr
      refine ⟨?_, ih tailDistinct⟩
      intro member
      rcases List.mem_append.mp member with previous | last
      · obtain ⟨original, present, same⟩ := List.mem_map.mp previous
        exact absent (castSucc_injective same ▸ present)
      · have same := List.mem_singleton.mp last
        have impossible : head.val = width := congrArg Fin.val same
        exact Nat.ne_of_lt head.isLt impossible

/-- The same translated gate inspected by the existing constant compiler. -/
def constantGate {inputs gates : Nat} (initial : Program inputs gates)
    (gate : Gate inputs gates) :
    Gate inputs (compileNANDConstantPropagation initial).gateCount :=
  ⟨gate.left.propagationRename (compileNANDConstantPropagation initial).alias,
    gate.right.propagationRename (compileNANDConstantPropagation initial).alias⟩

/-- Original coordinates are added exactly in the compiler's append branch.
An eliminated constant contributes no physical output gate. -/
def constantOrigins {inputs gates : Nat} (program : Program inputs gates) :
    List (Fin gates) :=
  match program with
  | .empty => []
  | .snoc initial gate =>
      match constantGateValue (constantGate initial gate) with
      | none => (constantOrigins initial).map Fin.castSucc ++ [Fin.last _]
      | some _ => (constantOrigins initial).map Fin.castSucc

theorem constantOrigins_length {inputs gates : Nat} (program : Program inputs gates) :
    (constantOrigins program).length =
      (compileNANDConstantPropagation program).gateCount := by
  induction program with
  | empty => rfl
  | snoc initial gate ih =>
      have countStep :
          (compileNANDConstantPropagation (initial.snoc gate)).gateCount =
            match constantGateValue (constantGate initial gate) with
            | none => (compileNANDConstantPropagation initial).gateCount + 1
            | some _ => (compileNANDConstantPropagation initial).gateCount := by
        conv =>
          lhs
          unfold compileNANDConstantPropagation
        dsimp only
        split
        · rename_i equation
          change constantGateValue (constantGate initial gate) = none at equation
          rw [equation]
          rfl
        · rename_i value equation
          change constantGateValue (constantGate initial gate) = some value at equation
          rw [equation]
          rfl
      rw [countStep]
      unfold constantOrigins
      split <;> simp_all only [List.length_append, List.length_map,
        List.length_cons, List.length_nil]

theorem constantOrigins_nodup {inputs gates : Nat} (program : Program inputs gates) :
    (constantOrigins program).Nodup := by
  induction program with
  | empty => exact List.nodup_nil
  | snoc initial gate ih =>
      unfold constantOrigins
      split
      · exact append_last_nodup _ ih
      · exact lift_nodup _ ih

/-- The same translated gate inspected by the existing structural-sharing pass. -/
def sharingGate {inputs gates : Nat} (initial : Program inputs gates)
    (gate : Gate inputs gates) :
    Gate inputs (compileNANDSharing initial).gateCount :=
  ⟨gate.left.sharingRename (compileNANDSharing initial).alias,
    gate.right.sharingRename (compileNANDSharing initial).alias⟩

/-- An original coordinate is retained only when its actual NAND is appended,
not when an earlier retained physical gate is reused. -/
def sharingOrigins {inputs gates : Nat} (program : Program inputs gates) :
    List (Fin gates) :=
  match program with
  | .empty => []
  | .snoc initial gate =>
      match sharingFindGate (compileNANDSharing initial).program
          (sharingGate initial gate) with
      | none => (sharingOrigins initial).map Fin.castSucc ++ [Fin.last _]
      | some _ => (sharingOrigins initial).map Fin.castSucc

theorem sharingOrigins_length {inputs gates : Nat} (program : Program inputs gates) :
    (sharingOrigins program).length = (compileNANDSharing program).gateCount := by
  induction program with
  | empty => rfl
  | snoc initial gate ih =>
      have countStep :
          (compileNANDSharing (initial.snoc gate)).gateCount =
            match sharingFindGate (compileNANDSharing initial).program
                (sharingGate initial gate) with
            | none => (compileNANDSharing initial).gateCount + 1
            | some _ => (compileNANDSharing initial).gateCount := by
        conv =>
          lhs
          unfold compileNANDSharing
        dsimp only
        split
        · rename_i equation
          change sharingFindGate (compileNANDSharing initial).program (sharingGate initial gate) = none at equation
          rw [equation]
          rfl
        · rename_i found equation
          change sharingFindGate (compileNANDSharing initial).program (sharingGate initial gate) = some found at equation
          rw [equation]
          rfl
      rw [countStep]
      unfold sharingOrigins
      split <;> simp_all only [List.length_append, List.length_map,
        List.length_cons, List.length_nil]

theorem sharingOrigins_nodup {inputs gates : Nat} (program : Program inputs gates) :
    (sharingOrigins program).Nodup := by
  induction program with
  | empty => exact List.nodup_nil
  | snoc initial gate ih =>
      unfold sharingOrigins
      split
      · exact append_last_nodup _ ih
      · exact lift_nodup _ ih

/-- The physical output position of a source alias, when it names a gate. -/
def sourcePosition {inputs gates : Nat} : Source inputs gates → Option Nat
  | .input _ => none
  | .constant _ => none
  | .gate index => some index.val

private theorem sourcePosition_weaken {inputs gates : Nat}
    (source : Source inputs gates) (extra : Nat) :
    sourcePosition (source.weakenGates extra) = sourcePosition source := by
  cases source <;> rfl

/-- Read the actual constant compiler's gate alias, not a count-based assignment. -/
def constantPosition {inputs gates : Nat} (program : Program inputs gates)
    (origin : Fin gates) : Option Nat :=
  sourcePosition ((compileNANDConstantPropagation program).alias origin)

private theorem constantPosition_castSucc {inputs gates : Nat}
    (initial : Program inputs gates) (gate : Gate inputs gates) (index : Fin gates) :
    constantPosition (initial.snoc gate) index.castSucc = constantPosition initial index := by
  unfold constantPosition
  simp only [compileNANDConstantPropagation]
  split
  · change sourcePosition (if within : index.val < gates then
        ((compileNANDConstantPropagation initial).alias ⟨index.val, within⟩).weakenGates 1
        else .gate (Fin.last (compileNANDConstantPropagation initial).gateCount)) = _
    rw [dif_pos index.isLt]
    exact sourcePosition_weaken _ 1
  · rename_i value _
    change sourcePosition (if within : index.val < gates then
        (compileNANDConstantPropagation initial).alias ⟨index.val, within⟩
        else .constant value) = _
    rw [dif_pos index.isLt]

private theorem constantPosition_last_of_append {inputs gates : Nat}
    (initial : Program inputs gates) (gate : Gate inputs gates)
    (checked : constantGateValue (constantGate initial gate) = none) :
    constantPosition (initial.snoc gate) (Fin.last gates) =
      some (compileNANDConstantPropagation initial).gateCount := by
  unfold constantPosition
  simp only [compileNANDConstantPropagation]
  split
  · change sourcePosition (if within : gates < gates then
        ((compileNANDConstantPropagation initial).alias ⟨gates, within⟩).weakenGates 1
        else .gate (Fin.last (compileNANDConstantPropagation initial).gateCount)) = _
    rw [dif_neg (Nat.lt_irrefl gates)]
    rfl
  · rename_i value equation
    change constantGateValue (constantGate initial gate) = some value at equation
    rw [checked] at equation
    cases equation

/-- In retained-origin order, the actual aliases name every physical output
position exactly once and in order. Eliminated constants cannot stand in for a
retained gate. -/
theorem constantOrigins_positions {inputs gates : Nat} (program : Program inputs gates) :
    (constantOrigins program).map (constantPosition program) =
      (List.range (compileNANDConstantPropagation program).gateCount).map some := by
  induction program with
  | empty => rfl
  | snoc initial gate ih =>
      have earlier :
          ((constantOrigins initial).map Fin.castSucc).map
              (constantPosition (initial.snoc gate)) =
            (constantOrigins initial).map (constantPosition initial) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro index _
        exact constantPosition_castSucc initial gate index
      rw [← constantOrigins_length (initial.snoc gate)]
      cases checked : constantGateValue (constantGate initial gate) with
      | none =>
          simp only [constantOrigins, checked, List.map_append, List.map_cons,
            List.map_nil, List.length_append, List.length_map, List.length_cons,
            List.length_nil, constantOrigins_length]
          rw [earlier, ih, constantPosition_last_of_append initial gate checked]
          simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
      | some value =>
          simp only [constantOrigins, checked, List.length_map, constantOrigins_length]
          rw [earlier, ih]

/-- Read the actual sharing compiler's physical alias, including reuse branches. -/
def sharingPosition {inputs gates : Nat} (program : Program inputs gates)
    (origin : Fin gates) : Nat :=
  ((compileNANDSharing program).alias origin).val

private theorem sharingPosition_castSucc {inputs gates : Nat}
    (initial : Program inputs gates) (gate : Gate inputs gates) (index : Fin gates) :
    sharingPosition (initial.snoc gate) index.castSucc = sharingPosition initial index := by
  unfold sharingPosition
  simp only [compileNANDSharing]
  split
  · change (if within : index.val < gates then
        ((compileNANDSharing initial).alias ⟨index.val, within⟩).castSucc
        else Fin.last (compileNANDSharing initial).gateCount).val = _
    rw [dif_pos index.isLt]
    rfl
  · rename_i found _
    change (if within : index.val < gates then
        (compileNANDSharing initial).alias ⟨index.val, within⟩ else found).val = _
    rw [dif_pos index.isLt]

private theorem sharingPosition_last_of_append {inputs gates : Nat}
    (initial : Program inputs gates) (gate : Gate inputs gates)
    (checked : sharingFindGate (compileNANDSharing initial).program
      (sharingGate initial gate) = none) :
    sharingPosition (initial.snoc gate) (Fin.last gates) =
      (compileNANDSharing initial).gateCount := by
  unfold sharingPosition
  simp only [compileNANDSharing]
  split
  · change (if within : gates < gates then
        ((compileNANDSharing initial).alias ⟨gates, within⟩).castSucc
        else Fin.last (compileNANDSharing initial).gateCount).val = _
    rw [dif_neg (Nat.lt_irrefl gates)]
    rfl
  · rename_i found equation
    change sharingFindGate (compileNANDSharing initial).program
      (sharingGate initial gate) = some found at equation
    rw [checked] at equation
    cases equation

/-- The retained representatives, rather than all possibly shared aliases,
enumerate the actual physical output positions in compiler order. -/
theorem sharingOrigins_positions {inputs gates : Nat} (program : Program inputs gates) :
    (sharingOrigins program).map (sharingPosition program) =
      List.range (compileNANDSharing program).gateCount := by
  induction program with
  | empty => rfl
  | snoc initial gate ih =>
      have earlier :
          ((sharingOrigins initial).map Fin.castSucc).map
              (sharingPosition (initial.snoc gate)) =
            (sharingOrigins initial).map (sharingPosition initial) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro index _
        exact sharingPosition_castSucc initial gate index
      rw [← sharingOrigins_length (initial.snoc gate)]
      cases checked : sharingFindGate (compileNANDSharing initial).program
          (sharingGate initial gate) with
      | none =>
          simp only [sharingOrigins, checked, List.map_append, List.map_cons,
            List.map_nil, List.length_append, List.length_map, List.length_cons,
            List.length_nil, sharingOrigins_length]
          rw [earlier, ih, sharingPosition_last_of_append initial gate checked]
          exact (List.range_succ).symm
      | some found =>
          simp only [sharingOrigins, checked, List.length_map, sharingOrigins_length]
          rw [earlier, ih]

/-- The actual original representative at a constant-compiled physical position. -/
def constantOrigin {inputs gates : Nat} (program : Program inputs gates)
    (position : Fin (compileNANDConstantPropagation program).gateCount) : Fin gates :=
  (constantOrigins program)[position.val]'(by
    rw [constantOrigins_length]
    exact position.isLt)

theorem constantOrigin_position {inputs gates : Nat} (program : Program inputs gates)
    (position : Fin (compileNANDConstantPropagation program).gateCount) :
    constantPosition program (constantOrigin program position) = some position.val := by
  have bounded : position.val < (constantOrigins program).length := by
    rw [constantOrigins_length]
    exact position.isLt
  have positions := congrArg (fun items : List (Option Nat) => items[position.val]?)
    (constantOrigins_positions program)
  rw [List.getElem?_map, List.getElem?_eq_getElem bounded,
    List.getElem?_map, List.getElem?_range position.isLt] at positions
  exact Option.some.inj positions

/-- Every retained origin aliases this exact physical gate, not merely a gate
with the same Boolean value. -/
theorem constantOrigin_alias {inputs gates : Nat} (program : Program inputs gates)
    (position : Fin (compileNANDConstantPropagation program).gateCount) :
    (compileNANDConstantPropagation program).alias (constantOrigin program position) =
      .gate position := by
  have same := constantOrigin_position program position
  unfold constantPosition at same
  cases aliasEq : (compileNANDConstantPropagation program).alias
      (constantOrigin program position) with
  | input index =>
      rw [aliasEq] at same
      cases same
  | constant value =>
      rw [aliasEq] at same
      cases same
  | gate actual =>
      rw [aliasEq] at same
      exact congrArg Source.gate (Fin.ext (Option.some.inj same))

theorem constantOrigin_injective {inputs gates : Nat} (program : Program inputs gates)
    {left right : Fin (compileNANDConstantPropagation program).gateCount}
    (same : constantOrigin program left = constantOrigin program right) : left = right := by
  have positions := congrArg (constantPosition program) same
  rw [constantOrigin_position, constantOrigin_position] at positions
  exact Fin.ext (Option.some.inj positions)

/-- The original representative actually emitted at a sharing-compiled position. -/
def sharingOrigin {inputs gates : Nat} (program : Program inputs gates)
    (position : Fin (compileNANDSharing program).gateCount) : Fin gates :=
  (sharingOrigins program)[position.val]'(by
    rw [sharingOrigins_length]
    exact position.isLt)

theorem sharingOrigin_position {inputs gates : Nat} (program : Program inputs gates)
    (position : Fin (compileNANDSharing program).gateCount) :
    sharingPosition program (sharingOrigin program position) = position.val := by
  have bounded : position.val < (sharingOrigins program).length := by
    rw [sharingOrigins_length]
    exact position.isLt
  have positions := congrArg (fun items : List Nat => items[position.val]?)
    (sharingOrigins_positions program)
  rw [List.getElem?_map, List.getElem?_eq_getElem bounded,
    List.getElem?_range position.isLt] at positions
  exact Option.some.inj positions

theorem sharingOrigin_alias {inputs gates : Nat} (program : Program inputs gates)
    (position : Fin (compileNANDSharing program).gateCount) :
    (compileNANDSharing program).alias (sharingOrigin program position) = position :=
  Fin.ext (sharingOrigin_position program position)

theorem sharingOrigin_injective {inputs gates : Nat} (program : Program inputs gates)
    {left right : Fin (compileNANDSharing program).gateCount}
    (same : sharingOrigin program left = sharingOrigin program right) : left = right := by
  have positions := congrArg (sharingPosition program) same
  rw [sharingOrigin_position, sharingOrigin_position] at positions
  exact Fin.ext positions

/-- Original physical gate at an actual position of the computed output cone. -/
def coneOrigin {inputs outputs : Nat} (current : Implementation inputs outputs)
    (position : Fin (outputConeImplementation current).gateCount) : Fin current.gateCount :=
  terminalExtractionOrigin current.candidate (outputConeRecords current.candidate) position

theorem coneOrigin_selected {inputs outputs : Nat} (current : Implementation inputs outputs)
    (position : Fin (outputConeImplementation current).gateCount) :
    TerminalPrimitiveRecord.gate (coneOrigin current position) ∈
      outputConeRecords current.candidate :=
  (terminalGateSelected_eq_true_iff _ _).mp
    (terminalExtractionOrigin_selected current.candidate
      (outputConeRecords current.candidate) position)

theorem coneOrigin_position {inputs outputs : Nat} (current : Implementation inputs outputs)
    (position : Fin (outputConeImplementation current).gateCount) :
    terminalExtractionGateIndex current.candidate (outputConeRecords current.candidate)
        (coneOrigin current position)
        (terminalExtractionOrigin_selected current.candidate
          (outputConeRecords current.candidate) position) = position :=
  terminalExtractionGateIndex_origin current.candidate
    (outputConeRecords current.candidate) position

theorem coneOrigin_injective {inputs outputs : Nat} (current : Implementation inputs outputs) :
    Function.Injective (coneOrigin current) := by
  intro left right same
  exact terminalExtractionOrigin_injective current.candidate
    (outputConeRecords current.candidate) same

/-- The image is precisely the derived physical cone, not a supplied support. -/
theorem coneOrigin_image {inputs outputs : Nat} (current : Implementation inputs outputs)
    (gate : Fin current.gateCount) :
    (∃ position, coneOrigin current position = gate) ↔
      TerminalPrimitiveRecord.gate gate ∈ outputConeRecords current.candidate := by
  constructor
  · intro witness
    obtain ⟨position, same⟩ := witness
    exact same ▸ coneOrigin_selected current position
  · intro member
    have selected := (terminalGateSelected_eq_true_iff _ _).mpr member
    exact ⟨terminalExtractionGateIndex current.candidate
      (outputConeRecords current.candidate) gate selected,
      terminalExtractionOrigin_gateIndex current.candidate
        (outputConeRecords current.candidate) gate selected⟩

/-- Read a source-bound origin from the actual member of the fixed pass family. -/
def passOrigin {inputs outputs : Nat} (pass : PhysicalNormalizationPass)
    (current : Implementation inputs outputs) :
    Fin (physicalNormalizationPassResult pass current).gateCount → Fin current.gateCount :=
  match pass with
  | .constants => constantOrigin current.candidate.program
  | .sharing => sharingOrigin current.candidate.program
  | .pruning => coneOrigin current

theorem passOrigin_injective {inputs outputs : Nat} (pass : PhysicalNormalizationPass)
    (current : Implementation inputs outputs) : Function.Injective (passOrigin pass current) := by
  cases pass with
  | constants =>
      intro left right same
      exact constantOrigin_injective current.candidate.program same
  | sharing =>
      intro left right same
      exact sharingOrigin_injective current.candidate.program same
  | pruning => exact coneOrigin_injective current

private def gainOrigin {inputs outputs : Nat} {current : Implementation inputs outputs}
    (gain : PhysicalNormalizationGain current) :
    Fin gain.result.gateCount → Fin current.gateCount :=
  passOrigin gain.pass current

private theorem gainOrigin_injective {inputs outputs : Nat}
    {current : Implementation inputs outputs} (gain : PhysicalNormalizationGain current) :
    Function.Injective (gainOrigin gain) := passOrigin_injective gain.pass current

/-- Compose only the actual compiler-origin maps occurring in the recorded run. -/
def traceOrigin {inputs outputs : Nat} {current final : Implementation inputs outputs} :
    PhysicalNormalizationTrace current final → Fin final.gateCount → Fin current.gateCount
  | .done _ _ => fun position => position
  | .step gain tail => fun position => gainOrigin gain (traceOrigin tail position)

theorem traceOrigin_injective {inputs outputs : Nat}
    {current final : Implementation inputs outputs}
    (trace : PhysicalNormalizationTrace current final) : Function.Injective (traceOrigin trace) := by
  induction trace with
  | done current quiet =>
      intro left right same
      exact same
  | step gain tail ih =>
      intro left right same
      exact ih (gainOrigin_injective gain same)

/-- No execution trace or provenance map is supplied for the concrete normalizer. -/
def normalizedOrigin {inputs outputs : Nat} (current : Implementation inputs outputs) :
    Fin (runPhysicalNormalization current).result.gateCount → Fin current.gateCount :=
  traceOrigin (runPhysicalNormalization current).trace

theorem normalizedOrigin_injective {inputs outputs : Nat}
    (current : Implementation inputs outputs) : Function.Injective (normalizedOrigin current) :=
  traceOrigin_injective (runPhysicalNormalization current).trace


private theorem listNoDuplicates_nodup {alpha : Type} {items : List alpha}
    (distinct : ListNoDuplicates items) : items.Nodup := by
  induction distinct with
  | nil => exact List.nodup_nil
  | cons absent _ ih => exact List.nodup_cons.mpr ⟨absent, ih⟩

private theorem allFin_nodup (width : Nat) : (allFin width).Nodup :=
  listNoDuplicates_nodup (allFin_noDuplicates width)

/-- Internal enumeration preserves the actual output-position order. -/
private def retainedBy {before after : Nat} (origin : Fin after → Fin before) :
    List (Fin before) :=
  (allFin after).map origin

private def removedBy {before after : Nat} (origin : Fin after → Fin before) :
    List (Fin before) :=
  (allFin before).filter fun gate => decide (gate ∉ retainedBy origin)

private theorem retainedBy_length {before after : Nat}
    (origin : Fin after → Fin before) : (retainedBy origin).length = after := by
  rw [retainedBy, List.length_map, allFin_length]

private theorem retainedBy_mem {before after : Nat}
    (origin : Fin after → Fin before) (gate : Fin before) :
    gate ∈ retainedBy origin ↔ ∃ position, origin position = gate := by
  constructor
  · intro member
    obtain ⟨position, _, same⟩ := List.mem_map.mp member
    exact ⟨position, same⟩
  · intro witness
    obtain ⟨position, same⟩ := witness
    exact List.mem_map.mpr ⟨position, mem_allFin position, same⟩

private theorem removedBy_mem {before after : Nat}
    (origin : Fin after → Fin before) (gate : Fin before) :
    gate ∈ removedBy origin ↔ gate ∉ retainedBy origin := by
  constructor
  · intro member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · intro absent
    exact List.mem_filter.mpr ⟨mem_allFin gate, decide_eq_true absent⟩

private theorem perm_of_nodup_members {alpha : Type} {left right : List alpha}
    (leftDistinct : left.Nodup) (rightDistinct : right.Nodup)
    (sameMembers : ∀ item, item ∈ left ↔ item ∈ right) : left.Perm right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact List.Perm.nil
      | cons head tail =>
          have impossible : head ∈ ([] : List alpha) :=
            (sameMembers head).mpr (List.Mem.head tail)
          cases impossible
  | cons head tail ih =>
      have present := (sameMembers head).mp (List.Mem.head tail)
      obtain ⟨before, after, rfl⟩ := List.append_of_mem present
      have middle : (before ++ head :: after).Perm (head :: (before ++ after)) :=
        List.perm_middle
      obtain ⟨headAbsent, restDistinct⟩ := List.nodup_cons.mp (middle.nodup rightDistinct)
      obtain ⟨tailAbsent, tailDistinct⟩ := List.nodup_cons.mp leftDistinct
      have remaining : ∀ item, item ∈ tail ↔ item ∈ before ++ after := by
        intro item
        constructor
        · intro member
          have inRight := middle.subset
            ((sameMembers item).mp (List.mem_cons_of_mem head member))
          rcases List.mem_cons.mp inRight with equal | member
          · exact False.elim (tailAbsent (equal ▸ member))
          · exact member
        · intro member
          have inLeft := (sameMembers item).mpr
            (middle.symm.subset (List.mem_cons_of_mem head member))
          rcases List.mem_cons.mp inLeft with equal | member
          · exact False.elim (headAbsent (equal ▸ member))
          · exact member
      exact ((ih tailDistinct restDistinct remaining).cons head).trans middle.symm

private theorem partitionBy {before after : Nat}
    (origin : Fin after → Fin before) (injective : Function.Injective origin) :
    (retainedBy origin ++ removedBy origin).Nodup ∧
      (retainedBy origin ++ removedBy origin).Perm (allFin before) := by
  have liveDistinct : (retainedBy origin).Nodup :=
    List.Pairwise.map origin
      (fun _ _ different same => different (injective same)) (allFin_nodup after)
  have removedDistinct : (removedBy origin).Nodup :=
    List.Pairwise.filter _ (allFin_nodup before)
  have distinct : (retainedBy origin ++ removedBy origin).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨liveDistinct, removedDistinct, ?_⟩
    intro live liveMember removed removedMember same
    exact (removedBy_mem origin removed).mp removedMember (same ▸ liveMember)
  refine ⟨distinct, ?_⟩
  apply perm_of_nodup_members distinct (allFin_nodup before)
  intro gate
  constructor
  · intro _
    exact mem_allFin gate
  · intro _
    by_cases alive : gate ∈ retainedBy origin
    · exact List.mem_append_left _ alive
    · exact List.mem_append_right _ ((removedBy_mem origin gate).mpr alive)

/-- Actual source origins in the physical output order of one pass. -/
def passRetained {inputs outputs : Nat} (pass : PhysicalNormalizationPass)
    (current : Implementation inputs outputs) : List (Fin current.gateCount) :=
  retainedBy (passOrigin pass current)

/-- The source gates absent from that actual pass's retained image, once each. -/
def passRemoved {inputs outputs : Nat} (pass : PhysicalNormalizationPass)
    (current : Implementation inputs outputs) : List (Fin current.gateCount) :=
  removedBy (passOrigin pass current)

theorem passRemoved_iff {inputs outputs : Nat} (pass : PhysicalNormalizationPass)
    (current : Implementation inputs outputs) (gate : Fin current.gateCount) :
    gate ∈ passRemoved pass current ↔
      ¬ ∃ position, passOrigin pass current position = gate := by
  exact (removedBy_mem (passOrigin pass current) gate).trans
    (not_congr (retainedBy_mem (passOrigin pass current) gate))

/-- Every original gate is either physically retained or removed, exactly once.
The removal count equals the actual pass's computed saving. -/
theorem pass_partition {inputs outputs : Nat} (pass : PhysicalNormalizationPass)
    (current : Implementation inputs outputs) :
    (passRetained pass current).length =
        (physicalNormalizationPassResult pass current).gateCount ∧
      (passRemoved pass current).length = physicalNormalizationPassSavings pass current ∧
      (passRetained pass current ++ passRemoved pass current).Nodup ∧
      (passRetained pass current ++ passRemoved pass current).Perm (allFin current.gateCount) := by
  have partition := partitionBy (passOrigin pass current) (passOrigin_injective pass current)
  have length := retainedBy_length (passOrigin pass current)
  have total := partition.2.length_eq
  rw [List.length_append, length, allFin_length] at total
  have accounting := physicalNormalizationPass_exact_accounting pass current
  refine ⟨length, ?_, partition.1, partition.2⟩
  change (removedBy (passOrigin pass current)).length = _
  omega

/-- Compose the actual origins first, then enumerate the final physical positions. -/
def traceRetained {inputs outputs : Nat} {current final : Implementation inputs outputs}
    (trace : PhysicalNormalizationTrace current final) : List (Fin current.gateCount) :=
  retainedBy (traceOrigin trace)

/-- A source gate removed by any pass appears once, not again in each later pass.
This list records source coordinates, not a chronological order of removals. -/
def traceRemoved {inputs outputs : Nat} {current final : Implementation inputs outputs}
    (trace : PhysicalNormalizationTrace current final) : List (Fin current.gateCount) :=
  removedBy (traceOrigin trace)

theorem traceRemoved_iff {inputs outputs : Nat}
    {current final : Implementation inputs outputs}
    (trace : PhysicalNormalizationTrace current final) (gate : Fin current.gateCount) :
    gate ∈ traceRemoved trace ↔ ¬ ∃ position, traceOrigin trace position = gate := by
  exact (removedBy_mem (traceOrigin trace) gate).trans
    (not_congr (retainedBy_mem (traceOrigin trace) gate))

/-- The complete trace conserves source identities as a disjoint exact partition,
not just the scalar gate-count balance. -/
theorem trace_partition {inputs outputs : Nat}
    {current final : Implementation inputs outputs}
    (trace : PhysicalNormalizationTrace current final) :
    (traceRetained trace).length = final.gateCount ∧
      (traceRemoved trace).length = trace.savedGates ∧
      (traceRetained trace ++ traceRemoved trace).Nodup ∧
      (traceRetained trace ++ traceRemoved trace).Perm (allFin current.gateCount) := by
  have partition := partitionBy (traceOrigin trace) (traceOrigin_injective trace)
  have length := retainedBy_length (traceOrigin trace)
  have total := partition.2.length_eq
  rw [List.length_append, length, allFin_length] at total
  have accounting := trace.checked.2.2.1
  refine ⟨length, ?_, partition.1, partition.2⟩
  change (removedBy (traceOrigin trace)).length = _
  omega

/-- Retained original identities from the computed normalizer; no trace is supplied. -/
def normalizedRetained {inputs outputs : Nat} (current : Implementation inputs outputs) :
    List (Fin current.gateCount) :=
  traceRetained (runPhysicalNormalization current).trace

/-- Removed original identities from the same computed normalization run. -/
def normalizedRemoved {inputs outputs : Nat} (current : Implementation inputs outputs) :
    List (Fin current.gateCount) :=
  traceRemoved (runPhysicalNormalization current).trace

theorem normalizedRemoved_iff {inputs outputs : Nat}
    (current : Implementation inputs outputs) (gate : Fin current.gateCount) :
    gate ∈ normalizedRemoved current ↔
      ¬ ∃ position, normalizedOrigin current position = gate :=
  traceRemoved_iff (runPhysicalNormalization current).trace gate

/-- Derived live/removed identities account for every original physical gate.
This is normalization provenance, not yet event allocation or ambient ownership. -/
theorem normalized_partition {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    (normalizedRetained current).length = (runPhysicalNormalization current).result.gateCount ∧
      (normalizedRemoved current).length = (runPhysicalNormalization current).trace.savedGates ∧
      (normalizedRetained current ++ normalizedRemoved current).Nodup ∧
      (normalizedRetained current ++ normalizedRemoved current).Perm (allFin current.gateCount) :=
  trace_partition (runPhysicalNormalization current).trace

end PNP.DirectWire.PhysicalGateProvenance

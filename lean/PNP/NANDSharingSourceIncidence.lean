/-
Copyright (c) 2026 PNP Labs.

Literal source incidence of the existing structural-sharing compiler.
A computed alias may merge producers and may commute a NAND's two input ports.
The exact source pair is preserved under the computed alias and an explicit
computed port swap. No independent-boundary identification is inferred.

This is a prerequisite for source-derived sharing closure, not a complete
cut comparison, profile transport, properness theorem or new progress credit.
-/

import PNP.PCCMinConstructiveNANDSharing

set_option autoImplicit false

namespace PNP.DirectWire.SharingSourceIncidence

def pairMap {alpha beta : Type} (mapping : alpha → beta) (pair : alpha × alpha) :
    beta × beta := (mapping pair.1, mapping pair.2)

def PairRelated {alpha : Type} (left right : alpha × alpha) : Prop :=
  left = right ∨ left = (right.2, right.1)

private theorem related_map {alpha beta : Type} (mapping : alpha → beta)
    {left right : alpha × alpha} (related : PairRelated left right) :
    PairRelated (pairMap mapping left) (pairMap mapping right) := by
  rcases related with same | swapped
  · exact Or.inl (congrArg (pairMap mapping) same)
  · right
    rw [swapped]
    rfl

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

private theorem rename_append {inputs fromGates toGates : Nat} (alias : Fin fromGates → Fin toGates)
    (source : Source inputs fromGates) :
    (source.weakenGates 1).sharingRename
        (extend (fun index => (alias index).castSucc) (Fin.last toGates)) =
      (source.sharingRename alias).weakenGates 1 := by
  cases source with
  | input _ => rfl
  | constant _ => rfl
  | gate index =>
      change Source.gate (extend (fun index => (alias index).castSucc)
        (Fin.last toGates) index.castSucc) = .gate (alias index).castSucc
      rw [extend_earlier]

private theorem rename_reuse {inputs fromGates toGates : Nat} (alias : Fin fromGates → Fin toGates)
    (found : Fin toGates) (source : Source inputs fromGates) :
    (source.weakenGates 1).sharingRename (extend alias found) =
      source.sharingRename alias := by
  cases source with
  | input _ => rfl
  | constant _ => rfl
  | gate index =>
      change Source.gate (extend alias found index.castSucc) = .gate (alias index)
      rw [extend_earlier]

/-- Literal coherence, retaining both allowed NAND port orientations. -/
def Coherent {inputs fromGates toGates : Nat} (original : Program inputs fromGates)
    (retained : Program inputs toGates) (alias : Fin fromGates → Fin toGates) : Prop :=
  ∀ index, PairRelated
    (pairMap (Source.sharingRename alias) (original.terminalGateSources index))
    (retained.terminalGateSources (alias index))

private theorem append_coherent {inputs fromGates toGates : Nat}
    (original : Program inputs fromGates) (retained : Program inputs toGates)
    (alias : Fin fromGates → Fin toGates) (gate : Gate inputs fromGates)
    (coherent : Coherent original retained alias) :
    Coherent (original.snoc gate)
      (retained.snoc ⟨gate.left.sharingRename alias, gate.right.sharingRename alias⟩)
      (extend (fun index => (alias index).castSucc) (Fin.last toGates)) := by
  intro index
  rcases index_cases index with ⟨earlier, rfl⟩ | rfl
  · rw [sources_earlier, extend_earlier, sources_earlier]
    change PairRelated
      (((original.terminalGateSources earlier).1.weakenGates 1).sharingRename _,
        ((original.terminalGateSources earlier).2.weakenGates 1).sharingRename _)
      (pairMap (fun source => source.weakenGates 1) (retained.terminalGateSources (alias earlier)))
    rw [rename_append, rename_append]
    exact related_map (fun source => source.weakenGates 1) (coherent earlier)
  · rw [sources_last, extend_last, sources_last]
    change PairRelated
      ((gate.left.weakenGates 1).sharingRename _, (gate.right.weakenGates 1).sharingRename _)
      ((gate.left.sharingRename alias).weakenGates 1, (gate.right.sharingRename alias).weakenGates 1)
    rw [rename_append, rename_append]
    exact Or.inl rfl

private theorem reuse_coherent {inputs fromGates toGates : Nat}
    (original : Program inputs fromGates) (retained : Program inputs toGates)
    (alias : Fin fromGates → Fin toGates) (gate : Gate inputs fromGates) (found : Fin toGates)
    (coherent : Coherent original retained alias)
    (matched : PairRelated (gate.left.sharingRename alias, gate.right.sharingRename alias)
      (retained.terminalGateSources found)) :
    Coherent (original.snoc gate) retained (extend alias found) := by
  intro index
  rcases index_cases index with ⟨earlier, rfl⟩ | rfl
  · rw [sources_earlier, extend_earlier]
    change PairRelated
      (((original.terminalGateSources earlier).1.weakenGates 1).sharingRename _,
        ((original.terminalGateSources earlier).2.weakenGates 1).sharingRename _)
      (retained.terminalGateSources (alias earlier))
    rw [rename_reuse, rename_reuse]
    exact coherent earlier
  · rw [sources_last, extend_last]
    change PairRelated
      ((gate.left.weakenGates 1).sharingRename _, (gate.right.weakenGates 1).sharingRename _)
      (retained.terminalGateSources found)
    rw [rename_reuse, rename_reuse]
    exact matched

/-- Read the actual search branch; do not substitute semantic equality. -/
theorem find_sources {inputs gates : Nat} (program : Program inputs gates)
    (gate : Gate inputs gates) (found : Fin gates)
    (checked : sharingFindGate program gate = some found) :
    PairRelated (gate.left, gate.right) (program.terminalGateSources found) := by
  unfold sharingFindGate at checked
  generalize allFin gates = indices at checked
  induction indices with
  | nil => cases checked
  | cons index remaining ih =>
      change (if decide
        (((program.terminalGateSources index).1 = gate.left ∧
          (program.terminalGateSources index).2 = gate.right) ∨
         ((program.terminalGateSources index).1 = gate.right ∧
          (program.terminalGateSources index).2 = gate.left))
        then some index else _) = some found at checked
      split at checked
      · rename_i matched
        have same : index = found := Option.some.inj checked
        subst found
        change decide
          (((program.terminalGateSources index).1 = gate.left ∧
            (program.terminalGateSources index).2 = gate.right) ∨
           ((program.terminalGateSources index).1 = gate.right ∧
            (program.terminalGateSources index).2 = gate.left)) = true at matched
        rcases of_decide_eq_true matched with ⟨left, right⟩ | ⟨right, left⟩
        · exact Or.inl (Prod.ext left.symm right.symm)
        · exact Or.inr (Prod.ext left.symm right.symm)
      · exact ih checked

/-- Every original gate has the derived literal source pair, even on reuse. -/
theorem actual_sources {inputs gates : Nat} (program : Program inputs gates) :
    Coherent program (compileNANDSharing program).program
      (compileNANDSharing program).alias := by
  induction program with
  | empty => intro index; exact Fin.elim0 index
  | snoc initial gate ih =>
      simp only [compileNANDSharing]
      split
      · exact append_coherent initial _ _ gate ih
      · rename_i found checked
        exact reuse_coherent initial _ _ gate found ih (find_sources _ _ found checked)

/-- Compute the orientation rather than asking a caller to provide a port map. -/
def sourceSwapped {inputs gates : Nat} (program : Program inputs gates)
    (index : Fin gates) : Bool :=
  if pairMap (Source.sharingRename (compileNANDSharing program).alias)
      (program.terminalGateSources index) =
        (compileNANDSharing program).program.terminalGateSources
          ((compileNANDSharing program).alias index)
  then false else true

theorem actual_ordered_sources {inputs gates : Nat} (program : Program inputs gates)
    (index : Fin gates) :
    pairMap (Source.sharingRename (compileNANDSharing program).alias)
        (program.terminalGateSources index) =
      let retained := (compileNANDSharing program).program.terminalGateSources
        ((compileNANDSharing program).alias index)
      if sourceSwapped program index then (retained.2, retained.1) else retained := by
  unfold sourceSwapped
  split
  · rename_i same
    exact same
  · rename_i different
    rcases actual_sources program index with same | swapped
    · exact False.elim (different same)
    · exact swapped

/-- Ordered output ports retain their precise computed source aliases. -/
theorem output_sources {inputs outputs : Nat} (current : Implementation inputs outputs)
    (output : Fin outputs) :
    (sharingImplementation current).candidate.directWireWord.source output =
      (current.candidate.directWireWord.source output).sharingRename
        (compileNANDSharing current.candidate.program).alias := by
  exact Candidate.ofDirectWireWord_pointwise _ _ output

end PNP.DirectWire.SharingSourceIncidence

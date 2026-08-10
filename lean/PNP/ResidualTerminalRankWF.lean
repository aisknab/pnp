/-
Copyright (c) 2026 PNP Labs.

The fixed ten-coordinate residual rank and its well-founded lexicographic order.
This reconstructs the `RankWF` order named immediately after
`RW-SaturatePositive` in the pinned manuscript. It does not claim that the
current finite terminal routes inhabit the complete global outcome system or
that any particular route decreases this rank.
-/

import PNP.ResidualTerminalFiniteSaturatePositive

namespace PNP
namespace DirectWire

/-! ## Fixed residual rank -/

/-- The manuscript's residual rank has exactly ten natural coordinates, in
    priority order: witness type, span type, mode, frontier defect, projection
    defect, saturation defect, anchor count, charge size, profile size, and
    canonical code. The product is right-associated so `Prod.lex` gives that
    order directly. -/
abbrev TerminalResidualRank : Type :=
  Nat × (Nat × (Nat × (Nat × (Nat × (Nat × (Nat × (Nat × (Nat × Nat))))))))

namespace TerminalResidualRank

/-- Named constructor preserving the manuscript coordinate order. -/
def mk
    (witnessType spanType mode frontierDefect projectionDefect
      saturationDefect anchorCount chargeSize profileSize canonicalCode : Nat) :
    TerminalResidualRank :=
  (witnessType, (spanType, (mode, (frontierDefect, (projectionDefect,
    (saturationDefect, (anchorCount, (chargeSize,
      (profileSize, canonicalCode)))))))))

def witnessType (rank : TerminalResidualRank) : Nat := rank.1
def spanType (rank : TerminalResidualRank) : Nat := rank.2.1
def mode (rank : TerminalResidualRank) : Nat := rank.2.2.1
def frontierDefect (rank : TerminalResidualRank) : Nat := rank.2.2.2.1
def projectionDefect (rank : TerminalResidualRank) : Nat := rank.2.2.2.2.1
def saturationDefect (rank : TerminalResidualRank) : Nat := rank.2.2.2.2.2.1
def anchorCount (rank : TerminalResidualRank) : Nat := rank.2.2.2.2.2.2.1
def chargeSize (rank : TerminalResidualRank) : Nat := rank.2.2.2.2.2.2.2.1
def profileSize (rank : TerminalResidualRank) : Nat := rank.2.2.2.2.2.2.2.2.1
def canonicalCode (rank : TerminalResidualRank) : Nat := rank.2.2.2.2.2.2.2.2.2

/-- Public ordered coordinate view used by regressions and external audits. -/
def coordinates (rank : TerminalResidualRank) : List Nat :=
  [rank.witnessType, rank.spanType, rank.mode, rank.frontierDefect,
    rank.projectionDefect, rank.saturationDefect, rank.anchorCount,
    rank.chargeSize, rank.profileSize, rank.canonicalCode]

@[simp] theorem coordinates_mk
    (witnessType spanType mode frontierDefect projectionDefect
      saturationDefect anchorCount chargeSize profileSize canonicalCode : Nat) :
    coordinates (mk witnessType spanType mode frontierDefect projectionDefect
      saturationDefect anchorCount chargeSize profileSize canonicalCode) =
      [witnessType, spanType, mode, frontierDefect, projectionDefect,
        saturationDefect, anchorCount, chargeSize, profileSize, canonicalCode] :=
  rfl

@[simp] theorem coordinates_length (rank : TerminalResidualRank) :
    rank.coordinates.length = 10 := by
  rfl

end TerminalResidualRank

/-! ## Exact lexicographic order -/

/-- Kernel-provided lexicographic well-founded relations, nested in the exact
    ten-coordinate priority order. -/
@[reducible] def terminalResidualRankWellFoundedRelation :
    WellFoundedRelation TerminalResidualRank :=
  Prod.lex Nat.lt_wfRel
    (Prod.lex Nat.lt_wfRel
      (Prod.lex Nat.lt_wfRel
        (Prod.lex Nat.lt_wfRel
          (Prod.lex Nat.lt_wfRel
            (Prod.lex Nat.lt_wfRel
              (Prod.lex Nat.lt_wfRel
                (Prod.lex Nat.lt_wfRel
                  (Prod.lex Nat.lt_wfRel Nat.lt_wfRel))))))))

/-- Strict lexicographic order on the ten manuscript coordinates. -/
@[reducible] def TerminalResidualRank.LexLT
    (after before : TerminalResidualRank) : Prop :=
  terminalResidualRankWellFoundedRelation.rel after before

@[reducible] private def decidableProdLex
    {α β : Type}
    {ra : α → α → Prop} {rb : β → β → Prop}
    (decEq : DecidableEq α)
    (decRa : DecidableRel ra)
    (decRb : DecidableRel rb) :
    DecidableRel (Prod.Lex ra rb) := by
  intro after before
  rcases after with ⟨afterHead, afterTail⟩
  rcases before with ⟨beforeHead, beforeTail⟩
  letI : Decidable (ra afterHead beforeHead) :=
    decRa afterHead beforeHead
  by_cases headSmaller : ra afterHead beforeHead
  · exact isTrue (Prod.Lex.left afterTail beforeTail headSmaller)
  · letI : Decidable (afterHead = beforeHead) :=
      decEq afterHead beforeHead
    by_cases headEqual : afterHead = beforeHead
    · subst beforeHead
      letI : Decidable (rb afterTail beforeTail) :=
        decRb afterTail beforeTail
      by_cases tailSmaller : rb afterTail beforeTail
      · exact isTrue (Prod.Lex.right afterHead tailSmaller)
      · exact isFalse (by
          intro relation
          cases relation with
          | left _ _ found => exact headSmaller found
          | right _ found => exact tailSmaller found)
    · exact isFalse (by
        intro relation
        cases relation with
        | left _ _ found => exact headSmaller found
        | right _ _ => exact headEqual rfl)

@[reducible] private def natLTDecidable : DecidableRel Nat.lt :=
  fun left right => Nat.decLt left right

@[reducible] private def natHeadLexDecidable
    {β : Type} {rb : β → β → Prop}
    (decRb : DecidableRel rb) :
    DecidableRel (Prod.Lex Nat.lt rb) :=
  decidableProdLex inferInstance natLTDecidable decRb

@[reducible] private def terminalResidualRankLexLTDecidableRel :
    DecidableRel TerminalResidualRank.LexLT := by
  change DecidableRel
    (Prod.Lex Nat.lt
      (Prod.Lex Nat.lt
        (Prod.Lex Nat.lt
          (Prod.Lex Nat.lt
            (Prod.Lex Nat.lt
              (Prod.Lex Nat.lt
                (Prod.Lex Nat.lt
                  (Prod.Lex Nat.lt
                    (Prod.Lex Nat.lt Nat.lt)))))))))
  exact natHeadLexDecidable
    (natHeadLexDecidable
      (natHeadLexDecidable
        (natHeadLexDecidable
          (natHeadLexDecidable
            (natHeadLexDecidable
              (natHeadLexDecidable
                (natHeadLexDecidable
                  (natHeadLexDecidable natLTDecidable))))))))

private instance terminalResidualRankLexLTDecidable
    (after before : TerminalResidualRank) :
    Decidable (after.LexLT before) :=
  terminalResidualRankLexLTDecidableRel after before

/-- Executable projection of the exact proof relation. -/
def terminalResidualRankLTBool
    (after before : TerminalResidualRank) : Bool :=
  decide (after.LexLT before)

theorem terminalResidualRankLTBool_eq_true_iff
    (after before : TerminalResidualRank) :
    terminalResidualRankLTBool after before = true ↔ after.LexLT before := by
  simp [terminalResidualRankLTBool]

theorem terminalResidualRankLTBool_eq_false_iff
    (after before : TerminalResidualRank) :
    terminalResidualRankLTBool after before = false ↔ ¬after.LexLT before := by
  simp [terminalResidualRankLTBool]

/-- The exact ten-coordinate order is well-founded. This is the reconstructed
    `RankWF` theorem surface; it requires no caller-supplied termination
    certificate. -/
theorem terminalResidualRankLexLT_wellFounded :
    WellFounded TerminalResidualRank.LexLT :=
  terminalResidualRankWellFoundedRelation.wf

/-- Every residual rank is accessible under the exact descending relation. -/
theorem terminalResidualRank_accessible (rank : TerminalResidualRank) :
    Acc TerminalResidualRank.LexLT rank :=
  terminalResidualRankLexLT_wellFounded.apply rank

/-- Well-founded induction over the manuscript residual rank. -/
theorem terminalResidualRank_induction
    {motive : TerminalResidualRank → Prop}
    (step : ∀ rank,
      (∀ smaller, smaller.LexLT rank → motive smaller) → motive rank) :
    ∀ rank, motive rank := by
  intro rank
  exact terminalResidualRankLexLT_wellFounded.induction rank step

/-! ## Coordinate-priority witnesses -/

theorem terminalResidualRank_witnessType_lt
    (afterWitness beforeWitness : Nat)
    (afterSpan afterMode afterFrontier afterProjection afterSaturation
      afterAnchors afterCharge afterProfile afterCode : Nat)
    (beforeSpan beforeMode beforeFrontier beforeProjection beforeSaturation
      beforeAnchors beforeCharge beforeProfile beforeCode : Nat)
    (smaller : afterWitness < beforeWitness) :
    (TerminalResidualRank.mk afterWitness afterSpan afterMode afterFrontier
      afterProjection afterSaturation afterAnchors afterCharge afterProfile
      afterCode).LexLT
    (TerminalResidualRank.mk beforeWitness beforeSpan beforeMode beforeFrontier
      beforeProjection beforeSaturation beforeAnchors beforeCharge beforeProfile
      beforeCode) :=
  Prod.Lex.left _ _ smaller

theorem terminalResidualRank_spanType_lt
    (witness afterSpan beforeSpan : Nat)
    (afterMode afterFrontier afterProjection afterSaturation afterAnchors
      afterCharge afterProfile afterCode : Nat)
    (beforeMode beforeFrontier beforeProjection beforeSaturation beforeAnchors
      beforeCharge beforeProfile beforeCode : Nat)
    (smaller : afterSpan < beforeSpan) :
    (TerminalResidualRank.mk witness afterSpan afterMode afterFrontier
      afterProjection afterSaturation afterAnchors afterCharge afterProfile
      afterCode).LexLT
    (TerminalResidualRank.mk witness beforeSpan beforeMode beforeFrontier
      beforeProjection beforeSaturation beforeAnchors beforeCharge beforeProfile
      beforeCode) :=
  Prod.Lex.right witness (Prod.Lex.left _ _ smaller)

theorem terminalResidualRank_mode_lt
    (witness span afterMode beforeMode : Nat)
    (afterFrontier afterProjection afterSaturation afterAnchors afterCharge
      afterProfile afterCode : Nat)
    (beforeFrontier beforeProjection beforeSaturation beforeAnchors beforeCharge
      beforeProfile beforeCode : Nat)
    (smaller : afterMode < beforeMode) :
    (TerminalResidualRank.mk witness span afterMode afterFrontier afterProjection
      afterSaturation afterAnchors afterCharge afterProfile afterCode).LexLT
    (TerminalResidualRank.mk witness span beforeMode beforeFrontier
      beforeProjection beforeSaturation beforeAnchors beforeCharge beforeProfile
      beforeCode) :=
  Prod.Lex.right witness
    (Prod.Lex.right span (Prod.Lex.left _ _ smaller))

theorem terminalResidualRank_frontierDefect_lt
    (witness span mode afterFrontier beforeFrontier : Nat)
    (afterProjection afterSaturation afterAnchors afterCharge afterProfile
      afterCode : Nat)
    (beforeProjection beforeSaturation beforeAnchors beforeCharge beforeProfile
      beforeCode : Nat)
    (smaller : afterFrontier < beforeFrontier) :
    (TerminalResidualRank.mk witness span mode afterFrontier afterProjection
      afterSaturation afterAnchors afterCharge afterProfile afterCode).LexLT
    (TerminalResidualRank.mk witness span mode beforeFrontier beforeProjection
      beforeSaturation beforeAnchors beforeCharge beforeProfile beforeCode) :=
  Prod.Lex.right witness (Prod.Lex.right span
    (Prod.Lex.right mode (Prod.Lex.left _ _ smaller)))

theorem terminalResidualRank_projectionDefect_lt
    (witness span mode frontier afterProjection beforeProjection : Nat)
    (afterSaturation afterAnchors afterCharge afterProfile afterCode : Nat)
    (beforeSaturation beforeAnchors beforeCharge beforeProfile beforeCode : Nat)
    (smaller : afterProjection < beforeProjection) :
    (TerminalResidualRank.mk witness span mode frontier afterProjection
      afterSaturation afterAnchors afterCharge afterProfile afterCode).LexLT
    (TerminalResidualRank.mk witness span mode frontier beforeProjection
      beforeSaturation beforeAnchors beforeCharge beforeProfile beforeCode) :=
  Prod.Lex.right witness (Prod.Lex.right span (Prod.Lex.right mode
    (Prod.Lex.right frontier (Prod.Lex.left _ _ smaller))))

theorem terminalResidualRank_saturationDefect_lt
    (witness span mode frontier projection afterSaturation beforeSaturation : Nat)
    (afterAnchors afterCharge afterProfile afterCode : Nat)
    (beforeAnchors beforeCharge beforeProfile beforeCode : Nat)
    (smaller : afterSaturation < beforeSaturation) :
    (TerminalResidualRank.mk witness span mode frontier projection
      afterSaturation afterAnchors afterCharge afterProfile afterCode).LexLT
    (TerminalResidualRank.mk witness span mode frontier projection
      beforeSaturation beforeAnchors beforeCharge beforeProfile beforeCode) :=
  Prod.Lex.right witness (Prod.Lex.right span (Prod.Lex.right mode
    (Prod.Lex.right frontier (Prod.Lex.right projection
      (Prod.Lex.left _ _ smaller)))))

theorem terminalResidualRank_anchorCount_lt
    (witness span mode frontier projection saturation
      afterAnchors beforeAnchors : Nat)
    (afterCharge afterProfile afterCode beforeCharge beforeProfile beforeCode : Nat)
    (smaller : afterAnchors < beforeAnchors) :
    (TerminalResidualRank.mk witness span mode frontier projection saturation
      afterAnchors afterCharge afterProfile afterCode).LexLT
    (TerminalResidualRank.mk witness span mode frontier projection saturation
      beforeAnchors beforeCharge beforeProfile beforeCode) :=
  Prod.Lex.right witness (Prod.Lex.right span (Prod.Lex.right mode
    (Prod.Lex.right frontier (Prod.Lex.right projection
      (Prod.Lex.right saturation (Prod.Lex.left _ _ smaller))))))

theorem terminalResidualRank_chargeSize_lt
    (witness span mode frontier projection saturation anchors
      afterCharge beforeCharge : Nat)
    (afterProfile afterCode beforeProfile beforeCode : Nat)
    (smaller : afterCharge < beforeCharge) :
    (TerminalResidualRank.mk witness span mode frontier projection saturation
      anchors afterCharge afterProfile afterCode).LexLT
    (TerminalResidualRank.mk witness span mode frontier projection saturation
      anchors beforeCharge beforeProfile beforeCode) :=
  Prod.Lex.right witness (Prod.Lex.right span (Prod.Lex.right mode
    (Prod.Lex.right frontier (Prod.Lex.right projection
      (Prod.Lex.right saturation (Prod.Lex.right anchors
        (Prod.Lex.left _ _ smaller)))))))

theorem terminalResidualRank_profileSize_lt
    (witness span mode frontier projection saturation anchors charge
      afterProfile beforeProfile : Nat)
    (afterCode beforeCode : Nat)
    (smaller : afterProfile < beforeProfile) :
    (TerminalResidualRank.mk witness span mode frontier projection saturation
      anchors charge afterProfile afterCode).LexLT
    (TerminalResidualRank.mk witness span mode frontier projection saturation
      anchors charge beforeProfile beforeCode) :=
  Prod.Lex.right witness (Prod.Lex.right span (Prod.Lex.right mode
    (Prod.Lex.right frontier (Prod.Lex.right projection
      (Prod.Lex.right saturation (Prod.Lex.right anchors
        (Prod.Lex.right charge (Prod.Lex.left _ _ smaller))))))))

theorem terminalResidualRank_canonicalCode_lt
    (witness span mode frontier projection saturation anchors charge profile
      afterCode beforeCode : Nat)
    (smaller : afterCode < beforeCode) :
    (TerminalResidualRank.mk witness span mode frontier projection saturation
      anchors charge profile afterCode).LexLT
    (TerminalResidualRank.mk witness span mode frontier projection saturation
      anchors charge profile beforeCode) :=
  Prod.Lex.right witness (Prod.Lex.right span (Prod.Lex.right mode
    (Prod.Lex.right frontier (Prod.Lex.right projection
      (Prod.Lex.right saturation (Prod.Lex.right anchors
        (Prod.Lex.right charge (Prod.Lex.right profile smaller))))))))

/-! ## Proof-bearing descent boundary -/

/-- A route may claim rank descent only by carrying the kernel proposition for
    its concrete before/after ranks. This record does not manufacture a route
    or infer descent from a Boolean flag. -/
structure TerminalResidualRankDescent where
  before : TerminalResidualRank
  after : TerminalResidualRank
  decreasing : after.LexLT before

def TerminalResidualRankDescent.Sound
    (descent : TerminalResidualRankDescent) : Prop :=
  descent.after.LexLT descent.before

theorem TerminalResidualRankDescent.sound
    (descent : TerminalResidualRankDescent) : descent.Sound :=
  descent.decreasing

end DirectWire
end PNP

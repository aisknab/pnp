/-
Copyright (c) 2026 PNP Labs.

Complete finite enumeration and signed maximization of the tight four-corner
bases attached to a computed terminal support square.  Each corner list is
bounded by that corner's existing ambient implementation, filtered to the
exact profile-constrained minimum, and then crossed with the other three
lists.  The existing executable coherence query filters the resulting finite
family.  No caller supplies a candidate list, coherence certificate, maximum,
or schedule.

This reconstructs the remaining local `BN2-CoherentOptimum` maximum in
Section 11.1 of the pinned manuscript: `delta_i(A,B)` is the maximum of the
signed incidence values of the complete finite tight-basis family whenever
the selected local coherence route is silent.  The quotient-promotion query
remains separate and unused.  This module does not prove BN2 square
legitimacy, connect local failures to the global no-outcome route system,
derive SaturatePositive, BCELReady, ZeroSlack, PCCMin, polynomial runtime,
SAT in P, or P = NP.
-/

import PNP.ResidualTerminalFourCornerSideTightCompletion

namespace PNP
namespace DirectWire

/-- One untyped implementation at every named corner.  Profile matching,
    exact minimality, and coherence are checked by the finite definitions
    below rather than carried as caller-supplied fields. -/
structure TerminalFourCornerImplementationBasis (inputs outputs : Nat) where
  meet : Implementation inputs outputs
  left : Implementation inputs outputs
  right : Implementation inputs outputs
  join : Implementation inputs outputs

/-- Select the implementation at one named corner. -/
def TerminalFourCornerImplementationBasis.at
    {inputs outputs : Nat}
    (basis : TerminalFourCornerImplementationBasis inputs outputs) :
    TerminalSupportSquareCorner -> Implementation inputs outputs
  | .meet => basis.meet
  | .left => basis.left
  | .right => basis.right
  | .join => basis.join

/-- Gate counts of all four named implementations. -/
def TerminalFourCornerImplementationBasis.sizes
    {inputs outputs : Nat}
    (basis : TerminalFourCornerImplementationBasis inputs outputs) :
    TerminalFourCornerSizes :=
  { meet := basis.meet.gateCount
    left := basis.left.gateCount
    right := basis.right.gateCount
    join := basis.join.gateCount }

/-- The exact four-corner minimum vector selected by one comparison mode. -/
def TerminalOptimumCoherenceMode.minimumSizes
    {inputs outputs profileWidth : Nat}
    (mode : TerminalOptimumCoherenceMode)
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) :
    TerminalFourCornerSizes :=
  match mode with
  | .full => corners.fullMinimumSizes
  | .quotient => corners.quotientMinimumSizes

/-- The signed minimum incidence value selected by one comparison mode. -/
def TerminalOptimumCoherenceMode.delta
    {inputs outputs profileWidth : Nat}
    (mode : TerminalOptimumCoherenceMode)
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) : Int :=
  match mode with
  | .full => corners.fullDelta
  | .quotient => corners.quotientDelta

/-- Exact executable profile matcher selected by one comparison mode. -/
def TerminalOptimumCoherenceMode.profileMatchBool
    {inputs outputs profileWidth : Nat}
    (mode : TerminalOptimumCoherenceMode)
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth)
    (corner : TerminalSupportSquareCorner)
    (implementation : Implementation inputs outputs) : Bool :=
  match mode with
  | .full => terminalFullProfileMatchBool corners.system
      (corners.at corner) implementation
  | .quotient => terminalQuotientProfileMatchBool corners.system
      corners.projection (corners.at corner) implementation

/-- Every selected minimum is bounded by the current implementation at its
    corner, so the corner-local bounded enumeration is complete. -/
theorem TerminalOptimumCoherenceMode.minimumAt_le_current
    {inputs outputs profileWidth : Nat}
    (mode : TerminalOptimumCoherenceMode)
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth)
    (corner : TerminalSupportSquareCorner) :
    (mode.minimumSizes corners).at corner ≤
      (corners.at corner).gateCount := by
  cases mode <;> cases corner
  · exact terminalFullProfileMinimum_le
      (terminalCurrentFullCarrierRealization corners.system corners.meet)
  · exact terminalFullProfileMinimum_le
      (terminalCurrentFullCarrierRealization corners.system corners.left)
  · exact terminalFullProfileMinimum_le
      (terminalCurrentFullCarrierRealization corners.system corners.right)
  · exact terminalFullProfileMinimum_le
      (terminalCurrentFullCarrierRealization corners.system corners.join)
  · exact terminalQuotientProfileMinimum_le
      (terminalCurrentQuotientComparison corners.system corners.projection
        corners.meet)
  · exact terminalQuotientProfileMinimum_le
      (terminalCurrentQuotientComparison corners.system corners.projection
        corners.left)
  · exact terminalQuotientProfileMinimum_le
      (terminalCurrentQuotientComparison corners.system corners.projection
        corners.right)
  · exact terminalQuotientProfileMinimum_le
      (terminalCurrentQuotientComparison corners.system corners.projection
        corners.join)

/-- Forget only the intrinsic bound proof of a bounded exact candidate. -/
def BoundedCandidate.implementation
    {inputs outputs gateBound : Nat}
    (candidate : BoundedCandidate inputs outputs gateBound) :
    Implementation inputs outputs :=
  ⟨candidate.1.val, candidate.2⟩

/-- Every exact profile-constrained minimum implementation at one corner.
    The bound is the existing ambient implementation at that same corner. -/
def TerminalProjectionFourCorners.minimumImplementationsAt
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (corner : TerminalSupportSquareCorner) :
    List (Implementation inputs outputs) :=
  ((allBoundedCandidates inputs outputs (corners.at corner).gateCount).filter
      fun candidate =>
        mode.profileMatchBool corners corner candidate.implementation &&
          candidate.1.val == (mode.minimumSizes corners).at corner).map
    BoundedCandidate.implementation

/-- The corner list is sound: every member matches the selected profile mode
    and has exactly the selected minimum gate count. -/
theorem TerminalProjectionFourCorners.mem_minimumImplementationsAt_sound
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (corner : TerminalSupportSquareCorner)
    (implementation : Implementation inputs outputs)
    (member : implementation ∈ corners.minimumImplementationsAt mode corner) :
    mode.profileMatchBool corners corner implementation = true ∧
      implementation.gateCount = (mode.minimumSizes corners).at corner := by
  obtain ⟨candidate, candidateMember, equal⟩ := List.mem_map.mp member
  have checked := (List.mem_filter.mp candidateMember).2
  have parts :
      mode.profileMatchBool corners corner candidate.implementation = true ∧
        (candidate.1.val == (mode.minimumSizes corners).at corner) = true := by
    simpa only [Bool.and_eq_true] using checked
  cases equal
  exact ⟨parts.1, (beq_iff_eq.mp parts.2)⟩

/-- The corner list is complete: every matching implementation at the exact
    selected minimum occurs in the bounded enumeration. -/
theorem TerminalProjectionFourCorners.mem_minimumImplementationsAt_complete
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (corner : TerminalSupportSquareCorner)
    (implementation : Implementation inputs outputs)
    (matching : mode.profileMatchBool corners corner implementation = true)
    (minimum : implementation.gateCount =
      (mode.minimumSizes corners).at corner) :
    implementation ∈ corners.minimumImplementationsAt mode corner := by
  have within : implementation.gateCount ≤
      (corners.at corner).gateCount := by
    rw [minimum]
    exact mode.minimumAt_le_current corners corner
  let bounded := boundedCandidateOfLE within implementation.candidate
  have boundedImplementation : bounded.implementation = implementation := by
    cases implementation
    rfl
  have boundedGateCount : bounded.1.val = implementation.gateCount := rfl
  apply List.mem_map.mpr
  refine ⟨bounded, List.mem_filter.mpr ⟨mem_allBoundedCandidates bounded, ?_⟩, ?_⟩
  · rw [boundedImplementation, boundedGateCount]
    simpa only [Bool.and_eq_true] using
      (And.intro matching (beq_iff_eq.mpr minimum))
  · exact boundedImplementation

/-- Exact membership characterization of a corner-local minimum list. -/
theorem TerminalProjectionFourCorners.mem_minimumImplementationsAt_iff
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (corner : TerminalSupportSquareCorner)
    (implementation : Implementation inputs outputs) :
    implementation ∈ corners.minimumImplementationsAt mode corner ↔
      mode.profileMatchBool corners corner implementation = true ∧
        implementation.gateCount =
          (mode.minimumSizes corners).at corner :=
  ⟨corners.mem_minimumImplementationsAt_sound mode corner implementation,
    fun exact => corners.mem_minimumImplementationsAt_complete mode corner
      implementation exact.1 exact.2⟩

private def fourCornerProducts
    {inputs outputs : Nat}
    (meet left right join : List (Implementation inputs outputs)) :
    List (TerminalFourCornerImplementationBasis inputs outputs) :=
  meet.flatMap fun meetImplementation =>
    left.flatMap fun leftImplementation =>
      right.flatMap fun rightImplementation =>
        join.map fun joinImplementation =>
          { meet := meetImplementation
            left := leftImplementation
            right := rightImplementation
            join := joinImplementation }

private theorem mem_fourCornerProducts_iff
    {inputs outputs : Nat}
    (meet left right join : List (Implementation inputs outputs))
    (basis : TerminalFourCornerImplementationBasis inputs outputs) :
    basis ∈ fourCornerProducts meet left right join ↔
      basis.meet ∈ meet ∧ basis.left ∈ left ∧ basis.right ∈ right ∧
        basis.join ∈ join := by
  constructor
  · intro member
    obtain ⟨meetImplementation, meetMember, leftProductMember⟩ :=
      List.mem_flatMap.mp member
    obtain ⟨leftImplementation, leftMember, rightProductMember⟩ :=
      List.mem_flatMap.mp leftProductMember
    obtain ⟨rightImplementation, rightMember, joinProductMember⟩ :=
      List.mem_flatMap.mp rightProductMember
    obtain ⟨joinImplementation, joinMember, equal⟩ :=
      List.mem_map.mp joinProductMember
    cases equal
    exact ⟨meetMember, leftMember, rightMember, joinMember⟩
  · rintro ⟨meetMember, leftMember, rightMember, joinMember⟩
    apply List.mem_flatMap.mpr
    refine ⟨basis.meet, meetMember, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨basis.left, leftMember, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨basis.right, rightMember, ?_⟩
    exact List.mem_map.mpr ⟨basis.join, joinMember, rfl⟩

/-- Complete Cartesian product of the four exact corner-minimum lists. -/
def TerminalProjectionFourCorners.minimumImplementationBases
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth)
    (mode : TerminalOptimumCoherenceMode) :
    List (TerminalFourCornerImplementationBasis inputs outputs) :=
  fourCornerProducts
    (corners.minimumImplementationsAt mode .meet)
    (corners.minimumImplementationsAt mode .left)
    (corners.minimumImplementationsAt mode .right)
    (corners.minimumImplementationsAt mode .join)

/-- Exact soundness and completeness of the four-corner minimum product. -/
theorem TerminalProjectionFourCorners.mem_minimumImplementationBases_iff
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (basis : TerminalFourCornerImplementationBasis inputs outputs) :
    basis ∈ corners.minimumImplementationBases mode ↔
      (mode.profileMatchBool corners .meet basis.meet = true ∧
        basis.meet.gateCount = (mode.minimumSizes corners).meet) ∧
      (mode.profileMatchBool corners .left basis.left = true ∧
        basis.left.gateCount = (mode.minimumSizes corners).left) ∧
      (mode.profileMatchBool corners .right basis.right = true ∧
        basis.right.gateCount = (mode.minimumSizes corners).right) ∧
      (mode.profileMatchBool corners .join basis.join = true ∧
        basis.join.gateCount = (mode.minimumSizes corners).join) := by
  rw [minimumImplementationBases, mem_fourCornerProducts_iff]
  rw [corners.mem_minimumImplementationsAt_iff mode .meet basis.meet,
    corners.mem_minimumImplementationsAt_iff mode .left basis.left,
    corners.mem_minimumImplementationsAt_iff mode .right basis.right,
    corners.mem_minimumImplementationsAt_iff mode .join basis.join]
  rfl

/-- Complete checked content of one tight coherent basis. -/
def TerminalFourCornerImplementationBasis.IsTightCoherent
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (basis : TerminalFourCornerImplementationBasis (inputs + gates) gates)
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode) : Prop :=
  let corners := carrier.optimizationCorners observe
  mode.profileMatchBool corners .meet basis.meet = true ∧
    mode.profileMatchBool corners .left basis.left = true ∧
    mode.profileMatchBool corners .right basis.right = true ∧
    mode.profileMatchBool corners .join basis.join = true ∧
    basis.sizes.NumericallySideTight (mode.minimumSizes corners) ∧
    carrier.firstBasisCoherenceFailure? observe mode basis.at = none

private def noFailureBool {failure : Type} : Option failure -> Bool
  | none => true
  | some _ => false

/-- Executable recognizer for all four profile matches, exact numerical
    tightness, and absence of a coherence failure. -/
def TerminalFourCornerCarrier.tightBasisBool
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (basis : TerminalFourCornerImplementationBasis (inputs + gates) gates) :
    Bool :=
  let corners := carrier.optimizationCorners observe
  mode.profileMatchBool corners .meet basis.meet &&
    (mode.profileMatchBool corners .left basis.left &&
      (mode.profileMatchBool corners .right basis.right &&
        (mode.profileMatchBool corners .join basis.join &&
          (basis.sizes.sideTightBool (mode.minimumSizes corners) &&
            noFailureBool
              (carrier.firstBasisCoherenceFailure? observe mode basis.at)))))

/-- The recognizer is true exactly for the proof-level tight coherent basis
    predicate. -/
theorem TerminalFourCornerCarrier.tightBasisBool_eq_true_iff
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (basis : TerminalFourCornerImplementationBasis (inputs + gates) gates) :
    carrier.tightBasisBool observe mode basis = true ↔
      basis.IsTightCoherent carrier observe mode := by
  unfold TerminalFourCornerCarrier.tightBasisBool
    TerminalFourCornerImplementationBasis.IsTightCoherent
  simp only [Bool.and_eq_true,
    TerminalFourCornerSizes.sideTightBool_eq_true_iff]
  cases carrier.firstBasisCoherenceFailure? observe mode basis.at <;>
    simp [noFailureBool]

/-- The finite tight family is the complete minimum product filtered by the
    same executable profile, size, and coherence checks. -/
def TerminalFourCornerCarrier.tightBasisFamily
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode) :
    List (TerminalFourCornerImplementationBasis (inputs + gates) gates) :=
  ((carrier.optimizationCorners observe).minimumImplementationBases mode).filter
    (carrier.tightBasisBool observe mode)

/-- Every enumerated tight basis has all checked tight-coherence properties. -/
theorem TerminalFourCornerCarrier.mem_tightBasisFamily_sound
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (basis : TerminalFourCornerImplementationBasis (inputs + gates) gates)
    (member : basis ∈ carrier.tightBasisFamily observe mode) :
    basis.IsTightCoherent carrier observe mode :=
  (carrier.tightBasisBool_eq_true_iff observe mode basis).1
    (List.mem_filter.mp member).2

/-- Every tight coherent basis is present in the finite family. -/
theorem TerminalFourCornerCarrier.mem_tightBasisFamily_complete
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (basis : TerminalFourCornerImplementationBasis (inputs + gates) gates)
    (tight : basis.IsTightCoherent carrier observe mode) :
    basis ∈ carrier.tightBasisFamily observe mode := by
  apply List.mem_filter.mpr
  refine ⟨?_, (carrier.tightBasisBool_eq_true_iff observe mode basis).2 tight⟩
  rw [(carrier.optimizationCorners observe).mem_minimumImplementationBases_iff]
  unfold TerminalFourCornerImplementationBasis.IsTightCoherent at tight
  have sizesEqual :=
    (TerminalFourCornerSizes.numericallySideTight_iff_eq _ _).1 tight.2.2.2.2.1
  have meetSize : basis.meet.gateCount =
      (mode.minimumSizes (carrier.optimizationCorners observe)).meet := by
    exact congrArg TerminalFourCornerSizes.meet sizesEqual
  have leftSize : basis.left.gateCount =
      (mode.minimumSizes (carrier.optimizationCorners observe)).left := by
    exact congrArg TerminalFourCornerSizes.left sizesEqual
  have rightSize : basis.right.gateCount =
      (mode.minimumSizes (carrier.optimizationCorners observe)).right := by
    exact congrArg TerminalFourCornerSizes.right sizesEqual
  have joinSize : basis.join.gateCount =
      (mode.minimumSizes (carrier.optimizationCorners observe)).join := by
    exact congrArg TerminalFourCornerSizes.join sizesEqual
  exact ⟨⟨tight.1, meetSize⟩, ⟨tight.2.1, leftSize⟩,
    ⟨tight.2.2.1, rightSize⟩, ⟨tight.2.2.2.1, joinSize⟩⟩

/-- Exact soundness and completeness of the complete finite tight family. -/
theorem TerminalFourCornerCarrier.mem_tightBasisFamily_iff
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (basis : TerminalFourCornerImplementationBasis (inputs + gates) gates) :
    basis ∈ carrier.tightBasisFamily observe mode ↔
      basis.IsTightCoherent carrier observe mode :=
  ⟨carrier.mem_tightBasisFamily_sound observe mode basis,
    carrier.mem_tightBasisFamily_complete observe mode basis⟩

/-- The canonical mode-appropriate four minimum implementations, viewed as
    an untyped implementation basis. -/
def TerminalFourCornerCarrier.canonicalImplementationBasis
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode) :
    TerminalFourCornerImplementationBasis (inputs + gates) gates :=
  let implementationAt :=
    (carrier.canonicalOptimumFamily observe).implementationAt mode
  { meet := implementationAt .meet
    left := implementationAt .left
    right := implementationAt .right
    join := implementationAt .join }

@[simp] theorem TerminalFourCornerCarrier.canonicalImplementationBasis_at
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (corner : TerminalSupportSquareCorner) :
    (carrier.canonicalImplementationBasis observe mode).at corner =
      (carrier.canonicalOptimumFamily observe).implementationAt mode corner := by
  cases corner <;> rfl

/-- The canonical implementation basis exactly attains the selected minimum
    vector. -/
theorem TerminalFourCornerCarrier.canonicalImplementationBasis_sizes
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode) :
    (carrier.canonicalImplementationBasis observe mode).sizes =
      mode.minimumSizes (carrier.optimizationCorners observe) := by
  cases mode <;> rfl

private theorem TerminalFourCornerCarrier.canonicalImplementationBasis_matches
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (corner : TerminalSupportSquareCorner) :
    mode.profileMatchBool (carrier.optimizationCorners observe) corner
      ((carrier.canonicalImplementationBasis observe mode).at corner) = true := by
  cases mode with
  | full =>
      rw [TerminalFourCornerCarrier.canonicalImplementationBasis_at]
      exact terminalFullProfileMatchBool_complete
        ((carrier.canonicalOptimumFamily observe).fullBasis.at corner)
  | quotient =>
      rw [TerminalFourCornerCarrier.canonicalImplementationBasis_at]
      exact terminalQuotientProfileMatchBool_complete
        ((carrier.canonicalOptimumFamily observe).quotientBasis.at corner)

/-- When the selected local route is silent, the canonical basis satisfies
    every independently recomputed tightness and coherence check. -/
theorem TerminalFourCornerCarrier.canonicalImplementationBasis_isTightCoherent
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (noRoute : carrier.NoOptimumCoherenceRoute observe mode) :
    (carrier.canonicalImplementationBasis observe mode).IsTightCoherent
      carrier observe mode := by
  unfold TerminalFourCornerImplementationBasis.IsTightCoherent
  refine ⟨carrier.canonicalImplementationBasis_matches observe mode .meet,
    carrier.canonicalImplementationBasis_matches observe mode .left,
    carrier.canonicalImplementationBasis_matches observe mode .right,
    carrier.canonicalImplementationBasis_matches observe mode .join, ?_, ?_⟩
  · exact (TerminalFourCornerSizes.numericallySideTight_iff_eq _ _).2
      (carrier.canonicalImplementationBasis_sizes observe mode)
  · have implementationsEqual :
        (carrier.canonicalImplementationBasis observe mode).at =
          (carrier.canonicalOptimumFamily observe).implementationAt mode := by
      funext corner
      exact carrier.canonicalImplementationBasis_at observe mode corner
    rw [implementationsEqual]
    rw [← carrier.firstOptimumCoherenceFailure?_eq_basis observe mode]
    exact noRoute

/-- Route silence places the canonical member in the complete finite family;
    in particular, the family is nonempty. -/
theorem TerminalFourCornerCarrier.canonicalImplementationBasis_mem_tightFamily
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (noRoute : carrier.NoOptimumCoherenceRoute observe mode) :
    carrier.canonicalImplementationBasis observe mode ∈
      carrier.tightBasisFamily observe mode :=
  carrier.mem_tightBasisFamily_complete observe mode _
    (carrier.canonicalImplementationBasis_isTightCoherent
      observe mode noRoute)

/-- Every member of the complete tight family has exactly the selected signed
    delta, including when that integer is negative. -/
theorem TerminalFourCornerCarrier.tightBasis_incidenceValue_eq_delta
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (basis : TerminalFourCornerImplementationBasis (inputs + gates) gates)
    (member : basis ∈ carrier.tightBasisFamily observe mode) :
    basis.sizes.incidenceValue =
      mode.delta (carrier.optimizationCorners observe) := by
  have tight := carrier.mem_tightBasisFamily_sound observe mode basis member
  have sizesEqual :=
    (TerminalFourCornerSizes.numericallySideTight_iff_eq _ _).1
      tight.2.2.2.2.1
  rw [sizesEqual]
  cases mode
  · exact (carrier.optimizationCorners observe).fullMinimumSizes_incidenceValue
  · exact
      (carrier.optimizationCorners observe).quotientMinimumSizes_incidenceValue

/-- Signed values of every member in the complete tight family. -/
def TerminalFourCornerCarrier.tightBasisValues
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode) : List Int :=
  (carrier.tightBasisFamily observe mode).map fun basis =>
    basis.sizes.incidenceValue

/-- Every enumerated tight-basis value is exactly the selected delta. -/
theorem TerminalFourCornerCarrier.mem_tightBasisValues_eq_delta
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (value : Int)
    (member : value ∈ carrier.tightBasisValues observe mode) :
    value = mode.delta (carrier.optimizationCorners observe) := by
  obtain ⟨basis, basisMember, equal⟩ := List.mem_map.mp member
  cases equal
  exact carrier.tightBasis_incidenceValue_eq_delta observe mode basis basisMember

private def signedMax (left right : Int) : Int :=
  if left ≤ right then right else left

/-- Maximum of a signed list without a synthetic zero seed.  An empty family
    has no maximum, and a nonempty all-negative family retains its true
    negative maximum. -/
def signedMaximum? : List Int -> Option Int
  | [] => none
  | head :: tail => some (tail.foldl signedMax head)

private theorem foldl_signedMax_eq_of_all_eq
    (values : List Int) (current expected : Int)
    (currentEqual : current = expected)
    (allEqual : forall value, value ∈ values -> value = expected) :
    values.foldl signedMax current = expected := by
  induction values generalizing current with
  | nil => exact currentEqual
  | cons head tail ih =>
      have headEqual := allEqual head (List.Mem.head tail)
      apply ih (signedMax current head)
      · cases currentEqual
        cases headEqual
        simp [signedMax]
      · intro value member
        exact allEqual value (List.Mem.tail head member)

private theorem signedMaximum?_eq_some_of_mem_and_all_eq
    (values : List Int) (expected : Int)
    (expectedMember : expected ∈ values)
    (allEqual : forall value, value ∈ values -> value = expected) :
    signedMaximum? values = some expected := by
  cases values with
  | nil => cases expectedMember
  | cons head tail =>
      change some (tail.foldl signedMax head) = some expected
      rw [foldl_signedMax_eq_of_all_eq tail head expected
        (allEqual head (List.Mem.head tail))]
      intro value member
      exact allEqual value (List.Mem.tail head member)

/-- Signed maximum of the complete finite tight-basis family. -/
def TerminalFourCornerCarrier.tightBasisMaximum?
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode) : Option Int :=
  signedMaximum? (carrier.tightBasisValues observe mode)

/-- The complete finite tight-basis maximum is exactly the selected delta
    whenever the selected local coherence route is silent. -/
theorem TerminalFourCornerCarrier.tightBasisMaximum?_eq_delta
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (noRoute : carrier.NoOptimumCoherenceRoute observe mode) :
    carrier.tightBasisMaximum? observe mode =
      some (mode.delta (carrier.optimizationCorners observe)) := by
  let canonical := carrier.canonicalImplementationBasis observe mode
  have canonicalMember :=
    carrier.canonicalImplementationBasis_mem_tightFamily
      observe mode noRoute
  have deltaMember : mode.delta (carrier.optimizationCorners observe) ∈
      carrier.tightBasisValues observe mode := by
    apply List.mem_map.mpr
    refine ⟨canonical, canonicalMember, ?_⟩
    exact carrier.tightBasis_incidenceValue_eq_delta
      observe mode canonical canonicalMember
  apply signedMaximum?_eq_some_of_mem_and_all_eq
    (carrier.tightBasisValues observe mode)
    (mode.delta (carrier.optimizationCorners observe)) deltaMember
  intro value member
  exact carrier.mem_tightBasisValues_eq_delta observe mode value member

/-- Full-profile instance of the complete tight-basis maximum theorem. -/
theorem TerminalFourCornerCarrier.tightBasisMaximum?_full
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (noRoute : carrier.NoOptimumCoherenceRoute observe .full) :
    carrier.tightBasisMaximum? observe .full =
      some (carrier.optimizationCorners observe).fullDelta :=
  carrier.tightBasisMaximum?_eq_delta observe .full noRoute

/-- Quotient-profile comparison instance.  It does not use or discharge the
    separate quotient-to-full promotion firewall. -/
theorem TerminalFourCornerCarrier.tightBasisMaximum?_quotient
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (noRoute : carrier.NoOptimumCoherenceRoute observe .quotient) :
    carrier.tightBasisMaximum? observe .quotient =
      some (carrier.optimizationCorners observe).quotientDelta :=
  carrier.tightBasisMaximum?_eq_delta observe .quotient noRoute

end DirectWire
end PNP

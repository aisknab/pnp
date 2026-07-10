/-
Copyright (c) 2026 PNP Labs.

Residual-slack accounting for the concrete Boolean direct-wire frame.  This
module is deliberately restricted to the empty-profile serial construction in
`NANDComposition`: it introduces no arbitrary support sets, profile records,
or polynomial/runtime claims.
-/

import PNP.NANDComposition
import PNP.NANDMinimum

namespace PNP
namespace DirectWire

/-! ## Typed implementations -/

/-- Forget only the static gate-count index by pairing a candidate with it. -/
def Candidate.toImplementation {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) :
    Implementation inputs outputs :=
  ⟨gates, candidate⟩

theorem Candidate.toImplementation_gateCount
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) :
    candidate.toImplementation.gateCount = gates := rfl

theorem Candidate.toImplementation_candidate
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) :
    candidate.toImplementation.candidate = candidate := rfl

/-- The implementation obtained by physically plugging a candidate into a
    concrete environment/continuation frame. -/
def FramedContext.plugImplementation
    {externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates supportGates : Nat}
    (context : FramedContext externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates)
    (support : Candidate supportInputs supportGates supportOutputs) :
    Implementation externalInputs outputs :=
  (context.plug support).toImplementation

theorem FramedContext.plugImplementation_gateCount
    {externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates supportGates : Nat}
    (context : FramedContext externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates)
    (support : Candidate supportInputs supportGates supportOutputs) :
    (context.plugImplementation support).gateCount =
      (environmentGates + supportGates) + continuationGates := rfl

/-! ## Constructive frame arithmetic -/

/-- Replacing a middle block by a smaller one changes subtraction slack by
    exactly the gate-count difference, provided the subtrahend fits in the
    smaller framed total. -/
theorem framedNatSub_difference
    {environment left right continuation minimum : Nat}
    (rightWithin : right ≤ left)
    (minimumWithin : minimum ≤ (environment + right) + continuation) :
    ((environment + left) + continuation) - minimum =
      (((environment + right) + continuation) - minimum) + (left - right) := by
  let difference := left - right
  let smallerRemainder := ((environment + right) + continuation) - minimum
  have rightPlusDifference : right + difference = left := by
    exact natAdd_sub_of_le rightWithin
  have minimumPlusRemainder :
      minimum + smallerRemainder = (environment + right) + continuation := by
    exact natAdd_sub_of_le minimumWithin
  have framedTotal :
      (environment + left) + continuation =
        minimum + (smallerRemainder + difference) := by
    calc
      (environment + left) + continuation =
          (environment + (right + difference)) + continuation := by
            rw [rightPlusDifference]
      _ = ((environment + right) + continuation) + difference := by
            calc
              (environment + (right + difference)) + continuation =
                  ((environment + right) + difference) + continuation := by
                    rw [Nat.add_assoc environment right difference]
              _ = (environment + right) + (difference + continuation) :=
                    Nat.add_assoc (environment + right) difference continuation
              _ = (environment + right) + (continuation + difference) := by
                    rw [Nat.add_comm difference continuation]
              _ = ((environment + right) + continuation) + difference :=
                    (Nat.add_assoc (environment + right) continuation difference).symm
      _ = (minimum + smallerRemainder) + difference := by
            rw [minimumPlusRemainder]
      _ = minimum + (smallerRemainder + difference) :=
            Nat.add_assoc minimum smallerRemainder difference
  rw [framedTotal]
  exact natAdd_sub_cancel_left minimum (smallerRemainder + difference)

/-- The slack internal to a middle block is bounded by the whole framed slack
    whenever the whole semantic minimum is no larger than the frame containing
    the middle semantic minimum. -/
theorem framedNatSub_lowerBound
    {environment support continuation supportMinimum wholeMinimum : Nat}
    (supportMinimumWithin : supportMinimum ≤ support)
    (wholeMinimumWithin :
      wholeMinimum ≤ (environment + supportMinimum) + continuation) :
    support - supportMinimum ≤
      ((environment + support) + continuation) - wholeMinimum := by
  let supportDifference := support - supportMinimum
  let wholeRemainder :=
    ((environment + supportMinimum) + continuation) - wholeMinimum
  have minimumPlusDifference :
      supportMinimum + supportDifference = support := by
    exact natAdd_sub_of_le supportMinimumWithin
  have wholeMinimumPlusRemainder :
      wholeMinimum + wholeRemainder =
        (environment + supportMinimum) + continuation := by
    exact natAdd_sub_of_le wholeMinimumWithin
  have framedTotal :
      (environment + support) + continuation =
        wholeMinimum + (wholeRemainder + supportDifference) := by
    calc
      (environment + support) + continuation =
          (environment + (supportMinimum + supportDifference)) + continuation := by
            rw [minimumPlusDifference]
      _ = ((environment + supportMinimum) + continuation) +
          supportDifference := by
            calc
              (environment + (supportMinimum + supportDifference)) + continuation =
                  ((environment + supportMinimum) + supportDifference) +
                    continuation := by
                    rw [Nat.add_assoc environment supportMinimum supportDifference]
              _ = (environment + supportMinimum) +
                  (supportDifference + continuation) :=
                    Nat.add_assoc (environment + supportMinimum)
                      supportDifference continuation
              _ = (environment + supportMinimum) +
                  (continuation + supportDifference) := by
                    rw [Nat.add_comm supportDifference continuation]
              _ = ((environment + supportMinimum) + continuation) +
                  supportDifference :=
                    (Nat.add_assoc (environment + supportMinimum)
                      continuation supportDifference).symm
      _ = (wholeMinimum + wholeRemainder) + supportDifference := by
            rw [wholeMinimumPlusRemainder]
      _ = wholeMinimum + (wholeRemainder + supportDifference) :=
            Nat.add_assoc wholeMinimum wholeRemainder supportDifference
  rw [framedTotal]
  rw [natAdd_sub_cancel_left]
  exact Nat.le_add_left supportDifference wholeRemainder

/-! ## Reference-minimum support replacement -/

/-- The exactly indexed reference-minimum candidate for a concrete support. -/
def Candidate.referenceMinimumReplacement
    {inputs gates outputs : Nat}
    (support : Candidate inputs gates outputs) :
    Candidate inputs (referenceMinimum support.toImplementation) outputs :=
  referenceMinimumWitness support.toImplementation

theorem Candidate.referenceMinimumReplacement_equivalent
    {inputs gates outputs : Nat}
    (support : Candidate inputs gates outputs) :
    Equivalent support.referenceMinimumReplacement.program
        support.referenceMinimumReplacement.directWireWord
      support.program support.directWireWord :=
  equivalentBool_sound
    (referenceMinimumWitness_equivalent support.toImplementation)

theorem Candidate.referenceMinimumReplacement_size
    {inputs gates outputs : Nat}
    (support : Candidate inputs gates outputs) :
    support.referenceMinimumReplacement.program.size =
      referenceMinimum support.toImplementation :=
  Candidate.program_size_eq_gateCount support.referenceMinimumReplacement

theorem Candidate.referenceMinimumReplacement_residualSlack_zero
    {inputs gates outputs : Nat}
    (support : Candidate inputs gates outputs) :
    residualSlack support.referenceMinimumReplacement.toImplementation = 0 := by
  unfold residualSlack
  rw [referenceMinimum_invariant
    support.referenceMinimumReplacement.toImplementation
    support.toImplementation
    support.referenceMinimumReplacement_equivalent]
  exact Nat.sub_self (referenceMinimum support.toImplementation)

theorem FramedContext.plug_referenceMinimumReplacement_equivalent
    {externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates supportGates : Nat}
    (context : FramedContext externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates)
    (support : Candidate supportInputs supportGates supportOutputs) :
    Equivalent
      (context.plug support.referenceMinimumReplacement).program
      (context.plug support.referenceMinimumReplacement).directWireWord
      (context.plug support).program
      (context.plug support).directWireWord :=
  compatibleReplacement_framed context
    support.referenceMinimumReplacement support
    support.referenceMinimumReplacement_equivalent

/-! ## Exact replacement and global slack laws -/

/-- Exact framed slack accounting for an equivalent, no-larger replacement. -/
theorem framedReplacement_residualSlack
    {externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates leftGates rightGates : Nat}
    (context : FramedContext externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates)
    (left : Candidate supportInputs leftGates supportOutputs)
    (right : Candidate supportInputs rightGates supportOutputs)
    (equivalent : Equivalent left.program left.directWireWord
      right.program right.directWireWord)
    (rightWithin : rightGates ≤ leftGates) :
    residualSlack (context.plugImplementation left) =
      residualSlack (context.plugImplementation right) +
        (leftGates - rightGates) := by
  let leftWhole := context.plugImplementation left
  let rightWhole := context.plugImplementation right
  have wholeEquivalent : Equivalent leftWhole.candidate.program
      leftWhole.candidate.directWireWord rightWhole.candidate.program
      rightWhole.candidate.directWireWord :=
    compatibleReplacement_framed context left right equivalent
  have minimaEqual : referenceMinimum leftWhole = referenceMinimum rightWhole :=
    referenceMinimum_invariant leftWhole rightWhole wholeEquivalent
  unfold residualSlack
  change ((environmentGates + leftGates) + continuationGates) -
      referenceMinimum leftWhole =
    (((environmentGates + rightGates) + continuationGates) -
      referenceMinimum rightWhole) + (leftGates - rightGates)
  rw [minimaEqual]
  exact framedNatSub_difference rightWithin
    (referenceMinimum_le_target rightWhole)

/-- The residual slack of a support never exceeds the residual slack of the
    whole concrete frame into which it is plugged. -/
theorem framedGlobalSlackLaw
    {externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates supportGates : Nat}
    (context : FramedContext externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates)
    (support : Candidate supportInputs supportGates supportOutputs) :
    residualSlack support.toImplementation ≤
      residualSlack (context.plugImplementation support) := by
  let supportTarget := support.toImplementation
  let wholeTarget := context.plugImplementation support
  let minimumSupport := support.referenceMinimumReplacement
  have wholeMinimumBound : referenceMinimum wholeTarget ≤
      (environmentGates + referenceMinimum supportTarget) + continuationGates := by
    apply referenceMinimum_le_of_equivalent wholeTarget
      (context.plug minimumSupport)
    exact context.plug_referenceMinimumReplacement_equivalent support
  unfold residualSlack
  change supportGates - referenceMinimum supportTarget ≤
    ((environmentGates + supportGates) + continuationGates) -
      referenceMinimum wholeTarget
  exact framedNatSub_lowerBound
    (referenceMinimum_le_target supportTarget) wholeMinimumBound

/-- Replacing one support gate gives exactly one unit of framed slack descent. -/
theorem framedReplacement_unit_descent
    {externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates leftGates rightGates : Nat}
    (context : FramedContext externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates)
    (left : Candidate supportInputs leftGates supportOutputs)
    (right : Candidate supportInputs rightGates supportOutputs)
    (equivalent : Equivalent left.program left.directWireWord
      right.program right.directWireWord)
    (oneGate : rightGates + 1 = leftGates) :
    residualSlack (context.plugImplementation left) =
      residualSlack (context.plugImplementation right) + 1 := by
  have rightWithin : rightGates ≤ leftGates := Nat.le.intro oneGate
  rw [framedReplacement_residualSlack context left right equivalent rightWithin]
  rw [← oneGate]
  rw [natAdd_sub_cancel_left]

end DirectWire
end PNP

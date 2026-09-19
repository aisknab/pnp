import PNP.NANDSemanticGateRetraction
import PNP.DirectWireBaseline

/-!
Independent research toward the manuscript's forced-cost obligation. The final
target is exact additivity for an arbitrary circuit extended by independent NAND
outputs on fresh input pairs. This file first proves the lower bound for every
circuit implementing that explicitly specified function; semantic agreement is
not a supplied lower-bound or correctness oracle. No general restoration-charge,
polynomial minimization, or global route-completeness claim is made.
-/

namespace PNP.DirectWire.FreshNandCost

variable {inputs gates outputs width : Nat}

def leftInput (index : Fin width) : Fin (inputs + (width + width)) :=
  Fin.natAdd inputs (Fin.castAdd width index)

def rightInput (index : Fin width) : Fin (inputs + (width + width)) :=
  Fin.natAdd inputs (Fin.natAdd width index)

def freshValue (valuation : Valuation (inputs + (width + width)))
    (index : Fin width) : Bool :=
  boolNand (valuation (leftInput index)) (valuation (rightInput index))

def joinInput (old : Valuation inputs) (left right : Valuation width) :
    Valuation (inputs + (width + width)) :=
  splitFin old (splitFin left right)

theorem freshValue_joinInput (old : Valuation inputs) (left right : Valuation width)
    (index : Fin width) :
    freshValue (joinInput old left right) index = boolNand (left index) (right index) := by
  unfold freshValue joinInput leftInput rightInput
  rw [splitFin_right, splitFin_left, splitFin_right, splitFin_right]

def FreshMatches (candidate : Candidate (inputs + (width + width)) gates (outputs + width)) :
    Prop :=
  ∀ valuation index, candidate.semantics valuation (Fin.natAdd outputs index) =
    freshValue valuation index

def OriginalMatches (target : Implementation inputs outputs)
    (candidate : Candidate (inputs + (width + width)) gates (outputs + width)) : Prop :=
  ∀ valuation output, candidate.semantics valuation (Fin.castAdd width output) =
    target.candidate.semantics (fun index => valuation (Fin.castAdd (width + width) index)) output

def freshCandidate (candidate : Candidate (inputs + (width + width)) gates (outputs + width)) :
    Candidate (inputs + (width + width)) gates width :=
  Candidate.ofDirectWireWord candidate.program
    ⟨fun index => candidate.directWireWord.source (Fin.natAdd outputs index)⟩

theorem freshCandidate_semantics
    (candidate : Candidate (inputs + (width + width)) gates (outputs + width))
    (valuation : Valuation (inputs + (width + width))) (index : Fin width) :
    (freshCandidate candidate).semantics valuation index =
      candidate.semantics valuation (Fin.natAdd outputs index) := by
  unfold freshCandidate
  rw [Candidate.ofDirectWireWord_semantics]
  rfl

theorem freshConditions
    (candidate : Candidate (inputs + (width + width)) gates (outputs + width))
    (matched : FreshMatches candidate) : BaselineOutputConditions (freshCandidate candidate) := by
  constructor
  · intro index
    refine ⟨fun _ => true, fun _ => false, ?_⟩
    rw [freshCandidate_semantics, matched, freshCandidate_semantics, matched]
    change false ≠ true
    decide
  · intro index input
    refine ⟨fun _ => true, ?_⟩
    rw [freshCandidate_semantics, matched]
    change false ≠ true
    decide
  · intro left right different
    let bits : Valuation width := fun index => if index = left then true else false
    refine ⟨joinInput (fun _ : Fin inputs => false) bits bits, ?_⟩
    rw [freshCandidate_semantics, matched, freshCandidate_semantics, matched]
    rw [freshValue_joinInput, freshValue_joinInput]
    simp only [bits, if_pos rfl, if_neg (Ne.symm different)]
    decide

def freshGate
    (candidate : Candidate (inputs + (width + width)) gates (outputs + width))
    (matched : FreshMatches candidate) (index : Fin width) : Fin gates :=
  outputGateIndex (freshCandidate candidate) (freshConditions candidate matched) index

theorem freshGate_source
    (candidate : Candidate (inputs + (width + width)) gates (outputs + width))
    (matched : FreshMatches candidate) (index : Fin width) :
    candidate.directWireWord.source (Fin.natAdd outputs index) =
      .gate (freshGate candidate matched index) := by
  unfold freshGate
  have sourceEqual :=
    outputGateIndex_source (freshCandidate candidate) (freshConditions candidate matched) index
  have roundTrip : (freshCandidate candidate).directWireWord.source index =
      candidate.directWireWord.source (Fin.natAdd outputs index) := by
    unfold freshCandidate
    exact Candidate.ofDirectWireWord_pointwise _ _ _
  exact roundTrip.symm.trans sourceEqual

theorem freshGate_injective
    (candidate : Candidate (inputs + (width + width)) gates (outputs + width))
    (matched : FreshMatches candidate) :
    Function.Injective (freshGate candidate matched) :=
  outputGateIndex_injective (freshCandidate candidate) (freshConditions candidate matched)

theorem freshGate_value
    (candidate : Candidate (inputs + (width + width)) gates (outputs + width))
    (matched : FreshMatches candidate)
    (valuation : Valuation (inputs + (width + width))) (index : Fin width) :
    candidate.program.eval valuation (freshGate candidate matched index) =
      freshValue valuation index := by
  have value := matched valuation index
  change (candidate.directWireWord.source (Fin.natAdd outputs index)).eval
    valuation (candidate.program.eval valuation) = _ at value
  rw [freshGate_source candidate matched] at value
  exact value

def erased
    (candidate : Candidate (inputs + (width + width)) gates (outputs + width))
    (matched : FreshMatches candidate) :
    SemanticGateRetraction.GateRecords (inputs + (width + width)) gates (outputs + width) :=
  (allFin width).map (fun index => .gate (freshGate candidate matched index))

theorem freshGate_selected
    (candidate : Candidate (inputs + (width + width)) gates (outputs + width))
    (matched : FreshMatches candidate) (index : Fin width) :
    terminalGateSelected (erased candidate matched) (freshGate candidate matched index) = true := by
  apply (terminalGateSelected_eq_true_iff _ _).mpr
  exact List.mem_map.mpr ⟨index, mem_allFin index, rfl⟩

theorem erased_count_lower_bound
    (candidate : Candidate (inputs + (width + width)) gates (outputs + width))
    (matched : FreshMatches candidate) :
    width ≤ (extractTerminalSupport candidate (erased candidate matched)).gateCount := by
  apply finCard_le_of_injective (fun index => terminalExtractionGateIndex
    candidate (erased candidate matched) (freshGate candidate matched index)
      (freshGate_selected candidate matched index))
  intro left right equal
  apply freshGate_injective candidate matched
  calc
    freshGate candidate matched left =
        terminalExtractionOrigin candidate (erased candidate matched)
          (terminalExtractionGateIndex candidate (erased candidate matched)
            (freshGate candidate matched left) (freshGate_selected candidate matched left)) :=
      (terminalExtractionOrigin_gateIndex candidate (erased candidate matched)
        (freshGate candidate matched left) (freshGate_selected candidate matched left)).symm
    _ = terminalExtractionOrigin candidate (erased candidate matched)
          (terminalExtractionGateIndex candidate (erased candidate matched)
            (freshGate candidate matched right) (freshGate_selected candidate matched right)) :=
      congrArg (terminalExtractionOrigin candidate (erased candidate matched)) equal
    _ = freshGate candidate matched right :=
      terminalExtractionOrigin_gateIndex candidate (erased candidate matched)
        (freshGate candidate matched right) (freshGate_selected candidate matched right)

def falseBinding : Fin (inputs + (width + width)) → Source inputs 0 :=
  splitFin (fun index => .input index) (fun _ => .constant false)

theorem restricted_oldInput (valuation : Valuation inputs) (index : Fin inputs) :
    SemanticGateRetraction.inducedInput (falseBinding (width := width)) valuation
      (Fin.castAdd (width + width) index) = valuation index := by
  unfold SemanticGateRetraction.inducedInput falseBinding
  rw [splitFin_left]
  rfl

theorem freshValue_restricted (valuation : Valuation inputs) (index : Fin width) :
    freshValue (SemanticGateRetraction.inducedInput falseBinding valuation) index = true := by
  unfold freshValue leftInput rightInput SemanticGateRetraction.inducedInput falseBinding
  rw [splitFin_right, splitFin_right]
  rfl

theorem erased_constant
    (candidate : Candidate (inputs + (width + width)) gates (outputs + width))
    (matched : FreshMatches candidate) :
    ∀ valuation gate, terminalGateSelected (erased candidate matched) gate = true →
      candidate.program.eval (SemanticGateRetraction.inducedInput falseBinding valuation) gate = true := by
  intro valuation gate selected
  have member := (terminalGateSelected_eq_true_iff _ _).mp selected
  obtain ⟨index, _listed, equal⟩ := List.mem_map.mp member
  have gateEqual := TerminalPrimitiveRecord.gate.inj equal
  rw [← gateEqual]
  exact (freshGate_value candidate matched _ index).trans (freshValue_restricted valuation index)

def retracted
    (candidate : Candidate (inputs + (width + width)) gates (outputs + width))
    (matched : FreshMatches candidate) : Implementation inputs (outputs + width) :=
  SemanticGateRetraction.implementation candidate (erased candidate matched) (fun _ => true)
    falseBinding

def oldCandidate
    (candidate : Candidate (inputs + (width + width)) gates (outputs + width))
    (matched : FreshMatches candidate) :
    Candidate inputs (retracted candidate matched).gateCount outputs :=
  Candidate.ofDirectWireWord (retracted candidate matched).candidate.program
    ⟨fun output => (retracted candidate matched).candidate.directWireWord.source
      (Fin.castAdd width output)⟩

theorem oldCandidate_semantics (target : Implementation inputs outputs)
    (candidate : Candidate (inputs + (width + width)) gates (outputs + width))
    (freshMatched : FreshMatches candidate) (oldMatched : OriginalMatches target candidate)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (oldCandidate candidate freshMatched).semantics valuation output =
      target.candidate.semantics valuation output := by
  unfold oldCandidate
  rw [Candidate.ofDirectWireWord_semantics]
  change (retracted candidate freshMatched).candidate.semantics valuation
    (Fin.castAdd width output) = _
  unfold retracted
  rw [SemanticGateRetraction.semantics candidate (erased candidate freshMatched)
    (fun _ => true) falseBinding (erased_constant candidate freshMatched)]
  rw [oldMatched]
  have restriction : (fun index => SemanticGateRetraction.inducedInput
      (falseBinding (width := width)) valuation (Fin.castAdd (width + width) index)) = valuation := by
    funext index
    exact restricted_oldInput valuation index
  rw [restriction]

theorem gateCount_lower_bound (target : Implementation inputs outputs)
    (candidate : Candidate (inputs + (width + width)) gates (outputs + width))
    (freshMatched : FreshMatches candidate) (oldMatched : OriginalMatches target candidate) :
    referenceMinimum target + width ≤ gates := by
  have oldLower : referenceMinimum target ≤ (retracted candidate freshMatched).gateCount :=
    referenceMinimum_le_of_equivalent target (oldCandidate candidate freshMatched)
      (oldCandidate_semantics target candidate freshMatched oldMatched)
  have freshLower := erased_count_lower_bound candidate freshMatched
  have partition := SemanticGateRetraction.gateCount_partition candidate
    (erased candidate freshMatched) (fun _ => true) falseBinding
  calc
    referenceMinimum target + width ≤ (retracted candidate freshMatched).gateCount +
        (extractTerminalSupport candidate (erased candidate freshMatched)).gateCount :=
      Nat.add_le_add oldLower freshLower
    _ = gates := partition

end PNP.DirectWire.FreshNandCost

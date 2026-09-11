import PNP.ResidualIndependentMaterializerCost

namespace PNP.DirectWire

-- Exact public interfaces at arbitrary dimensions.
example
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (count : Nat) :
    (appendIndependentNandMaterializers candidate count).program.size =
      gates + count :=
  appendIndependentNandMaterializers_size candidate count

example
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (count : Nat)
    (valuation : Valuation (inputs + (count + count))) (output : Fin outputs) :
    (appendIndependentNandMaterializers candidate count).semantics valuation
        (Fin.castAdd count output) =
      candidate.semantics
        (fun input => valuation (Fin.castAdd (count + count) input)) output :=
  appendIndependentNandMaterializers_original candidate count valuation output

example
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (count : Nat)
    (valuation : Valuation (inputs + (count + count))) (output : Fin count) :
    (appendIndependentNandMaterializers candidate count).semantics valuation
        (Fin.natAdd outputs output) =
      boolNand
        (valuation (Fin.natAdd inputs (Fin.castAdd count output)))
        (valuation (Fin.natAdd inputs (Fin.natAdd count output))) :=
  appendIndependentNandMaterializers_materializer candidate count valuation output

example
    {inputs gates outputs competingGates : Nat}
    (candidate : Candidate inputs gates outputs) (count : Nat)
    (competing : Candidate (inputs + (count + count)) competingGates (outputs + count))
    (equivalent : Equivalent competing.program competing.directWireWord
      (appendIndependentNandMaterializers candidate count).program
      (appendIndependentNandMaterializers candidate count).directWireWord) :
    referenceMinimum candidate.toImplementation + count ≤ competingGates :=
  appendIndependentNandMaterializers_lower_bound candidate count competing equivalent

example
    {inputs leftGates rightGates outputs : Nat}
    (left : Candidate inputs leftGates outputs)
    (right : Candidate inputs rightGates outputs) (count : Nat)
    (equivalent : Equivalent left.program left.directWireWord
      right.program right.directWireWord) :
    Equivalent (appendIndependentNandMaterializers left count).program
      (appendIndependentNandMaterializers left count).directWireWord
      (appendIndependentNandMaterializers right count).program
      (appendIndependentNandMaterializers right count).directWireWord :=
  appendIndependentNandMaterializers_equivalent left right count equivalent

example
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (count : Nat) :
    referenceMinimum (appendIndependentNandMaterializers candidate count).toImplementation =
      referenceMinimum candidate.toImplementation + count :=
  appendIndependentNandMaterializers_referenceMinimum candidate count

example
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (count : Nat) :
    residualSlack (appendIndependentNandMaterializers candidate count).toImplementation =
      residualSlack candidate.toImplementation :=
  appendIndependentNandMaterializers_residualSlack candidate count

#print axioms PNP.DirectWire.appendIndependentNandMaterializers_size
#print axioms PNP.DirectWire.appendIndependentNandMaterializers_original
#print axioms PNP.DirectWire.appendIndependentNandMaterializers_materializer
#print axioms PNP.DirectWire.appendIndependentNandMaterializers_lower_bound
#print axioms PNP.DirectWire.appendIndependentNandMaterializers_equivalent
#print axioms PNP.DirectWire.appendIndependentNandMaterializers_referenceMinimum
#print axioms PNP.DirectWire.appendIndependentNandMaterializers_residualSlack

namespace IndependentMaterializerRegression

def emptyCandidate : Candidate 0 0 0 :=
  Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩

def mixedWord (gates : Nat) : DirectWireWord 1 gates 4 :=
  ⟨fun output => if output.val < 2 then .constant false else .input 0⟩

-- Both constant and primary-input outputs are repeated. The physical gate
-- is redundant, so the original circuit is deliberately not minimum.
def redundantMixed : Candidate 1 1 4 :=
  Candidate.ofDirectWireWord
    (.snoc .empty { left := .input 0, right := .input 0 }) (mixedWord 1)

def zeroGateMixed : Candidate 1 0 4 :=
  Candidate.ofDirectWireWord .empty (mixedWord 0)

theorem redundantMixed_minimum : referenceMinimum redundantMixed.toImplementation = 0 := by
  apply Nat.le_zero.mp
  apply referenceMinimum_le_of_equivalent redundantMixed.toImplementation zeroGateMixed
  intro valuation output
  change zeroGateMixed.semantics valuation output =
    redundantMixed.semantics valuation output
  unfold zeroGateMixed redundantMixed
  rw [Candidate.ofDirectWireWord_semantics, Candidate.ofDirectWireWord_semantics]
  change ((mixedWord 0).source output).eval valuation _ =
    ((mixedWord 1).source output).eval valuation _
  unfold mixedWord
  dsimp only
  by_cases first : output.val < 2
  · simp only [if_pos first, Source.eval]
  · simp only [if_neg first, Source.eval]

example (count : Nat) :
    referenceMinimum
        (appendIndependentNandMaterializers redundantMixed count).toImplementation = count := by
  rw [appendIndependentNandMaterializers_referenceMinimum, redundantMixed_minimum,
    Nat.zero_add]

example (count : Nat) :
    residualSlack
        (appendIndependentNandMaterializers redundantMixed count).toImplementation = 1 := by
  rw [appendIndependentNandMaterializers_residualSlack]
  unfold residualSlack
  rw [redundantMixed_minimum]
  rfl

example {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs) :
    referenceMinimum (appendIndependentNandMaterializers candidate 0).toImplementation =
      referenceMinimum candidate.toImplementation := by
  simpa only [Nat.add_zero] using appendIndependentNandMaterializers_referenceMinimum candidate 0

example (count : Nat) :
    referenceMinimum
        (appendIndependentNandMaterializers emptyCandidate count).toImplementation = count := by
  have emptyMinimum : referenceMinimum emptyCandidate.toImplementation = 0 :=
    Nat.le_zero.mp (referenceMinimum_le_target emptyCandidate.toImplementation)
  rw [appendIndependentNandMaterializers_referenceMinimum, emptyMinimum, Nat.zero_add]

def originalNand : Candidate 2 1 1 :=
  Candidate.ofDirectWireWord
    (.snoc .empty { left := .input 0, right := .input 1 })
    ⟨fun _ => .gate 0⟩

-- The fresh bank gate is first, not a suffix. Its retained consumers
-- participate in the original output, so erasure must really rebind wires.
def interleavedProgram : Program 4 5 :=
  .snoc
    (.snoc
      (.snoc
        (.snoc
          (.snoc .empty { left := .input 2, right := .input 3 })
          { left := .gate 0, right := .constant false })
        { left := .input 0, right := .input 1 })
      { left := .gate 1, right := .gate 2 })
    { left := .gate 3, right := .gate 3 }

def interleaved : Candidate 4 5 2 :=
  Candidate.ofDirectWireWord interleavedProgram
    ⟨fun output => if output.val = 0 then .gate 4 else .gate 0⟩

theorem interleaved_equivalent :
    Equivalent interleaved.program interleaved.directWireWord
      (appendIndependentNandMaterializers originalNand 1).program
      (appendIndependentNandMaterializers originalNand 1).directWireWord :=
  equivalentBool_sound (by decide)

example : referenceMinimum originalNand.toImplementation + 1 ≤ 5 :=
  appendIndependentNandMaterializers_lower_bound originalNand 1
    interleaved interleaved_equivalent

-- Repeating an output or reusing the original input pair does not earn
-- a fresh independent unit: both outputs can share one physical NAND.
def repeatedNonfresh : Candidate 2 1 2 :=
  Candidate.ofDirectWireWord originalNand.program ⟨fun _ => .gate 0⟩

example : ¬ 2 ≤ referenceMinimum repeatedNonfresh.toImplementation := by
  have bound := referenceMinimum_le_target repeatedNonfresh.toImplementation
  change referenceMinimum repeatedNonfresh.toImplementation ≤ 1 at bound
  omega

-- Execute only the small construction/Boolean semantics, not reference minima.
-- This guarded runtime assertion is regression evidence, never theorem authority.
#eval do
  let one := appendIndependentNandMaterializers redundantMixed 1
  let two := appendIndependentNandMaterializers emptyCandidate 2
  let valuation : Valuation 4 :=
    fun index => if index.val = 0 ∨ index.val = 2 then true else false
  let outputs := (allFin 2).map (two.semantics valuation)
  if one.program.size == 2 && two.program.size == 2 &&
      outputs == [false, true] &&
      equivalentBool interleaved (appendIndependentNandMaterializers originalNand 1) then
    IO.println "m240-independent-materializer-construction-execution-ok"
  else
    throw (IO.userError "M240 independent materializer execution regression failed")

end IndependentMaterializerRegression

end PNP.DirectWire

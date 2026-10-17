import PNP.Concrete.ResidualReduction.SourceSelectorMenus
import PNP.Concrete.ResidualReduction.SourceSelectorResult
import PNP.Concrete.ResidualReduction.SourcePolynomialAffineQuery

/-! A closed affine-first selector block. The line menu is built only after
affine failure; plane pairs are built from the retained menu only after line
failure. Every search and construction is counted. This is the prepared-state
selector, not yet an all-bitstring Choice codec or a complete contraction. -/

namespace PNP.Concrete.ResidualReduction.SourceSelectorDispatch
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.SourceSelectionInvocation (Data)
open PNP.Concrete.ResidualReduction.SourceCandidateLoad (Held)
open PNP.Concrete.ResidualReduction.SourceCandidateSearch (current optional)
open PNP.Concrete.ResidualReduction.SourceCandidateQueries (base lineHit planeHit linePayload planePayload)
open PNP.Concrete.ResidualReduction.SourceSelectorState
open PNP.Concrete.ResidualReduction.SourceSelectorResult

theorem line_correct {n : Nat} (F : Family n) (a : Affine n) (w : LineWitness n F.length) (d : Data)
    (h : SourceCandidateSearch.Correct (base F 1) MatrixInstructions.affineWord linePayload
      (some (a,w)) d) : Correct F (.line a w) d :=
  ⟨⟨h.1,h.2.2.1⟩,h.2.1,h.2.2.2.1,h.2.2.2.2⟩
theorem plane_correct {n : Nat} (F : Family n)
    (hit : Option ((Affine n × Affine n) × (Point F.length × Point n))) (d : Data)
    (h : SourceCandidateSearch.Correct (base F 2) SourcePlaneMenuBytes.pairWord planePayload hit d) :
    Correct F (fromPlane hit) d := by
  cases hit with
  | none => exact ⟨⟨h.1,h.2.2.1⟩,h.2.2.2⟩
  | some pair =>
    rcases pair with ⟨p,w⟩
    exact ⟨⟨h.1,h.2.2.1⟩,h.2.1,h.2.2.2.1,h.2.2.2.2⟩

def lineStage : Block 48 := .seq SourceSelectorMenus.line (Frame.block 2 SourceCandidateQueries.line)
def planeStage : Block 48 := .seq SourceSelectorMenus.plane (Frame.block 2 SourceCandidateQueries.plane)
def lineStagePolynomial : NatPolynomial :=
  .add SourceSelectorMenus.linePolynomial SourceCandidateBudget.lineCostPolynomial
def planeStagePolynomial : NatPolynomial :=
  .add SourceSelectorMenus.planePolynomial SourceCandidateBudget.planeCostPolynomial

theorem lineStage_exec {n : Nat} (F : Family n) (count : Nat) (r : Store 38)
    (normal packet output oldMenu : BitString) (t : Held) :
    ∃ used after d, Exec lineStage
      (full r (current (base F count) normal packet output) t
        ⟨oldMenu,List.replicate (n + 1) true⟩) used
      (full after d ⟨[],List.replicate (n + 1) true⟩ (SourceSelectorMenus.retained F)) ∧
      SourceCandidateSearch.Correct (base F 1) MatrixInstructions.affineWord linePayload
        (lineHit F (sourceMenu F)) d ∧
      used ≤ lineStagePolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := by
  obtain ⟨menuUsed,middle,built,menuBound⟩ :=
    SourceSelectorMenus.line_exec F count r normal packet output oldMenu t
  obtain ⟨queryUsed,after,d,queried,correct,queryBound⟩ :=
    SourceCandidateBudget.line_menu_exec F middle normal packet output
  have last := Frame.execution queried (SourceSelectorMenus.retained F).store
  refine ⟨menuUsed + queryUsed,after,d,Exec.seq built last,correct,?_⟩
  simp only [lineStagePolynomial,NatPolynomial.eval_add]
  omega

theorem planeStage_exec {n : Nat} (F : Family n) (count : Nat) (r : Store 38)
    (normal packet output : BitString) (t : Held) :
    ∃ used after d, Exec planeStage
      (full r (current (base F count) normal packet output) t (SourceSelectorMenus.retained F)) used
      (full after d ⟨[],List.replicate (2 * (n + 1)) true⟩ (SourceSelectorMenus.retained F)) ∧
      Correct F (fromPlane (planeHit F (planeMenu (sourceMenu F)))) d ∧
      used ≤ planeStagePolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := by
  obtain ⟨menuUsed,middle,built,menuBound⟩ :=
    SourceSelectorMenus.plane_exec F count r normal packet output t
  obtain ⟨queryUsed,after,d,queried,correct,queryBound⟩ :=
    SourceCandidateBudget.plane_menu_exec F middle normal packet output
  have last := Frame.execution queried (SourceSelectorMenus.retained F).store
  refine ⟨menuUsed + queryUsed,after,d,Exec.seq built last,plane_correct F _ d correct,?_⟩
  simp only [planeStagePolynomial,NatPolynomial.eval_add]
  omega

def afterLine : Block 48 := .branch 43 .skip planeStage .skip
def lineFlow : Block 48 := .seq lineStage afterLine
def lineFlowPolynomial : NatPolynomial :=
  .add lineStagePolynomial (.add planeStagePolynomial (.constant 2))

theorem lineFlow_exec {n : Nat} (F : Family n) (count : Nat) (r : Store 38)
    (normal packet output oldMenu : BitString) (t : Held) :
    ∃ used after d lastHeld, Exec lineFlow
      (full r (current (base F count) normal packet output) t
        ⟨oldMenu,List.replicate (n + 1) true⟩) used
      (full after d lastHeld (SourceSelectorMenus.retained F)) ∧
      Correct F (remainder F) d ∧
      used ≤ lineFlowPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := by
  obtain ⟨used,middle,d,checked,correct,bound⟩ :=
    lineStage_exec F count r normal packet output oldMenu t
  cases hit : lineHit F (sourceMenu F) with
  | some pair =>
    rcases pair with ⟨a,w⟩
    rw [hit] at correct
    have output : d.output = true :: linePayload w := correct.2.2.2.2
    have stopped : Exec afterLine
        (full middle d ⟨[],List.replicate (n + 1) true⟩ (SourceSelectorMenus.retained F)) 2
        (full middle d ⟨[],List.replicate (n + 1) true⟩ (SourceSelectorMenus.retained F)) :=
      Exec.one ((output_get _ _ _ _).trans output) (.skip _)
    refine ⟨used + 2,middle,d,⟨[],List.replicate (n + 1) true⟩,
      Exec.seq checked stopped,?_,?_⟩
    · simpa only [remainder,hit] using line_correct F a w d correct
    · simp only [lineFlowPolynomial,NatPolynomial.eval_add,NatPolynomial.eval_constant]
      omega
  | none =>
    rw [hit] at correct
    have currentData := correct_current (base F 1) d MatrixInstructions.affineWord linePayload none correct
    obtain ⟨tailUsed,last,after,continued,tailCorrect,tailBound⟩ :=
      planeStage_exec F 1 middle d.normals d.packet d.output ⟨[],List.replicate (n + 1) true⟩
    rw [← currentData] at continued
    have finish : Exec afterLine
        (full middle d ⟨[],List.replicate (n + 1) true⟩ (SourceSelectorMenus.retained F))
        (1 + tailUsed)
        (full last after ⟨[],List.replicate (2 * (n + 1)) true⟩ (SourceSelectorMenus.retained F)) :=
      Exec.zero ((output_get _ _ _ _).trans correct.2.2.2) continued
    refine ⟨used + (1 + tailUsed),last,after,⟨[],List.replicate (2 * (n + 1)) true⟩,
      Exec.seq checked finish,?_,?_⟩
    · simpa only [remainder,hit] using tailCorrect
    · simp only [lineFlowPolynomial,NatPolynomial.eval_add,NatPolynomial.eval_constant]
      omega

def affine : Block 48 := Frame.block 2 (Frame.block 2
  (SourceSelectionQueryCall.affineCall (4 : Fin 6) 5))
def sourceData {n : Nat} (F : Family n) (normal output : BitString) : Data :=
  current (base F 0) normal (SourceMatrixEncoding.codec.encode ⟨n,F⟩) output
def affinePolynomial : NatPolynomial := .add SourcePolynomialAffineQuery.sourceFuel (.constant 40)

theorem affine_exec {n : Nat} (F : Family n) (r : Store 38)
    (normal output : BitString) (t : Held) (s : Saved) :
    ∃ used after, Exec affine (full r (sourceData F normal output) t s) used
      (full after (sourceData F normal (optional planePayload (sourceAffineQuery F))) t s) ∧
      used ≤ affinePolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := by
  let d := sourceData F normal output
  obtain ⟨used,after,checked,bound⟩ := SourceSelectionQueryCall.affine_call_exec r d.store (4 : Fin 6) 5
  have packet : d.store.get 4 = SourceMatrixEncoding.codec.encode ⟨n,F⟩ := rfl
  rw [packet,SourceAffineRawQuery.answer_canonical,← SourceCandidateQueries.plane_optional] at checked
  have run := Frame.execution (Frame.execution checked t.store) s.store
  refine ⟨used,after,?_,?_⟩
  · simpa only [affine,full,SourceCandidateLoad.full,SourceSelectionInvocation.full,d,
      sourceData,current,Data.store,Store.set,Store.indexCases] using run
  · rw [packet] at bound
    simp only [affinePolynomial,NatPolynomial.eval_add,NatPolynomial.eval_constant,
      SourcePolynomialAffineQuery.sourceFuel_eval]
    omega

def afterAffine : Block 48 := .branch 43 .skip lineFlow .skip
def block : Block 48 := .seq affine afterAffine
def costPolynomial : NatPolynomial := .add affinePolynomial (.add lineFlowPolynomial (.constant 2))
def initial {n : Nat} (F : Family n) (r : Store 38)
    (normal output oldMenu : BitString) (t : Held) : Store 48 :=
  full r (sourceData F normal output) t ⟨oldMenu,List.replicate (n + 1) true⟩

theorem block_exec {n : Nat} (F : Family n) (r : Store 38)
    (normal output oldMenu : BitString) (t : Held) :
    ∃ used after d lastHeld lastSaved,
      Exec block (initial F r normal output oldMenu t) used (full after d lastHeld lastSaved) ∧
      Correct F (select F) d ∧
      used ≤ costPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := by
  let s : Saved := ⟨oldMenu,List.replicate (n + 1) true⟩
  obtain ⟨used,middle,checked,bound⟩ := affine_exec F r normal output t s
  cases hit : sourceAffineQuery F with
  | some w =>
    rw [hit] at checked
    let d := sourceData F normal (optional planePayload (some w))
    have stopped : Exec afterAffine (full middle d t s) 2 (full middle d t s) :=
      Exec.one (output_get _ _ _ _) (.skip _)
    refine ⟨used + 2,middle,d,t,s,Exec.seq checked stopped,?_,?_⟩
    · simp only [select,hit]
      exact ⟨⟨rfl,rfl⟩,rfl,rfl⟩
    · simp only [costPolynomial,NatPolynomial.eval_add,NatPolynomial.eval_constant]
      omega
  | none =>
    rw [hit] at checked
    obtain ⟨tailUsed,last,d,lastHeld,continued,tailCorrect,tailBound⟩ :=
      lineFlow_exec F 0 middle normal (SourceMatrixEncoding.codec.encode ⟨n,F⟩)
        [false] oldMenu t
    have finish : Exec afterAffine
        (full middle (sourceData F normal [false]) t s) (1 + tailUsed)
        (full last d lastHeld (SourceSelectorMenus.retained F)) :=
      Exec.zero (output_get _ _ _ _) continued
    refine ⟨used + (1 + tailUsed),last,d,lastHeld,SourceSelectorMenus.retained F,
      Exec.seq checked finish,?_,?_⟩
    · simpa only [select,hit] using tailCorrect
    · simp only [costPolynomial,NatPolynomial.eval_add,NatPolynomial.eval_constant]
      omega

def program : Program 48 := block.program 0 43
theorem program_run {n : Nat} (F : Family n) (r : Store 38)
    (normal output oldMenu : BitString) (t : Held) :
    ∃ used after d lastHeld lastSaved,
      BitRegister.run program (used + 1) ⟨.running 0,initial F r normal output oldMenu t⟩ =
        ⟨.accepted,full after d lastHeld lastSaved⟩ ∧ Correct F (select F) d ∧
      used + 1 ≤ costPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length + 1 := by
  obtain ⟨used,after,d,lastHeld,lastSaved,checked,correct,bound⟩ :=
    block_exec F r normal output oldMenu t
  exact ⟨used,after,d,lastHeld,lastSaved,checked.program_run 0 43,correct,by omega⟩

end PNP.Concrete.ResidualReduction.SourceSelectorDispatch

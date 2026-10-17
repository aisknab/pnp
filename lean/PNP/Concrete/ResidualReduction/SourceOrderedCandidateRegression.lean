import PNP.Concrete.ResidualReduction.SourceCandidateBudget
import Lean

/-! Ordered-search contracts and adversarial driver regressions. Literal query
fixtures test the new control flow; existing query implementations are covered
by their reused general execution theorems. No fixture is roadmap credit. -/

namespace PNP.Concrete.ResidualReduction.SourceCandidateSearch.Regression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceCandidateSearch
open PNP.Concrete.ResidualReduction.SourceCandidateLoad (Held full)
open PNP.Concrete.ResidualReduction.SourceSelectionInvocation (Data)

private def query : Nat → Option Nat
  | 1 => some 7
  | 2 => some 9
  | _ => none

example : first query [] = none := rfl
example : first query [0,3,0] = none := rfl
example : first query [0,1,2] = some (1,7) := rfl
example : first query [0,2,1] = some (2,9) := rfl
example : first query [1,1,2] = some (1,7) := rfl
example : first query [0,0,2,0,1] = some (2,9) := rfl
example : first query [1,2] ≠ first query [2,1] := by decide
example : ¬ 0 < (0 : Nat) := by decide

example {α β : Type} (answer : α → Option β) (xs : List α) :
    first answer xs = SourceChain.firstSome (fun a => (answer a).map (fun b => (a,b))) xs :=
  first_exact answer xs
example {α β γ : Type} (answer : α → Option β) (f : α × β → γ) (xs : List α) :
    (first answer xs).map f =
      SourceChain.firstSome (fun a => (answer a).map (fun b => f (a,b))) xs :=
  first_map answer f xs
example (width budget : Nat) : loopBound width budget 0 = 1 := by
  simp only [loopBound,Nat.mul_zero,Nat.zero_add]
example (width budget : Nat) :
    2 + loopBound width budget 1 = SourceCandidateLoad.fuel width + budget + 6 := by
  unfold loopBound
  omega
example (r : Store 38) (d : Data) (t : Held) :
    Exec initialise (full r d t) 2 (full r {d with output := [false]} t) :=
  initialise_exec r d t
example (r : Store 38) (d : Data) (t : Held) (h : d.output = [false]) :
    Exec decision (full r d t) 2 (full r d t) := decision_none r d t h
example (r : Store 38) (d : Data) (t : Held) (tail : BitString)
    (h : d.output = true :: tail) :
    Exec decision (full r d t) 2 (full r d {t with pending := []}) :=
  decision_some r d t tail h
example (r : Store 38) (d : Data) (front suffix : BitString) :
    Exec SourceCandidateLoad.block
      (full r d ⟨front ++ suffix,List.replicate front.length true⟩)
      (SourceCandidateLoad.fuel front.length)
      (full (SourceCandidateLoad.core (SourceCandidateLoad.loaded front suffix))
        {d with normals := front} ⟨suffix,List.replicate front.length true⟩) :=
  SourceCandidateLoad.block_exec r d front suffix

example {α β : Type} (base : Data) (encode : α → BitString) (payload : β → BitString) (d : Data)
    (h : Correct base encode payload none d) : d.output = [false] := h.2.2.2
example {α β : Type} (base : Data) (encode : α → BitString) (payload : β → BitString)
    (a : α) (value : β) (d : Data) (h : Correct base encode payload (some (a,value)) d) :
    d.normals = encode a ∧ d.output = true :: payload value := h.2.2.2

example {n : Nat} (F : Family n) (us : List (Affine n)) :
    (SourceCandidateQueries.lineHit F us).map (fun p => SourceWitnessSelection.lineChoice p.1 p.2) =
      SourceWitnessSelection.lineSearch F us := SourceCandidateQueries.line_selection_exact F us
example {n : Nat} (F : Family n) (ps : List (Affine n × Affine n)) :
    (SourceCandidateQueries.planeHit F ps).map (fun p => SourceWitnessSelection.planeChoice p.1 p.2) =
      SourceWitnessSelection.planeSearch F ps := SourceCandidateQueries.plane_selection_exact F ps

example (r : Store 38) (d : Data) (width : BitString) :
    Exec SourceCandidateQueries.line (full r d ⟨[],width⟩) 3
      (full r {d with output := [false]} ⟨[],width⟩) :=
  Exec.seq (initialise_exec r d ⟨[],width⟩) (Exec.loopStop (pending_get _ _ _))
example (r : Store 38) (d : Data) (width : BitString) :
    Exec SourceCandidateQueries.plane (full r d ⟨[],width⟩) 3
      (full r {d with output := [false]} ⟨[],width⟩) :=
  Exec.seq (initialise_exec r d ⟨[],width⟩) (Exec.loopStop (pending_get _ _ _))

example {n : Nat} (F : Family n) :
    2 + loopBound (n + 1) (SourceCandidateQueries.lineBudget F) (sourceMenu F).length ≤
      SourceCandidateBudget.lineCostPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length :=
  SourceCandidateBudget.line_original_bound F
example {n : Nat} (F : Family n) :
    2 + loopBound (2 * (n + 1)) (SourceCandidateQueries.planeBudget F)
      (planeMenu (sourceMenu F)).length ≤
      SourceCandidateBudget.planeCostPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length :=
  SourceCandidateBudget.plane_original_bound F

example {n : Nat} (F : Family n) (r : Store 38) (normal packet oldOutput : BitString) :
    ∃ used after d,
      Exec SourceCandidateQueries.line (full r
        (current (SourceCandidateQueries.base F 1) normal packet oldOutput)
        ⟨MatrixInstructions.matrixBits (sourceMenu F),List.replicate (n + 1) true⟩) used
        (full after d ⟨[],List.replicate (n + 1) true⟩) ∧
      Correct (SourceCandidateQueries.base F 1) MatrixInstructions.affineWord
        SourceCandidateQueries.linePayload (SourceCandidateQueries.lineHit F (sourceMenu F)) d ∧
      used ≤ SourceCandidateBudget.lineCostPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length :=
  SourceCandidateBudget.line_menu_exec F r normal packet oldOutput
example {n : Nat} (F : Family n) (r : Store 38) (normal packet oldOutput : BitString) :
    ∃ used after d,
      Exec SourceCandidateQueries.plane (full r
        (current (SourceCandidateQueries.base F 2) normal packet oldOutput)
        ⟨SourcePlaneMenuBytes.pairBits (planeMenu (sourceMenu F)),List.replicate (2 * (n + 1)) true⟩) used
        (full after d ⟨[],List.replicate (2 * (n + 1)) true⟩) ∧
      Correct (SourceCandidateQueries.base F 2) SourcePlaneMenuBytes.pairWord
        SourceCandidateQueries.planePayload
        (SourceCandidateQueries.planeHit F (planeMenu (sourceMenu F))) d ∧
      used ≤ SourceCandidateBudget.planeCostPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length :=
  SourceCandidateBudget.plane_menu_exec F r normal packet oldOutput

#eval (show IO Unit from do
  let literalQuery : Block 44 := .seq (.action (.clear 43))
    (.branch 40 (.action (.push 43 false)) (.action (.push 43 false)) (.action (.copy 43 40)))
  let program := (block literalQuery).program 0 43
  let data : Data := ⟨[true,false],[true,false],[true,true,true],
    [false,true,true],[true,false,true],[true,true]⟩
  let dirty := (((Store.empty 38).set 0 [true,true]).set 3 [true,false]).set 37 [true]
  let cases : List (List BitString × BitString × BitString) :=
    [([],data.normals,[false]),
     ([[false,false]],[false,false],[false]),
     ([[false,false],[false,true]],[false,true],[false]),
     ([[false,true],[true,false],[true,true]],[true,false],[true,false]),
     ([[true,true],[true,false]],[true,true],[true,true]),
     ([[true,false],[true,false],[true,true]],[true,false],[true,false])]
  for (records,expectedNormal,expectedOutput) in cases do
    let input := full dirty data ⟨words id records,List.replicate 2 true⟩
    let final := BitRegister.run program 1024 ⟨.running 0,input⟩
    if final.control != .accepted || final.store.get 40 != expectedNormal ||
        final.store.get 43 != expectedOutput || final.store.get 44 != [] ||
        final.store.get 45 != [true,true] || final.store.get 38 != data.dimension ||
        final.store.get 39 != data.count || final.store.get 41 != data.family ||
        final.store.get 42 != data.packet then
      throw (IO.userError "Ordered first-success driver regression failed")
  let loader := SourceCandidateLoad.block.program 0 40
  for (front,suffix) in [([false,true],[true,false]),([true,false],[false,true]),([], [true])] do
    let final := BitRegister.run loader (SourceCandidateLoad.fuel front.length + 1)
      ⟨.running 0,full dirty data ⟨front ++ suffix,List.replicate front.length true⟩⟩
    if final.control != .accepted || final.store.get 40 != front ||
        final.store.get 44 != suffix || final.store.get 41 != data.family ||
        final.store.get 43 != data.output then
      throw (IO.userError "Complete candidate record loader regression failed"))

run_cmd do
  for name in [
    ``SourceCandidateLoad.loadWords_exec,
    ``SourceCandidateLoad.prepare_exec,
    ``SourceCandidateLoad.readRecord_exec,
    ``SourceCandidateLoad.capture_exec,
    ``SourceCandidateLoad.block_exec,
    ``SourceCandidateLoad.preserved_source,
    ``SourceCandidateSearch.first_exact,
    ``SourceCandidateSearch.first_map,
    ``SourceCandidateSearch.pending_get,
    ``SourceCandidateSearch.output_get,
    ``SourceCandidateSearch.initialise_exec,
    ``SourceCandidateSearch.decision_none,
    ``SourceCandidateSearch.decision_some,
    ``SourceCandidateSearch.words_present,
    ``SourceCandidateSearch.loop_exec,
    ``SourceCandidateSearch.block_exec,
    ``SourceCandidateQueries.line_optional,
    ``SourceCandidateQueries.plane_optional,
    ``SourceCandidateQueries.line_current,
    ``SourceCandidateQueries.plane_current,
    ``SourceCandidateQueries.line_contract,
    ``SourceCandidateQueries.plane_contract,
    ``SourceCandidateQueries.line_bytes,
    ``SourceCandidateQueries.plane_bytes,
    ``SourceCandidateQueries.line_exec,
    ``SourceCandidateQueries.plane_exec,
    ``SourceCandidateQueries.line_selection_exact,
    ``SourceCandidateQueries.plane_selection_exact,
    ``SourceCandidateQueries.line_program_run,
    ``SourceCandidateQueries.plane_program_run,
    ``SourceCandidateBudget.lineQueryPolynomial_eval,
    ``SourceCandidateBudget.planeQueryPolynomial_eval,
    ``SourceCandidateBudget.lineCostPolynomial_eval,
    ``SourceCandidateBudget.planeCostPolynomial_eval,
    ``SourceCandidateBudget.line_query_bound,
    ``SourceCandidateBudget.plane_query_bound,
    ``SourceCandidateBudget.line_count_bound,
    ``SourceCandidateBudget.plane_count_bound,
    ``SourceCandidateBudget.line_original_bound,
    ``SourceCandidateBudget.plane_original_bound,
    ``SourceCandidateBudget.line_menu_exec,
    ``SourceCandidateBudget.plane_menu_exec] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceCandidateSearch.loop_exec
#print axioms PNP.Concrete.ResidualReduction.SourceCandidateQueries.line_exec
#print axioms PNP.Concrete.ResidualReduction.SourceCandidateQueries.plane_exec
#print axioms PNP.Concrete.ResidualReduction.SourceCandidateBudget.line_menu_exec
#print axioms PNP.Concrete.ResidualReduction.SourceCandidateBudget.plane_menu_exec

end PNP.Concrete.ResidualReduction.SourceCandidateSearch.Regression

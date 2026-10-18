import PNP.Concrete.ResidualReduction.SourceSelectorDispatch
import Lean

/-! Prepared-selector contracts, skipped fallback branches, stale work registers,
source-derived menu retention and doubled-width handoff. The finite runtime
fixtures are regressions only; arbitrary-family correctness and instruction
bounds come from the execution theorems, not from these examples. -/

namespace PNP.Concrete.ResidualReduction.SourceSelectorDispatch.Regression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceSelectionInvocation (Data)
open PNP.Concrete.ResidualReduction.SourceCandidateLoad (Held)
open PNP.Concrete.ResidualReduction.SourceCandidateSearch (current optional)
open PNP.Concrete.ResidualReduction.SourceCandidateQueries (base)
open PNP.Concrete.ResidualReduction.SourceSelectorState
open PNP.Concrete.ResidualReduction.SourceSelectorResult

example (r : Store 38) (d : Data) (t : Held) (s : Saved) :
    Exec (countWrite []) (full r d t s) 1 (full r {d with count := []} t s) :=
  countWrite_exec r d t s []
example (r : Store 38) (d : Data) (t : Held) (s : Saved) :
    Exec (countWrite (natural 2)) (full r d t s) 4
      (full r {d with count := natural 2} t s) := countWrite_exec r d t s _
example (r : Store 38) (d : Data) (t : Held) (s : Saved) :
    Exec reset (full r d t s) 39 (full (Store.empty 38) d t s) := reset_exec r d t s
example (r : Store 38) (d : Data) (t : Held) (s : Saved) :
    Exec (copyMenu 7) (full r d t s) 1 (full r d t {s with menu := r.get 7}) :=
  copyMenu_exec r d t s 7
example (r : Store 38) (d : Data) (t : Held) (s : Saved) :
    Exec copyWidth (full r d t s) 1 (full r d {t with width := s.width} s) :=
  copyWidth_exec r d t s
example (r : Store 38) (d : Data) (t : Held) (s : Saved) (answer : BitString)
    (h : d.output = true :: answer) :
    Exec afterAffine (full r d t s) 2 (full r d t s) :=
  Exec.one ((output_get r d t s).trans h) (.skip _)
example (r : Store 38) (d : Data) (t : Held) (s : Saved) (answer : BitString)
    (h : d.output = true :: answer) :
    Exec afterLine (full r d t s) 2 (full r d t s) :=
  Exec.one ((output_get r d t s).trans h) (.skip _)

example {n : Nat} (F : Family n) :
    choice (select F) = SourceWitnessSelection.choose F := select_choice F
example {n : Nat} (F : Family (n + 1)) :
    globalStep F = (choice (select F)).bind (SourceWitnessSelection.build F) := global_exact F
example {n : Nat} (F : Family (n + 1)) (w : SourceWitnessSelection.Choice (n + 1) F.length)
    (h : choice (select F) = some w) : ∃ step, SourceWitnessSelection.build F w = some step :=
  selected_builds F w h
example {n m : Nat} (d : Data) :
    Realises (Result.absent : Result n m) d ↔ d.output = [false] := Iff.rfl
example {n m : Nat} (w : Point m × Point n) (d : Data)
    (h : Realises (.affine w) d) : d.count = natural 0 := h.1
example {n m : Nat} (a : Affine n) (w : SourceLine.LineWitness n m) (d : Data)
    (h : Realises (.line a w) d) : d.count = natural 1 ∧ d.normals = MatrixInstructions.affineWord a :=
  ⟨h.1,h.2.1⟩
example {n m : Nat} (p : Affine n × Affine n) (w : Point m × Point n) (d : Data)
    (h : Realises (.plane p w) d) : d.count = natural 2 ∧ d.normals = SourcePlaneMenuBytes.pairWord p :=
  ⟨h.1,h.2.1⟩
example (r : Occurrence.Registers) (width : Nat)
    (h : r.target = List.replicate width true) :
    Exec SourceSelectorMenus.doubleWidth r.store (3 * width + 3)
      (SourceSelectorMenus.doubled r width).store := SourceSelectorMenus.doubleWidth_exec r width h
example {n : Nat} (F : Family n) (r : Store 38) (normal output oldMenu : BitString) (t : Held) :
    ∃ used after d lastHeld lastSaved,
      Exec block (initial F r normal output oldMenu t) used (full after d lastHeld lastSaved) ∧
      Correct F (select F) d ∧
      used ≤ costPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length :=
  block_exec F r normal output oldMenu t
example {n : Nat} (F : Family n) (r : Store 38) (normal output oldMenu : BitString) (t : Held) :
    ∃ used after d lastHeld lastSaved,
      BitRegister.run program (used + 1) ⟨.running 0,initial F r normal output oldMenu t⟩ =
        ⟨.accepted,full after d lastHeld lastSaved⟩ ∧ Correct F (select F) d ∧
      used + 1 ≤ costPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length + 1 :=
  program_run F r normal output oldMenu t

#eval (show IO Unit from do
  let dirty := (((Store.empty 38).set 0 [true,false]).set 7 [false,true]).set 37 [true,true]
  let data : Data := ⟨[true,false],[true,true,false],[false,true],
    [true,false,true],[false,true,false],[true,false]⟩
  let held : Held := ⟨[true,false,true],[false]⟩
  let saved : Saved := ⟨[false,true,true],[true,true]⟩
  -- Both successful-route branches must leave every register unchanged.
  for branch in [afterAffine,afterLine] do
    let final := BitRegister.run (branch.program 0 43) 3 ⟨.running 0,full dirty data held saved⟩
    if final.control != .accepted then
      throw (IO.userError "Successful selector branch did not skip fallback")
    for i in List.finRange 48 do
      if final.store.get i != (full dirty data held saved).get i then
        throw (IO.userError "Skipped fallback changed a protected register")
  for word in [[],[false],[true,false],[true,true,false]] do
    let final := BitRegister.run ((countWrite word).program 0 39) (word.length + 2)
      ⟨.running 0,full dirty data held saved⟩
    if final.control != .accepted || final.store.get 39 != word ||
        final.store.get 38 != data.dimension || final.store.get 41 != data.family ||
        final.store.get 43 != data.output || final.store.get 46 != saved.menu ||
        final.store.get 47 != saved.width then
      throw (IO.userError "Selector route-tag write corrupted retained data")
  let cases : List (Family 2) :=
    [[],[⟨true,(true,(false,false)),(false,(true,false))⟩],
      [⟨true,(true,(false,true)),(false,(true,true))⟩,
       ⟨true,(true,(false,true)),(false,(true,true))⟩]]
  for F in cases do
    let input := full dirty (current (base F 0) data.normals data.packet data.output)
      held ⟨saved.menu,List.replicate 3 true⟩
    let mut menuState := BitRegister.run (SourceSelectorMenus.line.program 0 44) 0 ⟨.running 0,input⟩
    for _ in [0:20000] do
      if menuState.control == .accepted then break
      menuState := BitRegister.run (SourceSelectorMenus.line.program 0 44) 1 menuState
    let expected := MatrixInstructions.matrixBits (sourceMenu F)
    if menuState.control != .accepted || menuState.store.get 44 != expected ||
        menuState.store.get 46 != expected || menuState.store.get 45 != List.replicate 3 true ||
        menuState.store.get 47 != List.replicate 3 true ||
        menuState.store.get 39 != natural 1 || menuState.store.get 41 != input.get 41 ||
        menuState.store.get 43 != data.output then
      throw (IO.userError "Source-derived selector menu handoff failed")
    let mut pairState := BitRegister.run (SourceSelectorMenus.plane.program 0 44) 0 ⟨.running 0,menuState.store⟩
    for _ in [0:20000] do
      if pairState.control == .accepted then break
      pairState := BitRegister.run (SourceSelectorMenus.plane.program 0 44) 1 pairState
    if pairState.control != .accepted ||
        pairState.store.get 44 != SourcePlaneMenuBytes.pairBits (planeMenu (sourceMenu F)) ||
        pairState.store.get 45 != List.replicate 6 true || pairState.store.get 39 != natural 2 ||
        pairState.store.get 46 != expected || pairState.store.get 47 != List.replicate 3 true ||
        pairState.store.get 38 != input.get 38 || pairState.store.get 41 != input.get 41 ||
        pairState.store.get 42 != data.packet || pairState.store.get 43 != data.output then
      throw (IO.userError "Retained-menu plane fallback handoff failed")
  let cases : List (Sigma Family) :=
    [⟨0,[]⟩,⟨1,[]⟩,⟨2,[⟨true,(true,(false,false)),(false,(true,false))⟩]⟩]
  for ⟨n,F⟩ in cases do
    let input := initial F dirty data.normals data.output saved.menu held
    let mut final := BitRegister.run program 0 ⟨.running 0,input⟩
    for _ in [0:50000] do
      if final.control == .accepted then break
      final := BitRegister.run program 1 final
    if final.control != .accepted || final.store.get 38 != natural n ||
        final.store.get 41 != (SourceEncoding.familyCodec n).encode F ||
        final.store.get 47 != List.replicate (n + 1) true then
      throw (IO.userError "Prepared selector failed to terminate or preserve its source")
    match select F with
    | .absent =>
      if final.store.get 43 != [false] || final.store.get 39 != natural 2 then
        throw (IO.userError "All-searches-absent selector output mismatch")
    | .affine w =>
      if final.store.get 43 != optional SourceCandidateQueries.planePayload (some w) ||
          final.store.get 39 != natural 0 || final.store.get 46 != saved.menu ||
          final.store.get 44 != held.pending || final.store.get 45 != held.width then
        throw (IO.userError "Affine success incorrectly entered a later search")
    | .line a w =>
      if final.store.get 43 != optional SourceCandidateQueries.linePayload (some w) ||
          final.store.get 39 != natural 1 ||
          final.store.get 40 != MatrixInstructions.affineWord a then
        throw (IO.userError "First line success was lost or entered the plane search")
    | .plane p w =>
      if final.store.get 43 != optional SourceCandidateQueries.planePayload (some w) ||
          final.store.get 39 != natural 2 ||
          final.store.get 40 != SourcePlaneMenuBytes.pairWord p then
        throw (IO.userError "Plane fallback selected different normals or witness"))

run_cmd do
  for name in [
    ``SourceSelectorState.output_get,
    ``SourceSelectorState.pending_get,
    ``SourceSelectorState.menu_get,
    ``SourceSelectorState.width_get,
    ``SourceSelectorState.countPrefix_exec,
    ``SourceSelectorState.countWrite_exec,
    ``SourceSelectorState.reset_exec,
    ``SourceSelectorState.data_current,
    ``SourceSelectorState.correct_current,
    ``SourceSelectorState.prefix_working_get,
    ``SourceSelectorState.copyPending_exec,
    ``SourceSelectorState.copyMenu_exec,
    ``SourceSelectorState.copyWidth_exec,
    ``SourceSelectorMenus.lineLoad_exec,
    ``SourceSelectorMenus.linePrepare_exec,
    ``SourceSelectorMenus.lineCapture_exec,
    ``SourceSelectorMenus.line_exec,
    ``SourceSelectorMenus.planeLoad_exec,
    ``SourceSelectorMenus.planePrepare_exec,
    ``SourceSelectorMenus.widthLoop_exec,
    ``SourceSelectorMenus.doubleWidth_exec,
    ``SourceSelectorMenus.planeCapture_exec,
    ``SourceSelectorMenus.plane_exec,
    ``SourceSelectorResult.fromPlane_choice,
    ``SourceSelectorResult.select_choice,
    ``SourceSelectorResult.global_exact,
    ``SourceSelectorResult.selected_builds,
    ``SourceSelectorDispatch.line_correct,
    ``SourceSelectorDispatch.plane_correct,
    ``SourceSelectorDispatch.lineStage_exec,
    ``SourceSelectorDispatch.planeStage_exec,
    ``SourceSelectorDispatch.lineFlow_exec,
    ``SourceSelectorDispatch.affine_exec,
    ``SourceSelectorDispatch.block_exec,
    ``SourceSelectorDispatch.program_run] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceSelectorMenus.line_exec
#print axioms PNP.Concrete.ResidualReduction.SourceSelectorMenus.plane_exec
#print axioms PNP.Concrete.ResidualReduction.SourceSelectorResult.global_exact
#print axioms PNP.Concrete.ResidualReduction.SourceSelectorDispatch.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceSelectorDispatch.program_run

end PNP.Concrete.ResidualReduction.SourceSelectorDispatch.Regression

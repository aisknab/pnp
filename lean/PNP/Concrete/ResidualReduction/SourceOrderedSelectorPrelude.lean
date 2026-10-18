import PNP.Concrete.ResidualReduction.SourceOrderedMatrixScan

/-! The exact two-scan prelude of BilinearSelection.select.
The second scan is skipped when the first fails. Both original matrices are
retained, and all four coordinates are computed, not supplied. -/

namespace PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra
open PNP.Concrete.ResidualReduction.SourceLinePullback
  (copy_to_saved copy_from_saved clear_core transfers transfers_exec)

structure Saved where
  normal : BitString := []
  activity : BitString := []
  width : BitString := []
  firstRow : BitString := []
  firstColumn : BitString := []

def Saved.store (s : Saved) : Store 5 :=
  .cons s.normal (.cons s.activity (.cons s.width (.cons s.firstRow (.cons s.firstColumn .nil))))
def store (r : Registers) (s : Saved) : Store 14 := Frame.join r.store s.store
def data {m n : Nat} (A C : Matrix m n) : Saved :=
  ⟨coefficientMatrixBits A, coefficientMatrixBits C, List.replicate n true, [], []⟩
def ready (r : Registers) (s : Saved) : Registers :=
  {r with input := s.activity, target := s.normal, mode := s.width, excess := [], sign := [], output := []}
def prepareActions : List (Action 14) := [.copy 0 10, .copy 1 9, .copy 5 11, .clear 3, .clear 4, .clear 8]
def prepare : Block 14 := transfers prepareActions

theorem prepare_exec (r : Registers) (s : Saved) :
    Exec prepare (store r s) 7 (store (ready r s) s) := by
  exact transfers_exec prepareActions (store r s)

def captured (r : Registers) (s : Saved) : Saved :=
  {s with firstRow := r.target, firstColumn := r.excess}
def capture : Block 14 := transfers [.copy 12 1, .copy 13 3]
theorem capture_exec (r : Registers) (s : Saved) :
    Exec capture (store r s) 3 (store r (captured r s)) := by
  exact Exec.seq (copy_to_saved r.store s.store 3 1)
    (Exec.seq (copy_to_saved r.store ({s with firstRow := r.target}).store 4 3) (.skip _))

def first {m n : Nat} (r : Registers) (A C : Matrix m n) : Registers := SourceOrderedMatrixScan.result r false A C
def second {m n : Nat} (r : Registers) (A C : Matrix m n) : Registers := SourceOrderedMatrixScan.result (first r A C) true A C
def afterFirst {m n : Nat} (r : Registers) (A C : Matrix m n) : Store 14 :=
  store (first r A C) (data A C)
def afterSecond {m n : Nat} (r : Registers) (A C : Matrix m n) : Store 14 :=
  store (second r A C) (captured (first r A C) (data A C))
def continuation : Block 14 :=
  .seq capture (.seq prepare (Frame.block 5 (SourceOrderedMatrixScan.block true)))
def finish : Block 14 := .branch 4 .skip .skip continuation
def block : Block 14 :=
  .seq prepare (.seq (Frame.block 5 (SourceOrderedMatrixScan.block false)) finish)

def firstFound {m n : Nat} (A C : Matrix m n) : Bool := (SourceOrderedScan.matrixSearch false A C).1
def result {m n : Nat} (r : Registers) (A C : Matrix m n) : Store 14 :=
  if firstFound A C then afterSecond r A C else afterFirst r A C
def finishFuel {m n : Nat} (A C : Matrix m n) : Nat :=
  if firstFound A C then 1 + (3 + (7 + SourceOrderedMatrixScan.fuel true A C)) else 2
def fuel {m n : Nat} (A C : Matrix m n) : Nat :=
  7 + (SourceOrderedMatrixScan.fuel false A C + finishFuel A C)

theorem first_exec {m n : Nat} (r : Registers) (A C : Matrix m n) :
    Exec (Frame.block 5 (SourceOrderedMatrixScan.block false)) (store (ready r (data A C)) (data A C))
      (SourceOrderedMatrixScan.fuel false A C) (afterFirst r A C) :=
  Frame.execution (SourceOrderedMatrixScan.block_exec r false A C) (data A C).store

theorem continuation_exec {m n : Nat} (r : Registers) (A C : Matrix m n) :
    Exec continuation (afterFirst r A C) (3 + (7 + SourceOrderedMatrixScan.fuel true A C)) (afterSecond r A C) := by
  exact Exec.seq (capture_exec (first r A C) (data A C))
    (Exec.seq (prepare_exec (first r A C) (captured (first r A C) (data A C)))
      (Frame.execution (SourceOrderedMatrixScan.block_exec (first r A C) true A C)
        (captured (first r A C) (data A C)).store))

theorem first_flag {m n : Nat} (r : Registers) (A C : Matrix m n) :
    (afterFirst r A C).get 4 = SourceOrderedScan.flag (firstFound A C) := by
  have framed := Frame.get_core (first r A C).store (data A C).store (4 : Fin 9)
  change (afterFirst r A C).get 4 = (first r A C).store.get 4 at framed
  rw [framed]
  have flag := SourceOrderedMatrixScan.result_flag r false A C
  cases found : (SourceOrderedScan.matrixSearch false A C).1 <;>
    simpa only [first, firstFound, SourceOrderedMatrixScan.entry, found, Bool.false_eq_true,
      if_false, if_true, Option.isSome_some, Option.isSome_none] using flag

theorem finish_exec {m n : Nat} (r : Registers) (A C : Matrix m n) :
    Exec finish (afterFirst r A C) (finishFuel A C) (result r A C) := by
  cases found : firstFound A C with
  | false =>
    simp only [finishFuel, result, found, Bool.false_eq_true, if_false]
    exact Exec.empty ((first_flag r A C).trans (by rw [found]; rfl)) (Exec.skip _)
  | true =>
    simp only [finishFuel, result, found, if_true]
    exact Exec.one ((first_flag r A C).trans (by rw [found]; rfl)) (continuation_exec r A C)

theorem block_exec {m n : Nat} (r : Registers) (A C : Matrix m n) :
    Exec block (store r (data A C)) (fuel A C) (result r A C) :=
  Exec.seq (prepare_exec r (data A C)) (Exec.seq (first_exec r A C) (finish_exec r A C))

def entryPair {m n : Nat} (A C : Matrix m n) : Option ((Nat × Nat) × (Nat × Nat)) :=
  (SourceOrderedMatrixScan.entry false A C).bind fun e => (SourceOrderedMatrixScan.entry true A C).map (fun f => (e, f))

theorem entry_pair_exact {m n : Nat} (A C : Matrix m n) :
    ((BilinearSelection.scan (fun e : Fin m × Fin n => C e.1 e.2) (BilinearSelection.entries m n)).1.bind
      fun e => (BilinearSelection.scan (fun f : Fin m × Fin n => Bool.xor (C f.1 f.2) (A f.1 f.2))
        (BilinearSelection.entries m n)).1.map (fun f => ((e.1.val, e.2.val), (f.1.val, f.2.val)))) =
      entryPair A C := by
  unfold entryPair
  rw [← SourceOrderedMatrixScan.entry_exact false A C, ← SourceOrderedMatrixScan.entry_exact true A C]
  rw [SourceOrderedScan.nonzero_predicate, SourceOrderedScan.difference_predicate]
  simp only [Option.bind_map, Option.map_map, Function.comp_def]

theorem pair_none_first {m n : Nat} (A C : Matrix m n) (h : firstFound A C = false) :
    entryPair A C = none := by
  simp only [entryPair, SourceOrderedMatrixScan.entry, firstFound] at h ⊢
  rw [h]
  rfl

theorem result_flag {m n : Nat} (r : Registers) (A C : Matrix m n) :
    (result r A C).get 4 = SourceOrderedScan.flag (entryPair A C).isSome := by
  cases found : firstFound A C with
  | false =>
    simp only [result, found, Bool.false_eq_true, if_false, pair_none_first A C found, Option.isSome_none]
    exact (first_flag r A C).trans (by rw [found])
  | true =>
    simp only [result, found, if_true]
    have framed := Frame.get_core (second r A C).store (captured (first r A C) (data A C)).store (4 : Fin 9)
    change (afterSecond r A C).get 4 = (second r A C).store.get 4 at framed
    rw [framed]
    have checked := SourceOrderedMatrixScan.result_flag (first r A C) true A C
    have original : (SourceOrderedScan.matrixSearch false A C).1 = true := found
    simpa only [second, entryPair, SourceOrderedMatrixScan.entry, original, if_true,
      Option.bind_some, Option.isSome_map] using checked

theorem result_coordinates {m n : Nat} (r : Registers) (A C : Matrix m n)
    (e f : Nat × Nat) (h : entryPair A C = some (e, f)) :
    (result r A C).get 12 = List.replicate e.1 true ∧
      (result r A C).get 13 = List.replicate e.2 true ∧
      (result r A C).get 1 = List.replicate f.1 true ∧
      (result r A C).get 3 = List.replicate f.2 true := by
  cases he : SourceOrderedMatrixScan.entry false A C with
  | none => simp only [entryPair, he, Option.bind_none, reduceCtorEq] at h
  | some e' =>
    cases hf : SourceOrderedMatrixScan.entry true A C with
    | none => simp only [entryPair, he, hf, Option.bind_some, Option.map_none, reduceCtorEq] at h
    | some f' =>
      have equal : (e', f') = (e, f) := by
        simpa only [entryPair, he, hf, Option.bind_some, Option.map_some, Option.some.injEq] using h
      cases equal
      have found : firstFound A C = true := by
        cases hh : firstFound A C with
        | true => rfl
        | false => have absent := pair_none_first A C hh; rw [absent] at h; cases h
      rw [result, found]
      have firstCoordinates := SourceOrderedMatrixScan.result_coordinates r false A C e he
      have secondCoordinates := SourceOrderedMatrixScan.result_coordinates (first r A C) true A C f hf
      exact ⟨firstCoordinates.1, firstCoordinates.2, secondCoordinates.1, secondCoordinates.2⟩

theorem retained_normal {m n : Nat} (r : Registers) (A C : Matrix m n) :
    (result r A C).get 9 = coefficientMatrixBits A := by
  cases found : firstFound A C <;> simp only [result, found, Bool.false_eq_true, if_false, if_true]
  · exact Frame.get_frame (first r A C).store (data A C).store (0 : Fin 5)
  · exact Frame.get_frame (second r A C).store (captured (first r A C) (data A C)).store (0 : Fin 5)

theorem retained_activity {m n : Nat} (r : Registers) (A C : Matrix m n) :
    (result r A C).get 10 = coefficientMatrixBits C := by
  cases found : firstFound A C <;> simp only [result, found, Bool.false_eq_true, if_false, if_true]
  · exact Frame.get_frame (first r A C).store (data A C).store (1 : Fin 5)
  · exact Frame.get_frame (second r A C).store (captured (first r A C) (data A C)).store (1 : Fin 5)

def selectedSeeds {m n : Nat} (A C : Matrix m n) :
    Option ((Fin m × Fin n) × (Fin m × Fin n)) :=
  (BilinearSelection.scan (fun e : Fin m × Fin n => C e.1 e.2)
    (BilinearSelection.entries m n)).1.bind fun e =>
      (BilinearSelection.scan (fun f : Fin m × Fin n => Bool.xor (C f.1 f.2) (A f.1 f.2))
        (BilinearSelection.entries m n)).1.map (fun f => (e, f))

theorem selected_seeds_exact {m n : Nat} (A C : Matrix m n) :
    (selectedSeeds A C).map (fun p => ((p.1.1.val, p.1.2.val), (p.2.1.val, p.2.2.val))) =
      entryPair A C := by
  simpa only [selectedSeeds, Option.map_bind, Option.map_map, Function.comp_def] using entry_pair_exact A C

/-- The remaining candidate phase must consume these exact seeds in the
existing nine-candidate order; a different valid witness is not substituted. -/
theorem select_from_seeds {m n : Nat} (A C : Matrix m n) :
    (BilinearSelection.select A C).witness =
      (selectedSeeds A C).bind fun p =>
        (BilinearSelection.scan (BilinearSelection.accepts A C)
          (BilinearSelection.candidates p.1.1 p.2.1 p.1.2 p.2.2)).1 := by
  cases hn : (BilinearSelection.scan (fun e : Fin m × Fin n => C e.1 e.2)
    (BilinearSelection.entries m n)).1 with
  | none => simp only [BilinearSelection.select, selectedSeeds, hn, Option.bind_none]
  | some e =>
    cases hd : (BilinearSelection.scan (fun f : Fin m × Fin n => Bool.xor (C f.1 f.2) (A f.1 f.2))
      (BilinearSelection.entries m n)).1 <;>
      simp only [BilinearSelection.select, selectedSeeds, hn, hd,
        Option.bind_some, Option.map_none, Option.map_some, Option.bind_none]

theorem fuel_bound {m n : Nat} (A C : Matrix m n) :
    fuel A C ≤ 26 * (m * n) + 46 := by
  have firstBound := SourceOrderedMatrixScan.fuel_bound false A C
  have secondBound := SourceOrderedMatrixScan.fuel_bound true A C
  unfold fuel finishFuel
  split <;> omega

theorem source_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    fuel (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha) ≤
      52 * ((SourceDirectionEncoding.codec.encode ⟨n, [alpha], F⟩).length *
        (SourceDirectionEncoding.codec.encode ⟨n, [alpha], F⟩).length) + 46 := by
  have firstBound := SourceOrderedMatrixScan.source_bound F alpha false
  have secondBound := SourceOrderedMatrixScan.source_bound F alpha true
  unfold fuel finishFuel
  split <;> omega

def costPolynomial : NatPolynomial :=
  .add (.mul (.constant 26) (.mul .variable .variable)) (.constant 46)
def sourceCostPolynomial : NatPolynomial :=
  .add (.mul (.constant 52) (.mul .variable .variable)) (.constant 46)
theorem costPolynomial_eval (L : Nat) : costPolynomial.eval L = 26 * (L * L) + 46 := rfl
theorem sourceCostPolynomial_eval (L : Nat) : sourceCostPolynomial.eval L = 52 * (L * L) + 46 := rfl

def program : Program 14 := block.program 0 4
theorem program_run {m n : Nat} (r : Registers) (A C : Matrix m n) :
    BitRegister.run program (fuel A C + 1) ⟨.running 0, store r (data A C)⟩ =
      ⟨.accepted, result r A C⟩ := (block_exec r A C).program_run 0 4

end PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude

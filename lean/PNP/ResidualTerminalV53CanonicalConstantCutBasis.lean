/-
Copyright (c) 2026 PNP Labs.

Exact sparse constant-cut basis for the V53 hypergraph boundary.

The earlier complete activation classifier scans every proper carrier subset.
V53 rigidity makes that unnecessary for a sparse positive hypergraph.  At two
anchors the full-span weight suffices; at three anchors the three singleton
cuts suffice by complement symmetry; and at four or more anchors V53 proves
that constant cuts are equivalent to full-span-only support with the declared
full weight.

The classifier below checks only those canonical data.  It returns a typed
structural failure rather than silently treating a failed basis as constant.
This removes one powerset scan but proves no encoded-size bound for upstream
construction, no complete BN3--BN6 or PkgC route, no ZeroSlack or PCCMin result,
and no SAT-in-P or P = NP theorem.
-/

import PNP.ResidualTerminalConstantCutHypergraphRigidity

namespace PNP
namespace DirectWire

/-! ## Exact complement symmetry -/

/-- A carrier-contained hyperedge crosses a cut exactly when it crosses the
    canonical carrier complement of that cut. -/
theorem TerminalV53Hyperedge.crosses_complement_iff
    {Atom : Type} [DecidableEq Atom]
    (cell : TerminalV53Hyperedge Atom)
    (carrier cut : List Atom)
    (footprintSublist : cell.footprint.Sublist carrier) :
    cell.Crosses (terminalV54Complement carrier cut) ↔
      cell.Crosses cut := by
  constructor
  · rintro ⟨⟨outside, outsideFootprint, outsideComplement⟩,
      ⟨inside, insideFootprint, insideNotComplement⟩⟩
    have outsideNotCut : outside ∉ cut :=
      (mem_terminalV54Complement_iff carrier cut outside).1
        outsideComplement |>.2
    have insideCarrier : inside ∈ carrier :=
      footprintSublist.subset insideFootprint
    have insideCut : inside ∈ cut := by
      by_cases insideMember : inside ∈ cut
      · exact insideMember
      · exact False.elim (insideNotComplement
          ((mem_terminalV54Complement_iff carrier cut inside).2
            ⟨insideCarrier, insideMember⟩))
    exact ⟨⟨inside, insideFootprint, insideCut⟩,
      ⟨outside, outsideFootprint, outsideNotCut⟩⟩
  · rintro ⟨⟨inside, insideFootprint, insideCut⟩,
      ⟨outside, outsideFootprint, outsideNotCut⟩⟩
    have insideCarrier : inside ∈ carrier :=
      footprintSublist.subset insideFootprint
    have outsideCarrier : outside ∈ carrier :=
      footprintSublist.subset outsideFootprint
    have outsideComplement :
        outside ∈ terminalV54Complement carrier cut :=
      (mem_terminalV54Complement_iff carrier cut outside).2
        ⟨outsideCarrier, outsideNotCut⟩
    have insideNotComplement :
        inside ∉ terminalV54Complement carrier cut := by
      intro insideComplement
      exact (mem_terminalV54Complement_iff carrier cut inside).1
        insideComplement |>.2 insideCut
    exact ⟨⟨outside, outsideFootprint, outsideComplement⟩,
      ⟨inside, insideFootprint, insideNotComplement⟩⟩

/-- Executable crossing bits inherit exact complement symmetry. -/
theorem TerminalV53Hyperedge.crossesBool_complement
    {Atom : Type} [DecidableEq Atom]
    (cell : TerminalV53Hyperedge Atom)
    (carrier cut : List Atom)
    (footprintSublist : cell.footprint.Sublist carrier) :
    cell.crossesBool (terminalV54Complement carrier cut) =
      cell.crossesBool cut := by
  have equalTrue :
      cell.crossesBool (terminalV54Complement carrier cut) = true ↔
        cell.crossesBool cut = true := by
    rw [cell.crossesBool_eq_true_iff, cell.crossesBool_eq_true_iff]
    exact cell.crosses_complement_iff carrier cut footprintSublist
  cases left : cell.crossesBool (terminalV54Complement carrier cut) <;>
    cases right : cell.crossesBool cut <;> simp_all

/-- The complete sparse crossing-mass sum is invariant under canonical cut
    complementation. -/
theorem TerminalV53Hypergraph.cutWeight_complement
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (cut : List Atom) :
    system.cutWeight (terminalV54Complement system.carrier cut) =
      system.cutWeight cut := by
  unfold TerminalV53Hypergraph.cutWeight
  apply terminalV53_sum_congr
  intro cell cellMember
  unfold TerminalV53Hyperedge.cutContribution
  rw [cell.crossesBool_complement system.carrier cut
    (system.footprintSublist cell cellMember)]

/-! ## Full-span support -/

/-- A full-span cell crosses every nonempty proper carrier cut. -/
theorem TerminalV53Hypergraph.fullCell_crossesBool_eq_true
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (cell : TerminalV53Hyperedge Atom)
    (cellFull : cell.footprint = system.carrier)
    (cut : List Atom) (proper : system.ProperCut cut) :
    cell.crossesBool cut = true := by
  have carrierNotIncluded :
      ¬ TerminalV54Included system.carrier cut := by
    intro carrierIncluded
    have carrierSublistCut := terminalV53Sublist_of_included
      (List.Sublist.refl system.carrier) proper.1 system.carrierNodup
      carrierIncluded
    have equalLength : system.carrier.length = cut.length := by
      have cutLeCarrier := proper.1.length_le
      have carrierLeCut := carrierSublistCut.length_le
      omega
    have carrierCut : system.carrier = cut :=
      carrierSublistCut.eq_of_length equalLength
    exact proper.2.2 carrierCut.symm
  obtain ⟨outside, outsideCarrier, outsideNotCut⟩ :=
    terminalV53_notIncluded_has_witness system.carrier cut
      carrierNotIncluded
  have insideExists : ∃ inside, inside ∈ cut := by
    cases cut with
    | nil => exact False.elim (proper.2.1 rfl)
    | cons inside tail => exact ⟨inside, by simp⟩
  obtain ⟨inside, insideCut⟩ := insideExists
  apply (cell.crossesBool_eq_true_iff cut).2
  exact ⟨
    ⟨inside, by rw [cellFull]; exact proper.1.subset insideCut, insideCut⟩,
    ⟨outside, by rw [cellFull]; exact outsideCarrier, outsideNotCut⟩⟩

/-- If every listed positive cell is full-span, every proper cut has exactly
    the full-span footprint weight. -/
theorem TerminalV53Hypergraph.cutWeight_eq_fullWeight_of_cellsFull
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (cellsFull : ∀ cell, cell ∈ system.cells ->
      cell.footprint = system.carrier)
    (cut : List Atom) (proper : system.ProperCut cut) :
    system.cutWeight cut = system.footprintWeight system.carrier := by
  unfold TerminalV53Hypergraph.cutWeight
    TerminalV53Hypergraph.footprintWeight
  apply terminalV53_sum_congr
  intro cell cellMember
  unfold TerminalV53Hyperedge.cutContribution
  rw [system.fullCell_crossesBool_eq_true cell
    (cellsFull cell cellMember) cut proper]
  simp [cellsFull cell cellMember]

/-- Full-span-only support with the declared full weight proves the complete
    proper-cut equation directly. -/
theorem TerminalV53Hypergraph.constantProperCuts_of_cellsFull
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (cellsFull : ∀ cell, cell ∈ system.cells ->
      cell.footprint = system.carrier)
    (fullWeight :
      system.footprintWeight system.carrier = system.cutValue) :
    system.ConstantProperCuts := by
  intro cut proper
  exact (system.cutWeight_eq_fullWeight_of_cellsFull
    cellsFull cut proper).trans fullWeight

private theorem TerminalV53Hypergraph.cellsFull_of_carrierLengthTwo
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (carrierLength : system.carrier.length = 2) :
    ∀ cell, cell ∈ system.cells -> cell.footprint = system.carrier := by
  intro cell cellMember
  have footprintSublist := system.footprintSublist cell cellMember
  apply footprintSublist.eq_of_length
  have footprintBound := footprintSublist.length_le
  have footprintLarge := system.footprintLarge cell cellMember
  omega

/-! ## Three-anchor proper-cut classification -/

private theorem terminalV53_threeCarrier_properCut_classification
    {Atom : Type} {first second third : Atom} {cut : List Atom}
    (included : cut.Sublist [first, second, third])
    (nonempty : cut ≠ []) (proper : cut ≠ [first, second, third]) :
    cut = [first] ∨ cut = [second] ∨ cut = [third] ∨
      cut = [first, second] ∨ cut = [first, third] ∨
      cut = [second, third] := by
  rcases terminalV53_sublist_cons_cases included with
      skipFirst | ⟨firstRest, rfl, firstRestSublist⟩
  · rcases terminalV53_sublist_cons_cases skipFirst with
        skipSecond | ⟨secondRest, rfl, secondRestSublist⟩
    · rcases terminalV53_sublist_cons_cases skipSecond with
          skipThird | ⟨thirdRest, rfl, thirdRestSublist⟩
      · have cutNil : cut = [] := by cases skipThird; rfl
        exact False.elim (nonempty cutNil)
      · have thirdRestNil : thirdRest = [] := by cases thirdRestSublist; rfl
        subst thirdRest
        exact Or.inr (Or.inr (Or.inl rfl))
    · rcases terminalV53_sublist_cons_cases secondRestSublist with
          skipThird | ⟨thirdRest, rfl, thirdRestSublist⟩
      · have secondRestNil : secondRest = [] := by cases skipThird; rfl
        subst secondRest
        exact Or.inr (Or.inl rfl)
      · have thirdRestNil : thirdRest = [] := by cases thirdRestSublist; rfl
        subst thirdRest
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · rcases terminalV53_sublist_cons_cases firstRestSublist with
        skipSecond | ⟨secondRest, rfl, secondRestSublist⟩
    · rcases terminalV53_sublist_cons_cases skipSecond with
          skipThird | ⟨thirdRest, rfl, thirdRestSublist⟩
      · have firstRestNil : firstRest = [] := by cases skipThird; rfl
        subst firstRest
        exact Or.inl rfl
      · have thirdRestNil : thirdRest = [] := by cases thirdRestSublist; rfl
        subst thirdRest
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · rcases terminalV53_sublist_cons_cases secondRestSublist with
          skipThird | ⟨thirdRest, rfl, thirdRestSublist⟩
      · have secondRestNil : secondRest = [] := by cases skipThird; rfl
        subst secondRest
        exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · have thirdRestNil : thirdRest = [] := by cases thirdRestSublist; rfl
        subst thirdRest
        exact False.elim (proper rfl)

/-! ## Canonical sparse basis and exactness -/

/-- The canonical non-exhaustive cut basis selected by carrier shape. -/
def TerminalV53Hypergraph.CanonicalConstantCutBasis
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) : Prop :=
  match system.carrier with
  | [] => False
  | [_first] => False
  | [_first, _second] =>
      system.footprintWeight system.carrier = system.cutValue
  | [first, second, third] =>
      system.cutWeight [first] = system.cutValue ∧
      system.cutWeight [second] = system.cutValue ∧
      system.cutWeight [third] = system.cutValue
  | _first :: _second :: _third :: _fourth :: _rest =>
      (∀ cell, cell ∈ system.cells ->
        cell.footprint = system.carrier) ∧
      system.footprintWeight system.carrier = system.cutValue

private theorem TerminalV53Hypergraph.constantProperCuts_of_threeSingletons
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (first second third : Atom)
    (carrierEquation : system.carrier = [first, second, third])
    (firstCut : system.cutWeight [first] = system.cutValue)
    (secondCut : system.cutWeight [second] = system.cutValue)
    (thirdCut : system.cutWeight [third] = system.cutValue) :
    system.ConstantProperCuts := by
  have carrierNodup : [first, second, third].Nodup := by
    rw [← carrierEquation]
    exact system.carrierNodup
  have firstNotSecond : first ≠ second := by
    intro equal
    subst second
    simp at carrierNodup
  have firstNotThird : first ≠ third := by
    intro equal
    subst third
    simp at carrierNodup
  have secondNotThird : second ≠ third := by
    intro equal
    subst third
    simp at carrierNodup
  intro cut properCut
  have included : cut.Sublist [first, second, third] := by
    rw [← carrierEquation]
    exact properCut.1
  have nonempty : cut ≠ [] := properCut.2.1
  have notCarrier : cut ≠ [first, second, third] := by
    intro cutCarrier
    exact properCut.2.2 (cutCarrier.trans carrierEquation.symm)
  rcases terminalV53_threeCarrier_properCut_classification
      included nonempty notCarrier with
    cutFirst | cutSecond | cutThird | cutFirstSecond | cutFirstThird |
      cutSecondThird
  · simpa [cutFirst] using firstCut
  · simpa [cutSecond] using secondCut
  · simpa [cutThird] using thirdCut
  · subst cut
    have complement := system.cutWeight_complement [first, second]
    rw [carrierEquation] at complement
    have complementEquation :
        terminalV54Complement [first, second, third] [first, second] =
          [third] := by
      simp [terminalV54Complement, Ne.symm firstNotThird,
        Ne.symm secondNotThird]
    rw [complementEquation] at complement
    exact complement.symm.trans thirdCut
  · subst cut
    have complement := system.cutWeight_complement [first, third]
    rw [carrierEquation] at complement
    have complementEquation :
        terminalV54Complement [first, second, third] [first, third] =
          [second] := by
      simp [terminalV54Complement, Ne.symm firstNotSecond,
        secondNotThird]
    rw [complementEquation] at complement
    exact complement.symm.trans secondCut
  · subst cut
    have complement := system.cutWeight_complement [second, third]
    rw [carrierEquation] at complement
    have complementEquation :
        terminalV54Complement [first, second, third] [second, third] =
          [first] := by
      simp [terminalV54Complement, firstNotSecond, firstNotThird]
    rw [complementEquation] at complement
    exact complement.symm.trans firstCut

/-- V53 rigidity makes the canonical sparse basis exactly equivalent to the
    full proper-cut equation on every carrier of size at least two. -/
theorem terminalV53_canonicalConstantCutBasis_iff_constantProperCuts
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (carrierAtLeastTwo : 2 ≤ system.carrier.length) :
    system.CanonicalConstantCutBasis ↔ system.ConstantProperCuts := by
  constructor
  · intro basis
    cases carrierEquation : system.carrier with
    | nil => simp [carrierEquation] at carrierAtLeastTwo
    | cons first tail =>
      cases tail with
      | nil => simp [carrierEquation] at carrierAtLeastTwo
      | cons second tail =>
        cases tail with
        | nil =>
          have fullWeight :
              system.footprintWeight system.carrier = system.cutValue := by
            simpa [TerminalV53Hypergraph.CanonicalConstantCutBasis,
              carrierEquation] using basis
          exact system.constantProperCuts_of_cellsFull
            (system.cellsFull_of_carrierLengthTwo (by simp [carrierEquation]))
            fullWeight
        | cons third tail =>
          cases tail with
          | nil =>
            have singletonCuts :
                system.cutWeight [first] = system.cutValue ∧
                system.cutWeight [second] = system.cutValue ∧
                system.cutWeight [third] = system.cutValue := by
              simpa [TerminalV53Hypergraph.CanonicalConstantCutBasis,
                carrierEquation] using basis
            exact system.constantProperCuts_of_threeSingletons first second
              third carrierEquation singletonCuts.1 singletonCuts.2.1
              singletonCuts.2.2
          | cons fourth rest =>
            have largeBasis :
                (∀ cell, cell ∈ system.cells ->
                  cell.footprint = system.carrier) ∧
                system.footprintWeight system.carrier = system.cutValue := by
              simpa [TerminalV53Hypergraph.CanonicalConstantCutBasis,
                carrierEquation] using basis
            exact system.constantProperCuts_of_cellsFull largeBasis.1
              largeBasis.2
  · intro constantCuts
    cases carrierEquation : system.carrier with
    | nil => simp [carrierEquation] at carrierAtLeastTwo
    | cons first tail =>
      cases tail with
      | nil => simp [carrierEquation] at carrierAtLeastTwo
      | cons second tail =>
        cases tail with
        | nil =>
          have fullWeight := system.twoAnchor_fullWeight constantCuts
            (by simp [carrierEquation])
          simpa [TerminalV53Hypergraph.CanonicalConstantCutBasis,
            carrierEquation] using fullWeight
        | cons third tail =>
          cases tail with
          | nil =>
            have firstProper : system.ProperCut [first] := by
              unfold TerminalV53Hypergraph.ProperCut
              rw [carrierEquation]
              simp
            have secondProper : system.ProperCut [second] := by
              unfold TerminalV53Hypergraph.ProperCut
              rw [carrierEquation]
              simp
            have thirdProper : system.ProperCut [third] := by
              unfold TerminalV53Hypergraph.ProperCut
              rw [carrierEquation]
              simp
            have singletonCuts :
                system.cutWeight [first] = system.cutValue ∧
                system.cutWeight [second] = system.cutValue ∧
                system.cutWeight [third] = system.cutValue :=
              ⟨constantCuts [first] firstProper,
                constantCuts [second] secondProper,
                constantCuts [third] thirdProper⟩
            simpa [TerminalV53Hypergraph.CanonicalConstantCutBasis,
              carrierEquation] using singletonCuts
          | cons fourth rest =>
            have carrierLarge : 4 ≤ system.carrier.length := by
              simp [carrierEquation]
            have cellsFull := system.cellsFull_of_four constantCuts carrierLarge
            have fullWeight := system.fullWeight_eq_cutValue_of_cellsFull
              constantCuts (by omega) cellsFull
            have largeBasis :
                (∀ cell, cell ∈ system.cells ->
                  cell.footprint = system.carrier) ∧
                system.footprintWeight system.carrier = system.cutValue :=
              ⟨cellsFull, fullWeight⟩
            simpa [TerminalV53Hypergraph.CanonicalConstantCutBasis,
              carrierEquation] using largeBasis

/-! ## Total typed basis classifier -/

/-- First listed positive cell whose footprint is not the complete carrier. -/
def firstTerminalV53NonFullCell?
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) :
    Option (TerminalV53Hyperedge Atom) :=
  system.cells.find? fun cell =>
    decide (cell.footprint ≠ system.carrier)

theorem firstTerminalV53NonFullCell?_sound
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (cell : TerminalV53Hyperedge Atom)
    (found : firstTerminalV53NonFullCell? system = some cell) :
    cell ∈ system.cells ∧ cell.footprint ≠ system.carrier := by
  have member : cell ∈ system.cells := List.mem_of_find?_eq_some found
  have mismatchChecked :
      decide (cell.footprint ≠ system.carrier) = true :=
    @List.find?_some (TerminalV53Hyperedge Atom)
      (fun candidate => decide (candidate.footprint ≠ system.carrier))
      cell system.cells found
  exact ⟨member, of_decide_eq_true mismatchChecked⟩

theorem firstTerminalV53NonFullCell?_eq_none_all
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (noneFound : firstTerminalV53NonFullCell? system = none) :
    ∀ cell, cell ∈ system.cells -> cell.footprint = system.carrier := by
  intro cell cellMember
  by_cases cellFull : cell.footprint = system.carrier
  · exact cellFull
  · have mismatchChecked : decide
        (cell.footprint ≠ system.carrier) = true := decide_eq_true cellFull
    have someMismatch : (firstTerminalV53NonFullCell? system).isSome = true :=
      (List.find?_isSome).mpr ⟨cell, cellMember, mismatchChecked⟩
    rw [noneFound] at someMismatch
    exact False.elim (Bool.noConfusion someMismatch)

/-- Exact structural reason why the canonical sparse basis rejected. -/
inductive TerminalV53CanonicalConstantCutBasisRoute
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) where
  | insufficient (carrierSmall : system.carrier.length < 2)
  | twoFullWeightMismatch
      (carrierLength : system.carrier.length = 2)
      (mismatch : system.footprintWeight system.carrier ≠ system.cutValue)
  | threeSingletonMismatch
      (carrierLength : system.carrier.length = 3)
      (anchor : Atom) (anchorMember : anchor ∈ system.carrier)
      (mismatch : system.cutWeight [anchor] ≠ system.cutValue)
  | largeNonFullCell
      (carrierLarge : 4 ≤ system.carrier.length)
      (cell : TerminalV53Hyperedge Atom) (cellMember : cell ∈ system.cells)
      (mismatch : cell.footprint ≠ system.carrier)
  | largeFullWeightMismatch
      (carrierLarge : 4 ≤ system.carrier.length)
      (cellsFull : ∀ cell, cell ∈ system.cells ->
        cell.footprint = system.carrier)
      (mismatch : system.footprintWeight system.carrier ≠ system.cutValue)

/-- Total proof-bearing result of the non-exhaustive basis classifier. -/
inductive TerminalV53CanonicalConstantCutBasisClassification
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) where
  | coherent (basis : system.CanonicalConstantCutBasis)
  | routed (route : TerminalV53CanonicalConstantCutBasisRoute system)

/-- Check the exact sparse basis without enumerating carrier subsets. -/
def classifyTerminalV53CanonicalConstantCutBasis
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) :
    TerminalV53CanonicalConstantCutBasisClassification system := by
  cases carrierEquation : system.carrier with
  | nil =>
      exact .routed (.insufficient (by simp [carrierEquation]))
  | cons first tail =>
    cases tail with
    | nil =>
        exact .routed (.insufficient (by simp [carrierEquation]))
    | cons second tail =>
      cases tail with
      | nil =>
        by_cases fullWeight :
            system.footprintWeight system.carrier = system.cutValue
        · exact .coherent (by
            simpa [TerminalV53Hypergraph.CanonicalConstantCutBasis,
              carrierEquation] using fullWeight)
        · exact .routed (.twoFullWeightMismatch
            (by simp [carrierEquation]) fullWeight)
      | cons third tail =>
        cases tail with
        | nil =>
          by_cases firstCut : system.cutWeight [first] = system.cutValue
          · by_cases secondCut : system.cutWeight [second] = system.cutValue
            · by_cases thirdCut : system.cutWeight [third] = system.cutValue
              · exact .coherent (by
                  simpa [TerminalV53Hypergraph.CanonicalConstantCutBasis,
                    carrierEquation] using ⟨firstCut, secondCut, thirdCut⟩)
              · exact .routed (.threeSingletonMismatch
                  (by simp [carrierEquation]) third (by simp [carrierEquation])
                  thirdCut)
            · exact .routed (.threeSingletonMismatch
                (by simp [carrierEquation]) second (by simp [carrierEquation])
                secondCut)
          · exact .routed (.threeSingletonMismatch
              (by simp [carrierEquation]) first (by simp [carrierEquation])
              firstCut)
        | cons fourth rest =>
          match found : firstTerminalV53NonFullCell? system with
          | some cell =>
              have sound := firstTerminalV53NonFullCell?_sound system cell
                found
              exact .routed (.largeNonFullCell
                (by simp [carrierEquation]) cell sound.1 sound.2)
          | none =>
              have cellsFull :=
                firstTerminalV53NonFullCell?_eq_none_all system found
              by_cases fullWeight :
                  system.footprintWeight system.carrier = system.cutValue
              · have largeBasis :
                    (∀ candidate, candidate ∈ system.cells ->
                      candidate.footprint = system.carrier) ∧
                    system.footprintWeight system.carrier = system.cutValue :=
                  ⟨cellsFull, fullWeight⟩
                exact .coherent (by
                  simpa [TerminalV53Hypergraph.CanonicalConstantCutBasis,
                    carrierEquation] using largeBasis)
              · exact .routed (.largeFullWeightMismatch
                  (by simp [carrierEquation]) cellsFull fullWeight)

/-- Every finite sparse system receives one terminal typed basis result. -/
theorem classifyTerminalV53CanonicalConstantCutBasis_exhaustive
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) :
    Nonempty (TerminalV53CanonicalConstantCutBasisClassification system) :=
  ⟨classifyTerminalV53CanonicalConstantCutBasis system⟩

end DirectWire
end PNP

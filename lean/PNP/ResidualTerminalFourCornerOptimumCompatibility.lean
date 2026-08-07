/-
Copyright (c) 2026 PNP Labs.

Faithful common-carrier comparison of the four optimum realizers associated
with every finite computed terminal support square.  A corner open function
has its own boundary and interface widths.  This module embeds all four into
one canonical physical universe, proves that the embedding is reversible
without changing gate count or semantics, and then applies one shared profile
observer and one shared quotient projection to all four corners.

This reconstructs the `fourCornerOptimaCarrierCompatible` dependency in
Section 11.1 of the pinned manuscript.  It does not transport the four
realizers coherently along square legs, prove `sideTightCompletionExists`,
establish BN2 square legitimacy, derive the terminal dependency system,
construct arbitrary in-circuit replacement, or prove any later residual route,
runtime, SAT-in-P, or P = NP result.
-/

import PNP.ResidualTerminalFourCornerCarrier

namespace PNP
namespace DirectWire

private def locateMember {alpha : Type} [DecidableEq alpha] (item : alpha) :
    (items : List alpha) -> item ∈ items ->
      {index : Fin items.length // items.get index = item}
  | [], member => False.elim (by cases member)
  | head :: tail, member =>
      if equal : item = head then
        ⟨⟨0, by simp only [List.length_cons]; exact Nat.zero_lt_succ _⟩,
          by change head = item; exact equal.symm⟩
      else
        let tailMember : item ∈ tail :=
          (List.mem_cons.mp member).resolve_left equal
        let located := locateMember item tail tailMember
        ⟨located.1.succ, by
          change tail.get located.1 = item
          exact located.2⟩

private def memberIndex {alpha : Type} [DecidableEq alpha]
    {item : alpha} {items : List alpha} (member : item ∈ items) :
    Fin items.length :=
  (locateMember item items member).1

private theorem get_memberIndex {alpha : Type} [DecidableEq alpha]
    {item : alpha} {items : List alpha} (member : item ∈ items) :
    items.get (memberIndex member) = item :=
  (locateMember item items member).2

private theorem get_injective_of_nodup {alpha : Type} {items : List alpha}
    (distinct : items.Nodup) {left right : Fin items.length}
    (equal : items.get left = items.get right) : left = right := by
  apply Fin.ext
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro rightBeforeLeft
    have separated :=
      (List.pairwise_iff_getElem.mp distinct) right.val left.val
        right.isLt left.isLt rightBeforeLeft
    change items.get right ≠ items.get left at separated
    exact separated equal.symm
  · apply Nat.le_of_not_gt
    intro leftBeforeRight
    have separated :=
      (List.pairwise_iff_getElem.mp distinct) left.val right.val
        left.isLt right.isLt leftBeforeRight
    change items.get left ≠ items.get right at separated
    exact separated equal

private theorem memberIndex_get_of_nodup {alpha : Type} [DecidableEq alpha]
    {items : List alpha} (distinct : items.Nodup)
    (index : Fin items.length) :
    memberIndex (List.get_mem items index) = index := by
  apply get_injective_of_nodup distinct
  exact get_memberIndex (List.get_mem items index)

/-! ## Canonical ambient physical coordinates -/

/-- Embed a physical support wire into the common input universe consisting
    of all original inputs followed by all original gate outputs. -/
def TerminalSupportWire.ambientIndex {inputs gates : Nat} :
    TerminalSupportWire inputs gates -> Fin (inputs + gates)
  | .input index => Fin.castAdd gates index
  | .gate index => Fin.natAdd inputs index

/-- Decode one common input coordinate back to its exact physical wire. -/
def terminalSupportWireAt {inputs gates : Nat}
    (coordinate : Fin (inputs + gates)) : TerminalSupportWire inputs gates :=
  splitFin TerminalSupportWire.input TerminalSupportWire.gate coordinate

@[simp] theorem terminalSupportWireAt_ambientIndex
    {inputs gates : Nat} (wire : TerminalSupportWire inputs gates) :
    terminalSupportWireAt wire.ambientIndex = wire := by
  cases wire with
  | input index =>
      change splitFin TerminalSupportWire.input TerminalSupportWire.gate
        (Fin.castAdd gates index) = TerminalSupportWire.input index
      exact splitFin_left TerminalSupportWire.input TerminalSupportWire.gate index
  | gate index =>
      change splitFin TerminalSupportWire.input TerminalSupportWire.gate
        (Fin.natAdd inputs index) = TerminalSupportWire.gate index
      exact splitFin_right TerminalSupportWire.input TerminalSupportWire.gate index

@[simp] theorem TerminalSupportWire.ambientIndex_terminalSupportWireAt
    {inputs gates : Nat} (coordinate : Fin (inputs + gates)) :
    (terminalSupportWireAt coordinate).ambientIndex = coordinate := by
  unfold terminalSupportWireAt
  unfold splitFin
  split
  · rename_i isLeft
    apply Fin.ext
    rfl
  · rename_i notLeft
    apply Fin.ext
    exact natAdd_sub_of_le (Nat.le_of_not_gt notLeft)

theorem TerminalSupportWire.ambientIndex_injective {inputs gates : Nat} :
    Function.Injective
      (@TerminalSupportWire.ambientIndex inputs gates) := by
  intro left right equal
  have decoded := congrArg terminalSupportWireAt equal
  simpa only [terminalSupportWireAt_ambientIndex] using decoded

/-! ## Fail-closed corner coordinate queries -/

/-- Locate one ambient physical input in the exact ordered boundary of a
    corner.  Coordinates absent from that boundary return `none`. -/
def TerminalFourCornerCarrier.boundaryIndex?
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (coordinate : Fin (inputs + gates)) :
    Option (Fin (carrier.extracted corner).boundary.length) :=
  let wire := terminalSupportWireAt coordinate
  if member : wire ∈ (carrier.extracted corner).boundary then
    some (memberIndex member)
  else
    none

/-- Locate one ambient gate-output coordinate in the exact ordered interface
    of a corner.  Producers absent from that interface return `none`. -/
def TerminalFourCornerCarrier.interfaceIndex?
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (producer : Fin gates) :
    Option (Fin (carrier.extracted corner).interface.length) :=
  if member : producer ∈ (carrier.extracted corner).interface then
    some (memberIndex member)
  else
    none

theorem TerminalFourCornerCarrier.boundaryIndex?_eq_some_iff
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (coordinate : Fin (inputs + gates))
    (index : Fin (carrier.extracted corner).boundary.length) :
    carrier.boundaryIndex? corner coordinate = some index ↔
    (carrier.extracted corner).boundary.get index =
        terminalSupportWireAt coordinate := by
  unfold TerminalFourCornerCarrier.boundaryIndex?
  dsimp only
  split
  · rename_i member
    constructor
    · intro found
      cases found
      exact get_memberIndex member
    · intro equal
      have indexEqual : memberIndex member = index := by
        apply get_injective_of_nodup (carrier.boundary_nodup corner)
        exact (get_memberIndex member).trans equal.symm
      exact congrArg some indexEqual
  · rename_i absent
    constructor
    · intro impossible
      cases impossible
    · intro equal
      exact False.elim (absent (equal ▸ List.get_mem _ index))

theorem TerminalFourCornerCarrier.interfaceIndex?_eq_some_iff
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (producer : Fin gates)
    (index : Fin (carrier.extracted corner).interface.length) :
    carrier.interfaceIndex? corner producer = some index ↔
      (carrier.extracted corner).interface.get index = producer := by
  unfold TerminalFourCornerCarrier.interfaceIndex?
  split
  · rename_i member
    constructor
    · intro found
      cases found
      exact get_memberIndex member
    · intro equal
      have indexEqual : memberIndex member = index := by
        apply get_injective_of_nodup (carrier.interface_nodup corner)
        exact (get_memberIndex member).trans equal.symm
      exact congrArg some indexEqual
  · rename_i absent
    constructor
    · intro impossible
      cases impossible
    · intro equal
      exact False.elim (absent (equal ▸ List.get_mem _ index))

theorem TerminalFourCornerCarrier.boundaryIndex?_ambient_get
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (index : Fin (carrier.extracted corner).boundary.length) :
    carrier.boundaryIndex? corner
        ((carrier.extracted corner).boundary.get index).ambientIndex =
      some index := by
  apply (carrier.boundaryIndex?_eq_some_iff corner _ index).2
  rw [terminalSupportWireAt_ambientIndex]

theorem TerminalFourCornerCarrier.interfaceIndex?_get
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (index : Fin (carrier.extracted corner).interface.length) :
    carrier.interfaceIndex? corner
        ((carrier.extracted corner).interface.get index) = some index :=
  (carrier.interfaceIndex?_eq_some_iff corner _ index).2 rfl

/-! ## Faithful ambientization and localization -/

/-- Zero-gate input adapter from one exact corner boundary to the common
    physical input universe.  Every coordinate outside the corner boundary is
    fixed to `false`. -/
def TerminalFourCornerCarrier.boundaryAdapter
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner) :
    Candidate (carrier.extracted corner).boundary.length 0 (inputs + gates) :=
  Candidate.ofDirectWireWord .empty
    ⟨fun coordinate =>
      match carrier.boundaryIndex? corner coordinate with
      | some index => .input index
      | none => .constant false⟩

/-- Exact extracted implementation at one corner. -/
def TerminalFourCornerCarrier.cornerImplementation
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner) :
    Implementation (carrier.extracted corner).boundary.length
      (carrier.extracted corner).interface.length :=
  (carrier.extracted corner).extractedCandidate.toImplementation

/-- Embed one exact corner candidate into the common physical input and output
    universes.  Missing ambient outputs are fixed to `false`. -/
def TerminalFourCornerCarrier.ambientizeCandidate
    {inputs gates outputs profileWidth replacementGates : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (candidate : Candidate (carrier.extracted corner).boundary.length
      replacementGates (carrier.extracted corner).interface.length) :
    Candidate (inputs + gates) replacementGates gates :=
  let renamed := candidate.renameInputs fun index =>
    ((carrier.extracted corner).boundary.get index).ambientIndex
  Candidate.ofDirectWireWord renamed.program
    ⟨fun producer =>
      match carrier.interfaceIndex? corner producer with
      | some index => renamed.directWireWord.source index
      | none => .constant false⟩

/-- Canonical common-carrier representative of one extracted corner. -/
def TerminalFourCornerCarrier.ambientCandidate
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner) :
    Candidate (inputs + gates) (carrier.extracted corner).gateCount gates :=
  carrier.ambientizeCandidate corner
    (carrier.extracted corner).extractedCandidate

private def Source.liftZeroGates {inputs gates : Nat} :
    Source inputs 0 -> Source inputs gates
  | .input index => .input index
  | .constant value => .constant value
  | .gate index => Fin.elim0 index

private def Source.substituteZeroInputs
    {fromInputs toInputs gates : Nat}
    (binding : Fin fromInputs -> Source toInputs 0) :
    Source fromInputs gates -> Source toInputs gates
  | .input index => (binding index).liftZeroGates
  | .constant value => .constant value
  | .gate index => .gate index

private def Gate.substituteZeroInputs
    {fromInputs toInputs gates : Nat}
    (binding : Fin fromInputs -> Source toInputs 0)
    (gate : Gate fromInputs gates) : Gate toInputs gates :=
  ⟨gate.left.substituteZeroInputs binding,
    gate.right.substituteZeroInputs binding⟩

private def Program.substituteZeroInputs
    {fromInputs toInputs gates : Nat}
    (binding : Fin fromInputs -> Source toInputs 0) :
    Program fromInputs gates -> Program toInputs gates
  | .empty => .empty
  | .snoc initial gate =>
      .snoc (initial.substituteZeroInputs binding)
        (gate.substituteZeroInputs binding)

private def DirectWireWord.substituteZeroInputs
    {fromInputs toInputs gates outputCount : Nat}
    (binding : Fin fromInputs -> Source toInputs 0)
    (word : DirectWireWord fromInputs gates outputCount) :
    DirectWireWord toInputs gates outputCount :=
  ⟨fun output => (word.source output).substituteZeroInputs binding⟩

private def Candidate.precomposeZero
    {fromInputs toInputs gates outputCount : Nat}
    (binding : Fin fromInputs -> Source toInputs 0)
    (candidate : Candidate fromInputs gates outputCount) :
    Candidate toInputs gates outputCount :=
  Candidate.ofDirectWireWord
    (candidate.program.substituteZeroInputs binding)
    (candidate.directWireWord.substituteZeroInputs binding)

private theorem Source.eval_liftZeroGates
    {inputs gates : Nat} (source : Source inputs 0)
    (input : Valuation inputs) (gateValues : Valuation gates) :
    source.liftZeroGates.eval input gateValues =
      source.eval input (fun index => Fin.elim0 index) := by
  cases source with
  | input index => rfl
  | constant value => rfl
  | gate index => exact Fin.elim0 index

private theorem Source.eval_substituteZeroInputs
    {fromInputs toInputs gates : Nat}
    (source : Source fromInputs gates)
    (binding : Fin fromInputs -> Source toInputs 0)
    (input : Valuation toInputs) (gateValues : Valuation gates) :
    (source.substituteZeroInputs binding).eval input gateValues =
      source.eval
        (fun index => (binding index).eval input (fun gate => Fin.elim0 gate))
        gateValues := by
  cases source with
  | input index => exact Source.eval_liftZeroGates (binding index) input gateValues
  | constant value => rfl
  | gate index => rfl

private theorem Gate.eval_substituteZeroInputs
    {fromInputs toInputs gates : Nat}
    (gate : Gate fromInputs gates)
    (binding : Fin fromInputs -> Source toInputs 0)
    (input : Valuation toInputs) (gateValues : Valuation gates) :
    (gate.substituteZeroInputs binding).eval input gateValues =
      gate.eval
        (fun index => (binding index).eval input (fun found => Fin.elim0 found))
        gateValues := by
  unfold Gate.substituteZeroInputs Gate.eval
  rw [Source.eval_substituteZeroInputs, Source.eval_substituteZeroInputs]

private theorem Program.eval_substituteZeroInputs
    {fromInputs toInputs gates : Nat}
    (program : Program fromInputs gates)
    (binding : Fin fromInputs -> Source toInputs 0)
    (input : Valuation toInputs) (gate : Fin gates) :
    (program.substituteZeroInputs binding).eval input gate =
      program.eval
        (fun index => (binding index).eval input (fun found => Fin.elim0 found))
        gate := by
  induction program with
  | empty => exact Fin.elim0 gate
  | @snoc gates initial nextGate ih =>
      unfold Program.substituteZeroInputs Program.eval Valuation.snoc
      split
      · exact ih _
      · rw [Gate.eval_substituteZeroInputs]
        exact nextGate.eval_congr (fun _ => rfl) (fun index => ih index)

private theorem Candidate.precomposeZero_semantics
    {fromInputs toInputs gates outputCount : Nat}
    (binding : Fin fromInputs -> Source toInputs 0)
    (candidate : Candidate fromInputs gates outputCount)
    (input : Valuation toInputs) (output : Fin outputCount) :
    (candidate.precomposeZero binding).semantics input output =
      candidate.semantics
        (fun index => (binding index).eval input (fun found => Fin.elim0 found))
        output := by
  unfold Candidate.precomposeZero
  rw [Candidate.ofDirectWireWord_semantics]
  unfold DirectWire.semantics DirectWireWord.eval
  change ((candidate.directWireWord.source output).substituteZeroInputs binding).eval
      input ((candidate.program.substituteZeroInputs binding).eval input) = _
  rw [Source.eval_substituteZeroInputs]
  exact (candidate.directWireWord.source output).eval_congr (fun _ => rfl)
    (fun gate => Program.eval_substituteZeroInputs candidate.program binding input gate)

private def TerminalFourCornerCarrier.boundaryBinding
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (coordinate : Fin (inputs + gates)) :
    Source (carrier.extracted corner).boundary.length 0 :=
  match carrier.boundaryIndex? corner coordinate with
  | some index => .input index
  | none => .constant false

private theorem TerminalFourCornerCarrier.boundaryBinding_eval
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (input : Valuation (carrier.extracted corner).boundary.length)
    (coordinate : Fin (inputs + gates)) :
    (carrier.boundaryBinding corner coordinate).eval input
        (fun found => Fin.elim0 found) =
      (carrier.boundaryAdapter corner).semantics input coordinate := by
  unfold TerminalFourCornerCarrier.boundaryBinding
    TerminalFourCornerCarrier.boundaryAdapter
  rw [Candidate.ofDirectWireWord_semantics]
  unfold DirectWire.semantics DirectWireWord.eval
  change (match carrier.boundaryIndex? corner coordinate with
    | some index => Source.input index
    | none => Source.constant false).eval input (fun found => Fin.elim0 found) =
      (match carrier.boundaryIndex? corner coordinate with
      | some index => Source.input index
      | none => Source.constant false).eval input (Program.empty.eval input)
  rfl

/-- Restrict an ambient candidate back to the exact boundary and interface of
    one corner.  The zero-gate adapter and output selection do not change the
    candidate's gate count. -/
def TerminalFourCornerCarrier.localizeCandidate
    {inputs gates outputs profileWidth replacementGates : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (candidate : Candidate (inputs + gates) replacementGates gates) :
    Candidate (carrier.extracted corner).boundary.length replacementGates
      (carrier.extracted corner).interface.length :=
  let rebound := candidate.precomposeZero (carrier.boundaryBinding corner)
  Candidate.ofDirectWireWord rebound.program
      ⟨fun index => rebound.directWireWord.source
        ((carrier.extracted corner).interface.get index)⟩

@[simp] theorem TerminalFourCornerCarrier.boundaryAdapter_semantics_get
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (input : Valuation (carrier.extracted corner).boundary.length)
    (index : Fin (carrier.extracted corner).boundary.length) :
    (carrier.boundaryAdapter corner).semantics input
        ((carrier.extracted corner).boundary.get index).ambientIndex =
      input index := by
  unfold TerminalFourCornerCarrier.boundaryAdapter
  rw [Candidate.ofDirectWireWord_semantics]
  unfold DirectWire.semantics DirectWireWord.eval
  change (match carrier.boundaryIndex? corner
      ((carrier.extracted corner).boundary.get index).ambientIndex with
    | some found => Source.input found
    | none => Source.constant false).eval input (Program.empty.eval input) =
      input index
  rw [carrier.boundaryIndex?_ambient_get corner index]
  rfl

theorem TerminalFourCornerCarrier.ambientizeCandidate_semantics_present
    {inputs gates outputs profileWidth replacementGates : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (candidate : Candidate (carrier.extracted corner).boundary.length
      replacementGates (carrier.extracted corner).interface.length)
    (input : Valuation (inputs + gates))
    (index : Fin (carrier.extracted corner).interface.length) :
    (carrier.ambientizeCandidate corner candidate).semantics input
        ((carrier.extracted corner).interface.get index) =
      candidate.semantics
        (fun boundaryIndex => input
          ((carrier.extracted corner).boundary.get boundaryIndex).ambientIndex)
        index := by
  unfold TerminalFourCornerCarrier.ambientizeCandidate
  rw [Candidate.ofDirectWireWord_semantics]
  unfold DirectWire.semantics DirectWireWord.eval
  change (match carrier.interfaceIndex? corner
      ((carrier.extracted corner).interface.get index) with
    | some found =>
        (candidate.renameInputs fun boundaryIndex =>
          ((carrier.extracted corner).boundary.get boundaryIndex).ambientIndex).directWireWord.source found
    | none => Source.constant false).eval input
      ((candidate.renameInputs fun boundaryIndex =>
        ((carrier.extracted corner).boundary.get boundaryIndex).ambientIndex).program.eval input) = _
  rw [carrier.interfaceIndex?_get corner index]
  change (candidate.renameInputs fun boundaryIndex =>
      ((carrier.extracted corner).boundary.get boundaryIndex).ambientIndex).semantics
        input index = _
  exact Candidate.renameInputs_semantics _ candidate input index

theorem TerminalFourCornerCarrier.ambientizeCandidate_semantics_absent
    {inputs gates outputs profileWidth replacementGates : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (candidate : Candidate (carrier.extracted corner).boundary.length
      replacementGates (carrier.extracted corner).interface.length)
    (input : Valuation (inputs + gates)) (producer : Fin gates)
    (absent : producer ∉ (carrier.extracted corner).interface) :
    (carrier.ambientizeCandidate corner candidate).semantics input producer =
      false := by
  unfold TerminalFourCornerCarrier.ambientizeCandidate
  rw [Candidate.ofDirectWireWord_semantics]
  unfold DirectWire.semantics DirectWireWord.eval
  change (match carrier.interfaceIndex? corner producer with
    | some found =>
        (candidate.renameInputs fun boundaryIndex =>
          ((carrier.extracted corner).boundary.get boundaryIndex).ambientIndex).directWireWord.source found
    | none => Source.constant false).eval input
      ((candidate.renameInputs fun boundaryIndex =>
        ((carrier.extracted corner).boundary.get boundaryIndex).ambientIndex).program.eval input) = false
  have queryNone : carrier.interfaceIndex? corner producer = none := by
    unfold TerminalFourCornerCarrier.interfaceIndex?
    rw [dif_neg absent]
  rw [queryNone]
  rfl

theorem TerminalFourCornerCarrier.localizeCandidate_semantics
    {inputs gates outputs profileWidth replacementGates : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (candidate : Candidate (inputs + gates) replacementGates gates)
    (input : Valuation (carrier.extracted corner).boundary.length)
    (index : Fin (carrier.extracted corner).interface.length) :
    (carrier.localizeCandidate corner candidate).semantics input index =
      candidate.semantics ((carrier.boundaryAdapter corner).semantics input)
        ((carrier.extracted corner).interface.get index) := by
  unfold TerminalFourCornerCarrier.localizeCandidate
  rw [Candidate.ofDirectWireWord_semantics]
  unfold DirectWire.semantics DirectWireWord.eval
  change (candidate.precomposeZero (carrier.boundaryBinding corner)).semantics
      input ((carrier.extracted corner).interface.get index) = _
  rw [Candidate.precomposeZero_semantics]
  apply candidate.semantics_input_congr
  intro coordinate
  exact carrier.boundaryBinding_eval corner input coordinate

theorem TerminalFourCornerCarrier.localize_ambientize_semantics
    {inputs gates outputs profileWidth replacementGates : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (candidate : Candidate (carrier.extracted corner).boundary.length
      replacementGates (carrier.extracted corner).interface.length)
    (input : Valuation (carrier.extracted corner).boundary.length)
    (index : Fin (carrier.extracted corner).interface.length) :
    (carrier.localizeCandidate corner
        (carrier.ambientizeCandidate corner candidate)).semantics input index =
      candidate.semantics input index := by
  rw [carrier.localizeCandidate_semantics]
  rw [carrier.ambientizeCandidate_semantics_present]
  apply candidate.semantics_input_congr
  intro boundaryIndex
  exact carrier.boundaryAdapter_semantics_get corner input boundaryIndex

theorem TerminalFourCornerCarrier.ambientizeCandidate_gateCount
    {inputs gates outputs profileWidth replacementGates : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (candidate : Candidate (carrier.extracted corner).boundary.length
      replacementGates (carrier.extracted corner).interface.length) :
    (carrier.ambientizeCandidate corner candidate).program.size =
      candidate.program.size := by
  rw [Candidate.program_size_eq_gateCount, Candidate.program_size_eq_gateCount]

theorem TerminalFourCornerCarrier.localizeCandidate_gateCount
    {inputs gates outputs profileWidth replacementGates : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (candidate : Candidate (inputs + gates) replacementGates gates) :
    (carrier.localizeCandidate corner candidate).program.size =
      candidate.program.size := by
  rw [Candidate.program_size_eq_gateCount, Candidate.program_size_eq_gateCount]

/-! ## Semantic equivalence and exact minimum preservation -/

theorem TerminalFourCornerCarrier.ambientizeCandidate_equivalent
    {inputs gates outputs profileWidth leftGates rightGates : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (left : Candidate (carrier.extracted corner).boundary.length leftGates
      (carrier.extracted corner).interface.length)
    (right : Candidate (carrier.extracted corner).boundary.length rightGates
      (carrier.extracted corner).interface.length)
    (equivalent : Equivalent left.program left.directWireWord
      right.program right.directWireWord) :
    Equivalent (carrier.ambientizeCandidate corner left).program
        (carrier.ambientizeCandidate corner left).directWireWord
      (carrier.ambientizeCandidate corner right).program
        (carrier.ambientizeCandidate corner right).directWireWord := by
  intro input producer
  change (carrier.ambientizeCandidate corner left).semantics input producer =
    (carrier.ambientizeCandidate corner right).semantics input producer
  by_cases member : producer ∈ (carrier.extracted corner).interface
  · let index := memberIndex member
    have producerEqual :
        (carrier.extracted corner).interface.get index = producer :=
      get_memberIndex member
    rw [← producerEqual]
    rw [carrier.ambientizeCandidate_semantics_present,
      carrier.ambientizeCandidate_semantics_present]
    exact equivalent _ index
  · rw [carrier.ambientizeCandidate_semantics_absent corner left input producer
        member,
      carrier.ambientizeCandidate_semantics_absent corner right input producer
        member]

theorem TerminalFourCornerCarrier.localizeCandidate_equivalent
    {inputs gates outputs profileWidth leftGates rightGates : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (left : Candidate (inputs + gates) leftGates gates)
    (right : Candidate (inputs + gates) rightGates gates)
    (equivalent : Equivalent left.program left.directWireWord
      right.program right.directWireWord) :
    Equivalent (carrier.localizeCandidate corner left).program
        (carrier.localizeCandidate corner left).directWireWord
      (carrier.localizeCandidate corner right).program
        (carrier.localizeCandidate corner right).directWireWord := by
  intro input output
  change (carrier.localizeCandidate corner left).semantics input output =
    (carrier.localizeCandidate corner right).semantics input output
  rw [carrier.localizeCandidate_semantics,
    carrier.localizeCandidate_semantics]
  exact equivalent _ _

theorem TerminalFourCornerCarrier.localize_ambientize_equivalent
    {inputs gates outputs profileWidth replacementGates : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (candidate : Candidate (carrier.extracted corner).boundary.length
      replacementGates (carrier.extracted corner).interface.length) :
    Equivalent
        (carrier.localizeCandidate corner
          (carrier.ambientizeCandidate corner candidate)).program
        (carrier.localizeCandidate corner
          (carrier.ambientizeCandidate corner candidate)).directWireWord
      candidate.program candidate.directWireWord := by
  intro input output
  exact carrier.localize_ambientize_semantics corner candidate input output

/-- Common-carrier implementation of one exact extracted corner. -/
def TerminalFourCornerCarrier.ambientImplementation
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner) :
    Implementation (inputs + gates) gates :=
  (carrier.ambientCandidate corner).toImplementation

/-- Localization preserves the existential implementation gate count exactly. -/
def TerminalFourCornerCarrier.localizeImplementation
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (implementation : Implementation (inputs + gates) gates) :
    Implementation (carrier.extracted corner).boundary.length
      (carrier.extracted corner).interface.length :=
  ⟨implementation.gateCount,
    carrier.localizeCandidate corner implementation.candidate⟩

@[simp] theorem TerminalFourCornerCarrier.localizeImplementation_gateCount
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (implementation : Implementation (inputs + gates) gates) :
    (carrier.localizeImplementation corner implementation).gateCount =
      implementation.gateCount := rfl

/-- The canonical ambient extension neither creates nor destroys a cheaper
    semantic realization. -/
theorem TerminalFourCornerCarrier.ambient_referenceMinimum_eq_corner
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner) :
    referenceMinimum (carrier.ambientImplementation corner) =
      referenceMinimum (carrier.cornerImplementation corner) := by
  apply Nat.le_antisymm
  · apply referenceMinimum_le_of_equivalent
      (carrier.ambientImplementation corner)
      (carrier.ambientizeCandidate corner
        (referenceMinimumWitness (carrier.cornerImplementation corner)))
    apply carrier.ambientizeCandidate_equivalent
    exact equivalentBool_sound
      (referenceMinimumWitness_equivalent
        (carrier.cornerImplementation corner))
  · apply referenceMinimum_le_of_equivalent
      (carrier.cornerImplementation corner)
      (carrier.localizeCandidate corner
        (referenceMinimumWitness (carrier.ambientImplementation corner)))
    apply Equivalent.trans
    · apply carrier.localizeCandidate_equivalent
      exact equivalentBool_sound
        (referenceMinimumWitness_equivalent
          (carrier.ambientImplementation corner))
    · exact carrier.localize_ambientize_equivalent corner
        (carrier.extracted corner).extractedCandidate

/-! ## Shared profile observer and four-corner optimum family -/

/-- Select one named component of a four-corner size vector. -/
def TerminalFourCornerSizes.at (sizes : TerminalFourCornerSizes) :
    TerminalSupportSquareCorner -> Nat
  | .meet => sizes.meet
  | .left => sizes.left
  | .right => sizes.right
  | .join => sizes.join

/-- Select one named implementation from a four-corner family. -/
def TerminalProjectionFourCorners.at
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) :
    TerminalSupportSquareCorner -> Implementation inputs outputs
  | .meet => corners.meet
  | .left => corners.left
  | .right => corners.right
  | .join => corners.join

/-- Select one named full-profile realization from a typed basis. -/
def TerminalFullFourCornerBasis.at
    {inputs outputs profileWidth : Nat}
    {corners : TerminalProjectionFourCorners inputs outputs profileWidth}
    (basis : TerminalFullFourCornerBasis corners) :
    (corner : TerminalSupportSquareCorner) ->
      TerminalFullCarrierRealization corners.system (corners.at corner)
  | .meet => basis.meet
  | .left => basis.left
  | .right => basis.right
  | .join => basis.join

/-- Select one named quotient comparison from a typed basis. -/
def TerminalQuotientFourCornerBasis.at
    {inputs outputs profileWidth : Nat}
    {corners : TerminalProjectionFourCorners inputs outputs profileWidth}
    (basis : TerminalQuotientFourCornerBasis corners) :
    (corner : TerminalSupportSquareCorner) ->
      TerminalQuotientComparison corners.system corners.projection
        (corners.at corner)
  | .meet => basis.meet
  | .left => basis.left
  | .right => basis.right
  | .join => basis.join

/-- The shared ambient observer uses the saturation system's exact role map.
    The observer is executable data, not a compatibility certificate. -/
def TerminalFourCornerCarrier.ambientProfileSystem
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (_carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth) :
    TerminalProfileSystem (inputs + gates) gates profileWidth :=
  { role := system.profileSystem.role
    observe := observe }

/-- All four ambientized corners under exactly one observer and the carrier's
    one quotient projection. -/
def TerminalFourCornerCarrier.optimizationCorners
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth) :
    TerminalProjectionFourCorners (inputs + gates) gates profileWidth :=
  { system := carrier.ambientProfileSystem observe
    projection := carrier.projection
    meet := carrier.ambientImplementation .meet
    left := carrier.ambientImplementation .left
    right := carrier.ambientImplementation .right
    join := carrier.ambientImplementation .join }

@[simp] theorem TerminalFourCornerCarrier.optimizationCorners_at
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (corner : TerminalSupportSquareCorner) :
    (carrier.optimizationCorners observe).at corner =
      carrier.ambientImplementation corner := by
  cases corner <;> rfl

@[simp] theorem TerminalFourCornerCarrier.optimizationCorners_role
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (coordinate : Fin profileWidth) :
    (carrier.optimizationCorners observe).system.role coordinate =
      system.profileSystem.role coordinate := rfl

@[simp] theorem TerminalFourCornerCarrier.optimizationCorners_projection
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth) :
    (carrier.optimizationCorners observe).projection = carrier.projection := rfl

/-- Localize any ambient semantic realization to the exact extracted carrier
    at one corner. -/
def TerminalFourCornerCarrier.localizeRealization
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (realization : TerminalFullRealization
      (carrier.ambientImplementation corner)) :
    TerminalFullRealization (carrier.cornerImplementation corner) :=
  { implementation :=
      carrier.localizeImplementation corner realization.implementation
    equivalent := Equivalent.trans
      (carrier.localizeCandidate_equivalent corner
        realization.implementation.candidate
        (carrier.ambientImplementation corner).candidate
        realization.equivalent)
      (carrier.localize_ambientize_equivalent corner
        (carrier.extracted corner).extractedCandidate) }

@[simp] theorem TerminalFourCornerCarrier.localizeRealization_gateCount
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner)
    (realization : TerminalFullRealization
      (carrier.ambientImplementation corner)) :
    (carrier.localizeRealization corner realization).implementation.gateCount =
      realization.implementation.gateCount := rfl

/-- Full and quotient optima compared over one derived common carrier. -/
structure TerminalFourCornerOptimumFamily
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth) where
  fullBasis : TerminalFullFourCornerBasis
    (carrier.optimizationCorners observe)
  quotientBasis : TerminalQuotientFourCornerBasis
    (carrier.optimizationCorners observe)

/-- The canonical exhaustive full and quotient minima under the shared
    observer and projection. -/
def TerminalFourCornerCarrier.canonicalOptimumFamily
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth) :
    TerminalFourCornerOptimumFamily carrier observe :=
  { fullBasis := (carrier.optimizationCorners observe).canonicalFullBasis
    quotientBasis :=
      (carrier.optimizationCorners observe).canonicalQuotientBasis }

/-- Exact corner-local realization underlying one full-profile optimum. -/
def TerminalFourCornerOptimumFamily.fullLocalRealization
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    {observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth}
    (family : TerminalFourCornerOptimumFamily carrier observe) :
    (corner : TerminalSupportSquareCorner) ->
      TerminalFullRealization (carrier.cornerImplementation corner)
  | .meet => carrier.localizeRealization .meet family.fullBasis.meet.realization
  | .left => carrier.localizeRealization .left family.fullBasis.left.realization
  | .right => carrier.localizeRealization .right family.fullBasis.right.realization
  | .join => carrier.localizeRealization .join family.fullBasis.join.realization

/-- Exact corner-local realization underlying one quotient optimum.  The
    quotient evidence remains attached to the common ambient family. -/
def TerminalFourCornerOptimumFamily.quotientLocalRealization
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    {observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth}
    (family : TerminalFourCornerOptimumFamily carrier observe) :
    (corner : TerminalSupportSquareCorner) ->
      TerminalFullRealization (carrier.cornerImplementation corner)
  | .meet => carrier.localizeRealization .meet
      family.quotientBasis.meet.realization
  | .left => carrier.localizeRealization .left
      family.quotientBasis.left.realization
  | .right => carrier.localizeRealization .right
      family.quotientBasis.right.realization
  | .join => carrier.localizeRealization .join
      family.quotientBasis.join.realization

/-- Complete checked content of the legacy optimum-carrier compatibility
    obligation.  Coherent transport between these realizers is deliberately a
    separate downstream theorem. -/
structure TerminalFourCornerOptimumFamily.Compatible
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    {observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth}
    (family : TerminalFourCornerOptimumFamily carrier observe) : Prop where
  carrierCompatible : carrier.Compatible
  semanticMinimumPreserved : ∀ corner,
    referenceMinimum (carrier.ambientImplementation corner) =
      referenceMinimum (carrier.cornerImplementation corner)
  fullSizes : family.fullBasis.sizes =
    (carrier.optimizationCorners observe).fullMinimumSizes
  quotientSizes : family.quotientBasis.sizes =
    (carrier.optimizationCorners observe).quotientMinimumSizes
  fullLocalMinimum : ∀ corner,
    (family.fullLocalRealization corner).implementation.gateCount =
      (carrier.optimizationCorners observe).fullMinimumSizes.at corner
  quotientLocalMinimum : ∀ corner,
    (family.quotientLocalRealization corner).implementation.gateCount =
      (carrier.optimizationCorners observe).quotientMinimumSizes.at corner
  sharedRole : ∀ coordinate,
    (carrier.optimizationCorners observe).system.role coordinate =
      system.profileSystem.role coordinate
  sharedProjection :
    (carrier.optimizationCorners observe).projection = carrier.projection

/-- Every finite computed saturated terminal support square has full and
    quotient optimum realizers compared over one faithful common carrier. -/
theorem TerminalFourCornerCarrier.fourCornerOptimaCarrierCompatible
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth) :
    (carrier.canonicalOptimumFamily observe).Compatible := by
  refine
    { carrierCompatible := carrier.complete_transport
      semanticMinimumPreserved := carrier.ambient_referenceMinimum_eq_corner
      fullSizes := (carrier.optimizationCorners observe).canonicalFullBasis_sizes
      quotientSizes :=
        (carrier.optimizationCorners observe).canonicalQuotientBasis_sizes
      fullLocalMinimum := ?_
      quotientLocalMinimum := ?_
      sharedRole := carrier.optimizationCorners_role observe
      sharedProjection := carrier.optimizationCorners_projection observe }
  · intro corner
    cases corner <;> rfl
  · intro corner
    cases corner <;> rfl

end DirectWire
end PNP

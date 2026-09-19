/-
Copyright (c) 2026 PNP Labs.

Constructive extraction of an arbitrary finite terminal gate support.  The
extractor scans the intrinsically topological direct-wire program once.  It
retains every selected gate, internalises constants and selected predecessor
gates, and turns exactly the remaining physical sources into the canonical
incoming boundary inputs computed by `ResidualTerminalPhysicalSupportCompletion`.

This reconstructs the `(L_U, W_U) = Extract(C, U)` and
`[[W_U]] = F_{C,U}` edge from Section 2.2 of the pinned manuscript.  It does
not construct a replacement, establish global slack, classify a proper
positive support, or prove square legitimacy or projection compatibility.
-/

import PNP.ResidualTerminalPhysicalSupportCompletion
import PNP.NANDCausalBounds

namespace PNP
namespace DirectWire

universe u

/-- Constructively locate a witnessed item and retain the exact lookup proof. -/
private def locateMember {alpha : Type} [DecidableEq alpha] (item : alpha) :
    (items : List alpha) -> item ∈ items ->
      {index : Fin items.length // items.get index = item}
  | [], member => False.elim (by cases member)
  | head :: tail, member =>
      if equal : item = head then
        ⟨⟨0, Nat.zero_lt_succ _⟩, by simp [equal]⟩
      else
        let tailMember : item ∈ tail :=
          (List.mem_cons.mp member).resolve_left equal
        let located := locateMember item tail tailMember
        ⟨located.1.succ, located.2⟩

/-- The position carried by a constructive list-membership witness. -/
private def memberIndex {alpha : Type} [DecidableEq alpha]
    {item : alpha} {items : List alpha}
    (member : item ∈ items) : Fin items.length :=
  (locateMember item items member).1

/-- Looking up the position carried by a membership witness recovers the
    witnessed item. -/
private theorem get_memberIndex {alpha : Type} {item : alpha}
    [DecidableEq alpha]
    {items : List alpha} (member : item ∈ items) :
    items.get (memberIndex member) = item :=
  (locateMember item items member).2

private theorem bool_eq_false_of_ne_true (value : Bool)
    (notTrue : value ≠ true) : value = false := by
  cases value with
  | false => rfl
  | true => exact False.elim (notTrue rfl)

/-- Read one canonical boundary wire, returning `false` only for a wire which
    is not in the boundary.  Completeness later proves that this fallback is
    unreachable for every source of a selected gate. -/
private def terminalBoundaryValue
    {inputs gates : Nat} (boundary : List (TerminalSupportWire inputs gates))
    (valuation : Valuation boundary.length)
    (wire : TerminalSupportWire inputs gates) : Bool :=
  if member : wire ∈ boundary then valuation (memberIndex member) else false

/-- Canonical selected-gate order, obtained by scanning from the earliest gate
    to the latest gate. -/
def terminalSelectedGateIndices :
    {gates : Nat} -> (Fin gates -> Bool) -> List (Fin gates)
  | 0, _selected => []
  | gates + 1, selected =>
      let earlier := terminalSelectedGateIndices
        (fun gate : Fin gates => selected gate.castSucc)
      let lifted := earlier.map Fin.castSucc
      if selected (Fin.last gates) then lifted ++ [Fin.last gates] else lifted

/-- The canonical gate list selected by terminal primitive records. -/
def terminalSelectedGates
    {inputs gates outputs profileWidth : Nat}
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    List (Fin gates) :=
  terminalSelectedGateIndices (terminalGateSelected records)

private theorem mem_map_finCastSucc_iff
    {gates : Nat} (items : List (Fin gates)) (gate : Fin gates) :
    gate.castSucc ∈ items.map Fin.castSucc ↔ gate ∈ items := by
  constructor
  · intro member
    obtain ⟨found, foundMember, equal⟩ := List.mem_map.mp member
    have foundEqual : found = gate := Fin.ext
      (congrArg (fun index : Fin (gates + 1) => index.val) equal)
    simpa [foundEqual] using foundMember
  · intro member
    exact List.mem_map.mpr ⟨gate, member, rfl⟩

private theorem finLast_not_mem_map_castSucc
    {gates : Nat} (items : List (Fin gates)) :
    Fin.last gates ∉ items.map Fin.castSucc := by
  intro member
  obtain ⟨found, _foundMember, equal⟩ := List.mem_map.mp member
  have valueEqual : found.val = gates := congrArg Fin.val equal
  exact (Nat.ne_of_lt found.isLt) valueEqual

private theorem finCastSucc_ne_last
    {gates : Nat} (gate : Fin gates) :
    gate.castSucc ≠ Fin.last gates := by
  intro equal
  have valueEqual : gate.val = gates := congrArg Fin.val equal
  exact (Nat.ne_of_lt gate.isLt) valueEqual

/-- Constructive split of the last coordinate from all preceding coordinates.
    This avoids the wider classical dependency closure carried by the standard
    library's cast-successor equation for `Fin.lastCases`. -/
private def finLastCasesConstructive
    {gates : Nat} {motive : Fin (gates + 1) -> Sort u}
    (last : motive (Fin.last gates))
    (earlier : (gate : Fin gates) -> motive gate.castSucc)
    (gate : Fin (gates + 1)) : motive gate :=
  if beforeLast : gate.val < gates then
    let prior : Fin gates := ⟨gate.val, beforeLast⟩
    have equal : prior.castSucc = gate := Fin.ext rfl
    equal ▸ earlier prior
  else
    have valueLe : gate.val ≤ gates := Nat.le_of_lt_succ gate.isLt
    have gatesLe : gates ≤ gate.val := Nat.le_of_not_gt beforeLast
    have valueEqual : gates = gate.val := Nat.le_antisymm gatesLe valueLe
    have equal : Fin.last gates = gate := Fin.ext valueEqual
    equal ▸ last

private theorem finLastCasesConstructive_castSucc
    {gates : Nat} {motive : Fin (gates + 1) -> Sort u}
    (last : motive (Fin.last gates))
    (earlier : (gate : Fin gates) -> motive gate.castSucc)
    (gate : Fin gates) :
    finLastCasesConstructive last earlier gate.castSucc = earlier gate := by
  unfold finLastCasesConstructive
  split
  · rename_i beforeLast
    let prior : Fin gates := ⟨gate.val, beforeLast⟩
    have priorEqual : prior = gate := Fin.ext rfl
    subst prior
    rfl
  · rename_i notBeforeLast
    exact False.elim (notBeforeLast gate.isLt)

private theorem finLastCasesConstructive_last
    {gates : Nat} {motive : Fin (gates + 1) -> Sort u}
    (last : motive (Fin.last gates))
    (earlier : (gate : Fin gates) -> motive gate.castSucc) :
    finLastCasesConstructive last earlier (Fin.last gates) = last := by
  unfold finLastCasesConstructive
  split
  · rename_i beforeLast
    exact False.elim (Nat.lt_irrefl gates beforeLast)
  · rfl

private theorem nodup_map_injective {alpha beta : Type}
    (mapping : alpha -> beta) (injective : Function.Injective mapping)
    {items : List alpha} (distinct : items.Nodup) :
    (items.map mapping).Nodup := by
  induction items with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
      have split := List.nodup_cons.mp distinct
      apply List.nodup_cons.mpr
      constructor
      · intro member
        obtain ⟨item, itemMember, equal⟩ := List.mem_map.mp member
        exact split.1 (injective equal.symm ▸ itemMember)
      · exact ih split.2

/-- Canonical selection contains exactly the gates accepted by its selector. -/
theorem mem_terminalSelectedGateIndices_iff
    {gates : Nat} (selected : Fin gates -> Bool) (gate : Fin gates) :
    gate ∈ terminalSelectedGateIndices selected ↔ selected gate = true := by
  induction gates with
  | zero => exact Fin.elim0 gate
  | succ gates ih =>
      refine Fin.lastCases ?_ (fun earlier => ?_) gate
      · cases lastValue : selected (Fin.last gates) with
        | false =>
            simp only [terminalSelectedGateIndices, lastValue,
              Bool.false_eq_true, if_false]
            constructor
            · exact fun member => False.elim
                (finLast_not_mem_map_castSucc _ member)
            · intro impossible
              exact False.elim impossible
        | true =>
            simp only [terminalSelectedGateIndices, lastValue, if_true]
            constructor
            · intro _member
              trivial
            · intro _checked
              exact List.mem_append_right _ (List.Mem.head [])
      · cases lastValue : selected (Fin.last gates) with
        | false =>
            simp only [terminalSelectedGateIndices, lastValue,
              Bool.false_eq_true, if_false]
            exact (mem_map_finCastSucc_iff _ earlier).trans
              (ih (fun index => selected index.castSucc) earlier)
        | true =>
            simp only [terminalSelectedGateIndices, lastValue, if_true,
              List.mem_append]
            constructor
            · intro member
              cases member with
              | inl lifted =>
                  exact (ih (fun index => selected index.castSucc) earlier).1
                    ((mem_map_finCastSucc_iff _ earlier).1 lifted)
              | inr singleton =>
                  have equal := List.mem_singleton.mp singleton
                  exact False.elim (finCastSucc_ne_last earlier equal)
            · intro checked
              exact Or.inl ((mem_map_finCastSucc_iff _ earlier).2
                ((ih (fun index => selected index.castSucc) earlier).2 checked))

/-- Terminal records select exactly their gate-record coordinates. -/
theorem mem_terminalSelectedGates_iff
    {inputs gates outputs profileWidth : Nat}
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (gate : Fin gates) :
    gate ∈ terminalSelectedGates records ↔
      terminalGateSelected records gate = true :=
  mem_terminalSelectedGateIndices_iff (terminalGateSelected records) gate

/-- Canonical selection never duplicates a gate coordinate. -/
theorem terminalSelectedGateIndices_nodup
    {gates : Nat} (selected : Fin gates -> Bool) :
    (terminalSelectedGateIndices selected).Nodup := by
  induction gates with
  | zero => exact List.nodup_nil
  | succ gates ih =>
      let earlierSelected : Fin gates -> Bool :=
        fun gate => selected gate.castSucc
      have earlierNodup := ih earlierSelected
      have liftedNodup :
          ((terminalSelectedGateIndices earlierSelected).map Fin.castSucc).Nodup :=
        nodup_map_injective Fin.castSucc
          (fun left right equal => by
            apply Fin.ext
            exact congrArg (fun index : Fin (gates + 1) => index.val) equal)
          earlierNodup
      cases lastValue : selected (Fin.last gates) with
      | false =>
          simpa only [terminalSelectedGateIndices, lastValue,
            Bool.false_eq_true, if_false] using liftedNodup
      | true =>
          simp only [terminalSelectedGateIndices, lastValue, if_true]
          apply List.nodup_append.mpr
          refine ⟨liftedNodup, ?_, ?_⟩
          · apply List.nodup_cons.mpr
            constructor
            · intro impossible
              cases impossible
            · exact List.nodup_nil
          · intro left leftMember right rightMember equal
            have rightEqual : right = Fin.last gates :=
              List.mem_singleton.mp rightMember
            apply finLast_not_mem_map_castSucc
              (terminalSelectedGateIndices earlierSelected)
            rw [← rightEqual, ← equal]
            exact leftMember

/-- The terminal-record selected-gate list is duplicate-free. -/
theorem terminalSelectedGates_nodup
    {inputs gates outputs profileWidth : Nat}
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalSelectedGates records).Nodup :=
  terminalSelectedGateIndices_nodup (terminalGateSelected records)

/-- Evaluate a source in an open support: selected predecessors are internal;
    primary inputs and unselected predecessors are read from the boundary;
    constants remain local. -/
private def Source.evalTerminalOpen
    {inputs priorGates wireInputs wireGates : Nat}
    (source : Source inputs priorGates)
    (selected : Fin priorGates -> Bool)
    (inputWire : Fin inputs -> TerminalSupportWire wireInputs wireGates)
    (gateWire : Fin priorGates -> TerminalSupportWire wireInputs wireGates)
    (boundary : List (TerminalSupportWire wireInputs wireGates))
    (boundaryValuation : Valuation boundary.length)
    (gateValues : Valuation priorGates) : Bool :=
  match source with
  | .input index =>
      terminalBoundaryValue boundary boundaryValuation (inputWire index)
  | .constant value => value
  | .gate index =>
      if selected index then gateValues index
      else terminalBoundaryValue boundary boundaryValuation (gateWire index)

/-- Independent open-support evaluation over the original program coordinates.
    Unselected coordinates are assigned `false`; selected gates never observe
    that value because an unselected predecessor is read from the boundary. -/
private def Program.evalTerminalOpenAux
    {wireInputs wireGates : Nat}
    (boundary : List (TerminalSupportWire wireInputs wireGates))
    (boundaryValuation : Valuation boundary.length)
    {inputs gates : Nat} (program : Program inputs gates)
    (selected : Fin gates -> Bool)
    (inputWire : Fin inputs -> TerminalSupportWire wireInputs wireGates)
    (gateWire : Fin gates -> TerminalSupportWire wireInputs wireGates) :
    Valuation gates :=
  match program with
  | .empty => Fin.elim0
  | @snoc _ priorGates initial gate =>
      let earlierSelected : Fin priorGates -> Bool :=
        fun index => selected index.castSucc
      let earlierGateWire : Fin priorGates -> TerminalSupportWire wireInputs wireGates :=
        fun index => gateWire index.castSucc
      let earlierValues := evalTerminalOpenAux boundary boundaryValuation
        initial earlierSelected inputWire earlierGateWire
      let lastValue :=
        if selected (Fin.last priorGates) then
          boolNand
            (gate.left.evalTerminalOpen earlierSelected inputWire earlierGateWire
              boundary boundaryValuation earlierValues)
            (gate.right.evalTerminalOpen earlierSelected inputWire earlierGateWire
              boundary boundaryValuation earlierValues)
        else false
      earlierValues.snoc lastValue

private theorem Program.evalTerminalOpenAux_snoc_castSucc
    {wireInputs wireGates inputs gates : Nat}
    (boundary : List (TerminalSupportWire wireInputs wireGates))
    (boundaryValuation : Valuation boundary.length)
    (initial : Program inputs gates) (gate : Gate inputs gates)
    (selected : Fin (gates + 1) -> Bool)
    (inputWire : Fin inputs -> TerminalSupportWire wireInputs wireGates)
    (gateWire : Fin (gates + 1) -> TerminalSupportWire wireInputs wireGates)
    (index : Fin gates) :
    (Program.snoc initial gate).evalTerminalOpenAux boundary boundaryValuation
        selected inputWire gateWire index.castSucc =
      initial.evalTerminalOpenAux boundary boundaryValuation
        (fun earlier => selected earlier.castSucc) inputWire
        (fun earlier => gateWire earlier.castSucc) index := by
  change Valuation.snoc _ _ index.castSucc = _
  rw [Valuation.snoc_castSucc]

/-- Structural accounting predicate for one source in a selected program
    prefix. -/
private def Source.terminalAccounted
    {wireInputs wireGates inputs gates : Nat}
    (selected : Fin gates -> Bool)
    (inputWire : Fin inputs -> TerminalSupportWire wireInputs wireGates)
    (gateWire : Fin gates -> TerminalSupportWire wireInputs wireGates)
    (boundary : List (TerminalSupportWire wireInputs wireGates)) :
    Source inputs gates -> Prop
  | .input index => inputWire index ∈ boundary
  | .constant _value => True
  | .gate index => selected index = true ∨ gateWire index ∈ boundary

/-- Every stored source of every selected gate is structurally accounted for. -/
private def Program.terminalSourcesAccounted
    {wireInputs wireGates inputs gates : Nat}
    (program : Program inputs gates)
    (selected : Fin gates -> Bool)
    (inputWire : Fin inputs -> TerminalSupportWire wireInputs wireGates)
    (gateWire : Fin gates -> TerminalSupportWire wireInputs wireGates)
    (boundary : List (TerminalSupportWire wireInputs wireGates)) : Prop :=
  match program with
  | .empty => True
  | @snoc _ priorGates initial gate =>
      let earlierSelected : Fin priorGates -> Bool :=
        fun index => selected index.castSucc
      let earlierGateWire : Fin priorGates ->
          TerminalSupportWire wireInputs wireGates :=
        fun index => gateWire index.castSucc
      initial.terminalSourcesAccounted earlierSelected inputWire
          earlierGateWire boundary ∧
        (selected (Fin.last priorGates) = true ->
          gate.left.terminalAccounted earlierSelected inputWire
              earlierGateWire boundary ∧
            gate.right.terminalAccounted earlierSelected inputWire
              earlierGateWire boundary)

private theorem Source.terminalAccounted_weaken_one_iff
    {wireInputs wireGates inputs gates : Nat}
    (source : Source inputs gates)
    (selected : Fin (gates + 1) -> Bool)
    (inputWire : Fin inputs -> TerminalSupportWire wireInputs wireGates)
    (gateWire : Fin (gates + 1) -> TerminalSupportWire wireInputs wireGates)
    (boundary : List (TerminalSupportWire wireInputs wireGates)) :
    (source.weakenGates 1).terminalAccounted selected inputWire gateWire boundary ↔
      source.terminalAccounted (fun index => selected index.castSucc)
        inputWire (fun index => gateWire index.castSucc) boundary := by
  cases source with
  | input index => rfl
  | constant value => rfl
  | gate index =>
      have castEqual : Fin.castAdd 1 index = index.castSucc := Fin.ext rfl
      simp only [Source.weakenGates, Source.terminalAccounted, castEqual]

private theorem Program.terminalGateSources_snoc_castSucc
    {inputs gates : Nat} (initial : Program inputs gates)
    (gate : Gate inputs gates) (consumer : Fin gates) :
    (Program.snoc initial gate).terminalGateSources consumer.castSucc =
      let sources := initial.terminalGateSources consumer
      (sources.1.weakenGates 1, sources.2.weakenGates 1) := by
  change (if earlier : consumer.castSucc.val < gates then
      let sources := initial.terminalGateSources
        ⟨consumer.castSucc.val, earlier⟩
      (sources.1.weakenGates 1, sources.2.weakenGates 1)
    else (gate.left.weakenGates 1, gate.right.weakenGates 1)) = _
  split
  · rename_i isEarlier
    have indexEqual :
        (⟨consumer.castSucc.val, isEarlier⟩ : Fin gates) = consumer := Fin.ext rfl
    rw [indexEqual]
  · rename_i notEarlier
    exact False.elim (notEarlier consumer.isLt)

private theorem Program.terminalGateSources_snoc_last
    {inputs gates : Nat} (initial : Program inputs gates)
    (gate : Gate inputs gates) :
    (Program.snoc initial gate).terminalGateSources (Fin.last gates) =
      (gate.left.weakenGates 1, gate.right.weakenGates 1) := by
  change (if earlier : (Fin.last gates).val < gates then
      let sources := initial.terminalGateSources
        ⟨(Fin.last gates).val, earlier⟩
      (sources.1.weakenGates 1, sources.2.weakenGates 1)
    else (gate.left.weakenGates 1, gate.right.weakenGates 1)) = _
  split
  · rename_i impossible
    exact False.elim (Nat.lt_irrefl gates impossible)
  · rfl

private theorem Program.terminalSourcesAccounted_of_random_access
    {wireInputs wireGates inputs gates : Nat}
    (program : Program inputs gates)
    (selected : Fin gates -> Bool)
    (inputWire : Fin inputs -> TerminalSupportWire wireInputs wireGates)
    (gateWire : Fin gates -> TerminalSupportWire wireInputs wireGates)
    (boundary : List (TerminalSupportWire wireInputs wireGates))
    (accounted : forall consumer, selected consumer = true ->
      let sources := program.terminalGateSources consumer
      sources.1.terminalAccounted selected inputWire gateWire boundary ∧
        sources.2.terminalAccounted selected inputWire gateWire boundary) :
    program.terminalSourcesAccounted selected inputWire gateWire boundary := by
  induction program with
  | empty => trivial
  | @snoc gates initial gate ih =>
      let earlierSelected : Fin gates -> Bool :=
        fun index => selected index.castSucc
      let earlierGateWire : Fin gates -> TerminalSupportWire wireInputs wireGates :=
        fun index => gateWire index.castSucc
      constructor
      · apply ih earlierSelected earlierGateWire
        intro consumer selectedConsumer
        have full := accounted consumer.castSucc selectedConsumer
        rw [Program.terminalGateSources_snoc_castSucc] at full
        exact ⟨
          (Source.terminalAccounted_weaken_one_iff
            (initial.terminalGateSources consumer).1 selected inputWire
              gateWire boundary).1 full.1,
          (Source.terminalAccounted_weaken_one_iff
            (initial.terminalGateSources consumer).2 selected inputWire
              gateWire boundary).1 full.2⟩
      · intro selectedLast
        have full := accounted (Fin.last gates) selectedLast
        rw [Program.terminalGateSources_snoc_last] at full
        exact ⟨
          (Source.terminalAccounted_weaken_one_iff gate.left selected
            inputWire gateWire boundary).1 full.1,
          (Source.terminalAccounted_weaken_one_iff gate.right selected
            inputWire gateWire boundary).1 full.2⟩

private theorem Source.evalTerminalOpen_eq_of_accounted
    {wireInputs wireGates inputs gates : Nat}
    (source : Source inputs gates)
    (selected : Fin gates -> Bool)
    (inputWire : Fin inputs -> TerminalSupportWire wireInputs wireGates)
    (gateWire : Fin gates -> TerminalSupportWire wireInputs wireGates)
    (boundary : List (TerminalSupportWire wireInputs wireGates))
    (boundaryValuation : Valuation boundary.length)
    (openGateValues : Valuation gates)
    (inputValues : Valuation inputs) (gateValues : Valuation gates)
    (accounted : source.terminalAccounted selected inputWire gateWire boundary)
    (selectedCorrect : forall gate, selected gate = true ->
      openGateValues gate = gateValues gate)
    (inputCorrect : forall input,
      inputWire input ∈ boundary ->
        terminalBoundaryValue boundary boundaryValuation (inputWire input) =
          inputValues input)
    (gateCorrect : forall gate,
      gateWire gate ∈ boundary ->
        terminalBoundaryValue boundary boundaryValuation (gateWire gate) =
          gateValues gate) :
    source.evalTerminalOpen selected inputWire gateWire boundary
        boundaryValuation openGateValues =
      source.eval inputValues gateValues := by
  cases source with
  | input index =>
      exact inputCorrect index accounted
  | constant value => rfl
  | gate index =>
      cases selectedValue : selected index with
      | false =>
          simp only [Source.evalTerminalOpen, Source.eval, selectedValue,
            Bool.false_eq_true, if_false]
          cases accounted with
          | inl selectedGate =>
              rw [selectedValue] at selectedGate
              exact Bool.noConfusion selectedGate
          | inr boundaryGate => exact gateCorrect index boundaryGate
      | true =>
          simp only [Source.evalTerminalOpen, Source.eval, selectedValue, if_true]
          exact selectedCorrect index selectedValue

private theorem Program.evalTerminalOpenAux_eq_program
    {wireInputs wireGates inputs gates : Nat}
    (program : Program inputs gates)
    (selected : Fin gates -> Bool)
    (inputWire : Fin inputs -> TerminalSupportWire wireInputs wireGates)
    (gateWire : Fin gates -> TerminalSupportWire wireInputs wireGates)
    (boundary : List (TerminalSupportWire wireInputs wireGates))
    (boundaryValuation : Valuation boundary.length)
    (input : Valuation inputs)
    (accounted :
      program.terminalSourcesAccounted selected inputWire gateWire boundary)
    (inputCorrect : forall index,
      inputWire index ∈ boundary ->
        terminalBoundaryValue boundary boundaryValuation (inputWire index) =
          input index)
    (gateCorrect : forall index,
      gateWire index ∈ boundary ->
        terminalBoundaryValue boundary boundaryValuation (gateWire index) =
          program.eval input index) :
    forall gate, selected gate = true ->
      program.evalTerminalOpenAux boundary boundaryValuation selected
          inputWire gateWire gate =
        program.eval input gate := by
  induction program with
  | empty => intro gate; exact Fin.elim0 gate
  | @snoc gates initial gate ih =>
      let earlierSelected : Fin gates -> Bool :=
        fun index => selected index.castSucc
      let earlierGateWire : Fin gates -> TerminalSupportWire wireInputs wireGates :=
        fun index => gateWire index.castSucc
      have accountSplit :
          initial.terminalSourcesAccounted earlierSelected inputWire
              earlierGateWire boundary ∧
            (selected (Fin.last gates) = true ->
              gate.left.terminalAccounted earlierSelected inputWire
                  earlierGateWire boundary ∧
                gate.right.terminalAccounted earlierSelected inputWire
                  earlierGateWire boundary) := accounted
      have earlierGateCorrect : forall index,
          earlierGateWire index ∈ boundary ->
            terminalBoundaryValue boundary boundaryValuation
                (earlierGateWire index) =
              initial.eval input index := by
        intro index member
        have full := gateCorrect index.castSucc member
        rw [Program.eval_snoc_castSucc] at full
        exact full
      have earlierCorrect : forall index, earlierSelected index = true ->
          initial.evalTerminalOpenAux boundary boundaryValuation
              earlierSelected inputWire earlierGateWire index =
            initial.eval input index :=
        ih earlierSelected earlierGateWire accountSplit.1 earlierGateCorrect
      intro gateIndex
      refine Fin.lastCases ?_ (fun earlierIndex => ?_) gateIndex
      · intro selectedLast
        rw [Program.eval_snoc_last]
        change Valuation.snoc _ _ (Fin.last gates) = _
        rw [Valuation.snoc_last, if_pos selectedLast]
        unfold Gate.eval
        have currentAccount := accountSplit.2 selectedLast
        rw [gate.left.evalTerminalOpen_eq_of_accounted earlierSelected
          inputWire earlierGateWire boundary boundaryValuation
          (initial.evalTerminalOpenAux boundary boundaryValuation
            earlierSelected inputWire earlierGateWire)
          input (initial.eval input) currentAccount.1 earlierCorrect
          inputCorrect earlierGateCorrect]
        rw [gate.right.evalTerminalOpen_eq_of_accounted earlierSelected
          inputWire earlierGateWire boundary boundaryValuation
          (initial.evalTerminalOpenAux boundary boundaryValuation
            earlierSelected inputWire earlierGateWire)
          input (initial.eval input) currentAccount.2 earlierCorrect
          inputCorrect earlierGateCorrect]
      · intro selectedEarlier
        rw [Program.evalTerminalOpenAux_snoc_castSucc,
          Program.eval_snoc_castSucc]
        exact earlierCorrect earlierIndex selectedEarlier

/-- A proof-producing accumulator for the selected-program scan. -/
private structure TerminalExtractionState
    {wireInputs wireGates inputs gates : Nat}
    (program : Program inputs gates)
    (selected : Fin gates -> Bool)
    (inputWire : Fin inputs -> TerminalSupportWire wireInputs wireGates)
    (gateWire : Fin gates -> TerminalSupportWire wireInputs wireGates)
    (boundary : List (TerminalSupportWire wireInputs wireGates)) where
  gateCount : Nat
  extractedProgram : Program boundary.length gateCount
  gateCount_eq : gateCount = (terminalSelectedGateIndices selected).length
  gateIndex : (gate : Fin gates) -> selected gate = true -> Fin gateCount
  correct : forall (boundaryValuation : Valuation boundary.length)
      (gate : Fin gates) (selectedGate : selected gate = true),
    extractedProgram.eval boundaryValuation (gateIndex gate selectedGate) =
      program.evalTerminalOpenAux boundary boundaryValuation selected
        inputWire gateWire gate
  causalBound : ∀ (boundaryLabels : Fin boundary.length → Nat)
      (wireCaps : TerminalSupportWire wireInputs wireGates → Nat)
      (labels : Fin inputs → Nat) (caps : Fin gates → Nat),
    (∀ index, boundaryLabels index ≤ wireCaps (boundary.get index)) →
    (∀ index, wireCaps (inputWire index) ≤ labels index) →
    (∀ index, wireCaps (gateWire index) ≤ caps index) →
    CausalBound.Bounds program labels caps →
    ∀ index (selectedIndex : selected index = true),
      CausalBound.levels extractedProgram boundaryLabels
        (gateIndex index selectedIndex) ≤ caps index

private def boundaryInputSource
    {wireInputs wireGates : Nat}
    (boundary : List (TerminalSupportWire wireInputs wireGates))
    (wire : TerminalSupportWire wireInputs wireGates)
    (gateCount : Nat) : Source boundary.length gateCount :=
  if member : wire ∈ boundary then .input (memberIndex member)
  else .constant false

private theorem boundaryInputSource_eval
    {wireInputs wireGates : Nat}
    (boundary : List (TerminalSupportWire wireInputs wireGates))
    (wire : TerminalSupportWire wireInputs wireGates)
    (gateCount : Nat) (boundaryValuation : Valuation boundary.length)
    (gateValues : Valuation gateCount) :
    (boundaryInputSource boundary wire gateCount).eval boundaryValuation gateValues =
      terminalBoundaryValue boundary boundaryValuation wire := by
  unfold boundaryInputSource terminalBoundaryValue
  split <;> rfl

private def Source.extractTerminal
    {wireInputs wireGates inputs priorGates : Nat}
    {program : Program inputs priorGates}
    {selected : Fin priorGates -> Bool}
    {inputWire : Fin inputs -> TerminalSupportWire wireInputs wireGates}
    {gateWire : Fin priorGates -> TerminalSupportWire wireInputs wireGates}
    {boundary : List (TerminalSupportWire wireInputs wireGates)}
    (state : TerminalExtractionState program selected inputWire gateWire boundary) :
    Source inputs priorGates -> Source boundary.length state.gateCount
  | .input index => boundaryInputSource boundary (inputWire index) state.gateCount
  | .constant value => .constant value
  | .gate index =>
      if selectedGate : selected index = true then
        .gate (state.gateIndex index selectedGate)
      else boundaryInputSource boundary (gateWire index) state.gateCount

private theorem Source.extractTerminal_eval
    {wireInputs wireGates inputs priorGates : Nat}
    {program : Program inputs priorGates}
    {selected : Fin priorGates -> Bool}
    {inputWire : Fin inputs -> TerminalSupportWire wireInputs wireGates}
    {gateWire : Fin priorGates -> TerminalSupportWire wireInputs wireGates}
    {boundary : List (TerminalSupportWire wireInputs wireGates)}
    (state : TerminalExtractionState program selected inputWire gateWire boundary)
    (source : Source inputs priorGates)
    (boundaryValuation : Valuation boundary.length) :
    (source.extractTerminal state).eval boundaryValuation
        (state.extractedProgram.eval boundaryValuation) =
      source.evalTerminalOpen selected inputWire gateWire boundary
        boundaryValuation
        (program.evalTerminalOpenAux boundary boundaryValuation selected
          inputWire gateWire) := by
  cases source with
  | input index =>
      change (boundaryInputSource boundary (inputWire index) state.gateCount).eval
          boundaryValuation (state.extractedProgram.eval boundaryValuation) =
        terminalBoundaryValue boundary boundaryValuation (inputWire index)
      exact boundaryInputSource_eval boundary (inputWire index) state.gateCount
        boundaryValuation (state.extractedProgram.eval boundaryValuation)
  | constant value =>
      change value = value
      rfl
  | gate index =>
      change (if selectedGate : selected index = true then
          Source.gate (state.gateIndex index selectedGate)
        else boundaryInputSource boundary (gateWire index) state.gateCount).eval
          boundaryValuation (state.extractedProgram.eval boundaryValuation) =
        if selected index = true then
          program.evalTerminalOpenAux boundary boundaryValuation selected
            inputWire gateWire index
        else terminalBoundaryValue boundary boundaryValuation (gateWire index)
      by_cases selectedGate : selected index = true
      · rw [dif_pos selectedGate, if_pos selectedGate]
        exact state.correct boundaryValuation index selectedGate
      · have selectedFalse : selected index = false :=
          bool_eq_false_of_ne_true (selected index) selectedGate
        rw [dif_neg selectedGate, selectedFalse]
        exact boundaryInputSource_eval boundary (gateWire index) state.gateCount
          boundaryValuation (state.extractedProgram.eval boundaryValuation)

/-- The computed boundary-source lookup respects any pointwise wire caps.
An absent wire becomes a literal constant, whose causal level is zero. -/
private theorem boundaryInputSource_causal_bound
    {wireInputs wireGates gateCount : Nat}
    (boundary : List (TerminalSupportWire wireInputs wireGates))
    (wire : TerminalSupportWire wireInputs wireGates)
    (boundaryLabels : Fin boundary.length → Nat)
    (wireCaps : TerminalSupportWire wireInputs wireGates → Nat)
    (boundaryLe : ∀ index, boundaryLabels index ≤ wireCaps (boundary.get index))
    (gateLevels : Fin gateCount → Nat) :
    CausalBound.source (boundaryInputSource boundary wire gateCount)
      boundaryLabels gateLevels ≤ wireCaps wire := by
  unfold boundaryInputSource
  split
  · rename_i member
    change boundaryLabels (memberIndex member) ≤ wireCaps wire
    have bounded := boundaryLe (memberIndex member)
    rw [get_memberIndex] at bounded
    exact bounded
  · exact Nat.zero_le _

/-- Transport caps through the actual source translation, using the already
constructed bounds of selected predecessors. -/
private theorem Source.extractTerminal_causal_bound
    {wireInputs wireGates inputs priorGates : Nat}
    {program : Program inputs priorGates}
    {selected : Fin priorGates → Bool}
    {inputWire : Fin inputs → TerminalSupportWire wireInputs wireGates}
    {gateWire : Fin priorGates → TerminalSupportWire wireInputs wireGates}
    {boundary : List (TerminalSupportWire wireInputs wireGates)}
    (state : TerminalExtractionState program selected inputWire gateWire boundary)
    (wire : Source inputs priorGates)
    (labels : Fin inputs → Nat) (caps : Fin priorGates → Nat)
    (boundaryLabels : Fin boundary.length → Nat)
    (wireCaps : TerminalSupportWire wireInputs wireGates → Nat)
    (boundaryLe : ∀ index, boundaryLabels index ≤ wireCaps (boundary.get index))
    (inputLe : ∀ index, wireCaps (inputWire index) ≤ labels index)
    (gateLe : ∀ index, wireCaps (gateWire index) ≤ caps index)
    (bounded : ∀ index (selectedIndex : selected index = true),
      CausalBound.levels state.extractedProgram boundaryLabels
        (state.gateIndex index selectedIndex) ≤ caps index) :
    CausalBound.source (wire.extractTerminal state) boundaryLabels
        (CausalBound.levels state.extractedProgram boundaryLabels) ≤
      CausalBound.source wire labels caps := by
  cases wire with
  | input index =>
      change CausalBound.source
        (boundaryInputSource boundary (inputWire index) state.gateCount)
        boundaryLabels (CausalBound.levels state.extractedProgram boundaryLabels) ≤ labels index
      exact Nat.le_trans (boundaryInputSource_causal_bound boundary (inputWire index)
        boundaryLabels wireCaps boundaryLe _) (inputLe index)
  | constant value => exact Nat.le_refl _
  | gate index =>
      change CausalBound.source
        (if selectedIndex : selected index = true then .gate (state.gateIndex index selectedIndex)
          else boundaryInputSource boundary (gateWire index) state.gateCount)
        boundaryLabels (CausalBound.levels state.extractedProgram boundaryLabels) ≤ caps index
      by_cases selectedIndex : selected index = true
      · rw [dif_pos selectedIndex]
        exact bounded index selectedIndex
      · rw [dif_neg selectedIndex]
        exact Nat.le_trans (boundaryInputSource_causal_bound boundary (gateWire index)
          boundaryLabels wireCaps boundaryLe _) (gateLe index)

private def extractTerminalProgramAux
    {wireInputs wireGates : Nat}
    (boundary : List (TerminalSupportWire wireInputs wireGates)) :
    {inputs gates : Nat} -> (program : Program inputs gates) ->
      (selected : Fin gates -> Bool) ->
      (inputWire : Fin inputs -> TerminalSupportWire wireInputs wireGates) ->
      (gateWire : Fin gates -> TerminalSupportWire wireInputs wireGates) ->
      TerminalExtractionState program selected inputWire gateWire boundary
  | _inputs, 0, .empty, _selected, inputWire, gateWire =>
      { gateCount := 0
        extractedProgram := .empty
        gateCount_eq := rfl
        gateIndex := fun gate => Fin.elim0 gate
        correct := fun _ gate => Fin.elim0 gate
        causalBound := by
          intro _ _ _ _ _ _ _ _ index
          exact Fin.elim0 index }
  | inputs, gates + 1, .snoc initial gate, selected, inputWire, gateWire =>
      let earlierSelected : Fin gates -> Bool :=
        fun index => selected index.castSucc
      let earlierGateWire : Fin gates -> TerminalSupportWire wireInputs wireGates :=
        fun index => gateWire index.castSucc
      let earlier := extractTerminalProgramAux boundary initial earlierSelected
        inputWire earlierGateWire
      if lastSelected : selected (Fin.last gates) = true then
        { gateCount := earlier.gateCount + 1
          extractedProgram := .snoc earlier.extractedProgram
            { left := gate.left.extractTerminal earlier
              right := gate.right.extractTerminal earlier }
          gateCount_eq := by
            simp only [terminalSelectedGateIndices, lastSelected, if_pos,
              List.length_append, List.length_map, List.length_cons,
              List.length_nil]
            exact congrArg (fun count => count + 1) earlier.gateCount_eq
          gateIndex := fun index =>
            finLastCasesConstructive
              (motive := fun index =>
                selected index = true -> Fin (earlier.gateCount + 1))
              (fun _selectedIndex => Fin.last earlier.gateCount)
              (fun earlierIndex selectedIndex =>
                (earlier.gateIndex earlierIndex selectedIndex).castSucc)
              index
          correct := by
            intro boundaryValuation index
            refine Fin.lastCases ?_ (fun earlierIndex => ?_) index
            · intro selectedIndex
              simp only [finLastCasesConstructive_last]
              rw [Program.eval_snoc_last]
              unfold Gate.eval
              rw [gate.left.extractTerminal_eval earlier boundaryValuation]
              rw [gate.right.extractTerminal_eval earlier boundaryValuation]
              change _ = Valuation.snoc _ _ (Fin.last gates)
              rw [Valuation.snoc_last, if_pos lastSelected]
            · intro selectedIndex
              simp only [finLastCasesConstructive_castSucc]
              rw [Program.eval_snoc_castSucc]
              unfold Program.evalTerminalOpenAux
              rw [Valuation.snoc_castSucc]
              exact earlier.correct boundaryValuation earlierIndex selectedIndex
          causalBound := by
            intro boundaryLabels wireCaps labels caps boundaryLe inputLe gateLe bounded
            have earlierBound := earlier.causalBound boundaryLabels wireCaps labels
              (fun index => caps index.castSucc) boundaryLe inputLe
              (fun index => gateLe index.castSucc) bounded.1
            intro index selectedIndex
            rcases CausalBound.index_cases index with ⟨earlierIndex, rfl⟩ | rfl
            · simp only [finLastCasesConstructive_castSucc,
                CausalBound.levels_snoc_castSucc]
              exact earlierBound earlierIndex selectedIndex
            · simp only [finLastCasesConstructive_last, CausalBound.levels_snoc_last]
              have leftBound := Source.extractTerminal_causal_bound earlier gate.left labels
                (fun index => caps index.castSucc) boundaryLabels wireCaps boundaryLe inputLe
                (fun index => gateLe index.castSucc) earlierBound
              have rightBound := Source.extractTerminal_causal_bound earlier gate.right labels
                (fun index => caps index.castSucc) boundaryLabels wireCaps boundaryLe inputLe
                (fun index => gateLe index.castSucc) earlierBound
              change max (CausalBound.source (gate.left.extractTerminal earlier)
                  boundaryLabels (CausalBound.levels earlier.extractedProgram boundaryLabels))
                (CausalBound.source (gate.right.extractTerminal earlier)
                  boundaryLabels (CausalBound.levels earlier.extractedProgram boundaryLabels)) ≤
                    caps (Fin.last gates)
              exact Nat.max_le_of_le_of_le
                (Nat.le_trans leftBound (Nat.max_le.mp bounded.2).1)
                (Nat.le_trans rightBound (Nat.max_le.mp bounded.2).2) }
      else
        let lastFalse : selected (Fin.last gates) = false :=
          bool_eq_false_of_ne_true (selected (Fin.last gates)) lastSelected
        { gateCount := earlier.gateCount
          extractedProgram := earlier.extractedProgram
          gateCount_eq := by
            simp only [terminalSelectedGateIndices, lastFalse, Bool.false_eq_true,
              if_false, List.length_map]
            exact earlier.gateCount_eq
          gateIndex := fun index =>
            finLastCasesConstructive
              (motive := fun index =>
                selected index = true -> Fin earlier.gateCount)
              (fun selectedIndex => False.elim (lastSelected selectedIndex))
              (fun earlierIndex selectedIndex =>
                earlier.gateIndex earlierIndex selectedIndex)
              index
          correct := by
            intro boundaryValuation index
            refine Fin.lastCases ?_ (fun earlierIndex => ?_) index
            · intro selectedIndex
              simp only [finLastCasesConstructive_last]
              exact False.elim (lastSelected selectedIndex)
            · intro selectedIndex
              simp only [finLastCasesConstructive_castSucc]
              unfold Program.evalTerminalOpenAux
              rw [Valuation.snoc_castSucc]
              exact earlier.correct boundaryValuation earlierIndex selectedIndex
          causalBound := by
            intro boundaryLabels wireCaps labels caps boundaryLe inputLe gateLe bounded
            have earlierBound := earlier.causalBound boundaryLabels wireCaps labels
              (fun index => caps index.castSucc) boundaryLe inputLe
              (fun index => gateLe index.castSucc) bounded.1
            intro index selectedIndex
            rcases CausalBound.index_cases index with ⟨earlierIndex, rfl⟩ | rfl
            · simp only [finLastCasesConstructive_castSucc]
              exact earlierBound earlierIndex selectedIndex
            · exact False.elim (lastSelected selectedIndex) }

/-- A computed two-sided inverse for the actual extractor's gate positions.
This record is built from the scan, never supplied by the caller. -/
private structure TerminalExtractionOrigins
    {wireInputs wireGates inputs gates : Nat}
    {program : Program inputs gates} {selected : Fin gates → Bool}
    {inputWire : Fin inputs → TerminalSupportWire wireInputs wireGates}
    {gateWire : Fin gates → TerminalSupportWire wireInputs wireGates}
    {boundary : List (TerminalSupportWire wireInputs wireGates)}
    (state : TerminalExtractionState program selected inputWire gateWire boundary) where
  origin : Fin state.gateCount → Fin gates
  selected_origin : ∀ position, selected (origin position) = true
  index_origin : ∀ position,
    state.gateIndex (origin position) (selected_origin position) = position
  origin_index : ∀ gate (selectedGate : selected gate = true),
    origin (state.gateIndex gate selectedGate) = gate

/-- Follow the same append and skip branches as the physical extraction scan. -/
private def extractTerminalOriginsAux
    {wireInputs wireGates : Nat}
    (boundary : List (TerminalSupportWire wireInputs wireGates)) :
    {inputs gates : Nat} → (program : Program inputs gates) →
      (selected : Fin gates → Bool) →
      (inputWire : Fin inputs → TerminalSupportWire wireInputs wireGates) →
      (gateWire : Fin gates → TerminalSupportWire wireInputs wireGates) →
      TerminalExtractionOrigins
        (extractTerminalProgramAux boundary program selected inputWire gateWire)
  | _inputs, 0, .empty, _selected, _inputWire, _gateWire =>
      { origin := Fin.elim0
        selected_origin := fun position => Fin.elim0 position
        index_origin := fun position => Fin.elim0 position
        origin_index := fun gate _selectedGate => Fin.elim0 gate }
  | inputs, gates + 1, .snoc initial gate, selected, inputWire, gateWire => by
      let earlierSelected : Fin gates → Bool := fun index => selected index.castSucc
      let earlierGateWire : Fin gates → TerminalSupportWire wireInputs wireGates :=
        fun index => gateWire index.castSucc
      let earlier := extractTerminalOriginsAux boundary initial earlierSelected
        inputWire earlierGateWire
      simp only [extractTerminalProgramAux]
      split
      · rename_i lastSelected
        let prior := extractTerminalProgramAux boundary initial earlierSelected
          inputWire earlierGateWire
        let origin (position : Fin (prior.gateCount + 1)) : Fin (gates + 1) :=
          finLastCasesConstructive (motive := fun _ => Fin (gates + 1))
            (Fin.last gates) (fun previous => (earlier.origin previous).castSucc) position
        have originEarlier (position : Fin prior.gateCount) :
            origin position.castSucc = (earlier.origin position).castSucc :=
          finLastCasesConstructive_castSucc (motive := fun _ => Fin (gates + 1))
            (Fin.last gates) (fun previous => (earlier.origin previous).castSucc) position
        have originLast : origin (Fin.last prior.gateCount) = Fin.last gates :=
          finLastCasesConstructive_last (motive := fun _ => Fin (gates + 1))
            (Fin.last gates) (fun previous => (earlier.origin previous).castSucc)
        have selectedOrigin (position : Fin (prior.gateCount + 1)) :
            selected (origin position) = true := by
          rcases CausalBound.index_cases position with ⟨previous, rfl⟩ | rfl
          · rw [originEarlier]
            exact earlier.selected_origin previous
          · rw [originLast]
            exact lastSelected
        let reindex (index : Fin (gates + 1)) (selectedIndex : selected index = true) :
            Fin (prior.gateCount + 1) :=
          finLastCasesConstructive
            (motive := fun index => selected index = true → Fin (prior.gateCount + 1))
            (fun _ => Fin.last prior.gateCount)
            (fun previous selectedPrevious =>
              (prior.gateIndex previous selectedPrevious).castSucc) index selectedIndex
        have reindexEarlier (index : Fin gates)
            (selectedIndex : selected index.castSucc = true) :
            reindex index.castSucc selectedIndex =
              (prior.gateIndex index selectedIndex).castSucc := by
          dsimp only [reindex]
          rw [finLastCasesConstructive_castSucc]
        have reindexLast : reindex (Fin.last gates) lastSelected =
            Fin.last prior.gateCount := by
          dsimp only [reindex]
          rw [finLastCasesConstructive_last]
        have inverse (position : Fin (prior.gateCount + 1)) :
            reindex (origin position) (selectedOrigin position) = position := by
          rcases CausalBound.index_cases position with ⟨previous, rfl⟩ | rfl
          · have arguments :
                (⟨origin previous.castSucc, selectedOrigin previous.castSucc⟩ :
                  {index : Fin (gates + 1) // selected index = true}) =
                ⟨(earlier.origin previous).castSucc, earlier.selected_origin previous⟩ :=
              Subtype.ext (originEarlier previous)
            calc
              reindex (origin previous.castSucc) (selectedOrigin previous.castSucc) =
                  reindex (earlier.origin previous).castSucc
                    (earlier.selected_origin previous) :=
                congrArg (fun argument => reindex argument.val argument.property) arguments
              _ = (prior.gateIndex (earlier.origin previous)
                  (earlier.selected_origin previous)).castSucc := reindexEarlier _ _
              _ = previous.castSucc := congrArg Fin.castSucc (earlier.index_origin previous)
          · have arguments :
                (⟨origin (Fin.last prior.gateCount), selectedOrigin (Fin.last prior.gateCount)⟩ :
                  {index : Fin (gates + 1) // selected index = true}) =
                ⟨Fin.last gates, lastSelected⟩ := Subtype.ext originLast
            exact (congrArg (fun argument => reindex argument.val argument.property)
              arguments).trans reindexLast
        refine
          { origin := origin
            selected_origin := selectedOrigin
            index_origin := inverse
            origin_index := ?_ }
        intro index selectedIndex
        change origin (reindex index selectedIndex) = index
        rcases CausalBound.index_cases index with ⟨previous, rfl⟩ | rfl
        · rw [reindexEarlier, originEarlier]
          exact congrArg Fin.castSucc (earlier.origin_index previous selectedIndex)
        · rw [reindexLast, originLast]
      · rename_i lastUnselected
        refine
          { origin := fun position => (earlier.origin position).castSucc
            selected_origin := fun position => earlier.selected_origin position
            index_origin := ?_
            origin_index := ?_ }
        · intro position
          simp only [finLastCasesConstructive_castSucc]
          exact earlier.index_origin position
        · intro index selectedIndex
          rcases CausalBound.index_cases index with ⟨previous, rfl⟩ | rfl
          · simp only [finLastCasesConstructive_castSucc]
            exact congrArg Fin.castSucc (earlier.origin_index previous selectedIndex)
          · exact False.elim (lastUnselected selectedIndex)

/-- Bounds of the actual extraction accumulator, proved from its constructors.
The public instances below derive every cap from the input program itself. -/
private theorem extractTerminalProgramAux_causal_bound
    {wireInputs wireGates inputs gates : Nat}
    (boundary : List (TerminalSupportWire wireInputs wireGates))
    (boundaryLabels : Fin boundary.length → Nat)
    (wireCaps : TerminalSupportWire wireInputs wireGates → Nat)
    (boundaryLe : ∀ index, boundaryLabels index ≤ wireCaps (boundary.get index))
    (program : Program inputs gates) (selected : Fin gates → Bool)
    (inputWire : Fin inputs → TerminalSupportWire wireInputs wireGates)
    (gateWire : Fin gates → TerminalSupportWire wireInputs wireGates)
    (labels : Fin inputs → Nat) (caps : Fin gates → Nat)
    (inputLe : ∀ index, wireCaps (inputWire index) ≤ labels index)
    (gateLe : ∀ index, wireCaps (gateWire index) ≤ caps index)
    (bounded : CausalBound.Bounds program labels caps) :
    ∀ index (selectedIndex : selected index = true),
      CausalBound.levels
          (extractTerminalProgramAux boundary program selected inputWire gateWire).extractedProgram
          boundaryLabels
          ((extractTerminalProgramAux boundary program selected inputWire gateWire).gateIndex
            index selectedIndex) ≤ caps index := by
  exact (extractTerminalProgramAux boundary program selected inputWire gateWire).causalBound
    boundaryLabels wireCaps labels caps boundaryLe inputLe gateLe bounded

/-- Extracted direct-wire support with exact computed dimensions. -/
structure TerminalExtractedSupport
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs) where
  records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  boundary : List (TerminalSupportWire inputs gates)
  selectedGates : List (Fin gates)
  interface : List (Fin gates)
  gateCount : Nat
  gateCount_eq_selected : gateCount = selectedGates.length
  extractedCandidate : Candidate boundary.length gateCount interface.length

private def terminalExtractionState
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :=
  extractTerminalProgramAux
    (terminalBoundaryPorts candidate.program records)
    candidate.program (terminalGateSelected records)
    TerminalSupportWire.input TerminalSupportWire.gate

private theorem terminalInterfaceGet_selected
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (output : Fin (terminalInterfacePorts candidate records).length) :
    terminalGateSelected records
        ((terminalInterfacePorts candidate records).get output) = true := by
  have member := List.get_mem (terminalInterfacePorts candidate records) output
  have checked :=
    (mem_terminalInterfacePorts_iff candidate records
      ((terminalInterfacePorts candidate records).get output)).1 member
  simp only [terminalInterfaceGate, Bool.and_eq_true] at checked
  exact checked.1

private def terminalExtractedCandidate
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    Candidate
      (terminalBoundaryPorts candidate.program records).length
      (terminalExtractionState candidate records).gateCount
      (terminalInterfacePorts candidate records).length :=
  let state := terminalExtractionState candidate records
  let interface := terminalInterfacePorts candidate records
  let word : DirectWireWord
      (terminalBoundaryPorts candidate.program records).length
      state.gateCount interface.length :=
    { source := fun output =>
        let producer := interface.get output
        if selected : terminalGateSelected records producer = true then
          .gate (state.gateIndex producer selected)
        else .constant false }
  Candidate.ofDirectWireWord state.extractedProgram word

/-- Construct the extracted support solely from the candidate and selected
    terminal records. -/
def extractTerminalSupport
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalExtractedSupport (profileWidth := profileWidth) candidate :=
  let state := terminalExtractionState candidate records
  let interface := terminalInterfacePorts candidate records
  { records := records
    boundary := terminalBoundaryPorts candidate.program records
    selectedGates := terminalSelectedGates records
    interface := interface
    gateCount := state.gateCount
    gateCount_eq_selected := state.gateCount_eq
    extractedCandidate := terminalExtractedCandidate candidate records }

/-- The extractor retains the supplied terminal record list exactly. -/
theorem extractTerminalSupport_records
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (extractTerminalSupport candidate records).records = records := rfl

/-- The extractor uses the exact canonical physical boundary. -/
theorem extractTerminalSupport_boundary
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (extractTerminalSupport candidate records).boundary =
      terminalBoundaryPorts candidate.program records := rfl

/-- The extractor retains exactly the canonically selected gates. -/
theorem extractTerminalSupport_selectedGates
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (extractTerminalSupport candidate records).selectedGates =
      terminalSelectedGates records := rfl

/-- The extractor exposes the exact ordered physical interface. -/
theorem extractTerminalSupport_interface
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (extractTerminalSupport candidate records).interface =
      terminalInterfacePorts candidate records := rfl

/-- The extracted program has exactly one NAND gate per selected gate. -/
theorem extractTerminalSupport_gateCount
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (extractTerminalSupport candidate records).gateCount =
      (terminalSelectedGates records).length :=
  (extractTerminalSupport candidate records).gateCount_eq_selected

/-- The actual position used by the extractor for a selected original gate. -/
def terminalExtractionGateIndex
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (gate : Fin gates) (selectedGate : terminalGateSelected records gate = true) :
    Fin (extractTerminalSupport candidate records).gateCount :=
  (terminalExtractionState candidate records).gateIndex gate selectedGate

/-- Recover an original gate from its actual physical extracted position.
The inverse is computed from the extractor's append/skip scan. -/
def terminalExtractionOrigin
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (position : Fin (extractTerminalSupport candidate records).gateCount) : Fin gates :=
  (extractTerminalOriginsAux (terminalBoundaryPorts candidate.program records)
    candidate.program (terminalGateSelected records)
    TerminalSupportWire.input TerminalSupportWire.gate).origin position

theorem terminalExtractionOrigin_selected
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (position : Fin (extractTerminalSupport candidate records).gateCount) :
    terminalGateSelected records (terminalExtractionOrigin candidate records position) = true :=
  (extractTerminalOriginsAux (terminalBoundaryPorts candidate.program records)
    candidate.program (terminalGateSelected records)
    TerminalSupportWire.input TerminalSupportWire.gate).selected_origin position

/-- The recovered origin names this exact physical extracted gate. -/
theorem terminalExtractionGateIndex_origin
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (position : Fin (extractTerminalSupport candidate records).gateCount) :
    terminalExtractionGateIndex candidate records
        (terminalExtractionOrigin candidate records position)
        (terminalExtractionOrigin_selected candidate records position) = position :=
  (extractTerminalOriginsAux (terminalBoundaryPorts candidate.program records)
    candidate.program (terminalGateSelected records)
    TerminalSupportWire.input TerminalSupportWire.gate).index_origin position

/-- No selected original gate is lost or silently exchanged for another one. -/
theorem terminalExtractionOrigin_gateIndex
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (gate : Fin gates) (selectedGate : terminalGateSelected records gate = true) :
    terminalExtractionOrigin candidate records
      (terminalExtractionGateIndex candidate records gate selectedGate) = gate :=
  (extractTerminalOriginsAux (terminalBoundaryPorts candidate.program records)
    candidate.program (terminalGateSelected records)
    TerminalSupportWire.input TerminalSupportWire.gate).origin_index gate selectedGate

theorem terminalExtractionOrigin_injective
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    {left right : Fin (extractTerminalSupport candidate records).gateCount}
    (same : terminalExtractionOrigin candidate records left =
      terminalExtractionOrigin candidate records right) : left = right := by
  have arguments :
      (⟨terminalExtractionOrigin candidate records left,
        terminalExtractionOrigin_selected candidate records left⟩ :
        {gate : Fin gates // terminalGateSelected records gate = true}) =
      ⟨terminalExtractionOrigin candidate records right,
        terminalExtractionOrigin_selected candidate records right⟩ := Subtype.ext same
  have positions := congrArg
    (fun argument : {gate : Fin gates // terminalGateSelected records gate = true} =>
      terminalExtractionGateIndex candidate records argument.val argument.property) arguments
  exact (terminalExtractionGateIndex_origin candidate records left).symm.trans
    (positions.trans (terminalExtractionGateIndex_origin candidate records right))

/-- Independent open evaluation at every original gate coordinate.  Selected
    gates are computed; unselected coordinates are inert and are consulted
    only through the incoming boundary when a selected consumer uses them. -/
def terminalOpenGateEvaluation
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    Valuation (terminalBoundaryPorts candidate.program records).length ->
      Valuation gates :=
  fun boundaryValuation =>
    candidate.program.evalTerminalOpenAux
      (terminalBoundaryPorts candidate.program records) boundaryValuation
      (terminalGateSelected records) TerminalSupportWire.input
      TerminalSupportWire.gate

/-- The independently defined open function of the selected support. -/
def terminalOpenSupportSemantics
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    OpenFunction
      (terminalBoundaryPorts candidate.program records).length
      (terminalInterfacePorts candidate records).length :=
  fun boundaryValuation output =>
    terminalOpenGateEvaluation candidate records boundaryValuation
      ((terminalInterfacePorts candidate records).get output)

/-- Value carried by one physical support wire in the complete candidate. -/
def TerminalSupportWire.candidateValue
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (input : Valuation inputs) : TerminalSupportWire inputs gates -> Bool
  | .input index => input index
  | .gate index => candidate.program.eval input index

/-- Assign levels to original physical wires from input labels and gate caps. -/
def TerminalSupportWire.causalLevel
    {inputs gates : Nat} (labels : Fin inputs → Nat) (caps : Fin gates → Nat) :
    TerminalSupportWire inputs gates → Nat
  | .input index => labels index
  | .gate index => caps index

/-- The canonical boundary carries the levels of its actual original wires. -/
def terminalBoundaryCausalLabels
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (labels : Fin inputs → Nat) (caps : Fin gates → Nat) :
    Fin (terminalBoundaryPorts candidate.program records).length → Nat :=
  fun index =>
    ((terminalBoundaryPorts candidate.program records).get index).causalLevel labels caps

/-- Compute an extracted interface level from the actual extracted program and
its canonical original-wire boundary labels, not from Boolean equivalence. -/
def terminalExtractedInterfaceCausalLevel
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (labels : Fin inputs → Nat) (caps : Fin gates → Nat)
    (output : Fin (terminalInterfacePorts candidate records).length) : Nat :=
  let extracted := (extractTerminalSupport candidate records).extractedCandidate
  let boundaryLabels := terminalBoundaryCausalLabels candidate records labels caps
  CausalBound.source (extracted.directWireWord.source output) boundaryLabels
    (CausalBound.levels extracted.program boundaryLabels)

private theorem terminalExtractedInterfaceCausalLevel_le_caps
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (labels : Fin inputs → Nat) (caps : Fin gates → Nat)
    (bounded : CausalBound.Bounds candidate.program labels caps)
    (output : Fin (terminalInterfacePorts candidate records).length) :
    terminalExtractedInterfaceCausalLevel candidate records labels caps output ≤
      caps ((terminalInterfacePorts candidate records).get output) := by
  have selected := terminalInterfaceGet_selected candidate records output
  have outputSource :
      (terminalExtractedCandidate candidate records).directWireWord.source output =
        .gate ((terminalExtractionState candidate records).gateIndex
          ((terminalInterfacePorts candidate records).get output) selected) := by
    unfold terminalExtractedCandidate
    rw [Candidate.ofDirectWireWord_pointwise]
    exact dif_pos selected
  change CausalBound.source
      ((terminalExtractedCandidate candidate records).directWireWord.source output)
      (terminalBoundaryCausalLabels candidate records labels caps)
      (CausalBound.levels (terminalExtractionState candidate records).extractedProgram
        (terminalBoundaryCausalLabels candidate records labels caps)) ≤ _
  rw [outputSource]
  exact extractTerminalProgramAux_causal_bound
    (terminalBoundaryPorts candidate.program records)
    (terminalBoundaryCausalLabels candidate records labels caps)
    (TerminalSupportWire.causalLevel labels caps) (fun _ => Nat.le_refl _)
    candidate.program (terminalGateSelected records)
    TerminalSupportWire.input TerminalSupportWire.gate
    labels caps (fun _ => Nat.le_refl _) (fun _ => Nat.le_refl _) bounded
    ((terminalInterfacePorts candidate records).get output) selected

/-- Every extracted interface has at most its original producer's causal level.
All caps are computed from the original program; no correctness certificate,
coverage certificate or acyclicity assumption is supplied by the caller. -/
theorem extractTerminalSupport_causal_levels
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (labels : Fin inputs → Nat)
    (output : Fin (terminalInterfacePorts candidate records).length) :
    terminalExtractedInterfaceCausalLevel candidate records labels
        (CausalBound.levels candidate.program labels) output ≤
      CausalBound.levels candidate.program labels
        ((terminalInterfacePorts candidate records).get output) :=
  terminalExtractedInterfaceCausalLevel_le_caps candidate records labels
    (CausalBound.levels candidate.program labels)
    (CausalBound.bounds_levels candidate.program labels) output

/-- With original gate j labelled j + 1 and primary inputs labelled zero,
extraction never introduces dependence beyond its original interface producer.
This structural bound is derived for every candidate and record list. -/
theorem extractTerminalSupport_causal_index
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (output : Fin (terminalInterfacePorts candidate records).length) :
    terminalExtractedInterfaceCausalLevel candidate records
        (fun _ => 0) (fun index => index.val + 1) output ≤
      ((terminalInterfacePorts candidate records).get output).val + 1 :=
  terminalExtractedInterfaceCausalLevel_le_caps candidate records
    (fun _ => 0) (fun index => index.val + 1)
    (CausalBound.bounds_index candidate.program) output

/-- Restrict a whole-circuit execution to the canonical incoming boundary. -/
def terminalInducedBoundaryValuation
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (input : Valuation inputs) :
    Valuation (terminalBoundaryPorts candidate.program records).length :=
  fun boundaryIndex =>
    ((terminalBoundaryPorts candidate.program records).get boundaryIndex).candidateValue
      candidate input

private theorem terminalBoundaryValue_induced_of_mem
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (input : Valuation inputs) (wire : TerminalSupportWire inputs gates)
    (member : wire ∈ terminalBoundaryPorts candidate.program records) :
    terminalBoundaryValue (terminalBoundaryPorts candidate.program records)
        (terminalInducedBoundaryValuation candidate records input) wire =
      wire.candidateValue candidate input := by
  unfold terminalBoundaryValue
  split
  · rename_i found
    have proofEqual : found = member := Subsingleton.elim found member
    subst found
    unfold terminalInducedBoundaryValuation
    rw [get_memberIndex member]
  · rename_i absent
    exact False.elim (absent member)

private theorem physicalSourceAccounted_iff_terminalAccounted
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (source : Source inputs gates) :
    (completeTerminalPhysicalSupport candidate records).SourceAccounted source ↔
      source.terminalAccounted (terminalGateSelected records)
        TerminalSupportWire.input TerminalSupportWire.gate
        (terminalBoundaryPorts candidate.program records) := by
  cases source <;> rfl

private theorem physicalTerminalSourcesAccounted
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    candidate.program.terminalSourcesAccounted (terminalGateSelected records)
      TerminalSupportWire.input TerminalSupportWire.gate
      (terminalBoundaryPorts candidate.program records) := by
  apply Program.terminalSourcesAccounted_of_random_access
  intro consumer selected
  have incoming := completeTerminalPhysicalSupport_incoming_complete
    candidate records consumer selected
  exact ⟨
    (physicalSourceAccounted_iff_terminalAccounted candidate records _).1
      incoming.1,
    (physicalSourceAccounted_iff_terminalAccounted candidate records _).1
      incoming.2⟩

/-- The whole circuit induces boundary values under which every selected open
    gate recovers its original whole-circuit value. -/
theorem terminalOpenGateEvaluation_induced_selected
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (input : Valuation inputs) (gate : Fin gates)
    (selected : terminalGateSelected records gate = true) :
    terminalOpenGateEvaluation candidate records
        (terminalInducedBoundaryValuation candidate records input) gate =
      candidate.program.eval input gate := by
  apply Program.evalTerminalOpenAux_eq_program candidate.program
    (terminalGateSelected records) TerminalSupportWire.input
    TerminalSupportWire.gate (terminalBoundaryPorts candidate.program records)
    (terminalInducedBoundaryValuation candidate records input) input
    (physicalTerminalSourcesAccounted candidate records)
  · intro index member
    exact terminalBoundaryValue_induced_of_mem candidate records input
      (.input index) member
  · intro index member
    exact terminalBoundaryValue_induced_of_mem candidate records input
      (.gate index) member
  · exact selected

/-- On the induced boundary, every ordered support-interface output equals the
    corresponding gate value in the original whole circuit. -/
theorem terminalOpenSupportSemantics_induced
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (input : Valuation inputs)
    (output : Fin (terminalInterfacePorts candidate records).length) :
    terminalOpenSupportSemantics candidate records
        (terminalInducedBoundaryValuation candidate records input) output =
      candidate.program.eval input
        ((terminalInterfacePorts candidate records).get output) := by
  apply terminalOpenGateEvaluation_induced_selected
  exact terminalInterfaceGet_selected candidate records output

/-- For every boundary valuation, the extracted direct-wire candidate denotes
    exactly the independent open-support semantics. -/
theorem extractTerminalSupport_semantics
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (boundaryValuation :
      Valuation (terminalBoundaryPorts candidate.program records).length)
    (output : Fin (terminalInterfacePorts candidate records).length) :
    (extractTerminalSupport candidate records).extractedCandidate.semantics
        boundaryValuation output =
      terminalOpenSupportSemantics candidate records boundaryValuation output := by
  let state := terminalExtractionState candidate records
  have selected := terminalInterfaceGet_selected candidate records output
  change (terminalExtractedCandidate candidate records).semantics
      boundaryValuation output = _
  unfold terminalExtractedCandidate Candidate.semantics DirectWire.semantics
    DirectWireWord.eval
  rw [Candidate.ofDirectWireWord_pointwise]
  dsimp only
  rw [dif_pos selected]
  exact state.correct boundaryValuation
    ((terminalInterfacePorts candidate records).get output) selected

/-- Executing the extracted candidate on boundary values induced by the whole
    circuit recovers the original ordered interface gate value. -/
theorem extractTerminalSupport_induced
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (input : Valuation inputs)
    (output : Fin (terminalInterfacePorts candidate records).length) :
    (extractTerminalSupport candidate records).extractedCandidate.semantics
        (terminalInducedBoundaryValuation candidate records input) output =
      candidate.program.eval input
        ((terminalInterfacePorts candidate records).get output) :=
  (extractTerminalSupport_semantics candidate records
    (terminalInducedBoundaryValuation candidate records input) output).trans
      (terminalOpenSupportSemantics_induced candidate records input output)

/-- Every selected internal gate, including one absent from the ordinary
    output interface, retains its exact open-support value after extraction. -/
theorem extractTerminalSupport_gate_evaluation
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (boundaryValuation :
      Valuation (terminalBoundaryPorts candidate.program records).length)
    (gate : Fin gates) (selected : terminalGateSelected records gate = true) :
    (extractTerminalSupport candidate records).extractedCandidate.program.eval
        boundaryValuation (terminalExtractionGateIndex candidate records gate selected) =
      terminalOpenGateEvaluation candidate records boundaryValuation gate :=
  (terminalExtractionState candidate records).correct boundaryValuation gate selected

/-- At the induced boundary, an internal extracted gate recovers the actual
    original gate value, without requiring it to be an ordinary output. -/
theorem extractTerminalSupport_gate_induced
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (input : Valuation inputs)
    (gate : Fin gates) (selected : terminalGateSelected records gate = true) :
    (extractTerminalSupport candidate records).extractedCandidate.program.eval
        (terminalInducedBoundaryValuation candidate records input)
        (terminalExtractionGateIndex candidate records gate selected) =
      candidate.program.eval input gate :=
  (extractTerminalSupport_gate_evaluation candidate records
    (terminalInducedBoundaryValuation candidate records input) gate selected).trans
      (terminalOpenGateEvaluation_induced_selected candidate records input gate selected)

/-- Execute terminal saturation and then extract the resulting arbitrary gate
    support. -/
def extractSaturatedTerminalSupport
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalExtractedSupport (profileWidth := profileWidth) candidate :=
  extractTerminalSupport candidate (terminalSaturateRecords system seed)

/-- Composed extraction retains exactly the executable saturated record list. -/
theorem extractSaturatedTerminalSupport_records
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (extractSaturatedTerminalSupport candidate system seed).records =
      terminalSaturateRecords system seed := rfl

/-- Saturated extraction still has exactly one NAND gate per selected gate. -/
theorem extractSaturatedTerminalSupport_gateCount
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (extractSaturatedTerminalSupport candidate system seed).gateCount =
      (terminalSelectedGates (terminalSaturateRecords system seed)).length :=
  extractTerminalSupport_gateCount candidate (terminalSaturateRecords system seed)

/-- Saturation followed by extraction denotes the independently defined open
    support function at every boundary valuation and interface coordinate. -/
theorem extractSaturatedTerminalSupport_semantics
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (boundaryValuation : Valuation
      (terminalBoundaryPorts candidate.program
        (terminalSaturateRecords system seed)).length)
    (output : Fin
      (terminalInterfacePorts candidate
        (terminalSaturateRecords system seed)).length) :
    (extractSaturatedTerminalSupport candidate system seed).extractedCandidate.semantics
        boundaryValuation output =
      terminalOpenSupportSemantics candidate
        (terminalSaturateRecords system seed) boundaryValuation output :=
  extractTerminalSupport_semantics candidate
    (terminalSaturateRecords system seed) boundaryValuation output

/-- The saturated extraction also recovers original interface values under
    the induced whole-circuit boundary. -/
theorem extractSaturatedTerminalSupport_induced
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (input : Valuation inputs)
    (output : Fin
      (terminalInterfacePorts candidate
        (terminalSaturateRecords system seed)).length) :
    (extractSaturatedTerminalSupport candidate system seed).extractedCandidate.semantics
        (terminalInducedBoundaryValuation candidate
          (terminalSaturateRecords system seed) input) output =
      candidate.program.eval input
        ((terminalInterfacePorts candidate
          (terminalSaturateRecords system seed)).get output) :=
  extractTerminalSupport_induced candidate
    (terminalSaturateRecords system seed) input output

/-- Changing the record-list representation without changing its selected
    gates preserves every computed extraction field. Only the stored record
    list is replaced; no observer congruence is assumed. -/
theorem extractTerminalSupport_eq_of_gateSelected_eq
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (selectedEqual : terminalGateSelected left = terminalGateSelected right) :
    { extractTerminalSupport candidate left with records := right } =
      extractTerminalSupport candidate right := by
  have boundaryEqual :
      terminalBoundaryPorts candidate.program left =
        terminalBoundaryPorts candidate.program right := by
    rw [terminalBoundaryPorts_reference, terminalBoundaryPorts_reference]
    apply congrArg (fun predicate =>
      (allTerminalSupportWires inputs gates).filter predicate)
    funext wire
    unfold terminalBoundaryWire
    cases wire <;> simp only [terminalWireExternal, selectedEqual]
  have interfaceEqual :
      terminalInterfacePorts candidate left =
        terminalInterfacePorts candidate right := by
    unfold terminalInterfacePorts
    apply congrArg (fun predicate => (allFin gates).filter predicate)
    funext producer
    simp only [terminalInterfaceGate, terminalGateHasExternalConsumer,
      selectedEqual]
  let assemble
      (boundary : List (TerminalSupportWire inputs gates))
      (interface : List (Fin gates))
      (selected : Fin gates → Bool) :
      TerminalExtractedSupport (profileWidth := profileWidth) candidate :=
    let state := extractTerminalProgramAux boundary candidate.program selected
      TerminalSupportWire.input TerminalSupportWire.gate
    { records := right
      boundary := boundary
      selectedGates := terminalSelectedGateIndices selected
      interface := interface
      gateCount := state.gateCount
      gateCount_eq_selected := state.gateCount_eq
      extractedCandidate :=
        Candidate.ofDirectWireWord state.extractedProgram
          { source := fun output =>
              let producer := interface.get output
              if checked : selected producer = true then
                .gate (state.gateIndex producer checked)
              else .constant false } }
  change assemble (terminalBoundaryPorts candidate.program left)
      (terminalInterfacePorts candidate left) (terminalGateSelected left) =
    assemble (terminalBoundaryPorts candidate.program right)
      (terminalInterfacePorts candidate right) (terminalGateSelected right)
  rw [boundaryEqual, interfaceEqual, selectedEqual]

/-- Open-source evaluation is extensional in the boundary and preceding values. -/
private theorem Source.evalTerminalOpen_congr
    {wireInputs wireGates inputs gates : Nat}
    (source : Source inputs gates) (selected : Fin gates -> Bool)
    (inputWire : Fin inputs -> TerminalSupportWire wireInputs wireGates)
    (gateWire : Fin gates -> TerminalSupportWire wireInputs wireGates)
    (boundary : List (TerminalSupportWire wireInputs wireGates))
    (left right : Valuation boundary.length)
    (leftValues rightValues : Valuation gates)
    (inputEqual : forall index,
      terminalBoundaryValue boundary left (inputWire index) =
        terminalBoundaryValue boundary right (inputWire index))
    (gateEqual : forall index,
      terminalBoundaryValue boundary left (gateWire index) =
        terminalBoundaryValue boundary right (gateWire index))
    (valuesEqual : forall index, leftValues index = rightValues index) :
    source.evalTerminalOpen selected inputWire gateWire boundary left leftValues =
      source.evalTerminalOpen selected inputWire gateWire boundary right rightValues := by
  cases source with
  | input index => exact inputEqual index
  | constant value => rfl
  | gate index =>
      by_cases selectedGate : selected index = true
      · simpa only [Source.evalTerminalOpen, if_pos selectedGate] using valuesEqual index
      · simpa only [Source.evalTerminalOpen, if_neg selectedGate] using gateEqual index

/-- An original prefix can depend only on boundary wires preceding that prefix.
    The cutoff is arbitrary; the proof follows the actual program constructor. -/
private theorem Program.evalTerminalOpenAux_prefix_congr
    {wireInputs wireGates inputs gates : Nat}
    (program : Program inputs gates) (selected : Fin gates -> Bool)
    (inputWire : Fin inputs -> TerminalSupportWire wireInputs wireGates)
    (gateWire : Fin gates -> TerminalSupportWire wireInputs wireGates)
    (boundary : List (TerminalSupportWire wireInputs wireGates))
    (left right : Valuation boundary.length) (cutoff : Nat)
    (inputEqual : forall index,
      terminalBoundaryValue boundary left (inputWire index) =
        terminalBoundaryValue boundary right (inputWire index))
    (gateEqual : forall index, index.val < cutoff ->
      terminalBoundaryValue boundary left (gateWire index) =
        terminalBoundaryValue boundary right (gateWire index)) :
    forall index, index.val < cutoff ->
      program.evalTerminalOpenAux boundary left selected inputWire gateWire index =
        program.evalTerminalOpenAux boundary right selected inputWire gateWire index := by
  induction program with
  | empty => intro index; exact Fin.elim0 index
  | @snoc gates initial gate ih =>
      let earlierSelected : Fin gates -> Bool := fun index => selected index.castSucc
      let earlierGateWire : Fin gates -> TerminalSupportWire wireInputs wireGates :=
        fun index => gateWire index.castSucc
      have earlierBoundary : forall index : Fin gates, index.val < cutoff ->
          terminalBoundaryValue boundary left (earlierGateWire index) =
            terminalBoundaryValue boundary right (earlierGateWire index) :=
        fun index before => gateEqual index.castSucc before
      have earlierValues : forall index : Fin gates, index.val < cutoff ->
          initial.evalTerminalOpenAux boundary left earlierSelected inputWire
              earlierGateWire index =
            initial.evalTerminalOpenAux boundary right earlierSelected inputWire
              earlierGateWire index :=
        ih earlierSelected earlierGateWire earlierBoundary
      intro index
      refine Fin.lastCases ?_ (fun earlier => ?_) index
      · intro before
        change gates < cutoff at before
        change Valuation.snoc _ _ (Fin.last gates) =
          Valuation.snoc _ _ (Fin.last gates)
        rw [Valuation.snoc_last, Valuation.snoc_last]
        by_cases selectedLast : selected (Fin.last gates) = true
        · rw [if_pos selectedLast, if_pos selectedLast]
          rw [gate.left.evalTerminalOpen_congr earlierSelected inputWire
            earlierGateWire boundary left right _ _ inputEqual
            (fun prior => earlierBoundary prior (Nat.lt_trans prior.isLt before))
            (fun prior => earlierValues prior (Nat.lt_trans prior.isLt before))]
          rw [gate.right.evalTerminalOpen_congr earlierSelected inputWire
            earlierGateWire boundary left right _ _ inputEqual
            (fun prior => earlierBoundary prior (Nat.lt_trans prior.isLt before))
            (fun prior => earlierValues prior (Nat.lt_trans prior.isLt before))]
        · rw [if_neg selectedLast, if_neg selectedLast]
      · intro before
        rw [Program.evalTerminalOpenAux_snoc_castSucc,
          Program.evalTerminalOpenAux_snoc_castSucc]
        exact earlierValues earlier before

/-- Earlier open-support gate values are independent of later boundary gates.
    Agreement is required only on primary inputs and boundary gates before the
    chosen cutoff, not on all boundary coordinates or only induced valuations. -/
theorem terminalOpenGateEvaluation_prefix_congr
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (left right : Valuation (terminalBoundaryPorts candidate.program records).length)
    (cutoff : Nat)
    (agreement : forall port : Fin (terminalBoundaryPorts candidate.program records).length,
      (match (terminalBoundaryPorts candidate.program records).get port with
        | .input _ => True
        | .gate boundaryGate => boundaryGate.val < cutoff) ->
      left port = right port)
    (gate : Fin gates) (before : gate.val < cutoff) :
    terminalOpenGateEvaluation candidate records left gate =
      terminalOpenGateEvaluation candidate records right gate := by
  have wireEqual (wire : TerminalSupportWire inputs gates)
      (earlier : match wire with
        | .input _ => True
        | .gate boundaryGate => boundaryGate.val < cutoff) :
      terminalBoundaryValue (terminalBoundaryPorts candidate.program records) left wire =
        terminalBoundaryValue (terminalBoundaryPorts candidate.program records) right wire := by
    by_cases member : wire ∈ terminalBoundaryPorts candidate.program records
    · simp only [terminalBoundaryValue, dif_pos member]
      apply agreement
      rw [get_memberIndex]
      exact earlier
    · simp only [terminalBoundaryValue, dif_neg member]
  exact candidate.program.evalTerminalOpenAux_prefix_congr
    (terminalGateSelected records) TerminalSupportWire.input TerminalSupportWire.gate
    (terminalBoundaryPorts candidate.program records) left right cutoff
    (fun index => wireEqual (.input index) True.intro)
    (fun index preceding => wireEqual (.gate index) preceding) gate before

/-- With one external gate as the entire boundary, every earlier selected gate
    is constant as an open function, even when that boundary bit is unrealizable
    in a complete execution of the original circuit. -/
theorem terminalOpenGateEvaluation_single_gate_prefix
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (boundaryGate : Fin gates)
    (single : terminalBoundaryPorts candidate.program records = [.gate boundaryGate])
    (left right : Valuation (terminalBoundaryPorts candidate.program records).length)
    (gate : Fin gates) (before : gate.val < boundaryGate.val) :
    terminalOpenGateEvaluation candidate records left gate =
      terminalOpenGateEvaluation candidate records right gate := by
  apply terminalOpenGateEvaluation_prefix_congr candidate records left right
    boundaryGate.val ?_ gate before
  intro port earlier
  have member : (terminalBoundaryPorts candidate.program records).get port ∈
      [.gate boundaryGate] := by
    rw [← single]
    exact List.get_mem (terminalBoundaryPorts candidate.program records) port
  have portEqual : (terminalBoundaryPorts candidate.program records).get port =
      .gate boundaryGate := List.mem_singleton.mp member
  rw [portEqual] at earlier
  exact False.elim (Nat.lt_irrefl boundaryGate.val earlier)


/-! ## Computed open-boundary transport for nested physical supports -/

/-- Read a wire in an open support. Selected gates are computed internally;
    external wires are read from the actual boundary, not invented inputs. -/
def terminalOpenWireValue
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (valuation : Valuation (terminalBoundaryPorts candidate.program records).length) :
    TerminalSupportWire inputs gates -> Bool
  | .input index =>
      terminalBoundaryValue (terminalBoundaryPorts candidate.program records)
        valuation (.input index)
  | .gate index =>
      if terminalGateSelected records index then
        terminalOpenGateEvaluation candidate records valuation index
      else
        terminalBoundaryValue (terminalBoundaryPorts candidate.program records)
          valuation (.gate index)

/-- Compute the smaller boundary from the larger open support. In particular,
    a wire internalized by the larger support takes its computed gate value. -/
def terminalBoundaryPullback
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (small large : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (valuation : Valuation (terminalBoundaryPorts candidate.program large).length) :
    Valuation (terminalBoundaryPorts candidate.program small).length :=
  fun index => terminalOpenWireValue candidate large valuation
    ((terminalBoundaryPorts candidate.program small).get index)

private theorem terminalBoundaryValue_pullback
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (small large : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (valuation : Valuation (terminalBoundaryPorts candidate.program large).length)
    (wire : TerminalSupportWire inputs gates)
    (member : wire ∈ terminalBoundaryPorts candidate.program small) :
    terminalBoundaryValue (terminalBoundaryPorts candidate.program small)
        (terminalBoundaryPullback candidate small large valuation) wire =
      terminalOpenWireValue candidate large valuation wire := by
  unfold terminalBoundaryValue
  split
  · rename_i found
    change terminalOpenWireValue candidate large valuation
        ((terminalBoundaryPorts candidate.program small).get
          (memberIndex found)) = _
    rw [get_memberIndex found]
  · rename_i absent
    exact False.elim (absent member)

private theorem Source.evalTerminalOpen_nested
    {wireInputs wireGates inputs gates : Nat}
    (source : Source inputs gates)
    (smallSelected largeSelected : Fin gates -> Bool)
    (inputWire : Fin inputs -> TerminalSupportWire wireInputs wireGates)
    (gateWire : Fin gates -> TerminalSupportWire wireInputs wireGates)
    (smallBoundary largeBoundary : List (TerminalSupportWire wireInputs wireGates))
    (smallValuation : Valuation smallBoundary.length)
    (largeValuation : Valuation largeBoundary.length)
    (smallValues largeValues : Valuation gates)
    (accounted :
      source.terminalAccounted smallSelected inputWire gateWire smallBoundary)
    (included : forall gate, smallSelected gate = true -> largeSelected gate = true)
    (selectedCorrect : forall gate, smallSelected gate = true ->
      smallValues gate = largeValues gate)
    (inputAgreement : forall index, inputWire index ∈ smallBoundary ->
      terminalBoundaryValue smallBoundary smallValuation (inputWire index) =
        terminalBoundaryValue largeBoundary largeValuation (inputWire index))
    (gateAgreement : forall index, gateWire index ∈ smallBoundary ->
      terminalBoundaryValue smallBoundary smallValuation (gateWire index) =
        if largeSelected index then largeValues index
        else terminalBoundaryValue largeBoundary largeValuation (gateWire index)) :
    source.evalTerminalOpen smallSelected inputWire gateWire smallBoundary
        smallValuation smallValues =
      source.evalTerminalOpen largeSelected inputWire gateWire largeBoundary
        largeValuation largeValues := by
  cases source with
  | input index => exact inputAgreement index accounted
  | constant value => rfl
  | gate index =>
      change smallSelected index = true ∨ gateWire index ∈ smallBoundary at accounted
      cases selectedSmall : smallSelected index with
      | false =>
          have member : gateWire index ∈ smallBoundary := by
            cases accounted with
            | inl selected =>
                rw [selectedSmall] at selected
                cases selected
            | inr boundary => exact boundary
          simp only [Source.evalTerminalOpen, selectedSmall,
            Bool.false_eq_true, if_false]
          exact gateAgreement index member
      | true =>
          have selectedLarge := included index selectedSmall
          simp only [Source.evalTerminalOpen, selectedSmall, selectedLarge, if_true]
          exact selectedCorrect index selectedSmall

private theorem Program.evalTerminalOpenAux_nested
    {wireInputs wireGates inputs gates : Nat}
    (program : Program inputs gates)
    (smallSelected largeSelected : Fin gates -> Bool)
    (inputWire : Fin inputs -> TerminalSupportWire wireInputs wireGates)
    (gateWire : Fin gates -> TerminalSupportWire wireInputs wireGates)
    (smallBoundary largeBoundary : List (TerminalSupportWire wireInputs wireGates))
    (smallValuation : Valuation smallBoundary.length)
    (largeValuation : Valuation largeBoundary.length)
    (accounted :
      program.terminalSourcesAccounted smallSelected inputWire gateWire smallBoundary)
    (included : forall gate, smallSelected gate = true -> largeSelected gate = true)
    (inputAgreement : forall index, inputWire index ∈ smallBoundary ->
      terminalBoundaryValue smallBoundary smallValuation (inputWire index) =
        terminalBoundaryValue largeBoundary largeValuation (inputWire index))
    (gateAgreement : forall index, gateWire index ∈ smallBoundary ->
      terminalBoundaryValue smallBoundary smallValuation (gateWire index) =
        if largeSelected index then
          program.evalTerminalOpenAux largeBoundary largeValuation
            largeSelected inputWire gateWire index
        else terminalBoundaryValue largeBoundary largeValuation (gateWire index)) :
    forall gate, smallSelected gate = true ->
      program.evalTerminalOpenAux smallBoundary smallValuation
          smallSelected inputWire gateWire gate =
        program.evalTerminalOpenAux largeBoundary largeValuation
          largeSelected inputWire gateWire gate := by
  induction program with
  | empty => intro gate; exact Fin.elim0 gate
  | @snoc gates initial gate ih =>
      let smallEarlier : Fin gates -> Bool :=
        fun index => smallSelected index.castSucc
      let largeEarlier : Fin gates -> Bool :=
        fun index => largeSelected index.castSucc
      let earlierWire : Fin gates -> TerminalSupportWire wireInputs wireGates :=
        fun index => gateWire index.castSucc
      have accountSplit :
          initial.terminalSourcesAccounted smallEarlier inputWire
              earlierWire smallBoundary ∧
            (smallSelected (Fin.last gates) = true ->
              gate.left.terminalAccounted smallEarlier inputWire
                  earlierWire smallBoundary ∧
                gate.right.terminalAccounted smallEarlier inputWire
                  earlierWire smallBoundary) := accounted
      have earlierIncluded : forall index, smallEarlier index = true ->
          largeEarlier index = true := by
        intro index selected
        exact included index.castSucc selected
      have earlierGateAgreement : forall index, earlierWire index ∈ smallBoundary ->
          terminalBoundaryValue smallBoundary smallValuation (earlierWire index) =
            if largeEarlier index then
              initial.evalTerminalOpenAux largeBoundary largeValuation
                largeEarlier inputWire earlierWire index
            else terminalBoundaryValue largeBoundary largeValuation
              (earlierWire index) := by
        intro index member
        have full := gateAgreement index.castSucc member
        simpa only [Program.evalTerminalOpenAux_snoc_castSucc] using full
      have earlierCorrect : forall index, smallEarlier index = true ->
          initial.evalTerminalOpenAux smallBoundary smallValuation
              smallEarlier inputWire earlierWire index =
            initial.evalTerminalOpenAux largeBoundary largeValuation
              largeEarlier inputWire earlierWire index :=
        ih smallEarlier largeEarlier earlierWire accountSplit.1
          earlierIncluded earlierGateAgreement
      intro gateIndex
      refine Fin.lastCases ?_ (fun earlierIndex => ?_) gateIndex
      · intro selectedSmall
        have selectedLarge := included (Fin.last gates) selectedSmall
        change Valuation.snoc _ _ (Fin.last gates) =
          Valuation.snoc _ _ (Fin.last gates)
        rw [Valuation.snoc_last, Valuation.snoc_last,
          if_pos selectedSmall, if_pos selectedLarge]
        have currentAccount := accountSplit.2 selectedSmall
        have leftEquality :=
          (gate.left.evalTerminalOpen_nested smallEarlier largeEarlier
            inputWire earlierWire smallBoundary largeBoundary
            smallValuation largeValuation
            (initial.evalTerminalOpenAux smallBoundary smallValuation
              smallEarlier inputWire earlierWire)
            (initial.evalTerminalOpenAux largeBoundary largeValuation
              largeEarlier inputWire earlierWire)
            currentAccount.1 earlierIncluded earlierCorrect
            inputAgreement earlierGateAgreement)
        have rightEquality :=
          (gate.right.evalTerminalOpen_nested smallEarlier largeEarlier
            inputWire earlierWire smallBoundary largeBoundary
            smallValuation largeValuation
            (initial.evalTerminalOpenAux smallBoundary smallValuation
              smallEarlier inputWire earlierWire)
            (initial.evalTerminalOpenAux largeBoundary largeValuation
              largeEarlier inputWire earlierWire)
            currentAccount.2 earlierIncluded earlierCorrect
            inputAgreement earlierGateAgreement)
        rw [leftEquality, rightEquality]
      · intro selectedEarlier
        rw [Program.evalTerminalOpenAux_snoc_castSucc,
          Program.evalTerminalOpenAux_snoc_castSucc]
        exact earlierCorrect earlierIndex selectedEarlier

/-- Every selected smaller-support gate retains its value after the computed
    boundary substitution, for every valuation of the larger open boundary. -/
theorem terminalOpenGateEvaluation_pullback
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (small large : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (included : forall gate, terminalGateSelected small gate = true ->
      terminalGateSelected large gate = true)
    (valuation : Valuation (terminalBoundaryPorts candidate.program large).length)
    (gate : Fin gates) (selected : terminalGateSelected small gate = true) :
    terminalOpenGateEvaluation candidate small
        (terminalBoundaryPullback candidate small large valuation) gate =
      terminalOpenGateEvaluation candidate large valuation gate := by
  unfold terminalOpenGateEvaluation
  refine Program.evalTerminalOpenAux_nested candidate.program
    (terminalGateSelected small) (terminalGateSelected large)
    TerminalSupportWire.input TerminalSupportWire.gate
    (terminalBoundaryPorts candidate.program small)
    (terminalBoundaryPorts candidate.program large)
    (terminalBoundaryPullback candidate small large valuation) valuation
    (physicalTerminalSourcesAccounted candidate small) included ?_ ?_ gate selected
  · intro index member
    simpa only [terminalOpenWireValue] using
      terminalBoundaryValue_pullback candidate small large valuation (.input index) member
  · intro index member
    simpa only [terminalOpenWireValue, terminalOpenGateEvaluation] using
      terminalBoundaryValue_pullback candidate small large valuation (.gate index) member

/-- Every ordered smaller-support interface output denotes its actual selected
    gate in the larger open context, including internalized boundary wires. -/
theorem terminalOpenSupportSemantics_pullback
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (small large : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (included : forall gate, terminalGateSelected small gate = true ->
      terminalGateSelected large gate = true)
    (valuation : Valuation (terminalBoundaryPorts candidate.program large).length)
    (output : Fin (terminalInterfacePorts candidate small).length) :
    terminalOpenSupportSemantics candidate small
        (terminalBoundaryPullback candidate small large valuation) output =
      terminalOpenGateEvaluation candidate large valuation
        ((terminalInterfacePorts candidate small).get output) :=
  terminalOpenGateEvaluation_pullback candidate small large included valuation _
    (terminalInterfaceGet_selected candidate small output)


private theorem boundary_get_injective_of_nodup {alpha : Type} {items : List alpha}
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

private theorem terminalBoundaryValue_get
    {inputs gates : Nat} (boundary : List (TerminalSupportWire inputs gates))
    (distinct : boundary.Nodup) (valuation : Valuation boundary.length)
    (index : Fin boundary.length) :
    terminalBoundaryValue boundary valuation (boundary.get index) =
      valuation index := by
  unfold terminalBoundaryValue
  split
  · rename_i found
    have same : memberIndex found = index :=
      boundary_get_injective_of_nodup distinct (get_memberIndex found)
    rw [same]
  · rename_i absent
    exact False.elim (absent (List.get_mem boundary index))

private theorem terminalOpenWireValue_on_boundary
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (valuation : Valuation (terminalBoundaryPorts candidate.program records).length)
    (wire : TerminalSupportWire inputs gates)
    (member : wire ∈ terminalBoundaryPorts candidate.program records) :
    terminalOpenWireValue candidate records valuation wire =
      terminalBoundaryValue (terminalBoundaryPorts candidate.program records)
        valuation wire := by
  cases wire with
  | input index => rfl
  | gate index =>
      have external :=
        ((terminalBoundaryWire_eq_true_iff candidate.program records (.gate index)).1
          ((mem_terminalBoundaryPorts_iff candidate.program records (.gate index)).1
            member)).1
      change Bool.not (terminalGateSelected records index) = true at external
      cases selected : terminalGateSelected records index with
      | false =>
          simp only [terminalOpenWireValue, selected, Bool.false_eq_true, if_false]
      | true =>
          rw [selected] at external
          cases external

/-- Pulling an open boundary back to the same support is the identity map. -/
theorem terminalBoundaryPullback_identity
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (valuation : Valuation (terminalBoundaryPorts candidate.program records).length) :
    terminalBoundaryPullback candidate records records valuation = valuation := by
  funext index
  change terminalOpenWireValue candidate records valuation
      ((terminalBoundaryPorts candidate.program records).get index) = valuation index
  rw [terminalOpenWireValue_on_boundary candidate records valuation _
    (List.get_mem (terminalBoundaryPorts candidate.program records) index)]
  exact terminalBoundaryValue_get _ (terminalBoundaryPorts_nodup _ _) valuation index

private theorem terminalBoundaryPorts_nested_external
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (small large : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (included : forall gate, terminalGateSelected small gate = true ->
      terminalGateSelected large gate = true)
    (wire : TerminalSupportWire inputs gates)
    (member : wire ∈ terminalBoundaryPorts candidate.program small)
    (external : terminalWireExternal large wire = true) :
    wire ∈ terminalBoundaryPorts candidate.program large := by
  obtain ⟨_smallExternal, consumer, enumerated, selected, uses⟩ :=
    (terminalBoundaryWire_eq_true_iff candidate.program small wire).1
      ((mem_terminalBoundaryPorts_iff candidate.program small wire).1 member)
  apply (mem_terminalBoundaryPorts_iff candidate.program large wire).2
  exact (terminalBoundaryWire_eq_true_iff candidate.program large wire).2
    ⟨external, consumer, enumerated, included consumer selected, uses⟩


private theorem terminalOpenWireValue_pullback_on_boundary
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (small middle large :
      List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (smallIncluded : forall gate, terminalGateSelected small gate = true ->
      terminalGateSelected middle gate = true)
    (middleIncluded : forall gate, terminalGateSelected middle gate = true ->
      terminalGateSelected large gate = true)
    (valuation : Valuation (terminalBoundaryPorts candidate.program large).length)
    (wire : TerminalSupportWire inputs gates)
    (member : wire ∈ terminalBoundaryPorts candidate.program small) :
    terminalOpenWireValue candidate middle
        (terminalBoundaryPullback candidate middle large valuation) wire =
      terminalOpenWireValue candidate large valuation wire := by
  cases wire with
  | input index =>
      have retained :=
        terminalBoundaryPorts_nested_external candidate small middle smallIncluded
          (.input index) member rfl
      rw [terminalOpenWireValue_on_boundary candidate middle _ (.input index) retained]
      exact terminalBoundaryValue_pullback candidate middle large valuation
        (.input index) retained
  | gate index =>
      cases selectedMiddle : terminalGateSelected middle index with
      | false =>
          have external : terminalWireExternal middle (.gate index) = true := by
            change Bool.not (terminalGateSelected middle index) = true
            rw [selectedMiddle]
            rfl
          have retained :=
            terminalBoundaryPorts_nested_external candidate small middle smallIncluded
              (.gate index) member external
          rw [terminalOpenWireValue_on_boundary candidate middle _ (.gate index) retained]
          exact terminalBoundaryValue_pullback candidate middle large valuation
            (.gate index) retained
      | true =>
          have selectedLarge := middleIncluded index selectedMiddle
          simp only [terminalOpenWireValue, selectedMiddle, selectedLarge, if_true]
          exact terminalOpenGateEvaluation_pullback candidate middle large
            middleIncluded valuation index selectedMiddle

/-- Boundary substitutions compose for every three nested physical supports
    and every open valuation, including wires internalized at either stage. -/
theorem terminalBoundaryPullback_compose
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (small middle large :
      List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (smallIncluded : forall gate, terminalGateSelected small gate = true ->
      terminalGateSelected middle gate = true)
    (middleIncluded : forall gate, terminalGateSelected middle gate = true ->
      terminalGateSelected large gate = true)
    (valuation : Valuation (terminalBoundaryPorts candidate.program large).length) :
    terminalBoundaryPullback candidate small middle
        (terminalBoundaryPullback candidate middle large valuation) =
      terminalBoundaryPullback candidate small large valuation := by
  funext index
  change terminalOpenWireValue candidate middle
      (terminalBoundaryPullback candidate middle large valuation)
      ((terminalBoundaryPorts candidate.program small).get index) =
    terminalOpenWireValue candidate large valuation
      ((terminalBoundaryPorts candidate.program small).get index)
  exact terminalOpenWireValue_pullback_on_boundary candidate small middle large
    smallIncluded middleIncluded valuation _
    (List.get_mem (terminalBoundaryPorts candidate.program small) index)

/-! ## Literal source equations for independent open evaluation -/

private theorem Source.evalTerminalOpen_weaken_snoc
    {wireInputs wireGates inputs gates : Nat}
    (source : Source inputs gates) (initial : Program inputs gates) (gate : Gate inputs gates)
    (selected : Fin (gates + 1) -> Bool)
    (inputWire : Fin inputs -> TerminalSupportWire wireInputs wireGates)
    (gateWire : Fin (gates + 1) -> TerminalSupportWire wireInputs wireGates)
    (boundary : List (TerminalSupportWire wireInputs wireGates))
    (valuation : Valuation boundary.length) :
    (source.weakenGates 1).evalTerminalOpen selected inputWire gateWire boundary valuation
        ((initial.snoc gate).evalTerminalOpenAux boundary valuation selected inputWire gateWire) =
      source.evalTerminalOpen (fun index => selected index.castSucc) inputWire
        (fun index => gateWire index.castSucc) boundary valuation
        (initial.evalTerminalOpenAux boundary valuation
          (fun index => selected index.castSucc) inputWire (fun index => gateWire index.castSucc)) := by
  cases source with
  | input index => rfl
  | constant value => rfl
  | gate index =>
      change (if selected index.castSucc then
        (initial.snoc gate).evalTerminalOpenAux boundary valuation selected inputWire gateWire
          index.castSucc
        else terminalBoundaryValue boundary valuation (gateWire index.castSucc)) = _
      rw [Program.evalTerminalOpenAux_snoc_castSucc]
      rfl

private theorem Program.evalTerminalOpenAux_sources
    {wireInputs wireGates inputs gates : Nat} (program : Program inputs gates)
    (selected : Fin gates -> Bool)
    (inputWire : Fin inputs -> TerminalSupportWire wireInputs wireGates)
    (gateWire : Fin gates -> TerminalSupportWire wireInputs wireGates)
    (boundary : List (TerminalSupportWire wireInputs wireGates))
    (valuation : Valuation boundary.length) (node : Fin gates) :
    program.evalTerminalOpenAux boundary valuation selected inputWire gateWire node =
      if selected node then
        boolNand
          ((program.terminalGateSources node).1.evalTerminalOpen selected inputWire gateWire
            boundary valuation
            (program.evalTerminalOpenAux boundary valuation selected inputWire gateWire))
          ((program.terminalGateSources node).2.evalTerminalOpen selected inputWire gateWire
            boundary valuation
            (program.evalTerminalOpenAux boundary valuation selected inputWire gateWire))
      else false := by
  induction program with
  | empty => exact Fin.elim0 node
  | @snoc gates initial gate ih =>
      refine finLastCasesConstructive (motive := fun position =>
        (initial.snoc gate).evalTerminalOpenAux boundary valuation
            selected inputWire gateWire position =
          if selected position then
            boolNand
              (((initial.snoc gate).terminalGateSources position).1.evalTerminalOpen
                selected inputWire gateWire boundary valuation
                ((initial.snoc gate).evalTerminalOpenAux boundary valuation
                  selected inputWire gateWire))
              (((initial.snoc gate).terminalGateSources position).2.evalTerminalOpen
                selected inputWire gateWire boundary valuation
                ((initial.snoc gate).evalTerminalOpenAux boundary valuation
                  selected inputWire gateWire))
          else false) ?_ (fun earlier => ?_) node
      · rw [Program.terminalGateSources_snoc_last]
        rw [Source.evalTerminalOpen_weaken_snoc, Source.evalTerminalOpen_weaken_snoc]
        change Valuation.snoc _ _ (Fin.last gates) = _
        rw [Valuation.snoc_last]
      · rw [Program.evalTerminalOpenAux_snoc_castSucc,
          Program.terminalGateSources_snoc_castSucc]
        rw [Source.evalTerminalOpen_weaken_snoc, Source.evalTerminalOpen_weaken_snoc]
        exact ih (fun index => selected index.castSucc)
          (fun index => gateWire index.castSucc) earlier

/-- Read a literal source using the independently supplied boundary valuation.
    Constants remain local and selected gates use their computed open value. -/
def terminalOpenSourceValue
    {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (valuation : Valuation (terminalBoundaryPorts candidate.program records).length) :
    Source inputs gates -> Bool
  | .input index => terminalOpenWireValue candidate records valuation (.input index)
  | .constant value => value
  | .gate index => terminalOpenWireValue candidate records valuation (.gate index)

/-- The actual evaluator satisfies the literal gate equation for every open
    valuation; unselected coordinates stay inert. No whole-input premise appears. -/
theorem terminalOpenGateEvaluation_sourceEquation
    {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (valuation : Valuation (terminalBoundaryPorts candidate.program records).length)
    (node : Fin gates) :
    terminalOpenGateEvaluation candidate records valuation node =
      if terminalGateSelected records node then
        boolNand
          (terminalOpenSourceValue candidate records valuation
            (candidate.program.terminalGateSources node).1)
          (terminalOpenSourceValue candidate records valuation
            (candidate.program.terminalGateSources node).2)
      else false := by
  have sourceEquation (source : Source inputs gates) :
      source.evalTerminalOpen (terminalGateSelected records)
        TerminalSupportWire.input TerminalSupportWire.gate
        (terminalBoundaryPorts candidate.program records) valuation
        (terminalOpenGateEvaluation candidate records valuation) =
      terminalOpenSourceValue candidate records valuation source := by
    cases source <;> rfl
  have equation := Program.evalTerminalOpenAux_sources candidate.program
    (terminalGateSelected records) TerminalSupportWire.input TerminalSupportWire.gate
    (terminalBoundaryPorts candidate.program records) valuation node
  change terminalOpenGateEvaluation candidate records valuation node =
    if terminalGateSelected records node then
      boolNand
        ((candidate.program.terminalGateSources node).1.evalTerminalOpen
          (terminalGateSelected records) TerminalSupportWire.input TerminalSupportWire.gate
          (terminalBoundaryPorts candidate.program records) valuation
          (terminalOpenGateEvaluation candidate records valuation))
        ((candidate.program.terminalGateSources node).2.evalTerminalOpen
          (terminalGateSelected records) TerminalSupportWire.input TerminalSupportWire.gate
          (terminalBoundaryPorts candidate.program records) valuation
          (terminalOpenGateEvaluation candidate records valuation))
    else false at equation
  rw [sourceEquation, sourceEquation] at equation
  exact equation

/-- Canonical boundary lookup reads the corresponding independently chosen bit. -/
theorem terminalOpenWireValue_boundary_get
    {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (valuation : Valuation (terminalBoundaryPorts candidate.program records).length)
    (index : Fin (terminalBoundaryPorts candidate.program records).length) :
    terminalOpenWireValue candidate records valuation
        ((terminalBoundaryPorts candidate.program records).get index) = valuation index := by
  rw [terminalOpenWireValue_on_boundary candidate records valuation _
    (List.get_mem (terminalBoundaryPorts candidate.program records) index)]
  exact terminalBoundaryValue_get _ (terminalBoundaryPorts_nodup candidate.program records)
    valuation index

/-- An external wire absent from the actual boundary takes only the evaluator's
    inert fallback value; internal selected gate values are not covered here. -/
theorem terminalOpenWireValue_external_absent
    {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (valuation : Valuation (terminalBoundaryPorts candidate.program records).length)
    (wire : TerminalSupportWire inputs gates)
    (external : terminalWireExternal records wire = true)
    (absent : wire ∉ terminalBoundaryPorts candidate.program records) :
    terminalOpenWireValue candidate records valuation wire = false := by
  cases wire with
  | input index =>
      change terminalBoundaryValue (terminalBoundaryPorts candidate.program records)
        valuation (.input index) = false
      unfold terminalBoundaryValue
      rw [dif_neg absent]
  | gate index =>
      have unselected := (terminalWireExternal_eq_true_iff records (.gate index)).mp external
      simp only [terminalOpenWireValue, unselected, Bool.false_eq_true, if_false]
      unfold terminalBoundaryValue
      rw [dif_neg absent]

end DirectWire
end PNP

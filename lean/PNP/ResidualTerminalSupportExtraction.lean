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
        correct := fun _ gate => Fin.elim0 gate }
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
              exact earlier.correct boundaryValuation earlierIndex selectedIndex }
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
              exact earlier.correct boundaryValuation earlierIndex selectedIndex }

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

end DirectWire
end PNP

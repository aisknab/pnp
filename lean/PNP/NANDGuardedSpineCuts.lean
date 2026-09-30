import PNP.NANDGuardedSpineFamily

set_option autoImplicit false
set_option Elab.async false

/-! Exact crossing-wire predicates for arbitrary selections of the actual
guarded spine. This classifies production boundary/interface ports, not a
parallel cut representation or a supplied fragment certificate. -/

namespace PNP.DirectWire.GuardedSpineCuts
open GuardedSpineFamily (core candidate)

private theorem source_earlier {inputs gates : Nat} (initial : Program inputs gates)
    (gate : Gate inputs gates) (index : Fin gates) :
    (Program.snoc initial gate).terminalGateSources index.castSucc =
      ((initial.terminalGateSources index).1.weakenGates 1,
       (initial.terminalGateSources index).2.weakenGates 1) := by
  simp only [Program.terminalGateSources,Fin.val_castSucc,dif_pos index.isLt]

private theorem source_last {inputs gates : Nat} (initial : Program inputs gates)
    (gate : Gate inputs gates) :
    (Program.snoc initial gate).terminalGateSources (Fin.last gates) =
      (gate.left.weakenGates 1,gate.right.weakenGates 1) := by
  simp only [Program.terminalGateSources,Fin.val_last,Nat.lt_irrefl,dif_neg,not_false_eq_true]

private theorem core_output (n : Nat) : (core n).2 = .gate (Fin.last n) := by
  cases n <;> rfl

private theorem core_first (n : Nat) :
    (core n).1.terminalGateSources 0 = (.input 0,.input 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (Program.snoc ((core n).1.renameInputs Fin.castSucc) _).terminalGateSources
        (0 : Fin (n + 1)).castSucc = _
      rw [source_earlier,Program.terminalGateSources_renameInputs,ih]
      rfl

private theorem core_later (n : Nat) (index : Fin (n + 1)) (positive : 0 < index.val) :
    (core n).1.terminalGateSources index =
      (.gate ⟨index.val - 1,by omega⟩,.input index) := by
  induction n with
  | zero =>
      exfalso
      have upper := index.isLt
      omega
  | succ n ih =>
      rcases CausalBound.index_cases index with ⟨earlier,rfl⟩ | rfl
      · change (Program.snoc ((core n).1.renameInputs Fin.castSucc) _).terminalGateSources earlier.castSucc = _
        rw [source_earlier,Program.terminalGateSources_renameInputs,ih earlier positive]
        rfl
      · change (Program.snoc ((core n).1.renameInputs Fin.castSucc)
          ⟨(core n).2.renameInputs Fin.castSucc,.input (Fin.last (n + 1))⟩).terminalGateSources
            (Fin.last (n + 1)) = _
        rw [source_last,core_output]
        apply Prod.ext
        · apply congrArg Source.gate
          apply Fin.ext
          simp only [Fin.val_castAdd,Fin.val_last]
          omega
        · rfl

/-- Literal random-access sources of every gate in the existing constructor. -/
theorem sources (n : Nat) (index : Fin (n + 2)) :
    (candidate n).program.terminalGateSources index =
      if zero : index.val = 0 then (.input 0,.input 0)
      else if last : index.val = n + 1 then (.input 0,.gate ⟨n,by omega⟩)
      else (.gate ⟨index.val - 1,by omega⟩,.input ⟨index.val,by omega⟩) := by
  rcases CausalBound.index_cases index with ⟨earlier,rfl⟩ | rfl
  · change (Program.snoc (core n).1 ⟨.input 0,(core n).2⟩).terminalGateSources earlier.castSucc = _
    rw [source_earlier]
    have notLast : earlier.val ≠ n + 1 := Nat.ne_of_lt earlier.isLt
    by_cases zero : earlier.val = 0
    · have same : earlier = (0 : Fin (n + 1)) := Fin.ext zero
      subst earlier
      rw [core_first]
      simp only [Fin.val_castSucc,Fin.val_zero]
      rfl
    · simp only [Fin.val_castSucc,dif_neg zero,dif_neg notLast]
      rw [core_later n earlier (Nat.pos_of_ne_zero zero)]
      rfl
  · change (Program.snoc (core n).1 ⟨.input 0,(core n).2⟩).terminalGateSources (Fin.last (n + 1)) = _
    have notZero : n + 1 ≠ 0 := by omega
    rw [source_last,core_output]
    simp only [Fin.val_last,dif_neg notZero]
    rfl

private theorem uses_iff {inputs gates : Nat} (program : Program inputs gates)
    (consumer : Fin gates) (wire : TerminalSupportWire inputs gates) :
    program.terminalGateUsesWire consumer wire = true ↔
      (program.terminalGateSources consumer).1.terminalSupportWire? = some wire ∨
      (program.terminalGateSources consumer).2.terminalSupportWire? = some wire := by
  change (decide (_ = some wire) || decide (_ = some wire)) = true ↔ _
  simp only [Bool.or_eq_true,decide_eq_true_eq]

/-- Every gate output has only its immediate successor as a consumer. -/
theorem uses_gate_iff (n : Nat) (consumer producer : Fin (n + 2)) :
    (candidate n).program.terminalGateUsesWire consumer (.gate producer) = true ↔
      consumer.val = producer.val + 1 := by
  rw [uses_iff,sources]
  by_cases zero : consumer.val = 0
  · rw [dif_pos zero]
    constructor
    · rintro (impossible | impossible) <;> cases impossible
    · intro impossible
      exfalso
      omega
  · rw [dif_neg zero]
    by_cases last : consumer.val = n + 1
    · rw [dif_pos last]
      constructor
      · rintro (impossible | same)
        · cases impossible
        · have equal := congrArg Fin.val (TerminalSupportWire.gate.inj (Option.some.inj same))
          change n = producer.val at equal
          omega
      · intro next
        apply Or.inr
        have same : (⟨n,by omega⟩ : Fin (n + 2)) = producer := Fin.ext (by change n = producer.val; omega)
        exact congrArg (fun index : Fin (n + 2) => some (TerminalSupportWire.gate index)) same
    · rw [dif_neg last]
      constructor
      · rintro (same | impossible)
        · have equal := congrArg Fin.val (TerminalSupportWire.gate.inj (Option.some.inj same))
          change consumer.val - 1 = producer.val at equal
          omega
        · cases impossible
      · intro next
        apply Or.inl
        have same : (⟨consumer.val - 1,by omega⟩ : Fin (n + 2)) = producer := Fin.ext (by change consumer.val - 1 = producer.val; omega)
        exact congrArg (fun index : Fin (n + 2) => some (TerminalSupportWire.gate index)) same

/-- Only the first and final gates use the guard; every other primary input
is consumed by exactly its matching middle gate. -/
theorem uses_input_iff (n : Nat) (consumer : Fin (n + 2)) (input : Fin (n + 1)) :
    (candidate n).program.terminalGateUsesWire consumer (.input input) = true ↔
      (input.val = 0 ∧ (consumer.val = 0 ∨ consumer.val = n + 1)) ∨
      (0 < input.val ∧ consumer.val = input.val) := by
  rw [uses_iff,sources]
  by_cases zero : consumer.val = 0
  · rw [dif_pos zero]
    constructor
    · rintro (same | same)
      all_goals
        have equal := congrArg Fin.val (TerminalSupportWire.input.inj (Option.some.inj same))
        change 0 = input.val at equal
        exact Or.inl ⟨equal.symm,Or.inl zero⟩
    · rintro (⟨guard,_⟩ | ⟨positive,equal⟩)
      · apply Or.inl
        have same : (0 : Fin (n + 1)) = input := Fin.ext guard.symm
        exact congrArg (fun index : Fin (n + 1) => some (TerminalSupportWire.input index)) same
      · exfalso
        omega
  · rw [dif_neg zero]
    by_cases last : consumer.val = n + 1
    · rw [dif_pos last]
      constructor
      · rintro (same | impossible)
        · have equal := congrArg Fin.val (TerminalSupportWire.input.inj (Option.some.inj same))
          change 0 = input.val at equal
          exact Or.inl ⟨equal.symm,Or.inr last⟩
        · cases impossible
      · rintro (⟨guard,_⟩ | ⟨_,equal⟩)
        · apply Or.inl
          have same : (0 : Fin (n + 1)) = input := Fin.ext guard.symm
          exact congrArg (fun index : Fin (n + 1) => some (TerminalSupportWire.input index)) same
        · exfalso
          have upper := input.isLt
          omega
    · rw [dif_neg last]
      constructor
      · rintro (impossible | same)
        · cases impossible
        · have equal := congrArg Fin.val (TerminalSupportWire.input.inj (Option.some.inj same))
          change consumer.val = input.val at equal
          exact Or.inr ⟨by omega,equal⟩
      · rintro (⟨_,firstOrLast⟩ | ⟨_,equal⟩)
        · rcases firstOrLast with first | final
          · exact False.elim (zero first)
          · exact False.elim (last final)
        · apply Or.inr
          have bound : consumer.val < n + 1 := by have upper := consumer.isLt; omega
          have same : (⟨consumer.val,bound⟩ : Fin (n + 1)) = input := Fin.ext equal
          exact congrArg (fun index : Fin (n + 1) => some (TerminalSupportWire.input index)) same

theorem global_output_iff (n : Nat) (producer : Fin (n + 2)) :
    terminalGateIsGlobalOutput (candidate n).directWireWord producer = true ↔
      producer.val = n + 1 := by
  have outputValue (output : Fin 1) : (candidate n).directWireWord.source output =
      .gate (Fin.last (n + 1)) := Candidate.ofDirectWireWord_pointwise _ _ _
  rw [terminalGateIsGlobalOutput_eq_true_iff]
  constructor
  · rintro ⟨output,same⟩
    rw [outputValue] at same
    exact (congrArg Fin.val (Source.gate.inj same)).symm
  · intro last
    refine ⟨0,?_⟩
    rw [outputValue]
    exact congrArg Source.gate (Fin.ext last.symm)

variable {profileWidth : Nat}

/-- Guard aliasing creates one canonical input port even when both ends use it. -/
theorem guard_boundary_iff (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth)) :
    TerminalSupportWire.input 0 ∈ terminalBoundaryPorts (candidate n).program records ↔
      terminalGateSelected records 0 = true ∨ terminalGateSelected records (Fin.last (n + 1)) = true := by
  rw [mem_terminalBoundaryPorts_iff,terminalBoundaryWire_eq_true_iff]
  constructor
  · rintro ⟨_,consumer,_,selected,used⟩
    rcases (uses_input_iff n consumer 0).mp used with ⟨_,firstOrLast⟩ | ⟨impossible,_⟩
    · rcases firstOrLast with first | last
      · have same : consumer = 0 := Fin.ext first
        exact Or.inl (same ▸ selected)
      · have same : consumer = Fin.last (n + 1) := Fin.ext last
        exact Or.inr (same ▸ selected)
    · cases impossible
  · intro selected
    refine ⟨rfl,?_⟩
    rcases selected with first | last
    · exact ⟨0,mem_allFin _,first,(uses_input_iff n 0 0).mpr (Or.inl ⟨rfl,Or.inl rfl⟩)⟩
    · exact ⟨Fin.last (n + 1),mem_allFin _,last,
        (uses_input_iff n _ 0).mpr (Or.inl ⟨rfl,Or.inr rfl⟩)⟩

theorem fresh_boundary_iff (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (input : Fin (n + 1)) (positive : 0 < input.val) :
    TerminalSupportWire.input input ∈ terminalBoundaryPorts (candidate n).program records ↔
      terminalGateSelected records input.castSucc = true := by
  rw [mem_terminalBoundaryPorts_iff,terminalBoundaryWire_eq_true_iff]
  constructor
  · rintro ⟨_,consumer,_,selected,used⟩
    rcases (uses_input_iff n consumer input).mp used with ⟨zero,_⟩ | ⟨_,equal⟩
    · exfalso
      omega
    · have same : consumer = input.castSucc := Fin.ext equal
      exact same ▸ selected
  · intro selected
    exact ⟨rfl,input.castSucc,mem_allFin _,selected,
      (uses_input_iff n _ input).mpr (Or.inr ⟨positive,rfl⟩)⟩

/-- Incoming gate ports are exactly the unselected-to-selected transitions. -/
theorem gate_boundary_iff (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (producer : Fin (n + 2)) :
    TerminalSupportWire.gate producer ∈ terminalBoundaryPorts (candidate n).program records ↔
      terminalGateSelected records producer = false ∧
        ∃ consumer : Fin (n + 2), consumer.val = producer.val + 1 ∧
          terminalGateSelected records consumer = true := by
  rw [mem_terminalBoundaryPorts_iff,terminalBoundaryWire_eq_true_iff,terminalWireExternal_eq_true_iff]
  constructor
  · rintro ⟨outside,consumer,_,selected,used⟩
    exact ⟨outside,consumer,(uses_gate_iff n consumer producer).mp used,selected⟩
  · rintro ⟨outside,consumer,next,selected⟩
    exact ⟨outside,consumer,mem_allFin _,selected,(uses_gate_iff n consumer producer).mpr next⟩

/-- Outgoing ports are exactly selected-to-unselected transitions and the
selected final output. No interval or nonempty-selection premise is needed. -/
theorem interface_iff (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (producer : Fin (n + 2)) :
    producer ∈ terminalInterfacePorts (candidate n) records ↔
      terminalGateSelected records producer = true ∧
        (producer.val = n + 1 ∨ ∃ consumer : Fin (n + 2),
          consumer.val = producer.val + 1 ∧ terminalGateSelected records consumer = false) := by
  rw [mem_terminalInterfacePorts_iff,terminalInterfaceGate_eq_true_iff,
    terminalGateHasExternalConsumer_eq_true_iff,global_output_iff]
  constructor
  · rintro ⟨selected,externalOrFinal⟩
    refine ⟨selected,?_⟩
    rcases externalOrFinal with ⟨consumer,_,outside,used⟩ | last
    · exact Or.inr ⟨consumer,(uses_gate_iff n consumer producer).mp used,outside⟩
    · exact Or.inl last
  · rintro ⟨selected,lastOrExternal⟩
    refine ⟨selected,?_⟩
    rcases lastOrExternal with last | ⟨consumer,next,outside⟩
    · exact Or.inr last
    · exact Or.inl ⟨consumer,mem_allFin _,outside,(uses_gate_iff n consumer producer).mpr next⟩

theorem interface_succ_iff (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (producer : Fin (n + 1)) :
    producer.castSucc ∈ terminalInterfacePorts (candidate n) records ↔
      terminalGateSelected records producer.castSucc = true ∧
        terminalGateSelected records producer.succ = false := by
  rw [interface_iff]
  constructor
  · rintro ⟨selected,lastOrExternal⟩
    refine ⟨selected,?_⟩
    rcases lastOrExternal with last | ⟨consumer,next,outside⟩
    · exfalso
      have upper := producer.isLt
      change producer.val = n + 1 at last
      omega
    · have same : consumer = producer.succ := Fin.ext next
      exact same ▸ outside
  · rintro ⟨selected,outside⟩
    exact ⟨selected,Or.inr ⟨producer.succ,rfl,outside⟩⟩

theorem last_interface_iff (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth)) :
    Fin.last (n + 1) ∈ terminalInterfacePorts (candidate n) records ↔
      terminalGateSelected records (Fin.last (n + 1)) = true := by
  rw [interface_iff]
  exact ⟨fun both => both.1,fun selected => ⟨selected,Or.inl rfl⟩⟩

end PNP.DirectWire.GuardedSpineCuts

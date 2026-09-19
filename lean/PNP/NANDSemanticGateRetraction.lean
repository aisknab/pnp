import PNP.ResidualTerminalSaturatedSupportContext
import PNP.NANDComposition

/-!
Research helper for the fresh-field cost lower bound. Gates may be removed only
under an explicit, uniform semantic-constant condition after input substitution.
This is not an unconditional optimization route or forced-cost theorem. The
planned fresh-field theorem must derive this helper condition from its concrete
extension semantics; no standalone milestone or progress credit is claimed.
-/

namespace PNP.DirectWire.SemanticGateRetraction

variable {inputs gates outputs outerInputs : Nat}

abbrev GateRecords (inputs gates outputs : Nat) :=
  List (TerminalPrimitiveRecord inputs gates outputs 0)

def kept (erased : GateRecords inputs gates outputs) : GateRecords inputs gates outputs :=
  terminalPhysicalComplementRecords erased

def inducedInput (binding : Fin inputs → Source outerInputs 0)
    (valuation : Valuation outerInputs) : Valuation inputs :=
  fun index => (binding index).eval valuation (Program.empty.eval valuation)

def bindingForWire (binding : Fin inputs → Source outerInputs 0)
    (values : Fin gates → Bool) : TerminalSupportWire inputs gates → Source outerInputs 0
  | .input index => binding index
  | .gate gate => .constant (values gate)

def boundaryBinding (candidate : Candidate inputs gates outputs)
    (erased : GateRecords inputs gates outputs) (values : Fin gates → Bool)
    (binding : Fin inputs → Source outerInputs 0) :
    Fin (extractTerminalSupport candidate (kept erased)).boundary.length → Source outerInputs 0 :=
  fun index => bindingForWire binding values
    ((extractTerminalSupport candidate (kept erased)).boundary.get index)

def program (candidate : Candidate inputs gates outputs)
    (erased : GateRecords inputs gates outputs) (values : Fin gates → Bool)
    (binding : Fin inputs → Source outerInputs 0) :
    Program outerInputs (0 + (extractTerminalSupport candidate (kept erased)).gateCount) :=
  Program.empty.appendSubstituted (boundaryBinding candidate erased values binding)
    (extractTerminalSupport candidate (kept erased)).extractedCandidate.program

def reboundSource (candidate : Candidate inputs gates outputs)
    (erased : GateRecords inputs gates outputs) (values : Fin gates → Bool)
    (binding : Fin inputs → Source outerInputs 0) :
    Source inputs gates →
      Source outerInputs (0 + (extractTerminalSupport candidate (kept erased)).gateCount)
  | .input index =>
      (binding index).weakenGates (extractTerminalSupport candidate (kept erased)).gateCount
  | .constant value => .constant value
  | .gate gate =>
      if retained : terminalGateSelected (kept erased) gate = true then
        .gate (Fin.natAdd 0 (terminalExtractionGateIndex candidate (kept erased) gate retained))
      else .constant (values gate)

def implementation (candidate : Candidate inputs gates outputs)
    (erased : GateRecords inputs gates outputs) (values : Fin gates → Bool)
    (binding : Fin inputs → Source outerInputs 0) : Implementation outerInputs outputs :=
  (Candidate.ofDirectWireWord (program candidate erased values binding)
    ⟨fun output => reboundSource candidate erased values binding
      (candidate.directWireWord.source output)⟩).toImplementation

private theorem erased_of_not_kept (erased : GateRecords inputs gates outputs)
    (gate : Fin gates) (notKept : terminalGateSelected (kept erased) gate ≠ true) :
    terminalGateSelected erased gate = true := by
  cases value : terminalGateSelected erased gate with
  | true => rfl
  | false =>
      have retained : terminalGateSelected (kept erased) gate = true := by
        unfold kept
        rw [terminalPhysicalComplementRecords_selected, value]
        rfl
      exact False.elim (notKept retained)

private theorem bindingForWire_value (candidate : Candidate inputs gates outputs)
    (erased : GateRecords inputs gates outputs) (values : Fin gates → Bool)
    (binding : Fin inputs → Source outerInputs 0)
    (constantOn : ∀ valuation gate, terminalGateSelected erased gate = true →
      candidate.program.eval (inducedInput binding valuation) gate = values gate)
    (valuation : Valuation outerInputs) (wire : TerminalSupportWire inputs gates)
    (member : wire ∈ (extractTerminalSupport candidate (kept erased)).boundary) :
    (bindingForWire binding values wire).eval valuation (Program.empty.eval valuation) =
      wire.candidateValue candidate (inducedInput binding valuation) := by
  cases wire with
  | input index => rfl
  | gate gate =>
      have external := ((terminalBoundaryWire_eq_true_iff candidate.program (kept erased)
        (.gate gate)).mp
          ((mem_terminalBoundaryPorts_iff candidate.program (kept erased) (.gate gate)).mp member)).1
      have absent : terminalGateSelected (kept erased) gate = false :=
        (terminalWireExternal_eq_true_iff (kept erased) (.gate gate)).mp external
      have marked := erased_of_not_kept erased gate (by rw [absent]; intro impossible; cases impossible)
      exact (constantOn valuation gate marked).symm

theorem kept_gate_value (candidate : Candidate inputs gates outputs)
    (erased : GateRecords inputs gates outputs) (values : Fin gates → Bool)
    (binding : Fin inputs → Source outerInputs 0)
    (constantOn : ∀ valuation gate, terminalGateSelected erased gate = true →
      candidate.program.eval (inducedInput binding valuation) gate = values gate)
    (valuation : Valuation outerInputs) (gate : Fin gates)
    (retained : terminalGateSelected (kept erased) gate = true) :
    (program candidate erased values binding).eval valuation
        (Fin.natAdd 0 (terminalExtractionGateIndex candidate (kept erased) gate retained)) =
      candidate.program.eval (inducedInput binding valuation) gate := by
  have boundaryEqual :
      (fun index => (boundaryBinding candidate erased values binding index).eval
        valuation (Program.empty.eval valuation)) =
      terminalInducedBoundaryValuation candidate (kept erased) (inducedInput binding valuation) := by
    funext index
    exact bindingForWire_value candidate erased values binding constantOn valuation
      ((extractTerminalSupport candidate (kept erased)).boundary.get index)
      (List.get_mem _ index)
  unfold program
  rw [Program.eval_appendSubstituted_suffix, boundaryEqual]
  exact extractTerminalSupport_gate_induced candidate (kept erased)
    (inducedInput binding valuation) gate retained

theorem reboundSource_value (candidate : Candidate inputs gates outputs)
    (erased : GateRecords inputs gates outputs) (values : Fin gates → Bool)
    (binding : Fin inputs → Source outerInputs 0)
    (constantOn : ∀ valuation gate, terminalGateSelected erased gate = true →
      candidate.program.eval (inducedInput binding valuation) gate = values gate)
    (source : Source inputs gates) (valuation : Valuation outerInputs) :
    (reboundSource candidate erased values binding source).eval valuation
        ((program candidate erased values binding).eval valuation) =
      source.eval (inducedInput binding valuation)
        (candidate.program.eval (inducedInput binding valuation)) := by
  cases source with
  | input index =>
      unfold reboundSource
      rw [Source.eval_weakenGates]
      exact (binding index).eval_congr (fun _ => rfl) (fun impossible => Fin.elim0 impossible)
  | constant value => rfl
  | gate gate =>
      by_cases retained : terminalGateSelected (kept erased) gate = true
      · simpa only [reboundSource, dif_pos retained, Source.eval] using
          kept_gate_value candidate erased values binding constantOn valuation gate retained
      · simpa only [reboundSource, dif_neg retained, Source.eval] using
          (constantOn valuation gate (erased_of_not_kept erased gate retained)).symm

theorem semantics (candidate : Candidate inputs gates outputs)
    (erased : GateRecords inputs gates outputs) (values : Fin gates → Bool)
    (binding : Fin inputs → Source outerInputs 0)
    (constantOn : ∀ valuation gate, terminalGateSelected erased gate = true →
      candidate.program.eval (inducedInput binding valuation) gate = values gate)
    (valuation : Valuation outerInputs) (output : Fin outputs) :
    (implementation candidate erased values binding).candidate.semantics valuation output =
      candidate.semantics (inducedInput binding valuation) output := by
  change (Candidate.ofDirectWireWord (program candidate erased values binding)
    ⟨fun out => reboundSource candidate erased values binding
      (candidate.directWireWord.source out)⟩).semantics valuation output = _
  rw [Candidate.ofDirectWireWord_semantics]
  exact reboundSource_value candidate erased values binding constantOn
    (candidate.directWireWord.source output) valuation

theorem gateCount_partition (candidate : Candidate inputs gates outputs)
    (erased : GateRecords inputs gates outputs) (values : Fin gates → Bool)
    (binding : Fin inputs → Source outerInputs 0) :
    (implementation candidate erased values binding).gateCount +
      (extractTerminalSupport candidate erased).gateCount = gates := by
  change (0 + (extractTerminalSupport candidate (kept erased)).gateCount) +
    (extractTerminalSupport candidate erased).gateCount = gates
  rw [Nat.zero_add, Nat.add_comm]
  exact terminalPhysicalComplementRecords_gateCount_partition candidate erased

theorem gateCount_eq_sub (candidate : Candidate inputs gates outputs)
    (erased : GateRecords inputs gates outputs) (values : Fin gates → Bool)
    (binding : Fin inputs → Source outerInputs 0) :
    (implementation candidate erased values binding).gateCount =
      gates - (extractTerminalSupport candidate erased).gateCount := by
  have partition := gateCount_partition candidate erased values binding
  calc
    (implementation candidate erased values binding).gateCount =
        ((implementation candidate erased values binding).gateCount +
          (extractTerminalSupport candidate erased).gateCount) -
            (extractTerminalSupport candidate erased).gateCount :=
      (Nat.add_sub_cancel _ _).symm
    _ = gates - (extractTerminalSupport candidate erased).gateCount :=
      congrArg (fun count => count - (extractTerminalSupport candidate erased).gateCount) partition

end PNP.DirectWire.SemanticGateRetraction

/-
Copyright (c) 2026 PNP Labs.

Source-generated physical NAND window search. Candidates come from the exact
extracted boundary and interface, not a supplied universe or optimizer.
Causal caps exclude semantically equivalent but cyclic literal splices.
An exhausted window is not a global minimality or ZeroSlack certificate.
The full manuscript profile schema and encoded-runtime bound remain separate.
-/

import PNP.NANDArbitrarySupportSplice
import PNP.ResidualRoutes

namespace PNP.DirectWire.PhysicalWindowSearch

variable {inputs gates outputs profileWidth : Nat}

/-- Every exact-size candidate below the local budget, in deterministic order. -/
def smallerCandidates (boundary outputs budget : Nat) :
    List (Implementation boundary outputs) :=
  (List.range budget).flatMap fun size =>
    (allCandidates boundary size outputs).map Candidate.toImplementation

theorem mem_smallerCandidates {boundary outputs budget : Nat}
    (offered : Implementation boundary outputs) (smaller : offered.gateCount < budget) :
    offered ∈ smallerCandidates boundary outputs budget := by
  cases offered with
  | mk size candidate =>
      exact mem_flatMap_of_mem (List.mem_range.mpr smaller)
        (mem_map_of_mem Candidate.toImplementation (mem_allCandidates candidate))

variable (candidate : Candidate inputs gates outputs)
variable (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))

abbrev Offered := Implementation
  (terminalBoundaryPorts candidate.program records).length
  (terminalInterfacePorts candidate records).length

/-- Only actual original incoming-wire positions determine the causal check. -/
def causalCheck (offered : Offered candidate records) : Bool :=
  allTrue (allFin (terminalInterfacePorts candidate records).length) fun port =>
    decide (CausalBound.outputLevel offered.candidate
      (ArbitrarySupportSplice.causalBoundaryLabels candidate records) port ≤
        ((terminalInterfacePorts candidate records).get port).val + 1)

theorem causalCheck_eq_true_iff (offered : Offered candidate records) :
    causalCheck candidate records offered = true ↔
      ArbitrarySupportSplice.CausalInterfaceBound candidate records offered.candidate := by
  constructor
  · intro accepted port
    exact of_decide_eq_true (allTrue_sound accepted (mem_allFin port))
  · intro bounded
    apply allTrue_complete
    intro port _member
    exact decide_eq_true (bounded port)

/-- Full physical acceptance; no semantic correctness or size witness is supplied. -/
def check (offered : Offered candidate records) : Bool :=
  decide (offered.gateCount < (extractTerminalSupport candidate records).gateCount) &&
    equivalentBool offered.candidate (extractTerminalSupport candidate records).extractedCandidate &&
    causalCheck candidate records offered

def Valid (offered : Offered candidate records) : Prop :=
  offered.gateCount < (extractTerminalSupport candidate records).gateCount ∧
    Equivalent offered.candidate.program offered.candidate.directWireWord
      (extractTerminalSupport candidate records).extractedCandidate.program
      (extractTerminalSupport candidate records).extractedCandidate.directWireWord ∧
    ArbitrarySupportSplice.CausalInterfaceBound candidate records offered.candidate

theorem check_eq_true_iff (offered : Offered candidate records) :
    check candidate records offered = true ↔ Valid candidate records offered := by
  simp only [check, Valid, Bool.and_eq_true, decide_eq_true_eq,
    equivalentBool_eq_true_iff, causalCheck_eq_true_iff]
  exact and_assoc

/-- The source-derived finite universe of strictly smaller physical candidates. -/
def candidateUniverse : List (Offered candidate records) :=
  smallerCandidates (terminalBoundaryPorts candidate.program records).length
    (terminalInterfacePorts candidate records).length
    (extractTerminalSupport candidate records).gateCount

/-- Candidate discovery, not merely checking one caller-supplied offer. -/
def search : Option (Offered candidate records) :=
  (candidateUniverse candidate records).find? (check candidate records)

theorem search_sound {offered : Offered candidate records}
    (found : search candidate records = some offered) :
    Valid candidate records offered :=
  (check_eq_true_iff candidate records offered).mp (List.find?_some found)

/-- Exhaustion excludes exactly the local, causal, strictly smaller class. -/
theorem search_none_iff :
    search candidate records = none ↔
      ∀ offered : Offered candidate records, ¬Valid candidate records offered := by
  constructor
  · intro missing offered valid
    have absent := List.find?_eq_none.mp missing offered
      (mem_smallerCandidates offered valid.1)
    exact absent ((check_eq_true_iff candidate records offered).mpr valid)
  · intro absent
    apply List.find?_eq_none.mpr
    intro offered _member checked
    exact absent offered ((check_eq_true_iff candidate records offered).mp checked)

theorem search_complete (offered : Offered candidate records)
    (valid : Valid candidate records offered) :
    ∃ found, search candidate records = some found := by
  cases searched : search candidate records with
  | none => exact False.elim ((search_none_iff candidate records).mp searched offered valid)
  | some found => exact ⟨found, rfl⟩

/-- A discovered candidate retains the concrete search result and derived checks. -/
structure Found where
  offered : Offered candidate records
  found : search candidate records = some offered

namespace Found

variable {candidate records}

theorem valid (witness : Found candidate records) :
    Valid candidate records witness.offered :=
  search_sound candidate records witness.found

/-- The existing compiler computes the actual splice order; success follows from
the checked physical caps, not from an extra supplied compilation premise. -/
def compiled (witness : Found candidate records) :
    CompiledRawNandGraph
      (ArbitrarySupportSplice.graph candidate records witness.offered.candidate) :=
  match computed : ArbitrarySupportSplice.compile candidate records witness.offered.candidate with
  | some compiled => compiled
  | none => False.elim (by
      obtain ⟨compiled, accepted⟩ :=
        ArbitrarySupportSplice.compile_of_causalInterfaceBound candidate records
          witness.offered.candidate witness.valid.2.2
      have impossible := computed.symm.trans accepted
      cases impossible)

def result (witness : Found candidate records) : Implementation inputs outputs :=
  (ArbitrarySupportSplice.result candidate records witness.offered.candidate
    witness.compiled).toImplementation

theorem equivalent (witness : Found candidate records) :
    Equivalent witness.result.candidate.program witness.result.candidate.directWireWord
      candidate.program candidate.directWireWord := by
  intro input output
  exact ArbitrarySupportSplice.result_semantics candidate records witness.offered.candidate
    (funext fun valuation => funext fun port => witness.valid.2.1 valuation port)
    witness.compiled input output

theorem exact_cost (witness : Found candidate records) :
    witness.result.gateCount + (extractTerminalSupport candidate records).gateCount =
      gates + witness.offered.gateCount :=
  ArbitrarySupportSplice.result_exact_accounting candidate records witness.offered.candidate
    witness.compiled

def gain (witness : Found candidate records) :
    StrictEquivalentGain candidate.toImplementation witness.result :=
  ⟨ArbitrarySupportSplice.result_strict_gain candidate records witness.offered.candidate
      witness.valid.1 witness.compiled, witness.equivalent⟩

theorem strict_residual_descent (witness : Found candidate records) :
    residualSlack witness.result < residualSlack candidate.toImplementation :=
  witness.gain.strictResidualDescent

end Found

/-- Distinguish a schema-size guard from genuine exhaustive window silence. -/
inductive Outcome (limit : Nat) where
  | outside (tooLarge : limit < (extractTerminalSupport candidate records).gateCount)
  | exhausted (noLocalGain : ∀ offered : Offered candidate records,
      ¬Valid candidate records offered)
  | gain (witness : Found candidate records)

/-- Apply the window limit before constructing the candidate enumeration. -/
def run (limit : Nat) : Outcome candidate records limit :=
  if bounded : (extractTerminalSupport candidate records).gateCount ≤ limit then
    match found : search candidate records with
    | none => .exhausted ((search_none_iff candidate records).mp found)
    | some offered => .gain ⟨offered, found⟩
  else .outside (Nat.lt_of_not_ge bounded)

end PNP.DirectWire.PhysicalWindowSearch

import PNP.NANDPhysicalGateProvenance

open PNP.DirectWire PNP.DirectWire.PhysicalGateProvenance

-- These four statements quantify over arbitrary finite programs.
example {inputs gates : Nat} (program : Program inputs gates) :
    (constantOrigins program).length =
      (compileNANDConstantPropagation program).gateCount :=
  constantOrigins_length program

example {inputs gates : Nat} (program : Program inputs gates) :
    (constantOrigins program).Nodup := constantOrigins_nodup program

example {inputs gates : Nat} (program : Program inputs gates) :
    (sharingOrigins program).length = (compileNANDSharing program).gateCount :=
  sharingOrigins_length program

example {inputs gates : Nat} (program : Program inputs gates) :
    (sharingOrigins program).Nodup := sharingOrigins_nodup program

-- Runtime-free kernel fixtures distinguish actual original coordinates.
def bothConstants : Program 0 2 :=
  .snoc (.snoc .empty ⟨.constant false, .constant true⟩)
    ⟨.gate ⟨0, by decide⟩, .constant true⟩

example : (constantOrigins bothConstants).map Fin.val = [] := by decide

def sharedInputs : Program 2 3 :=
  .snoc
    (.snoc (.snoc .empty ⟨.input fin2Zero, .input fin2One⟩)
      ⟨.input fin2One, .input fin2Zero⟩)
    ⟨.gate ⟨1, by decide⟩, .constant true⟩

example : (sharingOrigins sharedInputs).map Fin.val = [0, 2] := by decide
example : (constantOrigins sharedInputs).map Fin.val = [0, 1, 2] := by decide

-- Actual aliases, not merely matching cardinalities, must enumerate positions.
example {inputs gates : Nat} (program : Program inputs gates) :
    (constantOrigins program).map (constantPosition program) =
      (List.range (compileNANDConstantPropagation program).gateCount).map some :=
  constantOrigins_positions program

example {inputs gates : Nat} (program : Program inputs gates) :
    (sharingOrigins program).map (sharingPosition program) =
      List.range (compileNANDSharing program).gateCount :=
  sharingOrigins_positions program

example : (constantOrigins sharedInputs).map (constantPosition sharedInputs) =
    [some 0, some 1, some 2] := by decide
example : (sharingOrigins sharedInputs).map (sharingPosition sharedInputs) =
    [0, 1] := by decide
-- The duplicate gate aliases position zero; it is not a fresh physical owner.
example : sharingPosition sharedInputs ⟨1, by decide⟩ = 0 := by decide
example : (constantOrigins bothConstants).map (constantPosition bothConstants) = [] := by decide

#print axioms constantOrigins_positions
#print axioms sharingOrigins_positions

-- Typed origins return the exact physical alias and are injective.
example {inputs gates : Nat} (program : Program inputs gates)
    (position : Fin (compileNANDConstantPropagation program).gateCount) :
    (compileNANDConstantPropagation program).alias (constantOrigin program position) =
      .gate position := constantOrigin_alias program position

example {inputs gates : Nat} (program : Program inputs gates)
    (position : Fin (compileNANDSharing program).gateCount) :
    (compileNANDSharing program).alias (sharingOrigin program position) = position :=
  sharingOrigin_alias program position

example {inputs gates : Nat} (program : Program inputs gates)
    {left right : Fin (compileNANDConstantPropagation program).gateCount}
    (same : constantOrigin program left = constantOrigin program right) : left = right :=
  constantOrigin_injective program same

example {inputs gates : Nat} (program : Program inputs gates)
    {left right : Fin (compileNANDSharing program).gateCount}
    (same : sharingOrigin program left = sharingOrigin program right) : left = right :=
  sharingOrigin_injective program same

example : (sharingOrigin sharedInputs ⟨1, by decide⟩).val = 2 := by decide
example : (constantOrigin sharedInputs ⟨2, by decide⟩).val = 2 := by decide

#print axioms constantOrigin_alias
#print axioms constantOrigin_injective
#print axioms sharingOrigin_alias
#print axioms sharingOrigin_injective

-- The extractor's actual append/skip scan has a source-bound two-sided inverse.
example {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (position : Fin (extractTerminalSupport candidate records).gateCount) :
    terminalExtractionGateIndex candidate records
        (terminalExtractionOrigin candidate records position)
        (terminalExtractionOrigin_selected candidate records position) = position :=
  terminalExtractionGateIndex_origin candidate records position

example {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (gate : Fin gates) (selected : terminalGateSelected records gate = true) :
    terminalExtractionOrigin candidate records
      (terminalExtractionGateIndex candidate records gate selected) = gate :=
  terminalExtractionOrigin_gateIndex candidate records gate selected

example {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    {left right : Fin (extractTerminalSupport candidate records).gateCount}
    (same : terminalExtractionOrigin candidate records left =
      terminalExtractionOrigin candidate records right) : left = right :=
  terminalExtractionOrigin_injective candidate records same

def sparseCandidate : Candidate 2 3 1 :=
  Candidate.ofDirectWireWord sharedInputs ⟨fun _ => .gate ⟨2, by decide⟩⟩

-- Duplicate, out-of-order requests do not duplicate or reorder physical gates.
def sparseRecords : List (TerminalPrimitiveRecord 2 3 1 0) :=
  [.gate ⟨2, by decide⟩, .gate ⟨0, by decide⟩, .gate ⟨2, by decide⟩]

example : (terminalExtractionOrigin sparseCandidate sparseRecords ⟨0, by decide⟩).val = 0 :=
  by decide
example : (terminalExtractionOrigin sparseCandidate sparseRecords ⟨1, by decide⟩).val = 2 :=
  by decide
example : (terminalExtractionGateIndex sparseCandidate sparseRecords ⟨2, by decide⟩
    (by decide)).val = 1 := by decide
example : terminalGateSelected sparseRecords ⟨1, by decide⟩ = false := by decide

#print axioms terminalExtractionOrigin_selected
#print axioms terminalExtractionGateIndex_origin
#print axioms terminalExtractionOrigin_gateIndex
#print axioms terminalExtractionOrigin_injective

-- All three real passes, and their complete computed trace, retain unique origins.
example {inputs outputs : Nat} (current : Implementation inputs outputs)
    (position : Fin (outputConeImplementation current).gateCount) :
    terminalExtractionGateIndex current.candidate (outputConeRecords current.candidate)
        (coneOrigin current position)
        (terminalExtractionOrigin_selected current.candidate
          (outputConeRecords current.candidate) position) = position :=
  coneOrigin_position current position

example {inputs outputs : Nat} (current : Implementation inputs outputs)
    (gate : Fin current.gateCount) :
    (∃ position, coneOrigin current position = gate) ↔
      TerminalPrimitiveRecord.gate gate ∈ outputConeRecords current.candidate :=
  coneOrigin_image current gate

example {inputs outputs : Nat} (pass : PhysicalNormalizationPass)
    (current : Implementation inputs outputs) : Function.Injective (passOrigin pass current) :=
  passOrigin_injective pass current

example {inputs outputs : Nat} {current final : Implementation inputs outputs}
    (trace : PhysicalNormalizationTrace current final) : Function.Injective (traceOrigin trace) :=
  traceOrigin_injective trace

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    Function.Injective (normalizedOrigin current) := normalizedOrigin_injective current

-- Constant removal, duplicate sharing and dead-gate pruning interact in one run.
def combinedProgram : Program 2 5 :=
  .snoc
    (.snoc
      (.snoc
        (.snoc (.snoc .empty ⟨.input fin2Zero, .input fin2One⟩)
          ⟨.input fin2One, .input fin2Zero⟩)
        ⟨.constant false, .constant true⟩)
      ⟨.gate ⟨1, by decide⟩, .constant true⟩)
    ⟨.input fin2Zero, .input fin2Zero⟩

def combined : Implementation 2 1 :=
  ⟨5, Candidate.ofDirectWireWord combinedProgram ⟨fun _ => .gate ⟨3, by decide⟩⟩⟩

-- Execute the well-founded run for this finite fixture. The arbitrary-run
-- provenance theorem above is kernel checked independently of this runtime test.
private def observedPasses {inputs outputs : Nat}
    {current final : Implementation inputs outputs} :
    PhysicalNormalizationTrace current final → List PhysicalNormalizationPass
  | .done _ _ => []
  | .step gain tail => gain.pass :: observedPasses tail

#eval show IO Unit from do
  let execution := runPhysicalNormalization combined
  unless execution.result.gateCount == 2 do
    throw (IO.userError "combined normalization retained an unexpected gate count")
  unless decide (observedPasses execution.trace = [.constants, .sharing, .pruning]) do
    throw (IO.userError "combined normalization did not exercise all three passes in order")
  let origins := (allFin execution.result.gateCount).map fun position =>
    (traceOrigin execution.trace position).val
  unless origins == [0, 3] do
    throw (IO.userError "combined normalization returned incorrect original gate positions")

#print axioms coneOrigin_selected
#print axioms coneOrigin_position
#print axioms coneOrigin_injective
#print axioms coneOrigin_image
#print axioms passOrigin_injective
#print axioms traceOrigin_injective
#print axioms normalizedOrigin_injective

#print axioms constantOrigins_length
#print axioms constantOrigins_nodup
#print axioms sharingOrigins_length
#print axioms sharingOrigins_nodup

-- The full original physical domain is partitioned, not merely counted.
example {inputs outputs : Nat} (pass : PhysicalNormalizationPass)
    (current : Implementation inputs outputs) :
    (passRetained pass current ++ passRemoved pass current).Nodup ∧
      (passRetained pass current ++ passRemoved pass current).Perm
        (allFin current.gateCount) :=
  (pass_partition pass current).2.2

example {inputs outputs : Nat} {current final : Implementation inputs outputs}
    (trace : PhysicalNormalizationTrace current final) :
    (traceRemoved trace).length = trace.savedGates :=
  (trace_partition trace).2.1

example {inputs outputs : Nat} (current : Implementation inputs outputs)
    (gate : Fin current.gateCount) :
    gate ∈ normalizedRemoved current ↔
      ¬ ∃ position, normalizedOrigin current position = gate :=
  normalizedRemoved_iff current gate

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    (normalizedRetained current ++ normalizedRemoved current).Perm
      (allFin current.gateCount) := (normalized_partition current).2.2.2

def noGates : Implementation 0 0 :=
  ⟨0, Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩⟩

-- Empty inputs, all-removed constants, shared representatives, and cone deletion.
example : (passRetained .constants noGates).map Fin.val = [] := by decide
example : (passRemoved .pruning noGates).map Fin.val = [] := by decide
example : (passRemoved .constants
    (⟨2, Candidate.ofDirectWireWord bothConstants ⟨Fin.elim0⟩⟩ : Implementation 0 0)).map
      Fin.val = [0, 1] := by decide
example : (passRetained .sharing (⟨3, sparseCandidate⟩ : Implementation 2 1)).map Fin.val =
    [0, 2] := by decide
example : (passRemoved .sharing (⟨3, sparseCandidate⟩ : Implementation 2 1)).map Fin.val =
    [1] := by decide
example : (passRemoved .pruning combined).map Fin.val = [0, 2, 4] := by decide

#eval show IO Unit from do
  let live := (normalizedRetained combined).map Fin.val
  let removed := (normalizedRemoved combined).map Fin.val
  unless live == [0, 3] && removed == [1, 2, 4] do
    throw (IO.userError "complete normalization lost or duplicated source gate identities")
  unless (normalizedRemoved noGates).isEmpty do
    throw (IO.userError "empty normalization invented a removed gate")

#print axioms passRemoved_iff
#print axioms pass_partition
#print axioms traceRemoved_iff
#print axioms trace_partition
#print axioms normalizedRemoved_iff
#print axioms normalized_partition

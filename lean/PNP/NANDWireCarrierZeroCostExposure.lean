/-
Copyright (c) 2026 PNP Labs.

Connect source-derived zero-cost recognition to the actual computational carrier.
The checker reads the carrier's literal field wires. An accepted exposure preserves
the minimum over every realization, not just the size of the current program.

This closes only the input/constant/old-output alias branch. It does not classify
all semantically free fields, route refused fields to Package E, construct a full
profile, or prove a positive-cost transparency or global saturation theorem.
-/

import PNP.NANDZeroCostExposure
import PNP.NANDWireCarrier

namespace PNP.DirectWire.WireCarrier

variable {inputs outputs fields : Nat}

private theorem recognized_exposed_equivalent
    (carrier : WireCarrier inputs outputs fields)
    (receipt : ZeroCostExposure.LayoutRecognition carrier.implementation carrier.source) :
    Equivalent carrier.exposed.candidate.program carrier.exposed.candidate.directWireWord
      (ZeroCostExposure.extend carrier.implementation receipt.layout).candidate.program
      (ZeroCostExposure.extend carrier.implementation receipt.layout).candidate.directWireWord := by
  intro valuation coordinate
  change carrier.exposed.candidate.semantics valuation coordinate =
    (ZeroCostExposure.extend carrier.implementation receipt.layout).candidate.semantics
      valuation coordinate
  rcases finSum_decompose coordinate with ⟨output, rfl⟩ | ⟨field, rfl⟩
  · rw [exposed_output, ZeroCostExposure.extend_original]
  · rw [exposed_field, ZeroCostExposure.extend_field]
    unfold fieldValue
    rw [← receipt.source_eq field]
    exact ZeroCostExposure.Reference.toSource_eval
      (receipt.layout field) carrier.implementation valuation

/-- For every carrier accepted by the source-derived Boolean checker, exposing
its actual ordered field tuple preserves the semantic minimum. No observer,
minimum, route or correctness certificate is supplied to the checker. -/
theorem exposed_referenceMinimum_of_checkLayout
    (carrier : WireCarrier inputs outputs fields)
    (checked : ZeroCostExposure.checkLayout carrier.implementation carrier.source = true) :
    referenceMinimum carrier.exposed = referenceMinimum carrier.implementation := by
  obtain ⟨receipt, _⟩ :=
    (ZeroCostExposure.compileLayout_success_iff carrier.implementation carrier.source).2 checked
  exact (referenceMinimum_invariant carrier.exposed
    (ZeroCostExposure.extend carrier.implementation receipt.layout)
    (recognized_exposed_equivalent carrier receipt)).trans
      (ZeroCostExposure.referenceMinimum_extend carrier.implementation receipt.layout)

theorem exposed_residualSlack_of_checkLayout
    (carrier : WireCarrier inputs outputs fields)
    (checked : ZeroCostExposure.checkLayout carrier.implementation carrier.source = true) :
    residualSlack carrier.exposed = residualSlack carrier.implementation := by
  unfold residualSlack
  rw [exposed_gateCount, exposed_referenceMinimum_of_checkLayout carrier checked]

/-- The final concrete exposure contract: the actual gate count, minimum and
residual slack all agree, with admission decided from actual source wires. -/
theorem checked_exposure_preserves_problem
    (carrier : WireCarrier inputs outputs fields) :
    ZeroCostExposure.checkLayout carrier.implementation carrier.source = true →
      carrier.exposed.gateCount = carrier.implementation.gateCount ∧
      referenceMinimum carrier.exposed = referenceMinimum carrier.implementation ∧
      residualSlack carrier.exposed = residualSlack carrier.implementation := by
  intro checked
  exact ⟨carrier.exposed_gateCount,
    carrier.exposed_referenceMinimum_of_checkLayout checked,
    carrier.exposed_residualSlack_of_checkLayout checked⟩

end PNP.DirectWire.WireCarrier

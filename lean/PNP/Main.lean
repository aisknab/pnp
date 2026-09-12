namespace PNP.Main

/-- Machine-readable publication status. This is data, not a P = NP theorem. -/
structure RootTheoremStatus where
  phase : String
  standardStatementFormalized : Bool
  unconditionalProofPresent : Bool
  externalAssumptionsRemain : Bool
  publicTheoremReleased : Bool
  blockers : List String
  deriving Repr, DecidableEq

/-- The conservative root status for the active formal reconstruction. -/
def rootTheoremStatus : RootTheoremStatus :=
  { phase := "formal-reconstruction-in-progress"
    standardStatementFormalized := true
    unconditionalProofPresent := false
    externalAssumptionsRemain := true
    publicTheoremReleased := false
    blockers := [
      "Concrete deterministic CNFSAT decider",
      "Complete residual-band exact-minimization algorithm",
      "Unconditional SaturatePositive, BCELReady and ZeroSlack",
      "Polynomial runtime, output-size and certificate-size bounds",
      "Eligible root theorem, exact type/fingerprints and publication audit"
    ] }

theorem rootTheoremStatus_not_released :
    rootTheoremStatus.publicTheoremReleased = false := rfl

theorem rootTheoremStatus_has_external_assumptions :
    rootTheoremStatus.externalAssumptionsRemain = true := rfl

end PNP.Main

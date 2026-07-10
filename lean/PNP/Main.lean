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
      "Complexity pipeline compilation/refinement to raw machine semantics",
      "Executable checker/reflection soundness",
      "PCCMin and ZeroSlack semantic soundness and polynomial bounds",
      "Residual-band reduction",
      "Global SAT-to-locked-NAND construction and threshold theorem",
      "SAT NP-hardness in the concrete model"
    ] }

theorem rootTheoremStatus_not_released :
    rootTheoremStatus.publicTheoremReleased = false := rfl

theorem rootTheoremStatus_has_external_assumptions :
    rootTheoremStatus.externalAssumptionsRemain = true := rfl

end PNP.Main

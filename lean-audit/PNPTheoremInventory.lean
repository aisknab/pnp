import Lean
import PNP

open Lean Elab Command

namespace PNP.TheoremInventory

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def kernelType (info : ConstantInfo) : String :=
  toString (repr info.type)

private def kernelValue? : ConstantInfo → Option String
  | .defnInfo value => some (toString (repr value.value))
  | .opaqueInfo value => some (toString (repr value.value))
  | _ => none

private def jsonNames (names : Array Name) : Json :=
  Json.arr (names.map fun name => toJson name.toString)

private structure InventoryRow where
  name : Name
  moduleName : Name
  info : ConstantInfo
  axioms : Array Name

private def InventoryRow.asJson (row : InventoryRow) : Json :=
  Json.mkObj [
    ("name", toJson row.name.toString),
    ("module", toJson row.moduleName.toString),
    ("kind", toJson (declarationKind row.info)),
    ("axioms", jsonNames row.axioms)
  ]

private def InventoryRow.asDetailedJson (row : InventoryRow) : Json :=
  Json.mkObj [
    ("name", toJson row.name.toString),
    ("module", toJson row.moduleName.toString),
    ("kind", toJson (declarationKind row.info)),
    ("kernelType", toJson (kernelType row.info)),
    ("kernelValue", toJson (kernelValue? row.info)),
    ("axioms", jsonNames row.axioms)
  ]

private def moduleFor (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some moduleIndex => env.header.moduleNames[moduleIndex]!
  | none => env.mainModule

private def isProjectModuleDeclaration (env : Environment) (name : Name) : Bool :=
  (`PNP).isPrefixOf (moduleFor env name)

private def isProjectDeclaration (env : Environment) (name : Name) : Bool :=
  !isPrivateName name && (`PNP).isPrefixOf name &&
    isProjectModuleDeclaration env name

private def reviewedMilestoneTheoremNames : Array Name := #[
  `PNP.Concrete.BitString.decodePair_pair,
  `PNP.Concrete.NatPolynomial.eval_mono,
  `PNP.Concrete.PolynomialTimeMachine.verdict_accepts_iff,
  `PNP.Concrete.PolynomialTimeMachine.verdict_ne_timeout,
  `PNP.Concrete.run_succ,
  `PNP.Concrete.run_zero,
  `PNP.DirectWire.ConditionalThresholdBoundaryPremises.fullResidualSlack_le_four,
  `PNP.DirectWire.ConditionalThresholdBoundaryPremises.satisfiable_iff_minimum_ge_succ,
  `PNP.DirectWire.Equivalent.trans,
  `PNP.DirectWire.StrictEquivalentGain.strictResidualDescent,
  `PNP.DirectWire.andCircuit_spec,
  `PNP.DirectWire.compatibleReplacement_framed,
  `PNP.DirectWire.constantOneDirect_referenceMinimum,
  `PNP.DirectWire.constantZeroDirect_referenceMinimum,
  `PNP.DirectWire.equalityDirect_referenceMinimum,
  `PNP.DirectWire.equivalentBool_eq_true_iff,
  `PNP.DirectWire.exactWidthEnumeration_complete,
  `PNP.DirectWire.firstListedGain_sound,
  `PNP.DirectWire.firstListedGain_none_no_listed_gain,
  `PNP.DirectWire.framedGlobalSlackLaw,
  `PNP.DirectWire.lockedBaselineCount_report_formula,
  `PNP.DirectWire.nandCircuit_spec,
  `PNP.DirectWire.prefixAndDirect_referenceMinimum,
  `PNP.DirectWire.referenceMinimum_invariant,
  `PNP.DirectWire.residualSlack_eq_zero_iff_minimum,
  `PNP.DirectWire.strictEquivalentGainBool_complete,
  `PNP.DirectWire.traceDirect_referenceMinimum,
  `PNP.DirectWire.unresolved_positiveSlack_regression
]

private def inventory : CommandElabM Json := do
  let env ← getEnv
  let allDeclarationNames := env.constants.fold
    (init := #[])
    (fun names name _ => names.push name)
  let excludedPrivateDeclarationCount :=
    (allDeclarationNames.filter fun name =>
      isPrivateName name && isProjectModuleDeclaration env name).size
  let declarationNames := env.constants.fold
    (init := #[])
    (fun names name _ =>
      if isProjectDeclaration env name then names.push name else names)
  let declarationNames := declarationNames.qsort fun left right =>
    left.toString < right.toString
  let mut rows : Array InventoryRow := #[]
  for name in declarationNames do
    let some info := env.find? name
      | throwError "compiled declaration disappeared from the environment: {name}"
    let axioms ← collectAxioms name
    let axioms := axioms.qsort fun left right =>
      left.toString < right.toString
    rows := rows.push { name, moduleName := moduleFor env name, info, axioms }
  let theoremRows := rows.filter fun row => declarationKind row.info == "theorem"
  let axiomRows := rows.filter fun row => declarationKind row.info == "axiom"
  let constructorRows := rows.filter fun row => declarationKind row.info == "constructor"
  let definitionRows := rows.filter fun row => declarationKind row.info == "definition"
  let inductiveRows := rows.filter fun row => declarationKind row.info == "inductive"
  let opaqueRows := rows.filter fun row => declarationKind row.info == "opaque"
  let quotientRows := rows.filter fun row => declarationKind row.info == "quotient"
  let recursorRows := rows.filter fun row => declarationKind row.info == "recursor"
  let assumptionFreeTheoremCount :=
    (theoremRows.filter fun row => row.axioms.isEmpty).size
  let mut sourceClosureModules : Array Name := #[]
  for row in rows do
    unless sourceClosureModules.contains row.moduleName do
      sourceClosureModules := sourceClosureModules.push row.moduleName
  sourceClosureModules := sourceClosureModules.qsort fun left right =>
    left.toString < right.toString
  let compatibilityRootName := `PNP.Main.p_eq_np
  let concreteTargetName := `PNP.Main.ConcretePEqualsNP
  let compatibilityRootCandidate :=
    rows.find? (fun row => row.name == compatibilityRootName)
  let concreteTargetCandidate :=
    rows.find? (fun row => row.name == concreteTargetName)
  let milestoneTheoremNames := reviewedMilestoneTheoremNames.qsort fun left right =>
    left.toString < right.toString
  let mut milestoneCandidates : Array InventoryRow := #[]
  for name in milestoneTheoremNames do
    let some row := rows.find? (fun row => row.name == name)
      | throwError "reviewed milestone theorem is absent from the compiled environment: {name}"
    unless declarationKind row.info == "theorem" do
      throwError "reviewed milestone declaration is not a theorem: {name}"
    milestoneCandidates := milestoneCandidates.push row
  return Json.mkObj [
    ("kind", toJson "PNPLeanTheoremInventory0"),
    ("version", toJson 0),
    ("coordinate", toJson "PNP-LEAN-THEOREM-INVENTORY-2026-07-10-11"),
    ("leanToolchain", toJson "leanprover/lean4:v4.31.0"),
    ("rootModule", toJson "PNP"),
    ("environmentProbeComplete", toJson true),
    ("declarationCount", toJson rows.size),
    ("excludedPrivateDeclarationCount", toJson excludedPrivateDeclarationCount),
    ("theoremCount", toJson theoremRows.size),
    ("assumptionFreeTheoremCount", toJson assumptionFreeTheoremCount),
    ("axiomCount", toJson axiomRows.size),
    ("declarationKindCounts", Json.mkObj [
      ("axiom", toJson axiomRows.size),
      ("constructor", toJson constructorRows.size),
      ("definition", toJson definitionRows.size),
      ("inductive", toJson inductiveRows.size),
      ("opaque", toJson opaqueRows.size),
      ("quotient", toJson quotientRows.size),
      ("recursor", toJson recursorRows.size),
      ("theorem", toJson theoremRows.size)
    ]),
    ("sourceClosureModuleCount", toJson sourceClosureModules.size),
    ("sourceClosureModules", Json.arr (sourceClosureModules.map fun name => toJson name.toString)),
    ("projectAxioms", Json.arr (axiomRows.map fun row => toJson row.name.toString)),
    ("compatibilityRootName", toJson compatibilityRootName.toString),
    ("compatibilityRootCandidate", toJson (compatibilityRootCandidate.map InventoryRow.asDetailedJson)),
    ("concreteTargetName", toJson concreteTargetName.toString),
    ("concreteTargetCandidate", toJson (concreteTargetCandidate.map InventoryRow.asDetailedJson)),
    ("milestoneCandidates", Json.arr (milestoneCandidates.map InventoryRow.asDetailedJson)),
    ("declarations", Json.arr (rows.map InventoryRow.asJson))
  ]

run_cmd do
  let output ← inventory
  liftIO <| IO.println output.compress

end PNP.TheoremInventory

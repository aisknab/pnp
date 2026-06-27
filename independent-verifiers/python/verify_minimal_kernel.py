#!/usr/bin/env python3
"""Independent Python verifier for the PNP minimal-kernel coordinate.

This verifier deliberately avoids importing the JavaScript checker implementation.
It consumes repository JSON artifacts as data and checks the public-review boundary
and minimal-kernel spine invariants from a second runtime.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

CHECKER = "independent-python-minimal-kernel0"
VERSION = 0

KERNEL_PATH = Path("kernel/PNP_MINIMAL_KERNEL.json")
REPORT_BINDINGS_PATH = Path("report-bindings/REPORT_THEOREM_BINDINGS.json")
KERNEL_COORDINATE = "PNP-MINIMAL-KERNEL-2026-06-27-01"
REPORT_BINDINGS_COORDINATE = "REPORT-THEOREM-BINDINGS-2026-06-27-01"

REMAINING_BLOCKERS = [
    "Release.UnrestrictedFinalSoundness",
    "ExternalReview.Acceptance",
]

QUARANTINED_FINAL_NODE_IDS = [
    "Final.PackageSoundness",
    "Final.GeneratedPackageSufficiency",
    "Final.AcceptedPackageImpliesSATinP",
    "Final.AcceptedPackageImpliesPEqualsNP",
]

PRIMITIVE_RULES = [
    "Eq",
    "Subst",
    "Record",
    "DAGInd",
    "LedgerInd",
    "OblTopoInd",
    "TraceInd",
    "FiniteExhaust",
    "DPInd",
    "Hall",
    "RankInd",
    "MinCounterexample",
    "IntArith",
    "Transport",
    "TruthVec",
    "FiniteRel",
]

SIGMA_THEOREMS = ["V53", "V54"]

REQUIRED_CHECKER_IDS = [
    "CheckVerifierFrag0",
    "CheckKImpl0",
    "CheckGlobalProofDAG0",
    "CheckGPack0",
    "CheckFinalFrameworkMatch0",
    "CheckSATDecision0",
    "CheckSATBounds0",
    "CheckPCCPackexp0",
    "CheckFinalPNPProofReport0",
    "CheckSuccessorPublicReviewReportSeal0",
    "audit-report-theorem-bindings0",
]

REQUIRED_SPINE_IDS = [
    "spine.kernel-rules",
    "spine.direct-wire-semantics",
    "spine.residual-band-minimization",
    "spine.locked-nand-sat-threshold",
    "spine.complexity-implication",
    "spine.package-acceptance",
    "spine.report-and-release-boundary",
]

REQUIRED_PACKAGE_THEOREM_IDS = [
    "E.VerifyDWSoundness",
    "N.TraceableNormalization",
    "Splice.BoundedAndComposed",
    "FT.FiniteTableCoverage",
    "X.CriticalWindowRouting",
    "BC.BranchCycleRouting",
    "UN.UnaryDecoderRouting",
    "HN.LeafTightness",
    "HResolve.GlobalHereditaryResolver",
    "BUD.BudgetResolver",
    "NORFF.FrontierFaithfulComparison",
    "RW.BCELReady",
    "BN2.SideTightCoherentOptimum",
    "BN3.SimultaneousEnvelope",
    "BN4.ActivationExact",
    "BN5.FullShadowLocalization",
    "PkgC.SeparatingConsumers",
    "BN6.HypergraphPacket",
    "Packet.SelectorSeeds",
    "R.SelectorRealization",
    "HB.NegativeClosure",
    "O.ZeroSlackOracle",
    "G.LockedNANDThreshold",
    "Final.FrameworkMatch",
    "PACK.PackageSufficiency",
]

EXPECTED_ENTRYPOINTS = {
    "kernelJson": "kernel/PNP_MINIMAL_KERNEL.json",
    "checker": "pcc-minimal-kernel0.mjs",
    "tests": "test/pcc-minimal-kernel0.test.mjs",
    "theoremBindingLedger": "report-bindings/REPORT_THEOREM_BINDINGS.json",
    "successorReportSeal": "successor-report-seals/PNP-REPORT-SEAL-2026-06-27-01/SEAL.json",
}

ACTIVATION_FIELDS = {
    "publicTheoremEmissionAllowed",
    "activatesPublicTheorem",
    "dischargesPublicTheorem",
}


@dataclass(frozen=True)
class Failure:
    coord: str
    path: list[Any]
    reason: str
    witness: dict[str, Any] | None = None

    def to_json(self) -> dict[str, Any]:
        return {
            "coord": self.coord,
            "path": self.path,
            "reason": self.reason,
            "witness": self.witness or {},
        }


class VerifyError(Exception):
    """Internal exception used only to turn validation failures into reject JSON."""

    def __init__(self, failure: Failure):
        super().__init__(failure.reason)
        self.failure = failure


def reject(coord: str, path: Iterable[Any], reason: str, witness: dict[str, Any] | None = None) -> None:
    raise VerifyError(Failure(coord=coord, path=list(path), reason=reason, witness=witness))


def read_json_with_digest(root: Path, relative_path: Path) -> tuple[Any, str]:
    path = root / relative_path
    try:
        data = path.read_bytes()
    except OSError as exc:
        reject("file.read", [str(relative_path)], "could not read required file", {"error": str(exc)})
    try:
        obj = json.loads(data.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        reject("file.json", [str(relative_path)], "required file is not valid UTF-8 JSON", {"error": str(exc)})
    return obj, hashlib.sha256(data).hexdigest()


def require_object(value: Any, path: list[Any], name: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        reject("shape.object", path, f"{name} must be an object", {"actualType": type(value).__name__})
    return value


def require_array(value: Any, path: list[Any], name: str, *, non_empty: bool = False) -> list[Any]:
    if not isinstance(value, list):
        reject("shape.array", path, f"{name} must be an array", {"actualType": type(value).__name__})
    if non_empty and not value:
        reject("shape.array.empty", path, f"{name} must not be empty")
    return value


def require_string_array(value: Any, path: list[Any], name: str, *, non_empty: bool = False) -> list[str]:
    arr = require_array(value, path, name, non_empty=non_empty)
    for index, item in enumerate(arr):
        if not isinstance(item, str) or not item:
            reject("shape.string-array", [*path, index], f"{name} must contain only non-empty strings")
    return arr


def require_equal(actual: Any, expected: Any, path: list[Any], reason: str) -> None:
    if actual != expected:
        reject("value.mismatch", path, reason, {"expected": expected, "actual": actual})


def require_same_list(actual: Any, expected: list[str], path: list[Any], reason: str) -> None:
    if actual != expected:
        reject("value.list-mismatch", path, reason, {"expected": expected, "actual": actual})


def require_unique_strings(values: list[str], path: list[Any], name: str) -> None:
    seen: set[str] = set()
    for index, value in enumerate(values):
        if value in seen:
            reject("value.duplicate", [*path, index], f"{name} contains a duplicate entry", {"entry": value})
        seen.add(value)


def verify_claim_boundary(boundary: Any, path: list[Any]) -> None:
    boundary_obj = require_object(boundary, path, "claim boundary")
    require_equal(boundary_obj.get("publicTheoremEmissionAllowed"), False, [*path, "publicTheoremEmissionAllowed"], "public theorem emission must remain disabled")
    require_equal(boundary_obj.get("finalTheoremReady"), False, [*path, "finalTheoremReady"], "final theorem readiness must remain disabled")
    require_same_list(boundary_obj.get("activeFinalNodeIds"), [], [*path, "activeFinalNodeIds"], "active final node ids must remain empty")
    require_same_list(boundary_obj.get("remainingBlockers"), REMAINING_BLOCKERS, [*path, "remainingBlockers"], "remaining blockers must remain exact")

    if "quarantinedFinalNodeIds" in boundary_obj:
        require_same_list(
            boundary_obj.get("quarantinedFinalNodeIds"),
            QUARANTINED_FINAL_NODE_IDS,
            [*path, "quarantinedFinalNodeIds"],
            "quarantined final node ids must remain exact",
        )


def verify_kernel(kernel: Any, root: Path) -> dict[str, Any]:
    kernel_obj = require_object(kernel, [], "minimal kernel")
    require_equal(kernel_obj.get("kind"), "PNPMinimalKernel0", ["kind"], "minimal kernel kind mismatch")
    require_equal(kernel_obj.get("version"), VERSION, ["version"], "minimal kernel version mismatch")
    require_equal(kernel_obj.get("coordinate"), KERNEL_COORDINATE, ["coordinate"], "minimal kernel coordinate mismatch")
    require_equal(kernel_obj.get("status"), "minimal-kernel-coordinate-ready", ["status"], "minimal kernel status mismatch")
    verify_claim_boundary(kernel_obj.get("claimBoundary"), ["claimBoundary"])

    entrypoints = require_object(kernel_obj.get("entrypoints"), ["entrypoints"], "entrypoints")
    require_equal(entrypoints, EXPECTED_ENTRYPOINTS, ["entrypoints"], "entrypoints must match the minimal-kernel coordinate")

    proof_kernel = require_object(kernel_obj.get("proofKernel"), ["proofKernel"], "proof kernel")
    require_equal(proof_kernel.get("primitiveRuleSource"), "pcc-kimpl0.mjs#KERNEL_RULES0", ["proofKernel", "primitiveRuleSource"], "primitive rule source mismatch")
    require_same_list(proof_kernel.get("primitiveRules"), PRIMITIVE_RULES, ["proofKernel", "primitiveRules"], "primitive rule list mismatch")
    require_equal(proof_kernel.get("sigmaSource"), "pcc-kimpl0.mjs#SIGMA_REQUIRED_THEOREMS0", ["proofKernel", "sigmaSource"], "Sigma source mismatch")
    require_same_list(proof_kernel.get("sigmaTheorems"), SIGMA_THEOREMS, ["proofKernel", "sigmaTheorems"], "Sigma theorem list mismatch")
    require_same_list(proof_kernel.get("quarantinedFinalNodeIds"), QUARANTINED_FINAL_NODE_IDS, ["proofKernel", "quarantinedFinalNodeIds"], "quarantined final node id list mismatch")
    require_same_list(proof_kernel.get("requiredPackageTheoremIds"), REQUIRED_PACKAGE_THEOREM_IDS, ["proofKernel", "requiredPackageTheoremIds"], "required package theorem id list mismatch")

    checker_surface = require_array(kernel_obj.get("checkerSurface"), ["checkerSurface"], "checker surface", non_empty=True)
    checker_ids: list[str] = []
    checker_files: list[str] = []
    for index, entry in enumerate(checker_surface):
        entry_obj = require_object(entry, ["checkerSurface", index], "checker surface entry")
        checker_id = entry_obj.get("id")
        checker_file = entry_obj.get("file")
        if not isinstance(checker_id, str) or not checker_id:
            reject("shape.checker-id", ["checkerSurface", index, "id"], "checker id must be a non-empty string")
        if not isinstance(checker_file, str) or not checker_file:
            reject("shape.checker-file", ["checkerSurface", index, "file"], "checker file must be a non-empty string")
        checker_ids.append(checker_id)
        checker_files.append(checker_file)
        if not (root / checker_file).is_file():
            reject("file.missing", ["checkerSurface", index, "file"], "declared checker file does not exist", {"file": checker_file})
    require_unique_strings(checker_ids, ["checkerSurface"], "checker surface")
    require_same_list(checker_ids, REQUIRED_CHECKER_IDS, ["checkerSurface"], "checker surface id list mismatch")

    predecessors = require_array(kernel_obj.get("predecessors"), ["predecessors"], "predecessors", non_empty=True)
    predecessor_ids = []
    for index, predecessor in enumerate(predecessors):
        pred_obj = require_object(predecessor, ["predecessors", index], "predecessor")
        predecessor_ids.append(pred_obj.get("id"))
        require_equal(pred_obj.get("ready"), True, ["predecessors", index, "ready"], "predecessor must be marked ready")
        require_equal(pred_obj.get("activatesPublicTheorem"), False, ["predecessors", index, "activatesPublicTheorem"], "predecessor cannot activate public theorem emission")
    for required_id in [REPORT_BINDINGS_COORDINATE, "PNP-REPORT-SEAL-2026-06-27-01", "GLOBAL-PROOF-DAG0"]:
        if required_id not in predecessor_ids:
            reject("value.predecessor-missing", ["predecessors"], "required predecessor is missing", {"requiredId": required_id})

    proof_spine = require_array(kernel_obj.get("proofSpine"), ["proofSpine"], "proof spine", non_empty=True)
    proof_spine_ids: list[str] = []
    primitive_rule_set = set(PRIMITIVE_RULES)
    checker_id_set = set(checker_ids)
    known_theorem_ids = set(REQUIRED_PACKAGE_THEOREM_IDS) | set(QUARANTINED_FINAL_NODE_IDS)
    referenced_report_binding_ids: set[str] = set()

    for index, stage in enumerate(proof_spine):
        stage_obj = require_object(stage, ["proofSpine", index], "proof-spine stage")
        stage_id = stage_obj.get("id")
        if not isinstance(stage_id, str) or not stage_id:
            reject("shape.spine-id", ["proofSpine", index, "id"], "proof-spine stage id must be a non-empty string")
        proof_spine_ids.append(stage_id)
        for rule in require_string_array(stage_obj.get("ruleFamilies"), ["proofSpine", index, "ruleFamilies"], "rule families", non_empty=True):
            if rule not in primitive_rule_set:
                reject("value.unknown-rule", ["proofSpine", index, "ruleFamilies"], "proof-spine rule family is not in primitive rule table", {"rule": rule})
        for checker_id in require_string_array(stage_obj.get("checkerIds"), ["proofSpine", index, "checkerIds"], "checker ids", non_empty=True):
            if checker_id not in checker_id_set:
                reject("value.unknown-checker", ["proofSpine", index, "checkerIds"], "proof-spine checker id is not declared in checker surface", {"checkerId": checker_id})
        for theorem_id in require_string_array(stage_obj.get("packageTheoremIds"), ["proofSpine", index, "packageTheoremIds"], "package theorem ids"):
            if theorem_id not in known_theorem_ids:
                reject("value.unknown-theorem", ["proofSpine", index, "packageTheoremIds"], "proof-spine package theorem id is unknown", {"theoremId": theorem_id})
        for binding_id in require_string_array(stage_obj.get("reportBindingIds"), ["proofSpine", index, "reportBindingIds"], "report binding ids", non_empty=True):
            referenced_report_binding_ids.add(binding_id)

    require_unique_strings(proof_spine_ids, ["proofSpine"], "proof spine")
    require_same_list(proof_spine_ids, REQUIRED_SPINE_IDS, ["proofSpine"], "proof-spine id list mismatch")

    quarantined = require_array(kernel_obj.get("quarantinedConclusions"), ["quarantinedConclusions"], "quarantined conclusions")
    if len(quarantined) != len(QUARANTINED_FINAL_NODE_IDS):
        reject("value.quarantine-count", ["quarantinedConclusions"], "quarantined conclusion count mismatch")
    for index, entry in enumerate(quarantined):
        entry_obj = require_object(entry, ["quarantinedConclusions", index], "quarantined conclusion")
        require_equal(entry_obj.get("id"), QUARANTINED_FINAL_NODE_IDS[index], ["quarantinedConclusions", index, "id"], "quarantined conclusion id mismatch")
        require_equal(entry_obj.get("notActive"), True, ["quarantinedConclusions", index, "notActive"], "quarantined conclusion must remain inactive")
        require_equal(entry_obj.get("publicTheoremEmissionAllowed"), False, ["quarantinedConclusions", index, "publicTheoremEmissionAllowed"], "quarantined conclusion cannot allow public theorem emission")

    scan_for_forbidden_activation(kernel_obj, [])

    return {
        "checkerIds": checker_ids,
        "checkerFiles": checker_files,
        "proofSpineIds": proof_spine_ids,
        "referencedReportBindingIds": sorted(referenced_report_binding_ids),
    }


def verify_report_bindings(ledger: Any, required_binding_ids: set[str]) -> None:
    ledger_obj = require_object(ledger, [], "theorem-binding ledger")
    require_equal(ledger_obj.get("kind"), "PNPReportTheoremBindings0", ["kind"], "theorem-binding ledger kind mismatch")
    require_equal(ledger_obj.get("version"), VERSION, ["version"], "theorem-binding ledger version mismatch")
    require_equal(ledger_obj.get("coordinate"), REPORT_BINDINGS_COORDINATE, ["coordinate"], "theorem-binding ledger coordinate mismatch")
    verify_claim_boundary(ledger_obj.get("claimBoundary"), ["claimBoundary"])

    theorem_bindings = require_array(ledger_obj.get("theoremBindings"), ["theoremBindings"], "theorem bindings", non_empty=True)
    actual_ids: set[str] = set()
    for index, binding in enumerate(theorem_bindings):
        binding_obj = require_object(binding, ["theoremBindings", index], "theorem binding")
        binding_id = binding_obj.get("id")
        if not isinstance(binding_id, str) or not binding_id:
            reject("shape.binding-id", ["theoremBindings", index, "id"], "theorem binding id must be a non-empty string")
        if binding_id in actual_ids:
            reject("value.duplicate", ["theoremBindings", index, "id"], "theorem binding ids must be unique", {"id": binding_id})
        actual_ids.add(binding_id)
        require_equal(binding_obj.get("claimEffect"), "audit-ledger-only", ["theoremBindings", index, "claimEffect"], "theorem binding claim effect must remain audit-ledger-only")
        require_equal(binding_obj.get("publicEmissionEffect"), "none", ["theoremBindings", index, "publicEmissionEffect"], "theorem binding public emission effect must remain none")
        require_equal(binding_obj.get("dischargesPublicTheorem"), False, ["theoremBindings", index, "dischargesPublicTheorem"], "theorem binding cannot discharge public theorem emission")

    missing = sorted(required_binding_ids - actual_ids)
    if missing:
        reject("value.binding-missing", ["theoremBindings"], "proof spine references report-binding ids absent from the ledger", {"missing": missing})

    scan_for_forbidden_activation(ledger_obj, [])


def scan_for_forbidden_activation(value: Any, path: list[Any]) -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            child_path = [*path, key]
            if key in ACTIVATION_FIELDS and child is not False:
                reject("value.activation-forbidden", child_path, "activation fields must be false in this verifier", {"actual": child})
            if key == "finalTheoremReady" and child is not False:
                reject("value.final-ready-forbidden", child_path, "final theorem readiness must be false", {"actual": child})
            if key == "activeFinalNodeIds" and child != []:
                reject("value.active-final-nodes-forbidden", child_path, "active final node ids must remain empty", {"actual": child})
            scan_for_forbidden_activation(child, child_path)
    elif isinstance(value, list):
        for index, child in enumerate(value):
            scan_for_forbidden_activation(child, [*path, index])


def verify_documents(kernel: Any, report_bindings: Any, root: Path) -> dict[str, Any]:
    kernel_summary = verify_kernel(kernel, root)
    verify_report_bindings(report_bindings, set(kernel_summary["referencedReportBindingIds"]))
    return kernel_summary


def verify_repo(root: Path) -> dict[str, Any]:
    kernel, kernel_sha256 = read_json_with_digest(root, KERNEL_PATH)
    report_bindings, report_bindings_sha256 = read_json_with_digest(root, REPORT_BINDINGS_PATH)
    kernel_summary = verify_documents(kernel, report_bindings, root)

    return {
        "tag": "accept",
        "kind": "accept",
        "checker": CHECKER,
        "version": VERSION,
        "claimStatus": "minimal-kernel-independent-python-accepted",
        "coordinate": KERNEL_COORDINATE,
        "kernelPath": str(KERNEL_PATH),
        "kernelSha256": kernel_sha256,
        "reportBindingsPath": str(REPORT_BINDINGS_PATH),
        "reportBindingsSha256": report_bindings_sha256,
        "checkerSurfaceCount": len(kernel_summary["checkerIds"]),
        "proofSpineCount": len(kernel_summary["proofSpineIds"]),
        "reportBindingReferenceCount": len(kernel_summary["referencedReportBindingIds"]),
        "publicTheoremEmissionAllowed": False,
        "finalTheoremReady": False,
        "activeFinalNodeIds": [],
        "quarantinedFinalNodeIds": QUARANTINED_FINAL_NODE_IDS,
        "remainingBlockers": REMAINING_BLOCKERS,
    }


def reject_verdict(failure: Failure) -> dict[str, Any]:
    return {
        "tag": "reject",
        "kind": "reject",
        "checker": CHECKER,
        "version": VERSION,
        "coord": failure.coord,
        "path": failure.path,
        "witness": {
            "reason": failure.reason,
            **(failure.witness or {}),
        },
    }


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Verify the PNP minimal-kernel coordinate using Python only.")
    parser.add_argument("--root", default=".", help="repository root; defaults to current working directory")
    parser.add_argument("--json", action="store_true", help="emit only JSON")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(list(sys.argv[1:] if argv is None else argv))
    root = Path(args.root).resolve()
    try:
        verdict = verify_repo(root)
        print(json.dumps(verdict, indent=2, sort_keys=True))
        return 0
    except VerifyError as exc:
        verdict = reject_verdict(exc.failure)
        stream = sys.stdout if args.json else sys.stderr
        print(json.dumps(verdict, indent=2, sort_keys=True), file=stream)
        return 1
    except Exception as exc:  # Defensive totalization for CLI use.
        failure = Failure(
            coord="python.unhandled-exception",
            path=[],
            reason="unhandled verifier exception",
            witness={"exceptionType": type(exc).__name__, "error": str(exc)},
        )
        stream = sys.stdout if args.json else sys.stderr
        print(json.dumps(reject_verdict(failure), indent=2, sort_keys=True), file=stream)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())

import copy
import unittest
from pathlib import Path

import verify_minimal_kernel as vmk


ROOT = Path(__file__).resolve().parents[2]


def load_documents():
    kernel, _ = vmk.read_json_with_digest(ROOT, vmk.KERNEL_PATH)
    ledger, _ = vmk.read_json_with_digest(ROOT, vmk.REPORT_BINDINGS_PATH)
    return kernel, ledger


class MinimalKernelVerifierTests(unittest.TestCase):
    def test_current_repository_accepts(self):
        verdict = vmk.verify_repo(ROOT)

        self.assertEqual(verdict["tag"], "accept")
        self.assertEqual(verdict["claimStatus"], "minimal-kernel-independent-python-accepted")
        self.assertFalse(verdict["publicTheoremEmissionAllowed"])
        self.assertFalse(verdict["finalTheoremReady"])
        self.assertEqual(verdict["activeFinalNodeIds"], [])
        self.assertEqual(verdict["remainingBlockers"], vmk.REMAINING_BLOCKERS)
        self.assertEqual(verdict["checkerSurfaceCount"], len(vmk.REQUIRED_CHECKER_IDS))
        self.assertEqual(verdict["proofSpineCount"], len(vmk.REQUIRED_SPINE_IDS))
        self.assertEqual(len(verdict["kernelSha256"]), 64)
        self.assertEqual(len(verdict["reportBindingsSha256"]), 64)

    def test_rejects_public_theorem_emission_mutation(self):
        kernel, ledger = load_documents()
        mutated = copy.deepcopy(kernel)
        mutated["claimBoundary"]["publicTheoremEmissionAllowed"] = True

        with self.assertRaises(vmk.VerifyError) as cm:
            vmk.verify_documents(mutated, ledger, ROOT)

        self.assertEqual(cm.exception.failure.coord, "value.mismatch")
        self.assertEqual(cm.exception.failure.path, ["claimBoundary", "publicTheoremEmissionAllowed"])

    def test_rejects_active_final_node_mutation(self):
        kernel, ledger = load_documents()
        mutated = copy.deepcopy(kernel)
        mutated["claimBoundary"]["activeFinalNodeIds"] = ["Final.AcceptedPackageImpliesPEqualsNP"]

        with self.assertRaises(vmk.VerifyError) as cm:
            vmk.verify_documents(mutated, ledger, ROOT)

        self.assertEqual(cm.exception.failure.coord, "value.list-mismatch")
        self.assertEqual(cm.exception.failure.path, ["claimBoundary", "activeFinalNodeIds"])

    def test_rejects_unknown_proof_spine_checker(self):
        kernel, ledger = load_documents()
        mutated = copy.deepcopy(kernel)
        mutated["proofSpine"][0]["checkerIds"] = ["CheckVerifierFrag0", "CheckMissingIndependent0"]

        with self.assertRaises(vmk.VerifyError) as cm:
            vmk.verify_documents(mutated, ledger, ROOT)

        self.assertEqual(cm.exception.failure.coord, "value.unknown-checker")
        self.assertEqual(cm.exception.failure.path, ["proofSpine", 0, "checkerIds"])

    def test_rejects_report_binding_reference_without_ledger_entry(self):
        kernel, ledger = load_documents()
        mutated = copy.deepcopy(kernel)
        mutated["proofSpine"][0]["reportBindingIds"] = ["THM-DOES-NOT-EXIST"]

        with self.assertRaises(vmk.VerifyError) as cm:
            vmk.verify_documents(mutated, ledger, ROOT)

        self.assertEqual(cm.exception.failure.coord, "value.binding-missing")
        self.assertEqual(cm.exception.failure.path, ["theoremBindings"])
        self.assertEqual(cm.exception.failure.witness, {"missing": ["THM-DOES-NOT-EXIST"]})

    def test_rejects_activation_claim_inside_report_binding_ledger(self):
        kernel, ledger = load_documents()
        mutated_ledger = copy.deepcopy(ledger)
        mutated_ledger["theoremBindings"][0]["dischargesPublicTheorem"] = True

        with self.assertRaises(vmk.VerifyError) as cm:
            vmk.verify_documents(kernel, mutated_ledger, ROOT)

        self.assertEqual(cm.exception.failure.coord, "value.mismatch")
        self.assertEqual(cm.exception.failure.path, ["theoremBindings", 0, "dischargesPublicTheorem"])


if __name__ == "__main__":
    unittest.main()

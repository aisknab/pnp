import PNP.Concrete.ResidualReduction.FactoredContraction
import PNP.Concrete.ResidualReduction.SharedRefutationCircuit

/-! Transport shared coefficient circuits through the existing linear chart.
Only affine leaves change. Gate references, output roots and gate count stay
unchanged; no multiplier is expanded into monomials. -/

namespace PNP.Concrete.ResidualReduction.SharedRefutationTransport
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SharedRefutationCircuit

def mapGate {n k : Nat} (f : Affine n → Affine k) : Gate n → Gate k
  | .input a => .input (f a)
  | .xorGate i j => .xorGate i j
  | .andGate i j => .andGate i j

def transport {n k : Nat} (f : Affine n → Affine k) (code : Code n) : Code k :=
  code.map (mapGate f)

theorem transport_length {n k : Nat} (f : Affine n → Affine k) (code : Code n) :
    (transport f code).length = code.length := by
  simp only [transport, List.length_map]

theorem gateEval_map {n k : Nat} (f : Affine n → Affine k)
    (project : Point k → Point n)
    (hf : ∀ a x, aEval (f a) x = aEval a (project x))
    (g : Gate n) (x : Point k) (values : List Bool) :
    gateEval (mapGate f g) x values = gateEval g (project x) values := by
  cases g with
  | input a => exact hf a x
  | xorGate i j => rfl
  | andGate i j => rfl

theorem evaluate_transport {n k : Nat} (f : Affine n → Affine k)
    (project : Point k → Point n)
    (hf : ∀ a x, aEval (f a) x = aEval a (project x))
    (code : Code n) (x : Point k) :
    evaluate (transport f code) x = evaluate code (project x) := by
  induction code with
  | nil => rfl
  | cons g code ih =>
    change evaluate (transport f code) x ++
      [gateEval (mapGate f g) x (evaluate (transport f code) x)] =
      evaluate code (project x) ++ [gateEval g (project x) (evaluate code (project x))]
    rw [ih, gateEval_map f project hf]

theorem outputs_transport {n k : Nat} (f : Affine n → Affine k)
    (project : Point k → Point n)
    (hf : ∀ a x, aEval (f a) x = aEval a (project x))
    (code : Code n) (x : Point k) (roots : List Nat) :
    outputs (transport f code) x roots = outputs code (project x) roots := by
  unfold outputs
  rw [evaluate_transport f project hf]

theorem gateValid_map {n k : Nat} (f : Affine n → Affine k) (g : Gate n) (older : Nat) :
    gateValid older (mapGate f g) = gateValid older g := by
  cases g <;> rfl

theorem codeValid_transport {n k : Nat} (f : Affine n → Affine k) (code : Code n) :
    codeValid (transport f code) = codeValid code := by
  induction code with
  | nil => rfl
  | cons g code ih =>
    change (codeValid (transport f code) &&
      gateValid (transport f code).length (mapGate f g)) =
      (codeValid code && gateValid code.length g)
    rw [ih, transport_length, gateValid_map]

/-- Pull back a reduced-coordinate affine leaf through the actual source chart. -/
def chartLeaf {n : Nat} (pivot : Fin (n + 1)) (direction : Point n)
    (a : Affine n) : Affine (n + 1) :=
  insert n pivot (aShear direction (false, a))

theorem chartLeaf_eval {n : Nat} (pivot : Fin (n + 1)) (direction : Point n)
    (a : Affine n) (x : Point (n + 1)) :
    aEval (chartLeaf pivot direction a) x = aEval a (chart pivot direction x).2 := by
  have h := aEval_cut n pivot (insert n pivot (aShear direction (false, a))) x
  rw [cut_insert] at h
  unfold chartLeaf
  rw [← h, aShear_eval]
  change aEval (n := n + 1) (false, a) (chart pivot direction x) =
    aEval a (chart pivot direction x).2
  cases chart pivot direction x
  simp only [aEval, Bool.false_and, Bool.false_xor]

def chartCode {n : Nat} (pivot : Fin (n + 1)) (direction : Point n) (code : Code n) :
    Code (n + 1) :=
  transport (chartLeaf pivot direction) code

theorem chartCode_outputs {n : Nat} (pivot : Fin (n + 1)) (direction : Point n)
    (code : Code n) (x : Point (n + 1)) (roots : List Nat) :
    outputs (chartCode pivot direction code) x roots =
      outputs code (chart pivot direction x).2 roots :=
  outputs_transport (chartLeaf pivot direction) (fun x => (chart pivot direction x).2)
    (chartLeaf_eval pivot direction) code x roots

theorem chartCode_length {n : Nat} (pivot : Fin (n + 1)) (direction : Point n)
    (code : Code n) : (chartCode pivot direction code).length = code.length :=
  transport_length _ _

theorem chartCode_valid {n : Nat} (pivot : Fin (n + 1)) (direction : Point n)
    (code : Code n) : codeValid (chartCode pivot direction code) = codeValid code :=
  codeValid_transport _ _

end PNP.Concrete.ResidualReduction.SharedRefutationTransport

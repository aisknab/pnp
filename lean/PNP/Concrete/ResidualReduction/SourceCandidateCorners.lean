import PNP.Concrete.ResidualReduction.SourceMatrixEntryInstructions
import PNP.Concrete.ResidualReduction.SourceCandidateChoiceInstructions

/-! Extract the eight candidate-decision bits from the actual encoded matrices.
Reverse read order puts them in the canonical decision order without assuming a
bulk reversal or matrix lookup primitive. All indices are input unary words. -/

namespace PNP.Concrete.ResidualReduction.SourceCandidateCorners
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra
open PNP.Concrete.ResidualReduction.SourceLinePullback (transfers transfers_exec)

structure Saved where
  normal : BitString
  activity : BitString
  width : BitString
  firstRow : BitString
  secondRow : BitString
  firstColumn : BitString
  secondColumn : BitString
def Saved.store (s : Saved) : Store 7 :=
  .cons s.normal (.cons s.activity (.cons s.width (.cons s.firstRow
    (.cons s.secondRow (.cons s.firstColumn (.cons s.secondColumn .nil))))))
def store (r : Registers) (s : Saved) : Store 16 := Frame.join r.store s.store
def data {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n) : Saved :=
  ⟨coefficientMatrixBits A, coefficientMatrixBits C, List.replicate n true,
    List.replicate i.val true, List.replicate k.val true, List.replicate j.val true, List.replicate l.val true⟩

abbrev Request := Bool × Bool × Bool
def requestMatrix {m n : Nat} (A C : Matrix m n) (q : Request) : Matrix m n := if q.1 then C else A
def requestRow {m : Nat} (i k : Fin m) (q : Request) : Fin m := if q.2.1 then k else i
def requestColumn {n : Nat} (j l : Fin n) (q : Request) : Fin n := if q.2.2 then l else j
def requestBit {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n) (q : Request) : Bool :=
  requestMatrix A C q (requestRow i k q) (requestColumn j l q)
def ready (r : Registers) (s : Saved) (q : Request) : Registers :=
  {r with
    input := if q.1 then s.activity else s.normal
    target := s.width
    remaining := []
    mode := if q.2.1 then s.secondRow else s.firstRow
    excess := if q.2.2 then s.secondColumn else s.firstColumn}
def prepareActions (q : Request) : List (Action 16) :=
  [.copy 0 (if q.1 then 10 else 9), .copy 1 11, .clear 2,
   .copy 5 (if q.2.1 then 13 else 12), .copy 3 (if q.2.2 then 15 else 14)]
def prepare (q : Request) : Block 16 := transfers (prepareActions q)

theorem prepare_exec (r : Registers) (s : Saved) (q : Request) :
    Exec (prepare q) (store r s) 6 (store (ready r s q) s) := by
  rcases q with ⟨which, row, column⟩
  cases which <;> cases row <;> cases column <;> exact transfers_exec _ _

def read (q : Request) : Block 16 := .seq (prepare q) (Frame.block 7 SourceMatrixEntry.block)
def readFuel {m n : Nat} (i k : Fin m) (j l : Fin n) (q : Request) : Nat :=
  6 + SourceMatrixEntry.fuel n (requestRow i k q).val (requestColumn j l q).val

theorem read_exec (r : Registers) {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n) (q : Request) :
    Exec (read q) (store r (data A C i k j l)) (readFuel i k j l q)
      (store (SourceMatrixEntry.result r n (requestBit A C i k j l q)) (data A C i k j l)) := by
  apply Exec.seq (prepare_exec r (data A C i k j l) q)
  rcases q with ⟨which, row, column⟩
  cases which <;> cases row <;> cases column <;>
    exact Frame.execution (SourceMatrixEntry.matrix_exec _ _ _ _) (data A C i k j l).store

def requests : List Request :=
  [(true,true,true), (true,true,false), (true,false,true), (true,false,false),
   (false,true,true), (false,true,false), (false,false,true), (false,false,false)]
def readRequests : List Request → Block 16
  | [] => .skip
  | q :: qs => .seq (read q) (readRequests qs)
def requestsFuel {m n : Nat} (i k : Fin m) (j l : Fin n) : List Request → Nat
  | [] => 1
  | q :: qs => readFuel i k j l q + requestsFuel i k j l qs
def requestsResult {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n) :
    List Request → Registers → Registers
  | [], r => r
  | q :: qs, r => requestsResult A C i k j l qs (SourceMatrixEntry.result r n (requestBit A C i k j l q))

theorem requests_exec (r : Registers) {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n) (qs : List Request) :
    Exec (readRequests qs) (store r (data A C i k j l)) (requestsFuel i k j l qs)
      (store (requestsResult A C i k j l qs r) (data A C i k j l)) := by
  induction qs generalizing r with
  | nil => exact Exec.skip _
  | cons q qs ih => exact Exec.seq (read_exec r A C i k j l q) (ih _)

def block : Block 16 := .seq (.action (.clear 8)) (readRequests requests)
def fuel {m n : Nat} (i k : Fin m) (j l : Fin n) : Nat := 1 + requestsFuel i k j l requests
def result {m n : Nat} (r : Registers) (A C : Matrix m n) (i k : Fin m) (j l : Fin n) : Registers :=
  {r with
    input := [], target := List.replicate n true, remaining := [], excess := [], mode := [],
    output := SourceCandidateChoice.inputBits (SourceCandidateChoice.corners A i k j l) (SourceCandidateChoice.corners C i k j l)}

theorem block_exec (r : Registers) {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n) :
    Exec block (store r (data A C i k j l)) (fuel i k j l) (store (result r A C i k j l) (data A C i k j l)) := by
  have clear : Exec (.action (.clear (8 : Fin 16))) (store r (data A C i k j l)) 1
      (store {r with output := []} (data A C i k j l)) :=
    Frame.execution (Exec.action (.clear (8 : Fin 9)) r.store) (data A C i k j l).store
  exact Exec.seq clear (requests_exec {r with output := []} A C i k j l requests)

theorem requests_bound {m n : Nat} (i k : Fin m) (j l : Fin n) (qs : List Request) :
    requestsFuel i k j l qs ≤ (6 + SourceMatrixEntry.budget m n) * qs.length + 1 := by
  induction qs with
  | nil => exact Nat.le_refl 1
  | cons q qs ih =>
    have one := SourceMatrixEntry.fuel_bound (requestRow i k q) (requestColumn j l q)
    simp only [requestsFuel, readFuel, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

theorem fuel_bound {m n : Nat} (i k : Fin m) (j l : Fin n) :
    fuel i k j l ≤ (6 + SourceMatrixEntry.budget m n) * 8 + 2 := by
  have bound := requests_bound i k j l requests
  change requestsFuel i k j l requests ≤ (6 + SourceMatrixEntry.budget m n) * 8 + 1 at bound
  unfold fuel
  omega

theorem output_exact (r : Registers) {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n) :
    (store (result r A C i k j l) (data A C i k j l)).get 8 =
      SourceCandidateChoice.inputBits (SourceCandidateChoice.corners A i k j l) (SourceCandidateChoice.corners C i k j l) :=
  Frame.get_core _ _ (8 : Fin 9)

end PNP.Concrete.ResidualReduction.SourceCandidateCorners

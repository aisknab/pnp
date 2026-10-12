import PNP.Concrete.NativeNormalization.MeasuredCollections

namespace PNP.Concrete.NativeNormalization.MeasuredSearch

open PNP.Concrete Matching MatchingCache MeasuredReach MeasuredFrontendCost

def scan (F : CNFFormula) (T : Table F.clauses.length F.variableCount) :
    Measured (Trace (Vertex F.clauses.length F.variableCount)) :=
  let indexes := MeasuredCollections.vertices F.clauses.length F.variableCount
  let found := MeasuredReach.explore (MeasuredMatching.seed T) (MeasuredMatching.edge F T)
    (F.clauses.length+F.variableCount) indexes.value []
  ⟨found.value,indexes.cost+found.cost+1⟩

theorem scan_value (F : CNFFormula) (T : Table F.clauses.length F.variableCount) :
    (scan F T).value = Matching.scan (CNFCore.incidence F) T.get := by
  simp only [scan,MeasuredCollections.vertices_value,MeasuredReach.explore_value,
    MeasuredMatching.seed_value,MeasuredMatching.edge_value,Matching.scan]

def scanBound (B : Nat) : Nat := scanEnvelope B+6*B*B+7*B+7

theorem scan_cost (F : CNFFormula) (T : Table F.clauses.length F.variableCount)
    (shape : ∀ i, (CNFCore.clause F i).length ≤ 3) (B : Nat)
    (size : F.clauses.length+F.variableCount ≤ B) :
    (scan F T).cost ≤ scanBound B := by
  have hg := MeasuredCollections.vertices_cost F.clauses.length F.variableCount B
    (by omega) (by omega)
  have hs := scan_le_envelope F T shape B size
  simp only [scan,MeasuredCollections.vertices_value]
  change (MeasuredCollections.vertices F.clauses.length F.variableCount).cost+
    (MeasuredMatching.scan F T).cost+1 ≤ scanBound B
  simp only [scanBound]
  omega

def owner (T : Table c n) (v : Fin n) : Measured (Option (Fin c)) :=
  let indexes := MeasuredCollections.range c
  let found := MeasuredReach.find (fun i =>
    let entry := MeasuredMatching.readMatching T i
    (⟨entry.value == some v,entry.cost+1⟩ : Measured Bool)) indexes.value
  ⟨found.value,indexes.cost+found.cost+1⟩

theorem owner_value (T : Table c n) (v : Fin n) :
    (owner T v).value = Matching.owner T.get v := by
  simp only [owner,MeasuredReach.find_value,MeasuredCollections.range_value,
    MeasuredMatching.readMatching_value,Matching.owner]

def ownerBound (B : Nat) : Nat := 3*B*B+(B+4)*B+3

theorem owner_cost (T : Table c n) (v : Fin n) (B : Nat) (hc : c ≤ B) :
    (owner T v).cost ≤ ownerBound B := by
  have hr := MeasuredCollections.range_cost c
  have hf := MeasuredReach.find_cost (fun i =>
    let entry := MeasuredMatching.readMatching T i
    (⟨entry.value == some v,entry.cost+1⟩ : Measured Bool))
    (MeasuredCollections.range c).value (c+3) (by
      intro i
      have h := MeasuredMatching.readMatching_cost T i
      dsimp
      omega)
  rw [MeasuredCollections.range_value,List.length_finRange] at hf
  rw [show c+3+1=c+4 by omega] at hf
  have hcc := Nat.mul_le_mul_left 3 (Nat.mul_le_mul hc hc)
  have hp := Nat.mul_le_mul (Nat.add_le_add_right hc 4) hc
  simp only [owner,MeasuredCollections.range_value,ownerBound]
  simp only [Nat.mul_assoc] at *
  omega

def candidateCheck (T : Table c n) (tr : Trace (Vertex c n)) (v : Fin n) : Measured Bool :=
  let found := owner T v
  let seen := nodeMember tr (.inr v)
  ⟨found.value.isNone && seen.value,found.cost+seen.cost+1⟩

theorem candidateCheck_value (T : Table c n) (tr : Trace (Vertex c n)) (v : Fin n) :
    (candidateCheck T tr v).value =
      ((Matching.owner T.get v).isNone && decide (Sum.inr v ∈ nodes tr)) := by
  simp only [candidateCheck,owner_value,nodeMember_value]
  by_cases h : Sum.inr v ∈ nodes tr <;> simp [h]

theorem candidateCheck_cost (T : Table c n) (tr : Trace (Vertex c n)) (v : Fin n)
    (B : Nat) (hc : c ≤ B) (ht : tr.length ≤ B) :
    (candidateCheck T tr v).cost ≤ ownerBound B+2*B+2 := by
  have ho := owner_cost T v B hc
  have hm := nodeMember_cost tr (.inr v)
  simp only [candidateCheck]
  omega

def candidate (T : Table c n) (tr : Trace (Vertex c n)) : Measured (Option (Fin n)) :=
  let indexes := MeasuredCollections.range n
  let found := MeasuredReach.find (candidateCheck T tr) indexes.value
  ⟨found.value,indexes.cost+found.cost+1⟩

theorem candidate_value (T : Table c n) (tr : Trace (Vertex c n)) :
    (candidate T tr).value = (List.finRange n).find? (fun v =>
      (Matching.owner T.get v).isNone && decide (Sum.inr v ∈ nodes tr)) := by
  simp only [candidate,MeasuredReach.find_value,MeasuredCollections.range_value,candidateCheck_value]

def candidateBound (B : Nat) : Nat := 3*B*B+(ownerBound B+2*B+3)*B+3

theorem candidate_cost (T : Table c n) (tr : Trace (Vertex c n)) (B : Nat)
    (hc : c ≤ B) (hn : n ≤ B) (ht : tr.length ≤ B) :
    (candidate T tr).cost ≤ candidateBound B := by
  have hr := MeasuredCollections.range_cost n
  have hf := MeasuredReach.find_cost (candidateCheck T tr)
    (MeasuredCollections.range n).value (ownerBound B+2*B+2)
    (fun v => candidateCheck_cost T tr v B hc ht)
  rw [MeasuredCollections.range_value,List.length_finRange] at hf
  rw [show ownerBound B+2*B+2+1=ownerBound B+2*B+3 by omega] at hf
  have hnn := Nat.mul_le_mul_left 3 (Nat.mul_le_mul hn hn)
  have hp := Nat.mul_le_mul_left (ownerBound B+2*B+3) hn
  simp only [candidate,MeasuredCollections.range_value,candidateBound]
  simp only [Nat.mul_assoc] at *
  omega

def path [DecidableEq α] : Trace α → α → Measured (Option (List α))
  | [], _ => ⟨none,1⟩
  | (w,p)::tr, v =>
      if v = w then
        match p with
        | none => ⟨some [v],3⟩
        | some u =>
            let tail := path tr u
            ⟨tail.value.map (v::·),tail.cost+3⟩
      else
        let tail := path tr v
        ⟨tail.value,tail.cost+2⟩

theorem path_value [DecidableEq α] (tr : Trace α) (v : α) :
    (path tr v).value = pathTo tr v := by
  induction tr generalizing v with
  | nil => rfl
  | cons p tr ih =>
      rcases p with ⟨w,p⟩
      by_cases h : v = w <;> cases p <;> simp [path,pathTo,h,ih]

theorem path_cost [DecidableEq α] (tr : Trace α) (v : α) :
    (path tr v).cost ≤ 3*tr.length+1 := by
  induction tr generalizing v with
  | nil => simp [path]
  | cons p tr ih =>
      rcases p with ⟨w,p⟩
      by_cases h : v = w
      · cases p with
        | none =>
            simp only [path,h,if_true,List.length_cons]
            omega
        | some u =>
            have ht := ih u
            simp only [path,h,if_true,List.length_cons]
            omega
      · have ht := ih v
        simp only [path,h,if_false,List.length_cons]
        omega

def search (F : CNFFormula) (T : Table F.clauses.length F.variableCount) :
    Measured (SearchOutput F.clauses.length F.variableCount) :=
  let scanned := scan F T
  let chosen := candidate T scanned.value
  match chosen.value with
  | none => ⟨.terminal scanned.value,scanned.cost+chosen.cost+1⟩
  | some v =>
      let route := path scanned.value (.inr v)
      ⟨.augment v (route.value.getD []),scanned.cost+chosen.cost+route.cost+2⟩

theorem search_value (F : CNFFormula) (T : Table F.clauses.length F.variableCount) :
    (search F T).value = Matching.search (CNFCore.incidence F) T.get := by
  have hc : (candidate T (Matching.scan (CNFCore.incidence F) T.get)).value =
      Matching.freeCandidate (CNFCore.incidence F) T.get := by
    rw [candidate_value]
    rfl
  simp only [search,scan_value,path_value,hc]
  cases h : Matching.freeCandidate (CNFCore.incidence F) T.get <;>
    simp only [h,Matching.search]

def searchBound (B : Nat) : Nat := scanBound B+candidateBound B+3*B+3

theorem search_cost (F : CNFFormula) (T : Table F.clauses.length F.variableCount)
    (shape : ∀ i, (CNFCore.clause F i).length ≤ 3) (B : Nat)
    (size : F.clauses.length+F.variableCount ≤ B) :
    (search F T).cost ≤ searchBound B := by
  have hs := scan_cost F T shape B size
  have ht : (scan F T).value.length ≤ B := by
    rw [scan_value]
    exact Nat.le_trans (Matching.scan_length (CNFCore.incidence F) T.get) size
  have hc := candidate_cost T (scan F T).value B (by omega) (by omega) ht
  cases h : (candidate T (scan F T).value).value with
  | none =>
      simp only [search,h,searchBound]
      omega
  | some v =>
      have hp := path_cost (scan F T).value (.inr v)
      simp only [search,h,searchBound]
      omega

theorem search_path_bound (F : CNFFormula) (T : Table F.clauses.length F.variableCount)
    (v : Fin F.variableCount) (route : List (Vertex F.clauses.length F.variableCount))
    (h : (search F T).value = .augment v route) : route.length ≤ F.clauses.length+F.variableCount := by
  have hc := Matching.search_correct (CNFCore.incidence F) T.get
  rw [← search_value F T,h] at hc
  exact hc.2.2.2


end PNP.Concrete.NativeNormalization.MeasuredSearch

import PNP.SignedTernary.CNF.Source

namespace PNP.SignedTernary.CNF
open PNP.SignedTernary.Field PNP.Concrete

/-- These finite lists enumerate actual sites; unused declared original sites are
retained. No claimed encoded-machine runtime follows from the list equations. -/
def auxSites : (k : Nat) → List (Aux k)
  | 0 => []
  | k+1 => [.inl .out,.inl .both,.inl .diff] ++ (auxSites k).map Sum.inr

theorem auxSites_length (k : Nat) : (auxSites k).length = 3*k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [auxSites,List.length_append,List.length_cons,List.length_nil,List.length_map,ih]
    omega

theorem auxSites_complete (k : Nat) : ∀ i : Aux k, i ∈ auxSites k := by
  induction k with
  | zero => intro i; nomatch i
  | succ k ih =>
    intro i
    cases i with
    | inl s =>
      cases s <;> simp only [auxSites,List.mem_append,List.mem_cons,
        true_or,or_true,eq_self]
    | inr i =>
      exact List.mem_append_right _ (List.mem_map.mpr ⟨i,ih i,rfl⟩)

def bankSites {α : Type} : (cs : List (List (Form α))) → List (Bank cs)
  | [] => []
  | c::cs => (auxSites c.length).map Sum.inl ++ (bankSites cs).map Sum.inr

theorem bankSites_length {α : Type} (cs : List (List (Form α))) :
    (bankSites cs).length = 3*occurrences cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [bankSites,List.length_append,List.length_map,auxSites_length,ih,occurrences]
    omega

theorem bankSites_complete {α : Type} (cs : List (List (Form α))) :
    ∀ i : Bank cs, i ∈ bankSites cs := by
  induction cs with
  | nil => intro i; nomatch i
  | cons c cs ih =>
    intro i
    cases i with
    | inl i => exact List.mem_append_left _ (List.mem_map.mpr ⟨i,auxSites_complete _ i,rfl⟩)
    | inr i => exact List.mem_append_right _ (List.mem_map.mpr ⟨i,ih i,rfl⟩)

def finSites : (n : Nat) → List (Fin n)
  | 0 => []
  | n+1 => ⟨0,Nat.zero_lt_succ n⟩ :: (finSites n).map Fin.succ

theorem finSites_length (n : Nat) : (finSites n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [finSites,List.length_cons,List.length_map,ih]

theorem finSites_complete (n : Nat) : ∀ i : Fin n, i ∈ finSites n := by
  induction n with
  | zero => intro i; nomatch i
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,ih j,rfl⟩)

def portSites (F : CNFFormula) : List (Port F) :=
  .inl none ::
    (((finSites F.variableCount).map (fun i => Sum.inl (some i))) ++
      (bankSites (inputs F)).map Sum.inr)

theorem portSites_length (F : CNFFormula) :
    (portSites F).length = F.variableCount + 1 + 3*occurrences F.clauses := by
  simp only [portSites,List.length_cons]
  rw [List.length_append,List.length_map,List.length_map,finSites_length,bankSites_length]
  rw [inputs,mapped_occurrences]
  omega

theorem portSites_complete (F : CNFFormula) : ∀ i : Port F, i ∈ portSites F := by
  intro i
  cases i with
  | inl i =>
    cases i with
    | none => exact List.mem_cons_self
    | some i =>
      exact List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_map.mpr ⟨i,finSites_complete _ i,rfl⟩))
  | inr i =>
    exact List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_map.mpr ⟨i,bankSites_complete _ i,rfl⟩))

theorem raw_positive_control : RawFeasible (encodeCNF ⟨0,[]⟩) := by
  apply (raw_iff_CNFSAT _).2
  exact ⟨⟨0,[]⟩,decodeEncodedCNF_canonical _,[],rfl,True.intro⟩

theorem negative_oob_control : ¬ Feasible ⟨0,[[⟨false,0⟩]]⟩ := by
  intro h
  obtain ⟨w,hw⟩ := (feasible_iff_satisfiable _).1 h
  have hn : w = [] := List.eq_nil_of_length_eq_zero hw.1
  subst w
  exact hw.2.1.elim (fun h => by cases h) (fun h => h)

end PNP.SignedTernary.CNF

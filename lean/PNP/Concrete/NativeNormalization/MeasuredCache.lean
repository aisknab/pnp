import PNP.Concrete.NativeNormalization.MeasuredOperations

namespace PNP.Concrete.NativeNormalization.MeasuredCache

open MeasuredReach NativeBasis MeasuredOperations

abbrev Triple (n : Nat) := Literal n × Literal n × Literal n

/-- Stored tables are tied to exact source values by erased equality proofs. -/
structure Cache (S : Selection n c) where
  literalData : List (Triple n)
  literal_eq : literalData = List.ofFn (fun i => (S.literal i .first,S.literal i .middle,S.literal i .last))
  ownerData : List (Fin c)
  owner_eq : ownerData = List.ofFn S.owner
  slotData : List Slot
  slot_eq : slotData = List.ofFn S.slot
  modeData : List (Option Slot)
  mode_eq : modeData = List.ofFn S.mode

def literal {S : Selection n c} (C : Cache S) (i : Fin c) (s : Slot) : Measured (Literal n) :=
  let row := MeasuredAccess.get C.literalData i.val
    (by rw [C.literal_eq,List.length_ofFn]; exact i.isLt)
  ⟨match s with | .first => row.value.1 | .middle => row.value.2.1 | .last => row.value.2.2,
    row.cost+1⟩

theorem literal_value {S : Selection n c} (C : Cache S) (i : Fin c) (s : Slot) :
    (literal C i s).value = S.literal i s := by
  cases s <;> simp only [literal,MeasuredAccess.get_value,C.literal_eq,List.getElem_ofFn]

theorem literal_cost {S : Selection n c} (C : Cache S) (i : Fin c) (s : Slot) :
    (literal C i s).cost ≤ c+1 := by
  simp only [literal,MeasuredAccess.get_cost]
  have h := i.isLt
  omega

def owner {S : Selection n c} (C : Cache S) (v : Fin n) : Measured (Fin c) :=
  MeasuredAccess.get C.ownerData v.val (by rw [C.owner_eq,List.length_ofFn]; exact v.isLt)

theorem owner_value {S : Selection n c} (C : Cache S) (v : Fin n) :
    (owner C v).value = S.owner v := by
  simp only [owner,MeasuredAccess.get_value,C.owner_eq,List.getElem_ofFn]

theorem owner_cost {S : Selection n c} (C : Cache S) (v : Fin n) : (owner C v).cost ≤ n := by
  simp only [owner,MeasuredAccess.get_cost]
  exact v.isLt

def slot {S : Selection n c} (C : Cache S) (v : Fin n) : Measured Slot :=
  MeasuredAccess.get C.slotData v.val (by rw [C.slot_eq,List.length_ofFn]; exact v.isLt)

theorem slot_value {S : Selection n c} (C : Cache S) (v : Fin n) :
    (slot C v).value = S.slot v := by
  simp only [slot,MeasuredAccess.get_value,C.slot_eq,List.getElem_ofFn]

theorem slot_cost {S : Selection n c} (C : Cache S) (v : Fin n) : (slot C v).cost ≤ n := by
  simp only [slot,MeasuredAccess.get_cost]
  exact v.isLt

def mode {S : Selection n c} (C : Cache S) (i : Fin c) : Measured (Option Slot) :=
  MeasuredAccess.get C.modeData i.val (by rw [C.mode_eq,List.length_ofFn]; exact i.isLt)

theorem mode_value {S : Selection n c} (C : Cache S) (i : Fin c) :
    (mode C i).value = S.mode i := by
  simp only [mode,MeasuredAccess.get_value,C.mode_eq,List.getElem_ofFn]

theorem mode_cost {S : Selection n c} (C : Cache S) (i : Fin c) : (mode C i).cost ≤ c := by
  simp only [mode,MeasuredAccess.get_cost]
  exact i.isLt

def operations {S : Selection n c} (C : Cache S) : Operations S :=
  { literal := literal C
    literal_eq := literal_value C
    owner := owner C
    owner_eq := owner_value C
    slot := slot C
    slot_eq := slot_value C
    mode := mode C
    mode_eq := mode_value C }

theorem operations_bounded {S : Selection n c} (C : Cache S) (B : Nat)
    (hn : n ≤ B) (hc : c ≤ B) : Bounded (operations C) (B+1) B B B := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i s
    exact Nat.le_trans (literal_cost C i s) (Nat.add_le_add_right hc 1)
  · intro v
    exact Nat.le_trans (owner_cost C v) hn
  · intro v
    exact Nat.le_trans (slot_cost C v) hn
  · intro i
    exact Nat.le_trans (mode_cost C i) hc

def selection {S : Selection n c} (C : Cache S) : Selection n c :=
  { literal := fun i s => (literal C i s).value
    owner := fun v => (owner C v).value
    slot := fun v => (slot C v).value
    mode := fun i => (mode C i).value
    ownerVariable := by
      intro v
      simp only [literal_value,owner_value,slot_value]
      exact S.ownerVariable v
    ownerMode := by
      intro v
      simp only [owner_value,slot_value,mode_value]
      exact S.ownerMode v }

theorem selection_eq {S : Selection n c} (C : Cache S) : selection C = S := by
  simp only [selection,literal_value,owner_value,slot_value,mode_value]

def triple {S : Selection n c} (ops : Operations S) (i : Fin c) : Measured (Triple n) :=
  let a := ops.literal i .first
  let b := ops.literal i .middle
  let d := ops.literal i .last
  ⟨(a.value,b.value,d.value),a.cost+b.cost+d.cost+1⟩

theorem triple_value {S : Selection n c} (ops : Operations S) (i : Fin c) :
    (triple ops i).value = (S.literal i .first,S.literal i .middle,S.literal i .last) := by
  simp only [triple,ops.literal_eq]

theorem triple_cost {S : Selection n c} (ops : Operations S) (i : Fin c) (L : Nat)
    (bound : ∀ i s, (ops.literal i s).cost ≤ L) : (triple ops i).cost ≤ 3*L+1 := by
  have h1 := bound i .first
  have h2 := bound i .middle
  have h3 := bound i .last
  simp only [triple]
  omega

def build {S : Selection n c} (ops : Operations S) : Measured (Cache S) :=
  let clauses := MeasuredCollections.range c
  let variables := MeasuredCollections.range n
  let literals := MeasuredCollections.map (triple ops) clauses.value
  let owners := MeasuredCollections.map ops.owner variables.value
  let slots := MeasuredCollections.map ops.slot variables.value
  let modes := MeasuredCollections.map ops.mode clauses.value
  let data : Cache S :=
    { literalData := literals.value
      literal_eq := by
        simp only [literals,MeasuredCollections.map_value,triple_value,clauses,
          MeasuredCollections.range_value,List.finRange,List.map_ofFn,Function.comp_def]
      ownerData := owners.value
      owner_eq := by
        simp only [owners,MeasuredCollections.map_value,ops.owner_eq,variables,
          MeasuredCollections.range_value,List.finRange,List.map_ofFn,Function.comp_def]
      slotData := slots.value
      slot_eq := by
        simp only [slots,MeasuredCollections.map_value,ops.slot_eq,variables,
          MeasuredCollections.range_value,List.finRange,List.map_ofFn,Function.comp_def]
      modeData := modes.value
      mode_eq := by
        simp only [modes,MeasuredCollections.map_value,ops.mode_eq,clauses,
          MeasuredCollections.range_value,List.finRange,List.map_ofFn,Function.comp_def] }
  ⟨data,clauses.cost+variables.cost+literals.cost+owners.cost+slots.cost+modes.cost+1⟩

theorem build_selection {S : Selection n c} (ops : Operations S) :
    selection (build ops).value = NativeSourceCache.cacheSelection S := by
  rw [selection_eq,NativeSourceCache.cacheSelection_eq]

def cacheBound (B L O D M : Nat) : Nat :=
  6*B*B+(3*L+3)*B+(O+2)*B+(D+2)*B+(M+2)*B+7

theorem build_cost {S : Selection n c} (ops : Operations S) (B L O D M : Nat)
    (hn : n ≤ B) (hc : c ≤ B) (bound : Bounded ops L O D M) :
    (build ops).cost ≤ cacheBound B L O D M := by
  have hrc := MeasuredCollections.range_cost c
  have hrn := MeasuredCollections.range_cost n
  have hl := MeasuredCollections.map_cost (triple ops) (MeasuredCollections.range c).value
    (3*L+1) (fun i => triple_cost ops i L bound.1)
  have ho := MeasuredCollections.map_cost ops.owner (MeasuredCollections.range n).value O bound.2.1
  have hs := MeasuredCollections.map_cost ops.slot (MeasuredCollections.range n).value D bound.2.2.1
  have hm := MeasuredCollections.map_cost ops.mode (MeasuredCollections.range c).value M bound.2.2.2
  rw [MeasuredCollections.range_value,List.length_finRange] at hl ho hs hm
  rw [show 3*L+1+2=3*L+3 by omega] at hl
  have hcc := Nat.mul_le_mul_left 3 (Nat.mul_le_mul hc hc)
  have hnn := Nat.mul_le_mul_left 3 (Nat.mul_le_mul hn hn)
  have hpl := Nat.mul_le_mul_left (3*L+3) hc
  have hpo := Nat.mul_le_mul_left (O+2) hn
  have hps := Nat.mul_le_mul_left (D+2) hn
  have hpm := Nat.mul_le_mul_left (M+2) hc
  simp only [build,MeasuredCollections.range_value,cacheBound]
  simp only [Nat.mul_assoc] at *
  omega


end PNP.Concrete.NativeNormalization.MeasuredCache

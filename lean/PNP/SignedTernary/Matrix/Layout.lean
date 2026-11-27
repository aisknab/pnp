import PNP.SignedTernary.Matrix.Linearity

set_option autoImplicit false

namespace PNP.SignedTernary.Encoding
open PNP.SignedTernary.Field PNP.SignedTernary.Linear PNP.SignedTernary.Gate PNP.SignedTernary.Relay PNP.SignedTernary.Marker PNP.SignedTernary.Network

def split : (n m : Nat) → Vec (m+n) → Vec n × Vec m
  | 0, _, x => ((),x)
  | n+1, m, x =>
      let p := split n m x.2
      ((x.1,p.1),p.2)

theorem split_join (n m : Nat) (x : Vec n) (y : Vec m) :
    split n m (join x y) = (x,y) := by
  induction n with
  | zero => cases x; rfl
  | succ n ih => simp only [join,split,ih]

theorem join_split (n m : Nat) (x : Vec (m+n)) :
    join (split n m x).1 (split n m x).2 = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (x.1,join (split n m x.2).1 (split n m x.2).2) = x
    rw [ih]
    rfl

@[reducible] def blockSize (width : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => blockSize width k + width

theorem blockSize_eq (width k : Nat) : blockSize width k = width*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [blockSize,ih,Nat.mul_succ]

def flatBlocks {width : Nat} : {k : Nat} → Blocks width k → Vec (blockSize width k)
  | 0, _ => ()
  | _+1, xs => join xs.1 (flatBlocks xs.2)

def unflatBlocks (width : Nat) : (k : Nat) → Vec (blockSize width k) → Blocks width k
  | 0, _ => ()
  | k+1, x => let p := split width (blockSize width k) x
             (p.1,unflatBlocks width k p.2)

theorem unflat_flat_blocks {width k : Nat} (x : Blocks width k) :
    unflatBlocks width k (flatBlocks x) = x := by
  induction k with
  | zero => cases x; rfl
  | succ k ih => simp only [flatBlocks,unflatBlocks,split_join,ih]

theorem flat_unflat_blocks (width k : Nat) (x : Vec (blockSize width k)) :
    flatBlocks (unflatBlocks width k x) = x := by
  induction k with
  | zero => cases x; rfl
  | succ k ih => simp only [unflatBlocks,flatBlocks,ih,join_split]

theorem flat_blocks_signed {width k : Nat} (xs : Blocks width k) :
    Signed (flatBlocks xs) ↔ BlocksSigned xs := by
  induction k with
  | zero => exact Iff.rfl
  | succ k ih =>
    change Signed (join xs.1 (flatBlocks xs.2)) ↔ _
    rw [signed_join,ih]
    exact Iff.rfl

theorem flat_blocks_plus {width k : Nat} (x y : Blocks width k) :
    flatBlocks (plusBlocks x y) = plus (flatBlocks x) (flatBlocks y) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [flatBlocks,plusBlocks,ih,plus_join]

abbrev Input (n m : Nat) := Vec 4 × (F3 × (Blocks 4 (stages m) × Vec n))

abbrev inputWidth (n m : Nat) := (n+blockSize 4 (stages m))+1+4

abbrev outputWidth (n m : Nat) := ((((m+m)+m+(n+1))+3)+blockSize 3 (stages m))+1

def flatInput {n m : Nat} (x : Input n m) : Vec (inputWidth n m) :=
  join x.1 (x.2.1,join (flatBlocks x.2.2.1) x.2.2.2)

def unflatInput (n m : Nat) (x : Vec (inputWidth n m)) : Input n m :=
  let a := split 4 ((n+blockSize 4 (stages m))+1) x
  let b := split (blockSize 4 (stages m)) n a.2.2
  (a.1,(a.2.1,(unflatBlocks 4 (stages m) b.1,b.2)))

def InputSigned {n m : Nat} (x : Input n m) :=
  Signed x.1 ∧ x.2.1 ≠ .z ∧ BlocksSigned x.2.2.1 ∧ Signed x.2.2.2

def plusInput {n m : Nat} (x y : Input n m) : Input n m :=
  (plus x.1 y.1,(add x.2.1 y.2.1,(plusBlocks x.2.2.1 y.2.2.1,plus x.2.2.2 y.2.2.2)))

theorem unflat_flat_input {n m : Nat} (x : Input n m) :
    unflatInput n m (flatInput x) = x := by
  simp only [unflatInput,flatInput,split_join,unflat_flat_blocks]

theorem flat_unflat_input (n m : Nat) (x : Vec (inputWidth n m)) :
    flatInput (unflatInput n m x) = x := by
  simp only [flatInput,unflatInput,flat_unflat_blocks,join_split]
  change join (split 4 ((n+blockSize 4 (stages m))+1) x).1
    (split 4 ((n+blockSize 4 (stages m))+1) x).2 = x
  exact join_split _ _ x

theorem flat_input_signed {n m : Nat} (x : Input n m) :
    Signed (flatInput x) ↔ InputSigned x := by
  change @Signed (inputWidth n m) (@join 4 ((n+blockSize 4 (stages m))+1) x.1 (x.2.1,join (flatBlocks x.2.2.1) x.2.2.2)) ↔ _
  rw [signed_join]
  change (Signed x.1 ∧ x.2.1 ≠ .z ∧ Signed (join (flatBlocks x.2.2.1) x.2.2.2)) ↔ _
  rw [signed_join,flat_blocks_signed]
  exact Iff.rfl

theorem flat_input_plus {n m : Nat} (x y : Input n m) :
    flatInput (plusInput x y) = plus (flatInput x) (flatInput y) := by
  simp only [flatInput,plusInput,flat_blocks_plus,plus_join]
  rfl

theorem unflat_input_plus (n m : Nat) (x y : Vec (inputWidth n m)) :
    unflatInput n m (plus x y) =
      plusInput (unflatInput n m x) (unflatInput n m y) := by
  have h := flat_input_plus (unflatInput n m x) (unflatInput n m y)
  rw [flat_unflat_input,flat_unflat_input] at h
  rw [←h,unflat_flat_input]

def flatBanks {m : Nat} (x : Banks m) : Vec ((m+m)+m) := join x.1 (join x.2.1 x.2.2)

theorem flat_banks_signed {m : Nat} (x : Banks m) :
    Signed (flatBanks x) ↔ BanksSigned x := by
  simp only [flatBanks,signed_join,BanksSigned]

theorem flat_banks_plus {m : Nat} (x y : Banks m) :
    flatBanks (plusBanks x y) = plus (flatBanks x) (flatBanks y) := by
  simp only [flatBanks,plusBanks,plus_join]

def flatOutput {n m : Nat} (y : F3 × PhysicalOutput n m) : Vec (outputWidth n m) :=
  (y.1,join (flatBlocks y.2.1)
    (join y.2.2.1 (join y.2.2.2.1 (flatBanks y.2.2.2.2))))

theorem flat_output_signed {n m : Nat} (y : F3 × PhysicalOutput n m) :
    Signed (flatOutput y) ↔ MarkedSigned y := by
  change (y.1 ≠ .z ∧ Signed (join (flatBlocks y.2.1)
    (join y.2.2.1 (join y.2.2.2.1 (flatBanks y.2.2.2.2))))) ↔ _
  rw [signed_join,signed_join,signed_join,flat_blocks_signed,flat_banks_signed]
  exact Iff.rfl

theorem flat_output_plus {n m : Nat} (x y : F3 × PhysicalOutput n m) :
    flatOutput (add x.1 y.1,plusOutput x.2 y.2) = plus (flatOutput x) (flatOutput y) := by
  simp only [flatOutput,plusOutput,flat_blocks_plus,flat_banks_plus,plus_join]
  rfl

def flatMap {n m : Nat} (L : Rows n m) (x : Vec (inputWidth n m)) : Vec (outputWidth n m) :=
  let p := unflatInput n m x
  flatOutput (marked L p.1 p.2.1 p.2.2.1 p.2.2.2)

theorem flatMap_plus {n m : Nat} (L : Rows n m) (x y : Vec (inputWidth n m)) :
    flatMap L (plus x y) = plus (flatMap L x) (flatMap L y) := by
  simp only [flatMap]
  rw [unflat_input_plus]
  simp only [plusInput]
  rw [marked_plus,flat_output_plus]

theorem flatMap_donor_iff {n m : Nat} (L : Rows n m) :
    (∃ x, Signed x ∧ Signed (flatMap L x)) ↔ TerminalDonor L := by
  constructor
  · rintro ⟨x,hx,ho⟩
    let p := unflatInput n m x
    have hp : InputSigned p := (flat_input_signed p).1 (by rw [flat_unflat_input]; exact hx)
    have hm : MarkedSigned (marked L p.1 p.2.1 p.2.2.1 p.2.2.2) :=
      (flat_output_signed _).1 ho
    exact ⟨p.1,p.2.1,p.2.2.1,p.2.2.2,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,hm⟩
  · rintro ⟨c,s,xs,x,hc,hs,hxs,hx,ho⟩
    refine ⟨flatInput (c,s,xs,x),(flat_input_signed _).2 ⟨hc,hs,hxs,hx⟩,?_⟩
    simp only [flatMap,unflat_flat_input]
    exact (flat_output_signed _).2 ho

theorem square_width (n m : Nat) : outputWidth n m = inputWidth n m := by
  simp only [outputWidth,inputWidth,blockSize_eq,stage_count]
  omega

def castVec {n m : Nat} (h : n=m) (x : Vec n) : Vec m := h ▸ x

theorem castVec_plus {n m : Nat} (h : n=m) (x y : Vec n) :
    castVec h (plus x y) = plus (castVec h x) (castVec h y) := by cases h; rfl

theorem castVec_signed {n m : Nat} (h : n=m) (x : Vec n) :
    Signed (castVec h x) ↔ Signed x := by cases h; exact Iff.rfl

def squareMap {n m : Nat} (L : Rows n m) (x : Vec (inputWidth n m)) : Vec (inputWidth n m) :=
  castVec (square_width n m) (flatMap L x)

theorem squareMap_plus {n m : Nat} (L : Rows n m) (x y : Vec (inputWidth n m)) :
    squareMap L (plus x y) = plus (squareMap L x) (squareMap L y) := by
  rw [squareMap,flatMap_plus,castVec_plus]
  rfl

theorem squareMap_donor_iff {n m : Nat} (L : Rows n m) :
    (∃ x, Signed x ∧ Signed (squareMap L x)) ↔ TerminalDonor L := by
  have he : ∀ x, Signed (squareMap L x) ↔ Signed (flatMap L x) :=
    fun x => castVec_signed (square_width n m) (flatMap L x)
  constructor
  · rintro ⟨x,hx,ho⟩
    exact (flatMap_donor_iff L).1 ⟨x,hx,(he x).1 ho⟩
  · intro h
    obtain ⟨x,hx,ho⟩ := (flatMap_donor_iff L).2 h
    exact ⟨x,hx,(he x).2 ho⟩

end PNP.SignedTernary.Encoding

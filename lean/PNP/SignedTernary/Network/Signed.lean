import PNP.SignedTernary.Network.BankShear

namespace PNP.SignedTernary.Network
open PNP.SignedTernary.Field PNP.SignedTernary.Linear PNP.SignedTernary.Gate PNP.SignedTernary.Relay PNP.SignedTernary.Marker
open PNP.Concrete (BitString CNFSAT)

abbrev PhysicalOutput (n m : Nat) :=
  Blocks 3 (stages m) × (Vec 3 × (Vec (n+1) × Banks m))

def physical {n m : Nat} (L : Rows n m) (c : Vec 4)
    (xs : Blocks 4 (stages m)) (x : Vec n) : PhysicalOutput n m :=
  let r := run c xs
  (r.1,(r.2.1.2,shear (anchoredRows L) (r.2.1.1,x) (splitBanks m r.2.2)))

def physicalNorm {n m : Nat} (y : PhysicalOutput n m) : F3 :=
  add (blockNorm y.1) (add (norm y.2.1) (add (norm y.2.2.1) (bankNorm y.2.2.2)))

def PhysicalSigned {n m : Nat} (y : PhysicalOutput n m) : Prop :=
  BlocksSigned y.1 ∧ Signed y.2.1 ∧ Signed y.2.2.1 ∧ BanksSigned y.2.2.2

theorem physical_norm {n m : Nat} (L : Rows n m) (c : Vec 4)
    (xs : Blocks 4 (stages m)) (x : Vec n) :
    physicalNorm (physical L c xs x) = add (add (norm c) (blockNorm xs)) (norm x) := by
  unfold physicalNorm physical
  rw [shear_norm,splitBanks_norm]
  have he : add (blockNorm (run c xs).1)
      (add (norm (run c xs).2.1.2)
        (add (@norm (n+1) ((run c xs).2.1.1,x)) (norm (run c xs).2.2))) =
      add (outputNorm (run c xs)) (norm x) := by
    simp only [outputNorm,norm,dot,add_assoc,add_comm,PNP.SignedTernary.Relay.add_left_comm]
  rw [he,run_norm]

theorem shear_positive {n m : Nat} (L : Rows n m) (x : Vec n) :
    shear (anchoredRows L) (.o,x) (positive m,(positive m,positive m)) =
      ((.o,x),(applyRows L x,(applyRows L x,applyRows L x))) := by
  simpa only [constant_positive] using shear_constant_banks L .o x

theorem physical_positive_exact {n m : Nat} (L : Rows n m)
    (xs : Blocks 4 (stages m)) (x : Vec n) (hx : BlocksSigned xs)
    (hv : BlocksSigned (run (positive 4) xs).1) :
    physical L (positive 4) xs x =
      ((run (positive 4) xs).1,(positive 3,((.o,x),
        (applyRows L x,(applyRows L x,applyRows L x))))) := by
  obtain ⟨_,hl,hb⟩ := run_forward xs hx hv
  simp only [physical]
  rw [hl,hb,splitBanks_positive]
  change ((run (positive 4) xs).1,(positive 3,
    shear (anchoredRows L) (.o,x) (positive m,(positive m,positive m)))) = _
  rw [shear_positive]

theorem physical_positive_iff {n m : Nat} (L : Rows n m)
    (xs : Blocks 4 (stages m)) (x : Vec n) (hx : BlocksSigned xs) :
    PhysicalSigned (physical L (positive 4) xs x) ↔
      Uniform xs ∧ Signed x ∧ Signed (applyRows L x) := by
  constructor
  · intro ho
    have hv : BlocksSigned (run (positive 4) xs).1 := ho.1
    rw [physical_positive_exact L xs x hx hv] at ho
    exact ⟨(run_forward xs hx hv).1,ho.2.2.1.2,ho.2.2.2.1⟩
  · rintro ⟨hu,hs,hl⟩
    have hv := (run_backward xs hx hu).1
    rw [physical_positive_exact L xs x hx hv]
    exact ⟨hv,positive_signed 3,⟨(by intro h; cases h),hs⟩,hl,hl,hl⟩

def PinnedDonor {n m : Nat} (L : Rows n m) : Prop :=
  ∃ xs : Blocks 4 (stages m), ∃ x : Vec n, BlocksSigned xs ∧ Signed x ∧
    PhysicalSigned (physical L (positive 4) xs x)

theorem pinned_iff_flat {n m : Nat} (L : Rows n m) :
    PinnedDonor L ↔ ∃ x, Signed x ∧ Signed (applyRows L x) := by
  constructor
  · rintro ⟨xs,x,hxs,hx,ho⟩
    exact ⟨x,hx,((physical_positive_iff L xs x hxs).1 ho).2.2⟩
  · rintro ⟨x,hx,hl⟩
    let xs := uniformDonor (positive (stages m))
    have hs := uniform_donor_signed (positive (stages m)) (positive_signed _)
    exact ⟨xs,x,hs,hx,(physical_positive_iff L xs x hs).2
      ⟨uniform_donor_uniform _,hx,hl⟩⟩

theorem pinned_iff_CNFSAT (raw : BitString) :
    PinnedDonor (sourceMatrix raw) ↔ CNFSAT raw :=
  (pinned_iff_flat _).trans (flat_iff_CNFSAT raw)

theorem scale_plus_vec {n : Nat} (a : F3) (x y : Vec n) :
    scale a (plus x y) = plus (scale a x) (scale a y) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [scale,plus,mul_add,ih]

theorem scale_minus_vec {n : Nat} (a : F3) (x y : Vec n) :
    scale a (minus x y) = minus (scale a x) (scale a y) := by
  simp only [minus,scale_plus_vec,scale_scale,mul_comm a .t]

def scaleBlocks {width : Nat} (a : F3) : {k : Nat} → Blocks width k → Blocks width k
  | 0, _ => ()
  | _+1, xs => (scale a xs.1,scaleBlocks a xs.2)

def scaleBanks {m : Nat} (a : F3) (z : Banks m) : Banks m :=
  (scale a z.1,(scale a z.2.1,scale a z.2.2))

def scaleOutput {n m : Nat} (a : F3) (y : PhysicalOutput n m) : PhysicalOutput n m :=
  (scaleBlocks a y.1,(scale a y.2.1,(scale a y.2.2.1,scaleBanks a y.2.2.2)))

theorem stage_scale (a : F3) (c z : Vec 4) :
    stage (scale a c) (scale a z) = scale a (stage c z) := by
  simp only [stage,←scale_join,gate,applyRows_scale]

theorem signals_scale (a : F3) (y : Vec 8) : signals (scale a y) = scale a (signals y) := rfl

theorem live_scale (a : F3) (y : Vec 8) : nextLive (scale a y) = scale a (nextLive y) := rfl

theorem pin_scale (a : F3) (y : Vec 8) : bankPin (scale a y) = mul a (bankPin y) := rfl

theorem run_scale {k : Nat} (a : F3) (c : Vec 4) (xs : Blocks 4 k) :
    run (scale a c) (scaleBlocks a xs) =
      (scaleBlocks a (run c xs).1,(scale a (run c xs).2.1,scale a (run c xs).2.2)) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    simp only [PNP.SignedTernary.Relay.run,scaleBlocks,stage_scale,signals_scale,live_scale,pin_scale,ih]
    rfl

theorem splitBanks_scale (m : Nat) (a : F3) (z : Vec (stages m)) :
    splitBanks m (scale a z) = scaleBanks a (splitBanks m z) := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [stages,splitBanks,scale,ih,scaleBanks]

theorem shear_scale {n m : Nat} (R : Rows n m) (a : F3) (h : Vec n) (z : Banks m) :
    shear R (scale a h) (scaleBanks a z) =
      (scale a (shear R h z).1,scaleBanks a (shear R h z).2) := by
  simp only [shear,scaleBanks,bankTotal,shiftBanks,←scale_plus_vec,applyRows_scale,
    ←scale_minus_vec]

theorem physical_scale {n m : Nat} (L : Rows n m) (a : F3)
    (c : Vec 4) (xs : Blocks 4 (stages m)) (x : Vec n) :
    physical L (scale a c) (scaleBlocks a xs) (scale a x) =
      scaleOutput a (physical L c xs x) := by
  simp only [physical]
  rw [run_scale]
  simp only [splitBanks_scale]
  change (scaleBlocks a (run c xs).1,(scale a (run c xs).2.1.2,
    shear (anchoredRows L) (scale a ((run c xs).2.1.1,x))
      (scaleBanks a (splitBanks m (run c xs).2.2)))) = _
  rw [shear_scale]
  rfl

theorem blocks_neg_signed {width k : Nat} (xs : Blocks width k) :
    BlocksSigned (scaleBlocks .t xs) ↔ BlocksSigned xs := by
  induction k with
  | zero => exact Iff.rfl
  | succ k ih =>
    change (Signed (scale .t xs.1) ∧ BlocksSigned (scaleBlocks .t xs.2)) ↔ _
    rw [signed_neg_iff,ih]
    exact Iff.rfl

theorem output_neg_signed {n m : Nat} (y : PhysicalOutput n m) :
    PhysicalSigned (scaleOutput .t y) ↔ PhysicalSigned y := by
  change (BlocksSigned (scaleBlocks .t y.1) ∧ Signed (scale .t y.2.1) ∧
    Signed (scale .t y.2.2.1) ∧ Signed (scale .t y.2.2.2.1) ∧
    Signed (scale .t y.2.2.2.2.1) ∧ Signed (scale .t y.2.2.2.2.2)) ↔ _
  rw [blocks_neg_signed,signed_neg_iff,signed_neg_iff,signed_neg_iff,signed_neg_iff,signed_neg_iff]
  exact Iff.rfl

end PNP.SignedTernary.Network

namespace PNP.SignedTernary.Network
open PNP.SignedTernary.Field PNP.SignedTernary.Linear PNP.SignedTernary.Gate PNP.SignedTernary.Relay PNP.SignedTernary.Marker
open PNP.Concrete (BitString CNFSAT)

theorem nonzero_square (a : F3) (ha : a ≠ .z) : mul a a = .o := by
  cases a <;> first | exact False.elim (ha rfl) | rfl

theorem signed_signals_norm {k : Nat} (xs : Blocks 3 k) (hx : BlocksSigned xs) :
    blockNorm xs = .z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change add (norm xs.1) (blockNorm xs.2) = .z
    rw [signed_norm xs.1 hx.1,ih xs.2 hx.2]
    rfl

theorem signed_knobs_norm (m : Nat) (xs : Blocks 4 (stages m))
    (hx : BlocksSigned xs) : blockNorm xs = .z := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change add (norm xs.1) (add (norm xs.2.1)
      (add (norm xs.2.2.1) (blockNorm xs.2.2.2))) = .z
    rw [signed_norm xs.1 hx.1,signed_norm xs.2.1 hx.2.1,
      signed_norm xs.2.2.1 hx.2.2.1,ih xs.2.2.2 hx.2.2.2]
    rfl

theorem signed_banks_norm {m : Nat} (z : Banks m) (hz : BanksSigned z) :
    bankNorm z = .z := by
  unfold bankNorm
  rw [signed_norm z.1 hz.1,signed_norm z.2.1 hz.2.1,signed_norm z.2.2 hz.2.2]
  exact scalar_triple _

theorem physical_signed_norm {n m : Nat} (y : PhysicalOutput n m)
    (hy : PhysicalSigned y) : physicalNorm y = signedNorm (n+1) := by
  unfold physicalNorm
  rw [signed_signals_norm y.1 hy.1,signed_norm y.2.1 hy.2.1,
    signed_norm y.2.2.1 hy.2.2.1,signed_banks_norm y.2.2.2 hy.2.2.2]
  change add .z (add .z (add (signedNorm (n+1)) .z)) = _
  rw [add_zero]
  rfl

/-- One new physical input and one permanently visible output. No output is hidden. -/
def marked {n m : Nat} (L : Rows n m) (c : Vec 4) (s : F3)
    (xs : Blocks 4 (stages m)) (x : Vec n) : F3 × PhysicalOutput n m :=
  (sentinel (project c), physical L (relay (project c) s) xs x)

def MarkedSigned {n m : Nat} (y : F3 × PhysicalOutput n m) : Prop :=
  y.1 ≠ .z ∧ PhysicalSigned y.2

def markedNorm {n m : Nat} (y : F3 × PhysicalOutput n m) : F3 :=
  add (mul y.1 y.1) (physicalNorm y.2)

/-- An explicit norm-defect identity for the actual composed map, all inputs. -/
theorem marked_norm {n m : Nat} (L : Rows n m) (c : Vec 4) (s : F3)
    (xs : Blocks 4 (stages m)) (x : Vec n) :
    markedNorm (marked L c s xs x) =
      add (add (norm c) (add (mul s s) (add (blockNorm xs) (norm x))))
        (neg (mul (dot nullDirection c) (dot nullDirection c))) := by
  simp only [markedNorm,marked,physical_norm]
  rw [add_assoc (norm (relay (project c) s)), ←add_assoc,
    reflection_norm,projection_norm]
  simp only [add_assoc,add_comm,PNP.SignedTernary.Relay.add_left_comm]

theorem marked_same_word {n m : Nat} (L : Rows n m) (c : Vec 4) (s : F3)
    (xs : Blocks 4 (stages m)) (x : Vec n)
    (hc : Signed c) (hs : s ≠ .z) (hxs : BlocksSigned xs) (hx : Signed x) :
    MarkedSigned (marked L c s xs x) ↔
      AllEqual4 c ∧ PhysicalSigned (physical L (constant4 s) xs x) := by
  constructor
  · intro ho
    have hn := physical_norm L (relay (project c) s) xs x
    rw [physical_signed_norm (physical L (relay (project c) s) xs x) ho.2,signed_knobs_norm m xs hxs,
      signed_norm x hx,add_zero] at hn
    have hrelay : norm (relay (project c) s) = .o :=
      (add_right_cancel .o _ (signedNorm n) hn).symm
    have hr := reflection_norm (project c) s
    rw [nonzero_square (sentinel (project c)) ho.1,hrelay,nonzero_square s hs] at hr
    have hp : norm (project c) = norm c := by
      rw [signed_norm c hc]
      exact (add_right_cancel .o _ .o hr).symm
    have hd := (projection_norm_iff c).1 hp
    have hf := projection_fixed c hd
    have hsent : sentinel c ≠ .z := by
      simpa only [marked,hf] using ho.1
    have he := sentinel_forces_constant c hc hd hsent
    have hcontrol : relay (project c) s = constant4 s := by
      rw [hf,equal_constant c he,constant_relay]
    exact ⟨he,by simpa only [marked,hcontrol] using ho.2⟩
  · rintro ⟨he,hout⟩
    rw [equal_constant c he,marked,constant_projection,constant_sentinel,constant_relay]
    exact ⟨hc.1,hout⟩

def TerminalDonor {n m : Nat} (L : Rows n m) : Prop :=
  ∃ c : Vec 4, ∃ s : F3, ∃ xs : Blocks 4 (stages m), ∃ x : Vec n,
    Signed c ∧ s ≠ .z ∧ BlocksSigned xs ∧ Signed x ∧ MarkedSigned (marked L c s xs x)

theorem terminal_iff_pinned {n m : Nat} (L : Rows n m) :
    TerminalDonor L ↔ PinnedDonor L := by
  constructor
  · rintro ⟨c,s,xs,x,hc,hs,hxs,hx,ho⟩
    have hout := ((marked_same_word L c s xs x hc hs hxs hx).1 ho).2
    cases s with
    | z => exact False.elim (hs rfl)
    | o => exact ⟨xs,x,hxs,hx,hout⟩
    | t =>
      refine ⟨scaleBlocks .t xs,scale .t x,(blocks_neg_signed xs).2 hxs,
        (signed_neg_iff x).2 hx,?_⟩
      have hneg := (output_neg_signed (physical L (constant4 .t) xs x)).2 hout
      rw [←physical_scale] at hneg
      exact hneg
  · rintro ⟨xs,x,hxs,hx,ho⟩
    have hc : Signed (constant4 .o) := constant_signed .o (by intro h; cases h)
    refine ⟨constant4 .o,.o,xs,x,hc,(by intro h; cases h),hxs,hx,?_⟩
    exact (marked_same_word L _ .o xs x hc (by intro h; cases h) hxs hx).2
      ⟨⟨rfl,rfl,rfl⟩,ho⟩

/-- All raw strict CNF inputs are tied to this one literal physical operator family. -/
theorem terminal_iff_CNFSAT (raw : BitString) :
    TerminalDonor (sourceMatrix raw) ↔ CNFSAT raw :=
  (terminal_iff_pinned _).trans (pinned_iff_CNFSAT raw)

end PNP.SignedTernary.Network

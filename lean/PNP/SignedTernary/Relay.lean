import PNP.SignedTernary.Gate

namespace PNP.SignedTernary.Relay
open PNP.SignedTernary.Field PNP.SignedTernary.Linear PNP.SignedTernary.Gate

@[reducible] def Blocks (width : Nat) : Nat → Type
  | 0 => Unit
  | k+1 => Vec width × Blocks width k

def BlocksSigned : {width k : Nat} → Blocks width k → Prop
  | _, 0, _ => True
  | _, _+1, xs => Signed xs.1 ∧ BlocksSigned xs.2

def blockNorm : {width k : Nat} → Blocks width k → F3
  | _, 0, _ => .z
  | _, _+1, xs => add (norm xs.1) (blockNorm xs.2)

def Uniform : {k : Nat} → Blocks 4 k → Prop
  | 0, _ => True
  | _+1, xs => (xs.1.2.1 = xs.1.1 ∧ xs.1.2.2.1 = xs.1.1 ∧
      xs.1.2.2.2.1 = xs.1.1) ∧ Uniform xs.2

def positive : (n : Nat) → Vec n
  | 0 => ()
  | n+1 => (F3.o,positive n)

theorem positive_signed (n : Nat) : Signed (positive n) := by
  induction n with
  | zero => exact True.intro
  | succ n ih => exact ⟨(by intro h; cases h),ih⟩

def signals (y : Vec 8) : Vec 3 := (y.1,(y.2.1,(y.2.2.1,())))

def nextLive (y : Vec 8) : Vec 4 :=
  v4 y.2.2.2.1 y.2.2.2.2.1 y.2.2.2.2.2.1 y.2.2.2.2.2.2.1

def bankPin (y : Vec 8) : F3 := y.2.2.2.2.2.2.2.1

def stage (c z : Vec 4) : Vec 8 := gate (join c z)

@[reducible] def Output (k : Nat) : Type := Blocks 3 k × (Vec 4 × Vec k)

def run : {k : Nat} → Vec 4 → Blocks 4 k → Output k
  | 0, c, _ => ((),(c,()))
  | _+1, c, xs =>
      let y := stage c xs.1
      let rest := run (nextLive y) xs.2
      ((signals y,rest.1),(rest.2.1,(bankPin y,rest.2.2)))

def outputNorm {k : Nat} (r : Output k) : F3 :=
  add (blockNorm r.1) (add (norm r.2.1) (norm r.2.2))

theorem local_forward (z : Vec 4) (hz : Signed z)
    (hv : Signed (signals (stage (positive 4) z))) :
    nextLive (stage (positive 4) z) = positive 4 ∧
    bankPin (stage (positive 4) z) = F3.o ∧
    (z.2.1 = z.1 ∧ z.2.2.1 = z.1 ∧ z.2.2.2.1 = z.1) := by
  rcases z with ⟨a,b,c,d,e⟩
  cases e
  have hs : VisibleSigned (gate (knobInput a b c d)) :=
    ⟨hv.1,hv.2.1,hv.2.2.1⟩
  have he := complete_four_to_seven a b c d hz.1 hz.2.1 hz.2.2.1 hz.2.2.2.1 hs
  have hq := visible_forces_equal a b c d hz.1 hz.2.1 hz.2.2.1 hz.2.2.2.1 hs
  change nextLive (gate (knobInput a b c d)) = positive 4 ∧
    bankPin (gate (knobInput a b c d)) = F3.o ∧ _
  rw [he.2.1]
  exact ⟨rfl,rfl,hq⟩

theorem local_backward (z : Vec 4) (hz : Signed z)
    (hu : z.2.1 = z.1 ∧ z.2.2.1 = z.1 ∧ z.2.2.2.1 = z.1) :
    Signed (signals (stage (positive 4) z)) ∧
    nextLive (stage (positive 4) z) = positive 4 ∧
    bankPin (stage (positive 4) z) = F3.o := by
  rcases z with ⟨a,b,c,d,e⟩
  cases e
  obtain ⟨hb,hc,hd⟩ := hu
  change b = a at hb
  change c = a at hc
  change d = a at hd
  subst b; subst c; subst d
  change Signed (signals (gate (commonKnob a))) ∧
    nextLive (gate (commonKnob a)) = positive 4 ∧
    bankPin (gate (commonKnob a)) = F3.o
  rw [common_knob_output]
  exact ⟨⟨hz.1,(by intro h; cases h),(by intro h; cases h),True.intro⟩,rfl,rfl⟩

theorem run_forward {k : Nat} (xs : Blocks 4 k) (hx : BlocksSigned xs)
    (hv : BlocksSigned (run (positive 4) xs).1) :
    Uniform xs ∧ (run (positive 4) xs).2.1 = positive 4 ∧
      (run (positive 4) xs).2.2 = positive k := by
  induction k with
  | zero => exact ⟨True.intro,rfl,rfl⟩
  | succ k ih =>
    have hs : Signed (signals (stage (positive 4) xs.1)) ∧
      BlocksSigned (run (nextLive (stage (positive 4) xs.1)) xs.2).1 := hv
    obtain ⟨hl,hb,hu⟩ := local_forward xs.1 hx.1 hs.1
    have hr : BlocksSigned (run (positive 4) xs.2).1 := by
      rw [hl] at hs
      exact hs.2
    obtain ⟨hrest,hfinal,hbank⟩ := ih xs.2 hx.2 hr
    refine ⟨⟨hu,hrest⟩,?_,?_⟩
    · simpa only [run,hl] using hfinal
    · change (bankPin (stage (positive 4) xs.1),
        (run (nextLive (stage (positive 4) xs.1)) xs.2).2.2) = (F3.o,positive k)
      rw [hl,hb,hbank]

theorem run_backward {k : Nat} (xs : Blocks 4 k) (hx : BlocksSigned xs)
    (hu : Uniform xs) :
    BlocksSigned (run (positive 4) xs).1 ∧
    (run (positive 4) xs).2.1 = positive 4 ∧
    (run (positive 4) xs).2.2 = positive k := by
  induction k with
  | zero => exact ⟨True.intro,rfl,rfl⟩
  | succ k ih =>
    obtain ⟨hs,hl,hb⟩ := local_backward xs.1 hx.1 hu.1
    obtain ⟨hr,hfinal,hbank⟩ := ih xs.2 hx.2 hu.2
    refine ⟨?_,?_,?_⟩
    · change Signed (signals (stage (positive 4) xs.1)) ∧
        BlocksSigned (run (nextLive (stage (positive 4) xs.1)) xs.2).1
      rw [hl]
      exact ⟨hs,hr⟩
    · simpa only [run,hl] using hfinal
    · change (bankPin (stage (positive 4) xs.1),
        (run (nextLive (stage (positive 4) xs.1)) xs.2).2.2) = (F3.o,positive k)
      rw [hl,hb,hbank]

def uniformDonor : {k : Nat} → Vec k → Blocks 4 k
  | 0, _ => ()
  | _+1, phases => (v4 phases.1 phases.1 phases.1 phases.1,uniformDonor phases.2)

theorem uniform_donor_signed {k : Nat} (phases : Vec k) (hp : Signed phases) :
    BlocksSigned (uniformDonor phases) := by
  induction k with
  | zero => exact True.intro
  | succ k ih => exact ⟨⟨hp.1,hp.1,hp.1,hp.1,True.intro⟩,ih phases.2 hp.2⟩

theorem uniform_donor_uniform {k : Nat} (phases : Vec k) :
    Uniform (uniformDonor phases) := by
  induction k with
  | zero => exact True.intro
  | succ k ih => exact ⟨⟨rfl,rfl,rfl⟩,ih phases.2⟩

theorem add_left_comm (a b c : F3) : add a (add b c) = add b (add a c) := by
  rw [← add_assoc,add_comm a b,add_assoc]

theorem split_gate_norm (y : Vec 8) :
    add (norm (signals y)) (add (norm (nextLive y)) (mul (bankPin y) (bankPin y))) =
      norm y := by
  rcases y with ⟨a,b,c,d,e,f,g,h,i⟩
  cases i
  simp only [signals,nextLive,bankPin,v4,norm,dot,add_zero,add_assoc]

theorem stage_norm (c z : Vec 4) :
    add (norm (signals (stage c z)))
      (add (norm (nextLive (stage c z))) (mul (bankPin (stage c z)) (bankPin (stage c z)))) =
      add (norm c) (norm z) := by
  rw [split_gate_norm]
  change norm (gate (join c z)) = _
  rw [gate_isometry,norm_join]

theorem output_norm_step {k : Nat} (c z : Vec 4) (xs : Blocks 4 k) :
    outputNorm (@run (k+1) c (z,xs)) =
      add (norm (signals (stage c z))) (add (mul (bankPin (stage c z)) (bankPin (stage c z)))
        (outputNorm (run (nextLive (stage c z)) xs))) := by
  simp only [outputNorm,run,blockNorm,norm,dot]
  simp only [add_assoc,add_comm,add_left_comm]

theorem run_norm {k : Nat} (c : Vec 4) (xs : Blocks 4 k) :
    outputNorm (run c xs) = add (norm c) (blockNorm xs) := by
  induction k generalizing c with
  | zero => simp only [outputNorm,run,blockNorm,norm,dot,zero_add,add_zero]
  | succ k ih =>
    rcases xs with ⟨z,xs⟩
    rw [output_norm_step,ih]
    have hreorder (a b c d : F3) :
        add a (add b (add c d)) = add (add a (add c b)) d := by
      simp only [add_comm,add_left_comm]
    rw [hreorder,stage_norm,add_assoc]
    rfl

end PNP.SignedTernary.Relay

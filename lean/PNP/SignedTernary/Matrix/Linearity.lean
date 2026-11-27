import PNP.SignedTernary.Network.Signed

set_option autoImplicit false

namespace PNP.SignedTernary.Encoding
open PNP.SignedTernary.Field PNP.SignedTernary.Linear PNP.SignedTernary.Gate PNP.SignedTernary.Relay PNP.SignedTernary.Marker PNP.SignedTernary.Network

theorem plus_comm_vec {n : Nat} (x y : Vec n) : plus x y = plus y x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [plus,add_comm,ih]

theorem plus_assoc_vec {n : Nat} (x y z : Vec n) : plus (plus x y) z = plus x (plus y z) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [plus,add_assoc,ih]

theorem plus_left_comm_vec {n : Nat} (x y z : Vec n) :
    plus x (plus y z) = plus y (plus x z) := by
  rw [←plus_assoc_vec,plus_comm_vec x y,plus_assoc_vec]

theorem plus_shuffle_vec {n : Nat} (a b c d : Vec n) :
    plus (plus a b) (plus c d) = plus (plus a c) (plus b d) := by
  simp only [plus_assoc_vec,plus_left_comm_vec]

theorem scale_add_scalar {n : Nat} (a b : F3) (x : Vec n) :
    scale (add a b) x = plus (scale a x) (scale b x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [scale,plus,add_mul,ih]

def plusBlocks {width : Nat} : {k : Nat} → Blocks width k → Blocks width k → Blocks width k
  | 0, _, _ => ()
  | _+1, x, y => (plus x.1 y.1,plusBlocks x.2 y.2)

def plusBanks {m : Nat} (x y : Banks m) : Banks m :=
  (plus x.1 y.1,(plus x.2.1 y.2.1,plus x.2.2 y.2.2))

def plusOutput {n m : Nat} (x y : PhysicalOutput n m) : PhysicalOutput n m :=
  (plusBlocks x.1 y.1,(plus x.2.1 y.2.1,
    (plus x.2.2.1 y.2.2.1,plusBanks x.2.2.2 y.2.2.2)))

theorem plus_join {n m : Nat} (a b : Vec n) (x y : Vec m) :
    join (plus a b) (plus x y) = plus (join a x) (join b y) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [join,plus,ih]

theorem stage_plus (a b c d : Vec 4) :
    stage (plus a b) (plus c d) = plus (stage a c) (stage b d) := by
  simp only [stage,plus_join,gate,applyRows_plus]

theorem signals_plus (x y : Vec 8) : signals (plus x y) = plus (signals x) (signals y) := rfl

theorem live_plus (x y : Vec 8) : nextLive (plus x y) = plus (nextLive x) (nextLive y) := rfl

theorem pin_plus (x y : Vec 8) : bankPin (plus x y) = add (bankPin x) (bankPin y) := rfl

theorem run_plus {k : Nat} (c d : Vec 4) (xs ys : Blocks 4 k) :
    run (plus c d) (plusBlocks xs ys) =
      (plusBlocks (run c xs).1 (run d ys).1,
        (plus (run c xs).2.1 (run d ys).2.1,plus (run c xs).2.2 (run d ys).2.2)) := by
  induction k generalizing c d with
  | zero => rfl
  | succ k ih =>
    simp only [run,plusBlocks,stage_plus,signals_plus,live_plus,pin_plus,ih]
    rfl

theorem splitBanks_plus (m : Nat) (x y : Vec (stages m)) :
    splitBanks m (plus x y) = plusBanks (splitBanks m x) (splitBanks m y) := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [stages,splitBanks,plus,ih,plusBanks]

theorem bankTotal_plus {m : Nat} (x y : Banks m) :
    bankTotal (plusBanks x y) = plus (bankTotal x) (bankTotal y) := by
  simp only [bankTotal,plusBanks,plus_assoc_vec,plus_left_comm_vec]

theorem shear_plus {n m : Nat} (R : Rows n m) (a b : Vec n) (x y : Banks m) :
    shear R (plus a b) (plusBanks x y) =
      (plus (shear R a x).1 (shear R b y).1,plusBanks (shear R a x).2 (shear R b y).2) := by
  simp only [shear]
  rw [bankTotal_plus]
  simp only [applyRows_plus,minus,scale_plus_vec,shiftBanks,plusBanks]
  simp only [plus_assoc_vec,plus_left_comm_vec]

theorem physical_plus {n m : Nat} (L : Rows n m) (c d : Vec 4)
    (xs ys : Blocks 4 (stages m)) (x y : Vec n) :
    physical L (plus c d) (plusBlocks xs ys) (plus x y) =
      plusOutput (physical L c xs x) (physical L d ys y) := by
  simp only [physical]
  rw [run_plus]
  simp only [splitBanks_plus]
  change (plusBlocks (run c xs).1 (run d ys).1,
    (plus (run c xs).2.1.2 (run d ys).2.1.2,
      shear (anchoredRows L) (plus ((run c xs).2.1.1,x) ((run d ys).2.1.1,y))
        (plusBanks (splitBanks m (run c xs).2.2) (splitBanks m (run d ys).2.2)))) = _
  rw [shear_plus]
  rfl

theorem project_plus (c d : Vec 4) : project (plus c d) = plus (project c) (project d) := by
  simp only [project,minus,dot_plus,scale_add_scalar,scale_plus_vec]
  exact plus_shuffle_vec _ _ _ _

theorem relay_plus (c d : Vec 4) (s tt : F3) :
    relay (plus c d) (add s tt) = plus (relay c s) (relay d tt) := by
  simp only [relay,dot_plus,neg_add]
  rw [add_shuffle,scale_add_scalar]
  exact plus_shuffle_vec _ _ _ _

theorem marked_plus {n m : Nat} (L : Rows n m) (c d : Vec 4) (s tt : F3)
    (xs ys : Blocks 4 (stages m)) (x y : Vec n) :
    marked L (plus c d) (add s tt) (plusBlocks xs ys) (plus x y) =
      (add (marked L c s xs x).1 (marked L d tt ys y).1,
        plusOutput (marked L c s xs x).2 (marked L d tt ys y).2) := by
  simp only [marked,project_plus,sentinel,dot_plus,relay_plus,physical_plus]

end PNP.SignedTernary.Encoding

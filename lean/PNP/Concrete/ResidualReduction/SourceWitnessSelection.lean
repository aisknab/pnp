import PNP.Concrete.ResidualReduction.SourceGlobalSelector

/-! Exact query-first selection for the existing global contraction step.
Construction can be postponed until after selection only because the chosen
query witness constructs successfully. In the line and plane branches this
uses the failed affine prelude; it is not a caller-supplied certificate.
This module establishes semantics, not a runtime bound or stopped-core solver. -/

namespace PNP.Concrete.ResidualReduction.SourceWitnessSelection
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceChain

structure Choice (n m : Nat) where
  weights : Point m
  direction : Point n
  normals : Option (Affine n × Affine n)

def affineChoice {n m : Nat} (w : Point m × Point n) : Choice n m := ⟨w.1,w.2,none⟩
def lineChoice {n m : Nat} (a : Affine n) (w : LineWitness n m) : Choice n m :=
  ⟨w.weights,w.direction,some (a,betaNormal w.beta)⟩
def planeChoice {n m : Nat} (p : Affine n × Affine n) (w : Point m × Point n) : Choice n m :=
  ⟨w.1,w.2,some p⟩

def lineQuery {n : Nat} (F : Family n) (a : Affine n) : Option (Choice n F.length) :=
  (sourceLineQuery F a).map (lineChoice a)
def planeQuery {n : Nat} (F : Family n) (p : Affine n × Affine n) : Option (Choice n F.length) :=
  (sourcePlaneQuery F p.1 p.2).map (planeChoice p)
def lineSearch {n : Nat} (F : Family n) (us : List (Affine n)) : Option (Choice n F.length) :=
  firstSome (lineQuery F) us
def planeSearch {n : Nat} (F : Family n) (ps : List (Affine n × Affine n)) : Option (Choice n F.length) :=
  firstSome (planeQuery F) ps

def choose {n : Nat} (F : Family n) : Option (Choice n F.length) :=
  match sourceAffineQuery F with
  | some w => some (affineChoice w)
  | none =>
    let us := sourceMenu F
    match lineSearch F us with
    | some w => some w
    | none => planeSearch F (planeMenu us)

def build {n : Nat} (F : Family (n+1)) (w : Choice (n+1) F.length) :
    Option (ConstructedStep n F.length) :=
  buildStep F w.weights w.direction w.normals

/-- Bind commutes with first-success search only when construction succeeds on
each query success in the searched list. No assertion is made without this
premise; the source-specific results below discharge it internally. -/
theorem firstSome_bind_exact {α β γ : Type} (f : α → Option β) (g : β → Option γ)
    (xs : List α) (total : ∀ a ∈ xs, ∀ b, f a = some b → ∃ c, g b = some c) :
    firstSome (fun a => (f a).bind g) xs = (firstSome f xs).bind g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases h : f a with
    | none =>
      have tail := ih (fun x hx b hb => total x (List.mem_cons_of_mem a hx) b hb)
      simpa only [firstSome,h,Option.bind] using tail
    | some b =>
      obtain ⟨c,hc⟩ := total a List.mem_cons_self b h
      simp only [firstSome,h,Option.bind,hc]

theorem affine_total {n : Nat} (F : Family (n+1)) (w : Point F.length × Point (n+1))
    (h : sourceAffineQuery F = some w) :
    ∃ s, build F (affineChoice w) = some s :=
  buildStep_affine_total F w (sourceAffineQuery_sound F w h)

theorem line_query_total {n : Nat} (F : Family (n+1)) (hn : sourceAffineQuery F = none)
    (a : Affine (n+1)) (w : Choice (n+1) F.length) (h : lineQuery F a = some w) :
    ∃ s, build F w = some s := by
  cases hq : sourceLineQuery F a with
  | none => simp only [lineQuery,hq,Option.map,reduceCtorEq] at h
  | some q =>
    have he : lineChoice a q = w := by simpa only [lineQuery,hq,Option.map,Option.some.injEq] using h
    subst w
    exact buildStep_line_total F hn a q (sourceLineQuery_sound F a q hq)

theorem plane_query_total {n : Nat} (F : Family (n+1)) (hn : sourceAffineQuery F = none)
    (p : Affine (n+1) × Affine (n+1)) (w : Choice (n+1) F.length)
    (h : planeQuery F p = some w) : ∃ s, build F w = some s := by
  cases hq : sourcePlaneQuery F p.1 p.2 with
  | none => simp only [planeQuery,hq,Option.map,reduceCtorEq] at h
  | some q =>
    have he : planeChoice p q = w := by simpa only [planeQuery,hq,Option.map,Option.some.injEq] using h
    subst w
    exact buildStep_plane_total F hn p.1 p.2 q (sourcePlaneQuery_sound F p.1 p.2 q hq)

theorem line_search_exact {n : Nat} (F : Family (n+1)) (hn : sourceAffineQuery F = none)
    (us : List (Affine (n+1))) :
    firstSome (lineCandidate F) us = (lineSearch F us).bind (build F) := by
  have functions : lineCandidate F = fun a => (lineQuery F a).bind (build F) := by
    funext a
    cases h : sourceLineQuery F a <;>
      simp only [lineCandidate,lineQuery,h,Option.map,Option.bind,build,lineChoice]
  rw [functions]
  exact firstSome_bind_exact (lineQuery F) (build F) us
    (fun a _ w h => line_query_total F hn a w h)

theorem plane_search_exact {n : Nat} (F : Family (n+1)) (hn : sourceAffineQuery F = none)
    (ps : List (Affine (n+1) × Affine (n+1))) :
    firstSome (planeCandidate F) ps = (planeSearch F ps).bind (build F) := by
  have functions : planeCandidate F = fun p => (planeQuery F p).bind (build F) := by
    funext p
    cases h : sourcePlaneQuery F p.1 p.2 <;>
      simp only [planeCandidate,planeQuery,h,Option.map,Option.bind,build,planeChoice]
  rw [functions]
  exact firstSome_bind_exact (planeQuery F) (build F) ps
    (fun p _ w h => plane_query_total F hn p w h)

theorem choose_total {n : Nat} (F : Family (n+1)) (w : Choice (n+1) F.length)
    (h : choose F = some w) : ∃ s, build F w = some s := by
  cases ha : sourceAffineQuery F with
  | some q =>
    have he : affineChoice q = w := by simpa only [choose,ha,Option.some.injEq] using h
    subst w
    exact affine_total F q ha
  | none =>
    cases hl : lineSearch F (sourceMenu F) with
    | some q =>
      have he : q = w := by simpa only [choose,ha,hl,Option.some.injEq] using h
      subst w
      obtain ⟨a,_,hq⟩ := firstSome_some (lineQuery F) (sourceMenu F) q hl
      exact line_query_total F ha a q hq
    | none =>
      have hp : planeSearch F (planeMenu (sourceMenu F)) = some w := by
        simpa only [choose,ha,hl] using h
      obtain ⟨p,_,hq⟩ := firstSome_some (planeQuery F) (planeMenu (sourceMenu F)) w hp
      exact plane_query_total F ha p w hq

/-- Literal equality with the existing selector, not merely equisatisfiability
or the existence of some possibly different successful contraction. -/
theorem global_exact {n : Nat} (F : Family (n+1)) :
    globalStep F = (choose F).bind (build F) := by
  cases ha : sourceAffineQuery F with
  | some q => simp only [globalStep,choose,ha,Option.bind,build,affineChoice]
  | none =>
    have lines := line_search_exact F ha (sourceMenu F)
    cases hl : lineSearch F (sourceMenu F) with
    | none =>
      simp only [hl,Option.bind] at lines
      simpa only [globalStep,choose,ha,lines,hl,Option.bind] using
        plane_search_exact F ha (planeMenu (sourceMenu F))
    | some w =>
      obtain ⟨a,_,hq⟩ := firstSome_some (lineQuery F) (sourceMenu F) w hl
      obtain ⟨s,hs⟩ := line_query_total F ha a w hq
      simp only [hl,Option.bind,hs] at lines
      simp only [globalStep,choose,ha,lines,hl,Option.bind,hs]

theorem choose_none_iff {n : Nat} (F : Family (n+1)) :
    choose F = none ↔ globalStep F = none := by
  rw [global_exact]
  cases hc : choose F with
  | none => simp only [Option.bind]
  | some w =>
    obtain ⟨s,hs⟩ := choose_total F w hc
    simp only [Option.bind,hs,reduceCtorEq]

theorem selected_step {n : Nat} (F : Family (n+1)) (w : Choice (n+1) F.length)
    (h : choose F = some w) :
    ∃ s, build F w = some s ∧ globalStep F = some s ∧ StepSound F s := by
  obtain ⟨s,hs⟩ := choose_total F w h
  have hg : globalStep F = some s := by rw [global_exact,h]; exact hs
  exact ⟨s,hs,hg,globalStep_sound F s hg⟩

end PNP.Concrete.ResidualReduction.SourceWitnessSelection

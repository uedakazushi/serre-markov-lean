import Lean
import Init.Data.Int.Gcd

/-!
# Four dihedral reflections with identity product

The reflection labelled by `n` satisfies `r_a r_b r_a = r_(2a-b)`.
This file proves the integer-label Hurwitz reduction used in the degenerate
classification. No Coxeter, geometric, or classification theorem is assumed.
The conclusion provides a finite list of actual adjacent Hurwitz moves.
-/

namespace SerreMarkov.Dihedral

@[ext] structure Quad where
  n1 : Int
  n2 : Int
  n3 : Int
  n4 : Int
  deriving DecidableEq, Repr

inductive Move where
  | m1 | m2 | m3 | i1 | i2 | i3
  deriving DecidableEq, Repr

def step : Move → Quad → Quad
  | .m1, q => ⟨2*q.n1-q.n2, q.n1, q.n3, q.n4⟩
  | .m2, q => ⟨q.n1, 2*q.n2-q.n3, q.n2, q.n4⟩
  | .m3, q => ⟨q.n1, q.n2, 2*q.n3-q.n4, q.n3⟩
  | .i1, q => ⟨q.n2, 2*q.n2-q.n1, q.n3, q.n4⟩
  | .i2, q => ⟨q.n1, q.n3, 2*q.n3-q.n2, q.n4⟩
  | .i3, q => ⟨q.n1, q.n2, q.n4, 2*q.n4-q.n3⟩

def applyWord (q : Quad) : List Move → Quad
  | [] => q
  | g :: gs => applyWord (step g q) gs

def Reachable (q q' : Quad) : Prop := ∃ word, applyWord q word=q'

theorem reachable_refl (q : Quad) : Reachable q q := ⟨[], rfl⟩

theorem applyWord_append (q : Quad) (u v : List Move) :
    applyWord q (u++v)=applyWord (applyWord q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons g gs ih => exact ih (step g q)

theorem reachable_trans {q q' q'' : Quad} (h : Reachable q q')
    (h' : Reachable q' q'') : Reachable q q'' := by
  rcases h with ⟨u, hu⟩
  rcases h' with ⟨v, hv⟩
  refine ⟨u++v, ?_⟩
  rw [applyWord_append, hu, hv]

def labels (a u v : Int) : Quad := ⟨a, a+u, a+u+v, a+v⟩

theorem labels_mu1 (a u v : Int) :
    step .m1 (labels a u v)=labels (a-u) u (u+v) := by
  ext <;> simp [step, labels] <;> grind

theorem labels_inv1 (a u v : Int) :
    step .i1 (labels a u v)=labels (a+u) u (v-u) := by
  ext <;> simp [step, labels] <;> grind

theorem labels_mu2 (a u v : Int) :
    step .m2 (labels a u v)=labels a (u-v) v := by
  ext <;> simp [step, labels] <;> grind

theorem labels_inv2 (a u v : Int) :
    step .i2 (labels a u v)=labels a (u+v) v := by
  ext <;> simp [step, labels] <;> grind

/-- The four elementary Euclidean operations, closed under finite composition. -/
inductive PairReach : Int → Int → Int → Int → Prop where
  | refl (u v) : PairReach u v u v
  | addUpper (u v) : PairReach u v (u+v) v
  | subUpper (u v) : PairReach u v (u-v) v
  | addLower (u v) : PairReach u v u (u+v)
  | subLower (u v) : PairReach u v u (v-u)
  | trans {u v a b c d} : PairReach u v a b → PairReach a b c d → PairReach u v c d

theorem pairReach_lift {u v u' v' : Int} (h : PairReach u v u' v') :
    ∀ a : Int, ∃ a' : Int, Reachable (labels a u v) (labels a' u' v') := by
  induction h with
  | refl u v => intro a; exact ⟨a, reachable_refl _⟩
  | addUpper u v => intro a; exact ⟨a, [.i2], labels_inv2 a u v⟩
  | subUpper u v => intro a; exact ⟨a, [.m2], labels_mu2 a u v⟩
  | addLower u v => intro a; exact ⟨a-u, [.m1], labels_mu1 a u v⟩
  | subLower u v => intro a; exact ⟨a+u, [.i1], labels_inv1 a u v⟩
  | trans h h' ih ih' =>
    intro a
    obtain ⟨b, hb⟩ := ih a
    obtain ⟨c, hc⟩ := ih' b
    exact ⟨c, reachable_trans hb hc⟩

theorem pairReach_rotate (u v : Int) : PairReach u v v (-u) := by
  have h1 := PairReach.addUpper u v
  have h2 := PairReach.subLower (u+v) v
  have h3 := PairReach.addUpper (u+v) (-u)
  have heq2 : v-(u+v) = -u := by grind
  have heq3 : u+v+(-u) = v := by grind
  rw [heq2] at h2
  rw [heq3] at h3
  exact .trans (.trans h1 h2) h3

theorem pairReach_negate (u v : Int) : PairReach u v (-u) (-v) :=
  .trans (pairReach_rotate u v) (pairReach_rotate v (-u))

theorem pairReach_upper_nat (u v : Int) (n : Nat) : PairReach u v (u+(n:Int)*v) v := by
  induction n with
  | zero => simpa using PairReach.refl u v
  | succ n ih =>
    have h := PairReach.trans ih (PairReach.addUpper (u+(n:Int)*v) v)
    have heq : u+(n:Int)*v+v = u+((n+1:Nat):Int)*v := by grind
    rw [heq] at h
    exact h

theorem pairReach_upper_nat_neg (u v : Int) (n : Nat) : PairReach u v (u-(n:Int)*v) v := by
  induction n with
  | zero => simpa using PairReach.refl u v
  | succ n ih =>
    have h := PairReach.trans ih (PairReach.subUpper (u-(n:Int)*v) v)
    have heq : u-(n:Int)*v-v = u-((n+1:Nat):Int)*v := by grind
    rw [heq] at h
    exact h

theorem pairReach_upper_int (u v n : Int) : PairReach u v (u+n*v) v := by
  cases n with
  | ofNat n => exact pairReach_upper_nat u v n
  | negSucc n =>
    have h := pairReach_upper_nat_neg u v (n+1)
    have heq : u-((n+1:Nat):Int)*v = u+(Int.negSucc n)*v := by
      simp only [Int.negSucc_eq, Int.natCast_add, Int.natCast_one]
      grind
    rw [heq] at h
    exact h

theorem pairReach_upper_mod (u v : Int) : PairReach u v (u%v) v := by
  have h := pairReach_upper_int u v (-(u/v))
  have heq : u+(-(u/v))*v = u%v := by
    have hd := Int.emod_add_mul_ediv u v
    grind
  rwa [heq] at h

/-- Euclid's algorithm terminates because the remainder's absolute value drops. -/
theorem pairReach_reduce (u v : Int) :
    ∃ g : Int, 0 ≤ g ∧ PairReach u v g 0 := by
  have hmain : ∀ n : Nat, ∀ u v : Int, v.natAbs=n →
      ∃ g : Int, 0 ≤ g ∧ PairReach u v g 0 := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro u v hv
      by_cases hz : v=0
      · subst v
        by_cases hu : 0 ≤ u
        · exact ⟨u, hu, PairReach.refl _ _⟩
        · exact ⟨-u, by omega, by simpa using pairReach_negate u 0⟩
      · let r := u%v
        have hr0 : 0 ≤ r := Int.emod_nonneg u hz
        have hrlt : r < (v.natAbs:Int) := Int.emod_lt u hz
        have hrabs : r.natAbs < n := by
          have habs : (r.natAbs:Int)=r := Int.natAbs_of_nonneg hr0
          omega
        obtain ⟨g, hg, hred⟩ := ih r.natAbs hrabs v (-r) (by simp)
        refine ⟨g, hg, PairReach.trans ?_ hred⟩
        exact .trans (pairReach_upper_mod u v) (pairReach_rotate r v)
  exact hmain v.natAbs u v rfl

theorem pairReach_gcd {u v u' v' : Int} (h : PairReach u v u' v') :
    Int.gcd u' v' = Int.gcd u v := by
  induction h with
  | refl => rfl
  | addUpper u v => simp
  | subUpper u v => simp
  | addLower u v => simp
  | subLower u v => simp
  | trans h h' ih ih' => exact ih'.trans ih

theorem pairReach_reduce_gcd (u v : Int) :
    PairReach u v (Int.gcd u v:Int) 0 := by
  obtain ⟨g, hg, h⟩ := pairReach_reduce u v
  have hd := pairReach_gcd h
  have heq : g=(Int.gcd u v:Int) := by
    have habs : (g.natAbs:Int)=g := Int.natAbs_of_nonneg hg
    simp only [Int.gcd_zero] at hd
    omega
  rwa [heq] at h

/-- Four integer-labelled reflections of product one have the stated Hurwitz form. -/
theorem identity_product_hurwitz (q : Quad)
    (hq : q.n1-q.n2+q.n3-q.n4=0) :
    ∃ a g : Int, 0 ≤ g ∧ Reachable q ⟨a, a+g, a+g, a⟩ := by
  let u := q.n2-q.n1
  let v := q.n3-q.n2
  have hqeq : q=labels q.n1 u v := by
    ext <;> simp [labels, u, v] <;> omega
  obtain ⟨g, hg, hred⟩ := pairReach_reduce u v
  obtain ⟨a, ha⟩ := pairReach_lift hred q.n1
  refine ⟨a, g, hg, ?_⟩
  rw [hqeq]
  simpa only [labels, Int.add_zero] using ha

end SerreMarkov.Dihedral

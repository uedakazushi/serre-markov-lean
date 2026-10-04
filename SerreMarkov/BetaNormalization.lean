import SerreMarkov.Census
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! # Relabeling every fixed-point-free cubic permutation on twelve vertices -/

namespace SerreMarkov.IndexTwelve

open Equiv.Perm

/-- An order-three function has an explicit two-step inverse. -/
def cubicPerm (b : VertexMap) (hb : ∀ i, b (b (b i)) = i) : Equiv.Perm Vertex :=
  { toFun := b
    invFun := fun i => b (b i)
    left_inv := hb
    right_inv := hb }

theorem cubicPerm_pow_three (b : VertexMap) (hb : ∀ i, b (b (b i)) = i) :
    cubicPerm b hb ^ 3 = 1 := by
  ext i
  simpa [pow_succ, Equiv.Perm.mul_apply, cubicPerm] using congrArg Fin.val (hb i)

theorem cubic_fixed_point_free_cycleType (b : VertexMap)
    (hb : ∀ i, b (b (b i)) = i) (hfree : ∀ i, b i ≠ i) :
    (cubicPerm b hb).cycleType = Multiset.replicate 4 3 := by
  let p := cubicPerm b hb
  have hp : p ^ 3 = 1 := cubicPerm_pow_three b hb
  have hcycles : ∀ n ∈ p.cycleType, n = 3 :=
    (Equiv.Perm.pow_prime_eq_one_iff (p := 3)).mp hp
  have hrepl : p.cycleType = Multiset.replicate p.cycleType.card 3 :=
    Multiset.eq_replicate_card.mpr hcycles
  have hsupport : p.support = Finset.univ := by
    ext i
    simp only [Finset.mem_univ, iff_true, Equiv.Perm.mem_support]
    exact hfree i
  have hsum : p.cycleType.sum = 12 := by
    rw [Equiv.Perm.sum_cycleType, hsupport]
    decide
  rw [hrepl, Multiset.sum_replicate] at hsum
  have hcard : p.cycleType.card = 4 := by
    simp only [nsmul_eq_mul, Nat.cast_id] at hsum
    omega
  simpa only [hcard] using hrepl

theorem beta_normalization (b : VertexMap)
    (hb : ∀ i, b (b (b i)) = i) (hfree : ∀ i, b i ≠ i) :
    ∃ c : Equiv.Perm Vertex, ∀ i, c (b i) = beta (c i) := by
  have htype : (cubicPerm b hb).cycleType = betaPerm.cycleType := by
    rw [cubic_fixed_point_free_cycleType b hb hfree]
    exact (cubic_fixed_point_free_cycleType beta beta_order_three beta_fixed_point_free).symm
  obtain ⟨c, hc⟩ := isConj_iff.mp (Equiv.Perm.isConj_of_cycleType_eq htype)
  refine ⟨c, ?_⟩
  intro i
  have hi := congrArg (fun p : Equiv.Perm Vertex => p (c i)) hc
  simpa [Equiv.Perm.mul_apply, cubicPerm, betaPerm] using hi

/-- The same relabeling transports the companion involution. -/
theorem beta_normalization_with_involution (a b : VertexMap)
    (ha : ∀ i, a (a i) = i) (hafree : ∀ i, a i ≠ i)
    (hb : ∀ i, b (b (b i)) = i) (hbfree : ∀ i, b i ≠ i) :
    ∃ (c : Equiv.Perm Vertex) (a' : VertexMap),
      (∀ i, c (b i) = beta (c i)) ∧
      (∀ i, c (a i) = a' (c i)) ∧
      (∀ i, a' (a' i) = i) ∧ (∀ i, a' i ≠ i) := by
  obtain ⟨c, hc⟩ := beta_normalization b hb hbfree
  let a' : VertexMap := fun i => c (a (c.symm i))
  refine ⟨c, a', hc, ?_, ?_, ?_⟩
  · intro i
    simp [a']
  · intro i
    simp [a', ha]
  · intro i h
    have he : a (c.symm i) = c.symm i := by
      apply c.injective
      simpa [a'] using h
    exact hafree (c.symm i) he

def evalPairWord (a b : VertexMap) : List Bool → Vertex → Vertex
  | [], i => i
  | bit :: word, i => evalPairWord a b word (if bit then b i else a i)

def PairTransitive (a b : VertexMap) : Prop :=
  ∀ x y, ∃ word, evalPairWord a b word x = y

theorem evalPairWord_beta (a : VertexMap) (word : List Bool) (i : Vertex) :
    evalPairWord a beta word i = evalWord a word i := by
  induction word generalizing i with
  | nil => rfl
  | cons bit word ih =>
    change evalPairWord a beta word (if bit then beta i else a i) = _
    rw [ih]
    rfl

theorem evalPairWord_intertwine {a b a' b' : VertexMap} (c : Equiv.Perm Vertex)
    (ha : ∀ i, c (a i) = a' (c i)) (hb : ∀ i, c (b i) = b' (c i))
    (word : List Bool) (i : Vertex) :
    c (evalPairWord a b word i) = evalPairWord a' b' word (c i) := by
  induction word generalizing i with
  | nil => rfl
  | cons bit word ih =>
    cases bit <;> simp [evalPairWord, ih, ha, hb]

theorem pairTransitive_transport {a b a' b' : VertexMap} (c : Equiv.Perm Vertex)
    (ha : ∀ i, c (a i) = a' (c i)) (hb : ∀ i, c (b i) = b' (c i))
    (h : PairTransitive a b) : PairTransitive a' b' := by
  intro x y
  obtain ⟨word, hw⟩ := h (c.symm x) (c.symm y)
  refine ⟨word, ?_⟩
  have he := congrArg c hw
  rw [evalPairWord_intertwine c ha hb] at he
  simpa using he

theorem pairTransitive_beta_iff (a : VertexMap) :
    PairTransitive a beta ↔ TransitivePair a := by
  simp only [PairTransitive, TransitivePair, Reachable, evalPairWord_beta]

theorem iterate_intertwine {p q : VertexMap} (c : Equiv.Perm Vertex)
    (h : ∀ i, c (p i) = q (c i)) (n : ℕ) (i : Vertex) :
    c ((p^[n]) i) = (q^[n]) (c i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h, ih]

theorem atMostTwoCycles_transport {p q : VertexMap} (c : Equiv.Perm Vertex)
    (h : ∀ i, c (p i) = q (c i)) (hp : AtMostTwoCycles p) : AtMostTwoCycles q := by
  obtain ⟨x, y, hxy⟩ := hp
  refine ⟨c x, c y, ?_⟩
  intro z
  rcases hxy (c.symm z) with ⟨n, hn⟩ | ⟨n, hn⟩
  · left
    refine ⟨n, ?_⟩
    rw [← iterate_intertwine c h, hn]
    simp
  · right
    refine ⟨n, ?_⟩
    rw [← iterate_intertwine c h, hn]
    simp

/-- Relabeling preserves both hypotheses used by the complete finite census. -/
theorem beta_normalization_census_hypotheses (a b : VertexMap)
    (ha : ∀ i, a (a i) = i) (hafree : ∀ i, a i ≠ i)
    (hb : ∀ i, b (b (b i)) = i) (hbfree : ∀ i, b i ≠ i)
    (ht : PairTransitive a b) (htwo : AtMostTwoCycles (fun i => a (b i))) :
    ∃ (c : Equiv.Perm Vertex) (a' : VertexMap),
      (∀ i, c (b i) = beta (c i)) ∧
      (∀ i, c (a i) = a' (c i)) ∧
      (∀ i, a' (a' i) = i) ∧ (∀ i, a' i ≠ i) ∧
      TransitivePair a' ∧ AtMostTwoCycles (cusp a') := by
  obtain ⟨c, a', hcb, hca, ha', hafree'⟩ :=
    beta_normalization_with_involution a b ha hafree hb hbfree
  refine ⟨c, a', hcb, hca, ha', hafree', ?_, ?_⟩
  · exact (pairTransitive_beta_iff a').mp (pairTransitive_transport c hca hcb ht)
  · apply atMostTwoCycles_transport c _ htwo
    intro i
    rw [hca, hcb]
    rfl

end SerreMarkov.IndexTwelve

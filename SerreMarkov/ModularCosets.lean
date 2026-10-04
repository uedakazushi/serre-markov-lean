import SerreMarkov.BetaNormalization
import SerreMarkov.ArbitraryBetaCensus
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Index

/-!
# Cosets of the abstract two-generator modular presentation

This file uses the abstract presentation `s² = t³ = 1`. It does not identify
this presented group with `PSL₂(ℤ)`. Involutive and cubic permutation data give
an actual group homomorphism and action; word transitivity proves index twelve.
-/

namespace SerreMarkov.ModularCosets

open SerreMarkov.IndexTwelve

def relations : Set (FreeGroup Bool) :=
  {FreeGroup.of false ^ 2, FreeGroup.of true ^ 3}

abbrev AbstractGroup := PresentedGroup relations

def s : AbstractGroup := PresentedGroup.of false
def t : AbstractGroup := PresentedGroup.of true

theorem s_square : s ^ 2 = 1 := by
  change (PresentedGroup.mk relations (FreeGroup.of false)) ^ 2 = 1
  rw [← map_pow]
  exact PresentedGroup.one_of_mem (by simp [relations])

theorem t_cube : t ^ 3 = 1 := by
  change (PresentedGroup.mk relations (FreeGroup.of true)) ^ 3 = 1
  rw [← map_pow]
  exact PresentedGroup.one_of_mem (by simp [relations])

theorem involutionPerm_square (a : VertexMap) (ha : ∀ i, a (a i) = i) :
    involutionPerm a ha ^ 2 = 1 := by
  ext i
  simpa [pow_two, Equiv.Perm.mul_apply, involutionPerm] using congrArg Fin.val (ha i)

def pairPerms (a b : VertexMap) (ha : ∀ i, a (a i) = i)
    (hb : ∀ i, b (b (b i)) = i) (bit : Bool) : Equiv.Perm Vertex :=
  if bit then cubicPerm b hb else involutionPerm a ha

theorem pairPerms_relations (a b : VertexMap) (ha : ∀ i, a (a i) = i)
    (hb : ∀ i, b (b (b i)) = i) :
    ∀ r ∈ relations, FreeGroup.lift (pairPerms a b ha hb) r = 1 := by
  intro r hr
  simp only [relations, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl
  · simpa [map_pow, pairPerms] using involutionPerm_square a ha
  · simpa [map_pow, pairPerms] using cubicPerm_pow_three b hb

def pairHom (a b : VertexMap) (ha : ∀ i, a (a i) = i)
    (hb : ∀ i, b (b (b i)) = i) : AbstractGroup →* Equiv.Perm Vertex :=
  PresentedGroup.toGroup (pairPerms_relations a b ha hb)

@[simp] theorem pairHom_s (a b : VertexMap) (ha : ∀ i, a (a i) = i)
    (hb : ∀ i, b (b (b i)) = i) : pairHom a b ha hb s = involutionPerm a ha := by
  simp [pairHom, s, pairPerms]

@[simp] theorem pairHom_t (a b : VertexMap) (ha : ∀ i, a (a i) = i)
    (hb : ∀ i, b (b (b i)) = i) : pairHom a b ha hb t = cubicPerm b hb := by
  simp [pairHom, t, pairPerms]

def groupWord : List Bool → AbstractGroup
  | [] => 1
  | bit :: word => groupWord word * (if bit then t else s)

theorem pairHom_word (a b : VertexMap) (ha : ∀ i, a (a i) = i)
    (hb : ∀ i, b (b (b i)) = i) (word : List Bool) (x : Vertex) :
    pairHom a b ha hb (groupWord word) x = evalPairWord a b word x := by
  induction word generalizing x with
  | nil => simp [groupWord, evalPairWord]
  | cons bit word ih =>
      cases bit
      · simpa [groupWord, map_mul, Equiv.Perm.mul_apply, evalPairWord,
          involutionPerm] using ih (a x)
      · simpa [groupWord, map_mul, Equiv.Perm.mul_apply, evalPairWord,
          cubicPerm] using ih (b x)

def pairAction (a b : VertexMap) (ha : ∀ i, a (a i) = i)
    (hb : ∀ i, b (b (b i)) = i) : MulAction AbstractGroup Vertex :=
  MulAction.compHom Vertex (pairHom a b ha hb)

def pairStabilizer (a b : VertexMap) (ha : ∀ i, a (a i) = i)
    (hb : ∀ i, b (b (b i)) = i) (x : Vertex) : Subgroup AbstractGroup :=
  letI := pairAction a b ha hb
  MulAction.stabilizer AbstractGroup x

theorem pairAction_pretransitive (a b : VertexMap) (ha : ∀ i, a (a i) = i)
    (hb : ∀ i, b (b (b i)) = i) (ht : PairTransitive a b) :
    letI := pairAction a b ha hb
    MulAction.IsPretransitive AbstractGroup Vertex := by
  letI := pairAction a b ha hb
  refine ⟨?_⟩
  intro x y
  obtain ⟨word, hword⟩ := ht x y
  refine ⟨groupWord word, ?_⟩
  change pairHom a b ha hb (groupWord word) x = y
  rw [pairHom_word, hword]

/-- Actual stabilizers, not an assumed subgroup classification, have index 12. -/
theorem pairStabilizer_index (a b : VertexMap) (ha : ∀ i, a (a i) = i)
    (hb : ∀ i, b (b (b i)) = i) (ht : PairTransitive a b) (x : Vertex) :
    (pairStabilizer a b ha hb x).index = 12 := by
  letI := pairAction a b ha hb
  letI := pairAction_pretransitive a b ha hb ht
  change (MulAction.stabilizer AbstractGroup x).index = 12
  rw [MulAction.index_stabilizer_of_transitive]
  simp

/-- The cosets of the stabilizer are exactly the twelve original vertices. -/
noncomputable def pairCosetEquiv (a b : VertexMap) (ha : ∀ i, a (a i) = i)
    (hb : ∀ i, b (b (b i)) = i) (ht : PairTransitive a b) (x : Vertex) :
    (AbstractGroup ⧸ pairStabilizer a b ha hb x) ≃ Vertex := by
  letI := pairAction a b ha hb
  refine Equiv.ofBijective (MulAction.ofQuotientStabilizer AbstractGroup x)
    ⟨MulAction.injective_ofQuotientStabilizer AbstractGroup x, ?_⟩
  intro y
  obtain ⟨word, hword⟩ := ht x y
  refine ⟨QuotientGroup.mk (groupWord word), ?_⟩
  change pairHom a b ha hb (groupWord word) x = y
  rw [pairHom_word, hword]

@[simp] theorem pairCosetEquiv_mk (a b : VertexMap) (ha : ∀ i, a (a i) = i)
    (hb : ∀ i, b (b (b i)) = i) (ht : PairTransitive a b) (x : Vertex)
    (g : AbstractGroup) :
    pairCosetEquiv a b ha hb ht x (QuotientGroup.mk g) = pairHom a b ha hb g x := rfl

theorem pairCosetEquiv_smul (a b : VertexMap) (ha : ∀ i, a (a i) = i)
    (hb : ∀ i, b (b (b i)) = i) (ht : PairTransitive a b) (x : Vertex)
    (g : AbstractGroup) (q : AbstractGroup ⧸ pairStabilizer a b ha hb x) :
    pairCosetEquiv a b ha hb ht x (g • q) =
      pairHom a b ha hb g (pairCosetEquiv a b ha hb ht x q) := by
  letI := pairAction a b ha hb
  exact MulAction.ofQuotientStabilizer_smul AbstractGroup x g q

theorem pairCosetEquiv_s (a b : VertexMap) (ha : ∀ i, a (a i) = i)
    (hb : ∀ i, b (b (b i)) = i) (ht : PairTransitive a b) (x : Vertex)
    (q : AbstractGroup ⧸ pairStabilizer a b ha hb x) :
    pairCosetEquiv a b ha hb ht x (s • q) = a (pairCosetEquiv a b ha hb ht x q) := by
  rw [pairCosetEquiv_smul, pairHom_s]
  rfl

theorem pairCosetEquiv_t (a b : VertexMap) (ha : ∀ i, a (a i) = i)
    (hb : ∀ i, b (b (b i)) = i) (ht : PairTransitive a b) (x : Vertex)
    (q : AbstractGroup ⧸ pairStabilizer a b ha hb x) :
    pairCosetEquiv a b ha hb ht x (t • q) = b (pairCosetEquiv a b ha hb ht x q) := by
  rw [pairCosetEquiv_smul, pairHom_t]
  rfl

theorem pairHom_intertwines {a b a' b' : VertexMap}
    (ha : ∀ i, a (a i) = i) (hb : ∀ i, b (b (b i)) = i)
    (ha' : ∀ i, a' (a' i) = i) (hb' : ∀ i, b' (b' (b' i)) = i)
    (c : Equiv.Perm Vertex) (hca : ∀ i, c (a i) = a' (c i))
    (hcb : ∀ i, c (b i) = b' (c i)) (g : AbstractGroup) (i : Vertex) :
    c (pairHom a b ha hb g i) = pairHom a' b' ha' hb' g (c i) := by
  have hh : (MulAut.conj c).toMonoidHom.comp (pairHom a b ha hb) =
      pairHom a' b' ha' hb' := by
    apply PresentedGroup.ext
    intro bit
    cases bit
    · change (MulAut.conj c) (pairHom a b ha hb s) = pairHom a' b' ha' hb' s
      rw [pairHom_s, pairHom_s]
      apply Equiv.ext
      intro j
      change c (a (c.symm j)) = a' j
      simpa using hca (c.symm j)
    · change (MulAut.conj c) (pairHom a b ha hb t) = pairHom a' b' ha' hb' t
      rw [pairHom_t, pairHom_t]
      apply Equiv.ext
      intro j
      change c (b (c.symm j)) = b' j
      simpa using hcb (c.symm j)
  have hg := congrArg (fun f : AbstractGroup →* Equiv.Perm Vertex => f g) hh
  have hc : c * pairHom a b ha hb g * c⁻¹ = pairHom a' b' ha' hb' g := hg
  calc
    c (pairHom a b ha hb g i) =
        (c * pairHom a b ha hb g * c⁻¹) (c i) := by simp
    _ = pairHom a' b' ha' hb' g (c i) := congrArg (fun p : Equiv.Perm Vertex => p (c i)) hc

theorem pairStabilizer_eq_of_intertwining {a b a' b' : VertexMap}
    (ha : ∀ i, a (a i) = i) (hb : ∀ i, b (b (b i)) = i)
    (ha' : ∀ i, a' (a' i) = i) (hb' : ∀ i, b' (b' (b' i)) = i)
    (c : Equiv.Perm Vertex) (hca : ∀ i, c (a i) = a' (c i))
    (hcb : ∀ i, c (b i) = b' (c i)) (x : Vertex) :
    pairStabilizer a b ha hb x = pairStabilizer a' b' ha' hb' (c x) := by
  ext g
  change (pairHom a b ha hb g x = x) ↔
    (pairHom a' b' ha' hb' g (c x) = c x)
  constructor
  · intro h
    rw [← pairHom_intertwines ha hb ha' hb' c hca hcb, h]
  · intro h
    apply c.injective
    rw [pairHom_intertwines ha hb ha' hb' c hca hcb, h]

theorem conjugate_pairs_conjugate_stabilizers {a b a' b' : VertexMap}
    (ha : ∀ i, a (a i) = i) (hb : ∀ i, b (b (b i)) = i)
    (ha' : ∀ i, a' (a' i) = i) (hb' : ∀ i, b' (b' (b' i)) = i)
    (ht' : PairTransitive a' b') (c : Equiv.Perm Vertex)
    (hca : ∀ i, c (a i) = a' (c i)) (hcb : ∀ i, c (b i) = b' (c i))
    (x y : Vertex) :
    ∃ g : AbstractGroup, pairStabilizer a b ha hb x =
      (pairStabilizer a' b' ha' hb' y).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨word, hw⟩ := ht' y (c x)
  letI := pairAction a' b' ha' hb'
  have hg : groupWord word • y = c x := by
    change pairHom a' b' ha' hb' (groupWord word) y = c x
    rw [pairHom_word, hw]
  refine ⟨groupWord word, ?_⟩
  rw [pairStabilizer_eq_of_intertwining ha hb ha' hb' c hca hcb, ← hg]
  exact MulAction.stabilizer_smul_eq_stabilizer_map_conj (groupWord word) y

theorem groupWord_append (u v : List Bool) :
    groupWord (u ++ v) = groupWord v * groupWord u := by
  induction u with
  | nil => simp [groupWord]
  | cons bit u ih => simp [groupWord, ih, mul_assoc]

theorem s_inverse : s⁻¹ = s := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, s_square]

theorem t_inverse : t⁻¹ = t * t := by
  rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← pow_two, ← pow_succ, t_cube]

def inverseGroupWord : List Bool → List Bool
  | [] => []
  | bit :: word => inverseGroupWord word ++ (if bit then [true,true] else [false])

theorem groupWord_inverse (word : List Bool) :
    groupWord (inverseGroupWord word) = (groupWord word)⁻¹ := by
  induction word with
  | nil => simp [inverseGroupWord, groupWord]
  | cons bit word ih =>
      cases bit <;> simp [inverseGroupWord, groupWord_append, groupWord, ih,
        s_inverse, t_inverse]

/-- Every presented-group element is represented by a positive Boolean word;
inverse letters are eliminated using the two defining relations. -/
theorem groupWord_surjective : Function.Surjective groupWord := by
  let K : Subgroup AbstractGroup :=
    { carrier := Set.range groupWord
      one_mem' := ⟨[], rfl⟩
      mul_mem' := by
        rintro g h ⟨u,rfl⟩ ⟨v,rfl⟩
        exact ⟨v ++ u, groupWord_append v u⟩
      inv_mem' := by
        rintro g ⟨u,rfl⟩
        exact ⟨inverseGroupWord u, groupWord_inverse u⟩ }
  intro g
  have hg : g ∈ K := PresentedGroup.generated_by relations K
    (by
      intro bit
      cases bit
      · exact ⟨[false], by simp [groupWord, s]⟩
      · exact ⟨[true], by simp [groupWord, t]⟩) g
  exact hg

noncomputable def subgroupCosetEquiv (H : Subgroup AbstractGroup) (hindex : H.index = 12) :
    (AbstractGroup ⧸ H) ≃ Vertex := by
  letI : H.FiniteIndex := ⟨by rw [hindex]; decide⟩
  exact Finite.equivFinOfCardEq (H.index_eq_card.symm.trans hindex)

def cosetAlpha (H : Subgroup AbstractGroup) (e : (AbstractGroup ⧸ H) ≃ Vertex) : VertexMap :=
  fun i => e (s • e.symm i)

def cosetBeta (H : Subgroup AbstractGroup) (e : (AbstractGroup ⧸ H) ≃ Vertex) : VertexMap :=
  fun i => e (t • e.symm i)

theorem cosetAlpha_involutive (H : Subgroup AbstractGroup)
    (e : (AbstractGroup ⧸ H) ≃ Vertex) : ∀ i, cosetAlpha H e (cosetAlpha H e i) = i := by
  intro i
  simp only [cosetAlpha, Equiv.symm_apply_apply, ← mul_smul, ← pow_two, s_square,
    one_smul, Equiv.apply_symm_apply]

theorem cosetBeta_cubic (H : Subgroup AbstractGroup)
    (e : (AbstractGroup ⧸ H) ≃ Vertex) : ∀ i, cosetBeta H e (cosetBeta H e (cosetBeta H e i)) = i := by
  intro i
  simp only [cosetBeta, Equiv.symm_apply_apply, ← mul_smul]
  rw [← mul_assoc, ← pow_two, ← pow_succ, t_cube, one_smul, Equiv.apply_symm_apply]

theorem coset_word (H : Subgroup AbstractGroup) (e : (AbstractGroup ⧸ H) ≃ Vertex)
    (word : List Bool) (q : AbstractGroup ⧸ H) :
    evalPairWord (cosetAlpha H e) (cosetBeta H e) word (e q) = e (groupWord word • q) := by
  induction word generalizing q with
  | nil => simp [evalPairWord, groupWord]
  | cons bit word ih =>
      cases bit <;> simp [evalPairWord, cosetAlpha, cosetBeta, groupWord, mul_smul, ih]

theorem coset_pair_transitive (H : Subgroup AbstractGroup)
    (e : (AbstractGroup ⧸ H) ≃ Vertex) : PairTransitive (cosetAlpha H e) (cosetBeta H e) := by
  intro i j
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq AbstractGroup (e.symm i) (e.symm j)
  obtain ⟨word,hw⟩ := groupWord_surjective g
  refine ⟨word, ?_⟩
  have hc := coset_word H e word (e.symm i)
  simpa [hw, hg] using hc

theorem coset_pairHom (H : Subgroup AbstractGroup) (e : (AbstractGroup ⧸ H) ≃ Vertex)
    (g : AbstractGroup) (i : Vertex) :
    pairHom (cosetAlpha H e) (cosetBeta H e) (cosetAlpha_involutive H e)
      (cosetBeta_cubic H e) g i = e (g • e.symm i) := by
  obtain ⟨word,hw⟩ := groupWord_surjective g
  rw [← hw, pairHom_word]
  simpa using coset_word H e word (e.symm i)

/-- Recovering the stabilizer at the identity coset recovers the original
subgroup exactly, rather than only up to isomorphism or equal index. -/
theorem coset_pairStabilizer (H : Subgroup AbstractGroup)
    (e : (AbstractGroup ⧸ H) ≃ Vertex) :
    pairStabilizer (cosetAlpha H e) (cosetBeta H e) (cosetAlpha_involutive H e)
      (cosetBeta_cubic H e) (e ((1 : AbstractGroup) : AbstractGroup ⧸ H)) = H := by
  ext g
  change (pairHom (cosetAlpha H e) (cosetBeta H e) _ _ g
    (e ((1 : AbstractGroup) : AbstractGroup ⧸ H)) =
      e ((1 : AbstractGroup) : AbstractGroup ⧸ H)) ↔ g ∈ H
  rw [coset_pairHom]
  simp only [Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq]
  change g ∈ MulAction.stabilizer AbstractGroup ((1 : AbstractGroup) : AbstractGroup ⧸ H) ↔ g ∈ H
  rw [MulAction.stabilizer_quotient]

theorem cosetAlpha_fixed_point_free (H : Subgroup AbstractGroup)
    (e : (AbstractGroup ⧸ H) ≃ Vertex) (hf : ∀ q : AbstractGroup ⧸ H, s • q ≠ q) :
    ∀ i, cosetAlpha H e i ≠ i := by
  intro i hi
  apply hf (e.symm i)
  apply e.injective
  simpa [cosetAlpha] using hi

theorem cosetBeta_fixed_point_free (H : Subgroup AbstractGroup)
    (e : (AbstractGroup ⧸ H) ≃ Vertex) (hf : ∀ q : AbstractGroup ⧸ H, t • q ≠ q) :
    ∀ i, cosetBeta H e i ≠ i := by
  intro i hi
  apply hf (e.symm i)
  apply e.injective
  simpa [cosetBeta] using hi

theorem coset_generator_fix_iff (H : Subgroup AbstractGroup) (h g : AbstractGroup) :
    h • (g : AbstractGroup ⧸ H) = (g : AbstractGroup ⧸ H) ↔ g⁻¹ * h * g ∈ H := by
  change ((h * g : AbstractGroup) : AbstractGroup ⧸ H) = (g : AbstractGroup ⧸ H) ↔ _
  rw [eq_comm, QuotientGroup.eq]
  simp only [mul_assoc]

theorem coset_generator_fixed_point_free_iff (H : Subgroup AbstractGroup) (h : AbstractGroup) :
    (∀ q : AbstractGroup ⧸ H, h • q ≠ q) ↔ ∀ g : AbstractGroup, g⁻¹ * h * g ∉ H := by
  constructor
  · intro hf g hg
    exact hf (g : AbstractGroup ⧸ H) ((coset_generator_fix_iff H h g).mpr hg)
  · intro hf q
    refine Quotient.inductionOn' q ?_
    intro g hg
    exact hf g ((coset_generator_fix_iff H h g).mp hg)

theorem quotientEquivOfEq_smul {H K : Subgroup AbstractGroup} (h : H = K)
    (g : AbstractGroup) (q : AbstractGroup ⧸ H) :
    Subgroup.quotientEquivOfEq h (g • q) = g • Subgroup.quotientEquivOfEq h q := by
  subst K
  refine Quotient.inductionOn' q ?_
  intro k
  rfl

/-- Equal pointed stabilizers give an actual equivariant relabeling of the
two transitive permutation pairs. -/
theorem equal_stabilizers_conjugate_pairs {a b a' b' : VertexMap}
    (ha : ∀ i, a (a i) = i) (hb : ∀ i, b (b (b i)) = i)
    (ha' : ∀ i, a' (a' i) = i) (hb' : ∀ i, b' (b' (b' i)) = i)
    (ht : PairTransitive a b) (ht' : PairTransitive a' b') (x y : Vertex)
    (hstab : pairStabilizer a b ha hb x = pairStabilizer a' b' ha' hb' y) :
    ∃ c : Equiv.Perm Vertex, (∀ i, c (a i) = a' (c i)) ∧
      (∀ i, c (b i) = b' (c i)) := by
  let E := pairCosetEquiv a b ha hb ht x
  let F := pairCosetEquiv a' b' ha' hb' ht' y
  let Q := Subgroup.quotientEquivOfEq hstab
  let c : Equiv.Perm Vertex := E.symm.trans (Q.trans F)
  have he : ∀ g i, c (pairHom a b ha hb g i) =
      pairHom a' b' ha' hb' g (c i) := by
    intro g i
    have hh : E.symm (pairHom a b ha hb g i) = g • E.symm i := by
      apply E.injective
      simp only [Equiv.apply_symm_apply]
      simpa only [Equiv.apply_symm_apply] using
        (pairCosetEquiv_smul a b ha hb ht x g
          ((pairCosetEquiv a b ha hb ht x).symm i)).symm
    change F (Q (E.symm (pairHom a b ha hb g i))) = _
    rw [hh, quotientEquivOfEq_smul]
    exact pairCosetEquiv_smul a' b' ha' hb' ht' y g (Q (E.symm i))
  refine ⟨c, ?_, ?_⟩
  · intro i
    have h := he s i
    simpa only [pairHom_s, involutionPerm] using h
  · intro i
    have h := he t i
    simpa only [pairHom_t, cubicPerm] using h

/-- Conjugacy of the two stabilizers is also sufficient for simultaneous
conjugacy of transitive permutation pairs. -/
theorem conjugate_stabilizers_conjugate_pairs {a b a' b' : VertexMap}
    (ha : ∀ i, a (a i) = i) (hb : ∀ i, b (b (b i)) = i)
    (ha' : ∀ i, a' (a' i) = i) (hb' : ∀ i, b' (b' (b' i)) = i)
    (ht : PairTransitive a b) (ht' : PairTransitive a' b') (x y : Vertex)
    (hstab : ∃ g : AbstractGroup, pairStabilizer a b ha hb x =
      (pairStabilizer a' b' ha' hb' y).map (MulAut.conj g).toMonoidHom) :
    ∃ c : Equiv.Perm Vertex, (∀ i, c (a i) = a' (c i)) ∧
      (∀ i, c (b i) = b' (c i)) := by
  obtain ⟨g,hg⟩ := hstab
  letI := pairAction a' b' ha' hb'
  have hy : pairStabilizer a' b' ha' hb' (g • y) =
      (pairStabilizer a' b' ha' hb' y).map (MulAut.conj g).toMonoidHom :=
    MulAction.stabilizer_smul_eq_stabilizer_map_conj g y
  exact equal_stabilizers_conjugate_pairs ha hb ha' hb' ht ht' x (g • y)
    (hg.trans hy.symm)

theorem transitive_pair_conjugacy_iff_stabilizers {a b a' b' : VertexMap}
    (ha : ∀ i, a (a i) = i) (hb : ∀ i, b (b (b i)) = i)
    (ha' : ∀ i, a' (a' i) = i) (hb' : ∀ i, b' (b' (b' i)) = i)
    (ht : PairTransitive a b) (ht' : PairTransitive a' b') (x y : Vertex) :
    (∃ c : Equiv.Perm Vertex, (∀ i, c (a i) = a' (c i)) ∧
      (∀ i, c (b i) = b' (c i))) ↔
    (∃ g : AbstractGroup, pairStabilizer a b ha hb x =
      (pairStabilizer a' b' ha' hb' y).map (MulAut.conj g).toMonoidHom) := by
  constructor
  · rintro ⟨c,hca,hcb⟩
    exact conjugate_pairs_conjugate_stabilizers ha hb ha' hb' ht' c hca hcb x y
  · exact conjugate_stabilizers_conjugate_pairs ha hb ha' hb' ht ht' x y

/-- At most two actual forward orbits of `st` on the coset space. This is a
coset-action condition, with no appeal to genus or hyperbolic area. -/
def AtMostTwoCosetCycles (H : Subgroup AbstractGroup) : Prop :=
  ∃ x y : AbstractGroup ⧸ H, ∀ z : AbstractGroup ⧸ H,
    (∃ n : ℕ, (fun q : AbstractGroup ⧸ H => s • (t • q))^[n] x = z) ∨
    (∃ n : ℕ, (fun q : AbstractGroup ⧸ H => s • (t • q))^[n] y = z)

theorem equiv_iterates {X Y : Type*} (e : X ≃ Y) (p : X → X) (q : Y → Y)
    (h : ∀ x, e (p x) = q (e x)) (n : ℕ) (x : X) :
    e (p^[n] x) = q^[n] (e x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', h, Function.iterate_succ_apply', ih]

theorem coset_pair_two_cycles (H : Subgroup AbstractGroup)
    (e : (AbstractGroup ⧸ H) ≃ Vertex) (h : AtMostTwoCosetCycles H) :
    AtMostTwoCycles (fun i => cosetAlpha H e (cosetBeta H e i)) := by
  obtain ⟨x,y,hxy⟩ := h
  have hi : ∀ z : AbstractGroup ⧸ H, e (s • (t • z)) =
      cosetAlpha H e (cosetBeta H e (e z)) := by
    intro z
    simp [cosetAlpha, cosetBeta]
  refine ⟨e x, e y, ?_⟩
  intro z
  rcases hxy (e.symm z) with ⟨n,hn⟩ | ⟨n,hn⟩
  · left
    refine ⟨n, ?_⟩
    have hn' := congrArg e hn
    rw [equiv_iterates e _ (fun i => cosetAlpha H e (cosetBeta H e i)) hi] at hn'
    simpa using hn'
  · right
    refine ⟨n, ?_⟩
    have hn' := congrArg e hn
    rw [equiv_iterates e _ (fun i => cosetAlpha H e (cosetBeta H e i)) hi] at hn'
    simpa using hn'

theorem pairCoset_two_cycles (a b : VertexMap)
    (ha : ∀ i, a (a i) = i) (hb : ∀ i, b (b (b i)) = i)
    (ht : PairTransitive a b) (v : Vertex)
    (htwo : AtMostTwoCycles (fun i => a (b i))) :
    AtMostTwoCosetCycles (pairStabilizer a b ha hb v) := by
  let E := pairCosetEquiv a b ha hb ht v
  obtain ⟨x,y,hxy⟩ := htwo
  have hi : ∀ z, E (s • (t • z)) = a (b (E z)) := by
    intro z
    rw [pairCosetEquiv_s, pairCosetEquiv_t]
  refine ⟨E.symm x, E.symm y, ?_⟩
  intro z
  rcases hxy (E z) with ⟨n,hn⟩ | ⟨n,hn⟩
  · left
    refine ⟨n, ?_⟩
    apply E.injective
    rw [equiv_iterates E _ (fun i => a (b i)) hi]
    simpa using hn
  · right
    refine ⟨n, ?_⟩
    apply E.injective
    rw [equiv_iterates E _ (fun i => a (b i)) hi]
    simpa using hn

theorem representative_pair_transitive (r : Fin 5) : PairTransitive (representative r) beta := by
  intro x y
  obtain ⟨word,hw⟩ := representative_transitive r x y
  exact ⟨word, (evalPairWord_beta _ _ _).trans hw⟩

def representativeSubgroup (r : Fin 5) : Subgroup AbstractGroup :=
  pairStabilizer (representative r) beta (representative_involutive r) beta_order_three 0

theorem representativeSubgroup_index (r : Fin 5) : (representativeSubgroup r).index = 12 :=
  pairStabilizer_index _ _ _ _ (representative_pair_transitive r) 0

theorem representativeSubgroup_admissible (r : Fin 5) :
    (representativeSubgroup r).index = 12 ∧
      (∀ q : AbstractGroup ⧸ representativeSubgroup r, s • q ≠ q) ∧
      (∀ q : AbstractGroup ⧸ representativeSubgroup r, t • q ≠ q) ∧
      AtMostTwoCosetCycles (representativeSubgroup r) := by
  refine ⟨representativeSubgroup_index r, ?_, ?_, ?_⟩
  · intro q hq
    let E := pairCosetEquiv (representative r) beta (representative_involutive r)
      beta_order_three (representative_pair_transitive r) 0
    have he := congrArg E hq
    have hs := pairCosetEquiv_s (representative r) beta (representative_involutive r)
      beta_order_three (representative_pair_transitive r) 0 q
    exact representative_fixed_point_free r (E q) (hs.symm.trans he)
  · intro q hq
    let E := pairCosetEquiv (representative r) beta (representative_involutive r)
      beta_order_three (representative_pair_transitive r) 0
    have he := congrArg E hq
    have ht := pairCosetEquiv_t (representative r) beta (representative_involutive r)
      beta_order_three (representative_pair_transitive r) 0 q
    exact beta_fixed_point_free (E q) (ht.symm.trans he)
  · exact pairCoset_two_cycles (representative r) beta (representative_involutive r)
      beta_order_three (representative_pair_transitive r) 0 (representative_atMostTwoCycles r)

/-- The finite census now classifies actual subgroups of the abstract
presentation. The hypotheses are explicit coset-action hypotheses; neither
`PSL₂(ℤ)` nor a geometric torsion or genus equivalence is assumed. -/
theorem abstract_subgroup_census_unique (H : Subgroup AbstractGroup) (hindex : H.index = 12)
    (hs : ∀ q : AbstractGroup ⧸ H, s • q ≠ q)
    (ht : ∀ q : AbstractGroup ⧸ H, t • q ≠ q) (htwo : AtMostTwoCosetCycles H) :
    ∃! r : Fin 5, ∃ g : AbstractGroup,
      H = (representativeSubgroup r).map (MulAut.conj g).toMonoidHom := by
  let e := subgroupCosetEquiv H hindex
  let a := cosetAlpha H e
  let b := cosetBeta H e
  let ha := cosetAlpha_involutive H e
  let hb := cosetBeta_cubic H e
  have htrans := coset_pair_transitive H e
  obtain ⟨r,hr,hunique⟩ := arbitrary_beta_census_unique a b ha
    (cosetAlpha_fixed_point_free H e hs) hb (cosetBeta_fixed_point_free H e ht)
    htrans (coset_pair_two_cycles H e htwo)
  obtain ⟨c,hca,hcb⟩ := hr
  let x : Vertex := e ((1 : AbstractGroup) : AbstractGroup ⧸ H)
  have hrecover : pairStabilizer a b ha hb x = H := coset_pairStabilizer H e
  obtain ⟨g,hg⟩ := conjugate_pairs_conjugate_stabilizers ha hb
    (representative_involutive r) beta_order_three (representative_pair_transitive r)
    c hca hcb x 0
  refine ⟨r, ⟨g, ?_⟩, ?_⟩
  · exact hrecover.symm.trans hg
  · intro r' hr'
    apply hunique r'
    obtain ⟨g,hg⟩ := hr'
    apply conjugate_stabilizers_conjugate_pairs ha hb
      (representative_involutive r') beta_order_three htrans
      (representative_pair_transitive r') x 0
    refine ⟨g, ?_⟩
    exact hrecover.trans hg

theorem representativeSubgroups_conjugate_iff (r r' : Fin 5) :
    (∃ g : AbstractGroup, representativeSubgroup r =
      (representativeSubgroup r').map (MulAut.conj g).toMonoidHom) ↔ r = r' := by
  have hone : (MulAut.conj (1 : AbstractGroup)).toMonoidHom = MonoidHom.id AbstractGroup := by
    ext g
    simp
  constructor
  · intro h
    obtain ⟨hindex,hs,ht,htwo⟩ := representativeSubgroup_admissible r
    obtain ⟨k,_,hunique⟩ :=
      abstract_subgroup_census_unique (representativeSubgroup r) hindex hs ht htwo
    have hself : ∃ g : AbstractGroup, representativeSubgroup r =
        (representativeSubgroup r).map (MulAut.conj g).toMonoidHom := by
      refine ⟨1, ?_⟩
      rw [hone, Subgroup.map_id]
    exact (hunique r hself).trans (hunique r' h).symm
  · rintro rfl
    refine ⟨1, ?_⟩
    rw [hone, Subgroup.map_id]

end SerreMarkov.ModularCosets

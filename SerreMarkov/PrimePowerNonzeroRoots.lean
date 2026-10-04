import SerreMarkov.UnitPrimePowerRoots
import SerreMarkov.PrimePowerZeroGeneral

/-! # Lifting nonzero square roots at odd prime powers

The equivalence uses the least representative of a reduced root, followed
by a lift index. It counts finite congruence roots and makes no orbit-count
assumption.
-/

namespace SerreMarkov.PrimePowerNonzeroRoots

open FamilyFiberFinite
noncomputable section

private theorem nat_square_eq_iff_int_dvd (n a u : ℕ) :
    (a : ZMod n)^2 = (u : ZMod n)^2 ↔
      (n:ℤ) ∣ (a:ℤ)^2-(u:ℤ)^2 := by
  have hc : (((a:ℤ)^2-(u:ℤ)^2 : ℤ) : ZMod n) =
      (a : ZMod n)^2-(u : ZMod n)^2 := by push_cast; rfl
  rw [← sub_eq_zero, ← hc, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Cancel the common squared scale in a congruence. -/
theorem scaled_square_eq_iff (q k a u : ℕ) (hq : 0 < q) :
    ((q*a : ℕ) : ZMod (q^2*k))^2 = ((q*u : ℕ) : ZMod (q^2*k))^2 ↔
      (a : ZMod k)^2 = (u : ZMod k)^2 := by
  rw [nat_square_eq_iff_int_dvd, nat_square_eq_iff_int_dvd]
  push_cast
  have heq : ((q:ℤ)*(a:ℤ))^2-((q:ℤ)*(u:ℤ))^2 =
      (q:ℤ)^2*((a:ℤ)^2-(u:ℤ)^2) := by ring
  rw [heq, mul_dvd_mul_iff_left]
  exact pow_ne_zero 2 (by exact_mod_cast hq.ne')

private theorem lifted_bound (q k : ℕ) (hk : 0 < k)
    (a : ZMod k) (t : Fin q) : a.val+k*t.val < q*k := by
  letI : NeZero k := ⟨hk.ne'⟩
  calc
    a.val+k*t.val < k+k*t.val := Nat.add_lt_add_right (ZMod.val_lt a) _
    _ = k*(t.val+1) := by ring
    _ ≤ k*q := Nat.mul_le_mul_left k (by omega)
    _ = q*k := Nat.mul_comm _ _

/-- Scale-divisible roots split uniquely into a reduced root and one of `q` lifts. -/
def scaledSquareRootEquiv (q k u : ℕ) (hq : 0 < q) (hk : 0 < k)
    (hdiv : ∀ z : ZMod (q^2*k), z^2=((q*u : ℕ) : ZMod (q^2*k))^2 → q ∣ z.val) :
    Roots (q^2*k) (((q*u : ℕ) : ZMod (q^2*k))^2) ≃
      Roots k ((u : ZMod k)^2) × Fin q := by
  letI : NeZero k := ⟨hk.ne'⟩
  letI : NeZero (q^2*k) := ⟨mul_ne_zero (pow_ne_zero 2 hq.ne') hk.ne'⟩
  have hreduce (z : Roots (q^2*k) (((q*u : ℕ) : ZMod (q^2*k))^2)) :
      (z.val.val/q : ZMod k)^2 = (u : ZMod k)^2 := by
    have hz : ((z.val.val : ℕ) : ZMod (q^2*k))^2 = ((q*u : ℕ) : ZMod (q^2*k))^2 := by
      rw [ZMod.natCast_zmod_val]
      exact z.property
    have hval : z.val.val = q*(z.val.val/q) :=
      (Nat.mul_div_cancel' (hdiv z.val z.property)).symm
    rw [hval] at hz
    exact (scaled_square_eq_iff q k _ u hq).mp hz
  have hquot (z : ZMod (q^2*k)) : z.val/q < q*k := by
    apply (Nat.div_lt_iff_lt_mul hq).mpr
    simpa only [pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ZMod.val_lt z
  have hencode (a : Roots k ((u : ZMod k)^2)) (t : Fin q) :
      ((q*(a.val.val+k*t.val) : ℕ) : ZMod (q^2*k))^2 =
        ((q*u : ℕ) : ZMod (q^2*k))^2 := by
    apply (scaled_square_eq_iff q k _ u hq).mpr
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
      ZMod.natCast_zmod_val]
    exact a.property
  have hbound (a : ZMod k) (t : Fin q) : q*(a.val+k*t.val) < q^2*k := by
    simpa only [pow_two, Nat.mul_assoc] using
      Nat.mul_lt_mul_of_pos_left (lifted_bound q k hk a t) hq
  refine {
    toFun := fun z => (⟨(z.val.val/q : ℕ), hreduce z⟩,
      ⟨z.val.val/q/k, (Nat.div_lt_iff_lt_mul hk).mpr (hquot z.val)⟩)
    invFun := fun pair => ⟨((q*(pair.1.val.val+k*pair.2.val) : ℕ) : ZMod (q^2*k)), hencode pair.1 pair.2⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro z
    apply Subtype.ext
    change ((q*(((z.val.val/q : ℕ) : ZMod k).val+k*(z.val.val/q/k)) : ℕ) : ZMod (q^2*k)) = z.val
    rw [ZMod.val_natCast, Nat.mod_add_div,
      Nat.mul_div_cancel' (hdiv z.val z.property), ZMod.natCast_zmod_val]
  · rintro ⟨a,t⟩
    apply Prod.ext
    · apply Subtype.ext
      change ((((q*(a.val.val+k*t.val) : ℕ) : ZMod (q^2*k)).val/q : ℕ) : ZMod k) = a.val
      rw [ZMod.val_natCast_of_lt (hbound a.val t), Nat.mul_div_cancel_left _ hq,
        Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
        ZMod.natCast_zmod_val]
    · apply Fin.ext
      change (((q*(a.val.val+k*t.val) : ℕ) : ZMod (q^2*k)).val/q/k) = t.val
      rw [ZMod.val_natCast_of_lt (hbound a.val t), Nat.mul_div_cancel_left _ hq,
        Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt (ZMod.val_lt a.val), Nat.zero_add]

/-- The representative used to lift a reduced root. -/
@[simp] theorem scaledSquareRootEquiv_symm_apply (q k u : ℕ) (hq : 0 < q) (hk : 0 < k)
    (hdiv : ∀ z : ZMod (q^2*k), z^2=((q*u : ℕ) : ZMod (q^2*k))^2 → q ∣ z.val)
    (a : Roots k ((u : ZMod k)^2)) (t : Fin q) :
    ((scaledSquareRootEquiv q k u hq hk hdiv).symm (a,t)).val =
      ((q*(a.val.val+k*t.val) : ℕ) : ZMod (q^2*k)) := rfl

/-- Reduction divides the least representative by the common scale. -/
@[simp] theorem scaledSquareRootEquiv_apply_root (q k u : ℕ) (hq : 0 < q) (hk : 0 < k)
    (hdiv : ∀ z : ZMod (q^2*k), z^2=((q*u : ℕ) : ZMod (q^2*k))^2 → q ∣ z.val)
    (z : Roots (q^2*k) (((q*u : ℕ) : ZMod (q^2*k))^2)) :
    ((scaledSquareRootEquiv q k u hq hk hdiv z).1).val =
      (z.val.val/q : ℕ) := rfl

/-- The lift index is the quotient after division by both scale and modulus. -/
@[simp] theorem scaledSquareRootEquiv_apply_lift (q k u : ℕ) (hq : 0 < q) (hk : 0 < k)
    (hdiv : ∀ z : ZMod (q^2*k), z^2=((q*u : ℕ) : ZMod (q^2*k))^2 → q ∣ z.val)
    (z : Roots (q^2*k) (((q*u : ℕ) : ZMod (q^2*k))^2)) :
    ((scaledSquareRootEquiv q k u hq hk hdiv z).2).val = z.val.val/q/k := rfl

/-- A lifting factor has exactly `q` choices above each reduced root. -/
theorem scaled_square_roots_natCard (q k u : ℕ) (hq : 0 < q) (hk : 0 < k)
    (hdiv : ∀ z : ZMod (q^2*k), z^2=((q*u : ℕ) : ZMod (q^2*k))^2 → q ∣ z.val) :
    Nat.card (Roots (q^2*k) (((q*u : ℕ) : ZMod (q^2*k))^2)) =
      Nat.card (Roots k ((u : ZMod k)^2))*q := by
  rw [Nat.card_congr (scaledSquareRootEquiv q k u hq hk hdiv), Nat.card_prod, Nat.card_fin]


private theorem primePower_factor (p e b : ℕ) (hb : 2*b ≤ e) :
    p^e = (p^b)^2 * p^(e-2*b) := by
  symm
  calc
    (p^b)^2 * p^(e-2*b) = p^(b*2) * p^(e-2*b) := by rw [pow_mul]
    _ = p^(b*2+(e-2*b)) := by rw [pow_add]
    _ = p^e := by congr 1; omega

/-- Every nonzero odd-prime-power square root is given by a sign and one
of `p^b` lifts of the corresponding unit root.  The lift uses the least
representative modulo `p^(e-2*b)`. -/
def nonzeroPrimePowerRootsEquiv (p e b u : ℕ) (hp : p.Prime)
    (hodd : Odd p) (hb : 2*b < e) (hu : ¬ p ∣ u) :
    (Bool × Fin (p^b)) ≃
      Roots (p^e) (((p^b*u : ℕ) : ZMod (p^e))^2) := by
  have hq : 0 < p^b := pow_pos hp.pos _
  have hk : 0 < p^(e-2*b) := pow_pos hp.pos _
  have hy : ¬ (p:ℤ) ∣ (u:ℤ) := fun hd => hu (Int.natCast_dvd_natCast.mp hd)
  have hunit : Bool ≃ Roots (p^(e-2*b)) ((u : ZMod (p^(e-2*b)))^2) := by
    simpa only [Int.cast_natCast] using
      UnitPrimePowerRoots.unitRootsEquiv hp hodd (by omega : 0 < e-2*b) (u:ℤ) hy
  have hdiv : ∀ z : ZMod (p^e), z^2=((p^b*u : ℕ) : ZMod (p^e))^2 → p^b ∣ z.val := by
    intro z hz
    exact root_representative_divisible p e b u hp (by omega) z hz
  have hfactor := primePower_factor p e b (by omega : 2*b ≤ e)
  rw [hfactor] at hdiv ⊢
  exact (Equiv.prodCongr hunit (Equiv.refl _)).trans
    (scaledSquareRootEquiv (p^b) (p^(e-2*b)) u hq hk hdiv).symm

/-- The exact local factor in the nonzero branch: `2*p^b` congruence roots. -/
theorem nonzero_primePower_roots_natCard (p e b u : ℕ) (hp : p.Prime)
    (hodd : Odd p) (hb : 2*b < e) (hu : ¬ p ∣ u) :
    Nat.card (Roots (p^e) (((p^b*u : ℕ) : ZMod (p^e))^2)) = 2*p^b := by
  rw [← Nat.card_congr (nonzeroPrimePowerRootsEquiv p e b u hp hodd hb hu),
    Nat.card_prod, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_bool]


private theorem square_scaled_natAbs (p e b : ℕ) (u : ℤ) :
    (((p^b*u.natAbs : ℕ) : ZMod (p^e))^2) =
      ((p : ZMod (p^e))^b*(u : ZMod (p^e)))^2 := by
  have hs : (u.natAbs : ZMod (p^e))^2 = (u : ZMod (p^e))^2 := by
    simpa only [Int.cast_pow, Int.cast_natCast] using
      congrArg (fun a : ℤ => (a : ZMod (p^e))) (Int.natAbs_pow_two u)
  simp only [Nat.cast_mul, Nat.cast_pow, mul_pow, hs]

/-- The same sign/lift parametrization for an arbitrary integral unit factor. -/
def nonzeroPrimePowerIntegerRootsEquiv (p e b : ℕ) (u : ℤ) (hp : p.Prime)
    (hodd : Odd p) (hb : 2*b < e) (hu : ¬ (p:ℤ) ∣ u) :
    (Bool × Fin (p^b)) ≃
      Roots (p^e) (((p : ZMod (p^e))^b*(u : ZMod (p^e)))^2) := by
  rw [← square_scaled_natAbs p e b u]
  exact nonzeroPrimePowerRootsEquiv p e b u.natAbs hp hodd hb
    (fun hd => hu (Int.natCast_dvd.mpr hd))

/-- Exact cardinality with an arbitrary integer unit factor, of either sign. -/
theorem nonzero_primePower_integer_roots_natCard (p e b : ℕ) (u : ℤ) (hp : p.Prime)
    (hodd : Odd p) (hb : 2*b < e) (hu : ¬ (p:ℤ) ∣ u) :
    Nat.card (Roots (p^e) (((p : ZMod (p^e))^b*(u : ZMod (p^e)))^2)) = 2*p^b := by
  rw [← Nat.card_congr (nonzeroPrimePowerIntegerRootsEquiv p e b u hp hodd hb hu),
    Nat.card_prod, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_bool]

end
end SerreMarkov.PrimePowerNonzeroRoots

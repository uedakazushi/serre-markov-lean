import SerreMarkov.FamilyFiberFinite

/-! # Coprime product formula for modular square-root sets

The actual CRT ring equivalence restricts to a bijection of square-root
subtypes. Thus the product formula is a cardinality consequence of a proved
bijection, independent of any classification of Euler lattices.
-/

namespace SerreMarkov.ChineseRoots

open FamilyFiberFinite
noncomputable section

/-- CRT preserves the equation defining the square-root subtype. -/
def rootsCRT {m n : ℕ} (h : Nat.Coprime m n) (c : ZMod (m*n)) :
    Roots (m*n) c ≃
      Roots m ((ZMod.chineseRemainder h c).1) ×
      Roots n ((ZMod.chineseRemainder h c).2) where
  toFun x :=
    (⟨(ZMod.chineseRemainder h x.val).1,by
      have hx := congrArg (fun z => (ZMod.chineseRemainder h z).1) x.property
      simpa only [map_pow] using hx⟩,
     ⟨(ZMod.chineseRemainder h x.val).2,by
      have hx := congrArg (fun z => (ZMod.chineseRemainder h z).2) x.property
      simpa only [map_pow] using hx⟩)
  invFun x := ⟨(ZMod.chineseRemainder h).symm (x.1.val,x.2.val),by
    apply (ZMod.chineseRemainder h).injective
    rw [map_pow,RingEquiv.apply_symm_apply]
    apply Prod.ext
    · exact x.1.property
    · exact x.2.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (ZMod.chineseRemainder h).symm_apply_apply x.val
  right_inv x := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst ((ZMod.chineseRemainder h).apply_symm_apply (x.1.val,x.2.val))
    · exact congrArg Prod.snd ((ZMod.chineseRemainder h).apply_symm_apply (x.1.val,x.2.val))

@[simp] theorem CRT_int_square {m n : ℕ} (h : Nat.Coprime m n) (y : ℤ) :
    ZMod.chineseRemainder h ((y : ZMod (m*n))^2) =
      ((y : ZMod m)^2,(y : ZMod n)^2) := by
  apply Prod.ext
  · change ((RingHom.fst (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom) ((y : ZMod (m*n))^2) = _
    simp
  · change ((RingHom.snd (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom) ((y : ZMod (m*n))^2) = _
    simp

/-- The precise square-root sets used in the family-fiber arithmetic are
bijective to the product of their coprime local factors. -/
def squareRootsCRT {m n : ℕ} (h : Nat.Coprime m n) (y : ℤ) :
    Roots (m*n) ((y : ZMod (m*n))^2) ≃
      Roots m ((y : ZMod m)^2) × Roots n ((y : ZMod n)^2) := by
  have he := rootsCRT h ((y : ZMod (m*n))^2)
  rw [CRT_int_square] at he
  exact he

/-- The coprime product formula for the actual root-set cardinalities. -/
theorem squareRoots_card_mul (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h : Nat.Coprime m n) (y : ℤ) :
    Nat.card (Roots (m*n) ((y : ZMod (m*n))^2)) =
      Nat.card (Roots m ((y : ZMod m)^2))*Nat.card (Roots n ((y : ZMod n)^2)) := by
  calc
    _ = Nat.card (Roots m ((y : ZMod m)^2) × Roots n ((y : ZMod n)^2)) :=
      Nat.card_congr (squareRootsCRT h y)
    _ = _ := Nat.card_prod _ _

end
end SerreMarkov.ChineseRoots

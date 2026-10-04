import SerreMarkov.NegativeAdjacentReduction
import SerreMarkov.NegativeBoundary

/-! # An orthogonal pair with opposite pairing of absolute value one

The unbounded solution equations first give a finite bound on the remaining
four coefficients. A kernel-checked finite statement then gives an actual
single braid move to two zero edges, where the arithmetic classification is
already proved.
-/

namespace SerreMarkov.NegativeZeroUnitBoundary
open NegativeBoundary

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem square_fourteen_bounds (x : ℤ) (hx : x^2 ≤ 14) :
    -3 ≤ x ∧ x ≤ 3 := by
  constructor
  · by_contra h
    have hh : x ≤ -4 := by omega
    nlinarith [sq_nonneg (x+4)]
  · by_contra h
    have hh : 4 ≤ x := by omega
    nlinarith [sq_nonneg (x-4)]

theorem zero_unit_bounds (b c d e : ℤ) (hz : isSolution ⟨0,b,c,d,e,1⟩) :
    (-3 ≤ b ∧ b ≤ 3) ∧ (-3 ≤ c ∧ c ≤ 3) ∧
    (-3 ≤ d ∧ d ≤ 3) ∧ (-3 ≤ e ∧ e ≤ 3) := by
  have hq := hz.1
  simp only [q1,zero_mul,zero_sub,zero_pow,one_pow,mul_one] at hq
  have hs : b^2+c^2+d^2+e^2+(b-c)^2+(d-e)^2=14 := by nlinarith [hq]
  exact ⟨square_fourteen_bounds b (by nlinarith [sq_nonneg c,sq_nonneg d,sq_nonneg e,sq_nonneg (b-c),sq_nonneg (d-e)]),
    square_fourteen_bounds c (by nlinarith [sq_nonneg b,sq_nonneg d,sq_nonneg e,sq_nonneg (b-c),sq_nonneg (d-e)]),
    square_fourteen_bounds d (by nlinarith [sq_nonneg b,sq_nonneg c,sq_nonneg e,sq_nonneg (b-c),sq_nonneg (d-e)]),
    square_fourteen_bounds e (by nlinarith [sq_nonneg b,sq_nonneg c,sq_nonneg d,sq_nonneg (b-c),sq_nonneg (d-e)])⟩

private theorem finite_zero_unit_check : ∀ b c d e : Fin 7,
    let z : Six := ⟨0,(b.val:ℤ)-3,(c.val:ℤ)-3,(d.val:ℤ)-3,(e.val:ℤ)-3,1⟩
    isSolution z → TwoZeroEdges z ∨ TwoZeroEdges (mu3 z) := by
  unfold isSolution TwoZeroEdges q1 q2 mu3
  decide +kernel

theorem zero_unit_two_zeros (b c d e : ℤ) (hz : isSolution ⟨0,b,c,d,e,1⟩) :
    TwoZeroEdges ⟨0,b,c,d,e,1⟩ ∨ TwoZeroEdges (mu3 ⟨0,b,c,d,e,1⟩) := by
  obtain ⟨hb,hc,hd,he⟩ := zero_unit_bounds b c d e hz
  let B : Fin 7 := ⟨(b+3).toNat,by omega⟩
  let C : Fin 7 := ⟨(c+3).toNat,by omega⟩
  let D : Fin 7 := ⟨(d+3).toNat,by omega⟩
  let E : Fin 7 := ⟨(e+3).toNat,by omega⟩
  have hB : (B.val:ℤ)-3=b := by dsimp [B]; omega
  have hC : (C.val:ℤ)-3=c := by dsimp [C]; omega
  have hD : (D.val:ℤ)-3=d := by dsimp [D]; omega
  have hE : (E.val:ℤ)-3=e := by dsimp [E]; omega
  simpa only [hB,hC,hD,hE] using finite_zero_unit_check B C D E (by
    simpa only [hB,hC,hD,hE] using hz)

theorem zero_positive_unit_reachable_family (b c d e : ℤ)
    (hz : isSolution ⟨0,b,c,d,e,1⟩)
    (hneg : IntrinsicSigns.thirdMinorSum ⟨0,b,c,d,e,1⟩ < 0) :
    ∃ x y : ℤ, Reachable ⟨0,b,c,d,e,1⟩ (family x y) := by
  rcases zero_unit_two_zeros b c d e hz with hzero | hzero
  · exact two_zero_edges_reachable_family _ hz hneg hzero
  · have hr : Reachable ⟨0,b,c,d,e,1⟩ (mu3 ⟨0,b,c,d,e,1⟩) := ⟨[.m3],rfl⟩
    obtain ⟨x,y,hxy⟩ := two_zero_edges_reachable_family _
      (reachable_preserves_solution hr hz)
      (NegativeAdjacentReduction.reachable_negative hz hneg hr) hzero
    exact ⟨x,y,reachable_trans hr hxy⟩

theorem zero_opposite_unit_reachable_family (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (ha : z.a=0) (hf : |z.f|=1) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  have hsign : z.f=1 ∨ z.f=-1 := (abs_eq (by norm_num : (0:ℤ)≤1)).mp hf
  rcases hsign with hf | hf
  · have ht : z=⟨0,z.b,z.c,z.d,z.e,1⟩ := by ext <;> simp [ha,hf]
    rw [ht] at hz hneg ⊢
    exact zero_positive_unit_reachable_family _ _ _ _ hz hneg
  · have hr : Reachable z (eps4 z) := ⟨[.s4],rfl⟩
    have ht : eps4 z=⟨0,z.b,-z.c,z.d,-z.e,1⟩ := by ext <;> simp [eps4,ha,hf]
    obtain ⟨x,y,hxy⟩ := zero_positive_unit_reachable_family z.b (-z.c) z.d (-z.e)
      (ht ▸ reachable_preserves_solution hr hz)
      (ht ▸ NegativeAdjacentReduction.reachable_negative hz hneg hr)
    exact ⟨x,y,reachable_trans hr (by simpa only [ht] using hxy)⟩

end SerreMarkov.NegativeZeroUnitBoundary

import SerreMarkov.ModularPresentation
import SerreMarkov.ModularFreeProduct
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.GroupTheory.CoprodI

/-!
# Ping-pong domains for the actual projective modular generators

The action of `SL₂(ℤ)` descends through its actual center. The positive and
negative real half-planes are disjoint ping-pong domains for `S` and `S*T`.
-/

namespace SerreMarkov.ModularPingPong

open Matrix ModularGroup ModularPresentation UpperHalfPlane
open scoped MatrixGroups

noncomputable section

def SLActionHom : SL2Z →* Equiv.Perm ℍ := MulAction.toPermHom SL2Z ℍ

theorem center_acts_trivially (g : SL2Z) (hg : g ∈ Subgroup.center SL2Z) :
    SLActionHom g = 1 := by
  rcases (SL2Z_center_iff g).mp hg with rfl | rfl
  · exact map_one _
  · apply Equiv.ext
    intro z
    change (-1 : SL2Z) • z = z
    simp only [ModularGroup.SL_neg_smul, one_smul]

def projectiveActionHom : PSL2Z →* Equiv.Perm ℍ :=
  QuotientGroup.lift (Subgroup.center SL2Z) SLActionHom center_acts_trivially

instance projectiveAction : MulAction PSL2Z ℍ := MulAction.compHom ℍ projectiveActionHom

theorem project_smul (g : SL2Z) (z : ℍ) : project g • z = g • z := rfl

theorem S_re (z : ℍ) : (S • z).re = -z.re / Complex.normSq (z : ℂ) := by
  rw [UpperHalfPlane.modular_S_smul]
  simp only [UpperHalfPlane.mk_re, Complex.inv_re, Complex.neg_re, Complex.normSq_neg, neg_div, UpperHalfPlane.coe_re]

theorem R_re (z : ℍ) : ((S*T) • z).re = -(z.re+1) / Complex.normSq ((z : ℂ)+1) := by
  rw [MulAction.mul_smul, S_re, UpperHalfPlane.modular_T_smul]
  simp [UpperHalfPlane.coe_vadd, add_comm]

theorem R_square_re (z : ℍ) : ((S*T)^2 • z).re = -1-z.re/Complex.normSq (z : ℂ) := by
  have hc : ((((S*T)^2) • z : ℍ) : ℂ) = (-(z : ℂ)-1)/(z : ℂ) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    norm_num [pow_two, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.S, ModularGroup.T,
      Matrix.mul_fin_two]
    ring
  change (((((S*T)^2) • z : ℍ) : ℂ)).re = _
  rw [hc]
  have he : (-(z : ℂ)-1)/(z : ℂ) = -1-(z : ℂ)⁻¹ := by
    field_simp [z.ne_zero]
  rw [he]
  simp [Complex.inv_re]

def domain (b : Bool) : Set ℍ := if b then {z | z.re < 0} else {z | 0 < z.re}

theorem domain_nonempty (b : Bool) : (domain b).Nonempty := by
  cases b
  · exact ⟨(1 : ℝ) +ᵥ UpperHalfPlane.I, by norm_num [domain]⟩
  · exact ⟨(-1 : ℝ) +ᵥ UpperHalfPlane.I, by norm_num [domain]⟩

theorem domain_disjoint : Pairwise (Function.onFun Disjoint domain) := by
  intro i j hij
  cases i <;> cases j
  · exact False.elim (hij rfl)
  · apply Set.disjoint_left.mpr
    intro z hpos hneg
    change 0 < z.re at hpos
    change z.re < 0 at hneg
    exact lt_asymm hpos hneg
  · apply Set.disjoint_left.mpr
    intro z hneg hpos
    change z.re < 0 at hneg
    change 0 < z.re at hpos
    exact lt_asymm hneg hpos
  · exact False.elim (hij rfl)

theorem S_ping_pong (z : ℍ) (hz : z.re < 0) : 0 < (projectiveS • z).re := by
  rw [projectiveS, project_smul, S_re]
  exact div_pos (neg_pos.mpr hz) z.normSq_pos

theorem R_ping_pong (z : ℍ) (hz : 0 < z.re) : (projectiveR • z).re < 0 := by
  rw [projectiveR, project_smul, R_re]
  have hnorm : 0 < Complex.normSq ((z : ℂ)+1) := by
    apply Complex.normSq_pos.mpr
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact ne_of_gt z.im_pos hi
  exact div_neg_of_neg_of_pos (by linarith) hnorm

theorem R_square_ping_pong (z : ℍ) (hz : 0 < z.re) : (projectiveR^2 • z).re < 0 := by
  rw [projectiveR, ← map_pow, project_smul, R_square_re]
  have hpos : 0 < z.re / Complex.normSq (z : ℂ) := div_pos hz z.normSq_pos
  linarith

open ModularFreeProduct

theorem projectiveGenerator_pow (b : Bool) :
    (if b then projectiveR else projectiveS)^(factorOrder b)=1 := by
  cases b
  · exact projectiveS_square
  · exact projectiveR_cube

def factorToProjective (b : Bool) : Factor b →* PSL2Z :=
  cyclicHom (factorOrder b) (if b then projectiveR else projectiveS)
    (projectiveGenerator_pow b)

@[simp] theorem factorToProjective_generator (b : Bool) :
    factorToProjective b (factorGenerator b) = if b then projectiveR else projectiveS := by
  exact cyclicHom_generator _ _ _

private theorem factor_val_ne_zero (b : Bool) (v : Factor b) (hv : v ≠ 1) :
    v.toAdd.val ≠ 0 := by
  intro he
  apply hv
  apply Multiplicative.toAdd.injective
  change v.toAdd = 0
  exact (ZMod.val_eq_zero v.toAdd).mp he

open scoped Pointwise

theorem factor_ping_pong : Pairwise fun i j => ∀ v : Factor i,
    v ≠ 1 → factorToProjective i v • domain j ⊆ domain i := by
  intro i j hij v hv z hz
  rcases hz with ⟨w,hw,rfl⟩
  cases i <;> cases j
  · exact False.elim (hij rfl)
  · have hval : v.toAdd.val = 1 := by
      have hlt := ZMod.val_lt v.toAdd
      have hne := factor_val_ne_zero false v hv
      simp only [factorOrder, Bool.false_eq_true, ite_false] at hlt
      omega
    change 0 < (factorToProjective false v • w).re
    change w.re < 0 at hw
    change 0 < (projectiveS ^ v.toAdd.val • w).re
    rw [hval, pow_one]
    exact S_ping_pong w hw
  · have hval : v.toAdd.val = 1 ∨ v.toAdd.val = 2 := by
      have hlt := ZMod.val_lt v.toAdd
      have hne := factor_val_ne_zero true v hv
      simp only [factorOrder, ite_true] at hlt
      omega
    change (factorToProjective true v • w).re < 0
    change 0 < w.re at hw
    rcases hval with hval | hval
    · change (projectiveR ^ v.toAdd.val • w).re < 0
      rw [hval, pow_one]
      exact R_ping_pong w hw
    · change (projectiveR ^ v.toAdd.val • w).re < 0
      rw [hval]
      exact R_square_ping_pong w hw
  · exact False.elim (hij rfl)

/-- The actual projective modular generators faithfully realize the cyclic free product. -/
theorem freeProductHom_injective :
    Function.Injective (Monoid.CoprodI.lift factorToProjective) := by
  apply Monoid.CoprodI.lift_injective_of_ping_pong factorToProjective _ domain
    domain_nonempty domain_disjoint factor_ping_pong
  right
  refine ⟨true, ?_⟩
  norm_num [Cardinal.mk_fintype, Factor, factorOrder]

private theorem presentationHom_eq_lift :
    presentationHom = (Monoid.CoprodI.lift factorToProjective).comp
      presentationEquiv.toMonoidHom := by
  apply PresentedGroup.ext
  intro b
  cases b
  · change presentationHom ModularCosets.s =
      Monoid.CoprodI.lift factorToProjective (presentationEquiv ModularCosets.s)
    simp [freeGenerator]
  · change presentationHom ModularCosets.t =
      Monoid.CoprodI.lift factorToProjective (presentationEquiv ModularCosets.t)
    simp [freeGenerator]

/-- The actual projective modular presentation has no additional relations. -/
theorem presentationHom_injective : Function.Injective presentationHom := by
  rw [presentationHom_eq_lift]
  exact freeProductHom_injective.comp presentationEquiv.injective

/-- The genuine presentation isomorphism with the center quotient `PSL₂(ℤ)`. -/
def presentationPSLEquiv : ModularCosets.AbstractGroup ≃* PSL2Z :=
  MulEquiv.ofBijective presentationHom
    ⟨presentationHom_injective, presentationHom_surjective⟩

@[simp] theorem presentationPSLEquiv_s :
    presentationPSLEquiv ModularCosets.s = projectiveS := presentationHom_s

@[simp] theorem presentationPSLEquiv_t :
    presentationPSLEquiv ModularCosets.t = projectiveR := presentationHom_t

end
end SerreMarkov.ModularPingPong

import SerreMarkov.ModularCosets
import Mathlib.GroupTheory.CoprodI

/-! # The modular presentation is the actual cyclic free product

The maps in both directions are constructed by the two universal properties.
The inverse identities are verified on all generators and all cyclic-factor
elements, so no presentation or normal-form classification is assumed.
-/

namespace SerreMarkov.ModularFreeProduct

open ModularCosets

/-- A finite cyclic group maps to any monoid element satisfying its relation. -/
def cyclicHom {G : Type*} [Monoid G] (n : ℕ) [NeZero n] (g : G) (hg : g^n=1) :
    Multiplicative (ZMod n) →* G where
  toFun z := g ^ z.toAdd.val
  map_one' := by simp
  map_mul' z w := by
    change g ^ (z.toAdd+w.toAdd).val = g^z.toAdd.val*g^w.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod (z.toAdd.val+w.toAdd.val) hg).symm

@[simp] theorem cyclicHom_generator {G : Type*} [Monoid G] (n : ℕ) [NeZero n]
    (g : G) (hg : g^n=1) : cyclicHom n g hg (Multiplicative.ofAdd (1 : ZMod n)) = g := by
  change g ^ (1 : ZMod n).val = g
  rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hg, pow_one]

/-- False is the order-two factor; true the order-three factor. -/
def factorOrder (b : Bool) : ℕ := if b then 3 else 2
abbrev Factor (b : Bool) := Multiplicative (ZMod (factorOrder b))
abbrev FreeProduct := Monoid.CoprodI Factor

instance factorOrder_neZero (b : Bool) : NeZero (factorOrder b) := by
  cases b <;> exact ⟨by decide⟩

def factorGenerator (b : Bool) : Factor b := Multiplicative.ofAdd 1

theorem factorGenerator_pow (b : Bool) : (factorGenerator b)^(factorOrder b)=1 := by
  cases b <;> decide

/-- Every factor element is an actual power of its chosen generator. -/
theorem factor_eq_generator_pow (b : Bool) (v : Factor b) :
    v = (factorGenerator b)^v.toAdd.val := by
  apply Multiplicative.toAdd.injective
  change v.toAdd = v.toAdd.val • (1 : ZMod (factorOrder b))
  simp only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

def freeGenerator (b : Bool) : FreeProduct := Monoid.CoprodI.of (factorGenerator b)

theorem freeGenerator_pow (b : Bool) : (freeGenerator b)^(factorOrder b)=1 := by
  rw [freeGenerator, ← map_pow, factorGenerator_pow, map_one]

private theorem free_relations : ∀ r ∈ relations, FreeGroup.lift freeGenerator r = 1 := by
  intro r hr
  simp only [relations,Set.mem_insert_iff,Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl
  · simpa only [map_pow,FreeGroup.lift_apply_of,factorOrder,Bool.false_eq_true,ite_false]
      using freeGenerator_pow false
  · simpa only [map_pow,FreeGroup.lift_apply_of,factorOrder,ite_true]
      using freeGenerator_pow true

def toFreeProduct : AbstractGroup →* FreeProduct := PresentedGroup.toGroup free_relations

@[simp] theorem toFreeProduct_s : toFreeProduct s = freeGenerator false := by
  simp [toFreeProduct,s]
@[simp] theorem toFreeProduct_t : toFreeProduct t = freeGenerator true := by
  simp [toFreeProduct,t]

private theorem abstract_generator_pow (b : Bool) :
    (if b then t else s)^(factorOrder b)=1 := by
  cases b
  · exact s_square
  · exact t_cube

def factorToAbstract (b : Bool) : Factor b →* AbstractGroup :=
  cyclicHom (factorOrder b) (if b then t else s) (abstract_generator_pow b)

@[simp] theorem factorToAbstract_generator (b : Bool) :
    factorToAbstract b (factorGenerator b) = if b then t else s := by
  exact cyclicHom_generator _ _ _

def fromFreeProduct : FreeProduct →* AbstractGroup := Monoid.CoprodI.lift factorToAbstract

@[simp] theorem fromFreeProduct_generator (b : Bool) :
    fromFreeProduct (freeGenerator b) = if b then t else s := by
  simp [fromFreeProduct,freeGenerator]

private theorem from_to : fromFreeProduct.comp toFreeProduct = MonoidHom.id AbstractGroup := by
  apply PresentedGroup.ext
  intro b
  cases b
  · change fromFreeProduct (toFreeProduct s) = s
    simp
  · change fromFreeProduct (toFreeProduct t) = t
    simp

private theorem to_from : toFreeProduct.comp fromFreeProduct = MonoidHom.id FreeProduct := by
  apply Monoid.CoprodI.ext_hom
  intro b
  apply MonoidHom.ext
  intro v
  obtain ⟨n,hn⟩ : ∃ n : ℕ, v = (factorGenerator b)^n := ⟨v.toAdd.val,factor_eq_generator_pow b v⟩
  rw [hn,map_pow,map_pow]
  congr 1
  change toFreeProduct (fromFreeProduct (freeGenerator b)) = freeGenerator b
  rw [fromFreeProduct_generator]
  cases b <;> simp

/-- The genuine free-product identification of the abstract modular group. -/
def presentationEquiv : AbstractGroup ≃* FreeProduct where
  toFun := toFreeProduct
  invFun := fromFreeProduct
  left_inv g := DFunLike.congr_fun from_to g
  right_inv g := DFunLike.congr_fun to_from g
  map_mul' := toFreeProduct.map_mul

@[simp] theorem presentationEquiv_s : presentationEquiv s = freeGenerator false := toFreeProduct_s
@[simp] theorem presentationEquiv_t : presentationEquiv t = freeGenerator true := toFreeProduct_t

end SerreMarkov.ModularFreeProduct

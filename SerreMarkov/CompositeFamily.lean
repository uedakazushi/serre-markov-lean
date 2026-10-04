import SerreMarkov.IsometryNecessary
import SerreMarkov.Basis

/-!
# A composite-total orbit invariant stronger than squares and gcd

Modulo fifteen, the signed mutation orbit of `F(14,1)` is contained in an
explicit set of thirty-two points. Closure is checked for all ten generators
by kernel reduction. `F(11,4)` is outside this set, although the two integral
lattices are isometric and the gcd and square invariants agree.

The same file records actual words showing why a generic modulo-total
invariant cannot always recover the family parameter up to one global sign.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace SerreMarkov
namespace CompositeFamily

open Matrix

@[ext] structure SixMod (m : ℕ) where
  a : ZMod m
  b : ZMod m
  c : ZMod m
  d : ZMod m
  e : ZMod m
  f : ZMod m
  deriving DecidableEq

def reduceMod (m : ℕ) (z : Six) : SixMod m := ⟨z.a, z.b, z.c, z.d, z.e, z.f⟩

def stepMod {m : ℕ} : Generator → SixMod m → SixMod m
  | .m1, z => ⟨z.a, z.a*z.b-z.d, z.a*z.c-z.e, z.b, z.c, z.f⟩
  | .i1, z => ⟨z.a, z.d, z.e, z.a*z.d-z.b, z.a*z.e-z.c, z.f⟩
  | .m2, z => ⟨z.a*z.d-z.b, z.a, z.c, z.d, z.d*z.e-z.f, z.e⟩
  | .i2, z => ⟨z.b, z.b*z.d-z.a, z.c, z.d, z.f, z.d*z.f-z.e⟩
  | .m3, z => ⟨z.a, z.f*z.b-z.c, z.b, z.f*z.d-z.e, z.d, z.f⟩
  | .i3, z => ⟨z.a, z.c, z.f*z.c-z.b, z.e, z.f*z.e-z.d, z.f⟩
  | .s1, z => ⟨-z.a, -z.b, -z.c, z.d, z.e, z.f⟩
  | .s2, z => ⟨-z.a, z.b, z.c, -z.d, -z.e, z.f⟩
  | .s3, z => ⟨z.a, -z.b, z.c, -z.d, z.e, -z.f⟩
  | .s4, z => ⟨z.a, z.b, -z.c, z.d, -z.e, -z.f⟩

theorem reduceMod_step (m : ℕ) (g : Generator) (z : Six) :
    reduceMod m (step g z) = stepMod g (reduceMod m z) := by
  cases g <;> apply SixMod.ext <;>
    simp [reduceMod, stepMod, step, mu1, mu2, mu3, inv1, inv2, inv3,
      eps1, eps2, eps3, eps4]

def applyWordMod {m : ℕ} (z : SixMod m) : List Generator → SixMod m
  | [] => z
  | g :: gs => applyWordMod (stepMod g z) gs

theorem reduceMod_word (m : ℕ) (z : Six) (word : List Generator) :
    reduceMod m (applyWord z word) = applyWordMod (reduceMod m z) word := by
  induction word generalizing z with
  | nil => rfl
  | cons g gs ih =>
    simp only [applyWord, applyWordMod, ih, reduceMod_step]

def source : Six := family 14 1
def target : Six := family 11 4

def sourceOrbit15 : List (SixMod 15) :=
  [⟨1, 1, 1, 14, 2, 14⟩,
   ⟨1, 1, 2, 2, 1, 1⟩,
   ⟨1, 1, 13, 2, 14, 14⟩,
   ⟨1, 1, 14, 14, 13, 1⟩,
   ⟨1, 2, 1, 1, 14, 1⟩,
   ⟨1, 2, 14, 1, 1, 14⟩,
   ⟨1, 13, 1, 14, 14, 14⟩,
   ⟨1, 13, 14, 14, 1, 1⟩,
   ⟨1, 14, 1, 1, 2, 1⟩,
   ⟨1, 14, 2, 13, 1, 14⟩,
   ⟨1, 14, 13, 13, 14, 1⟩,
   ⟨1, 14, 14, 1, 13, 14⟩,
   ⟨2, 1, 1, 1, 1, 2⟩,
   ⟨2, 1, 14, 1, 14, 13⟩,
   ⟨2, 14, 1, 14, 1, 13⟩,
   ⟨2, 14, 14, 14, 14, 2⟩,
   ⟨13, 1, 1, 14, 14, 2⟩,
   ⟨13, 1, 14, 14, 1, 13⟩,
   ⟨13, 14, 1, 1, 14, 13⟩,
   ⟨13, 14, 14, 1, 1, 2⟩,
   ⟨14, 1, 1, 1, 13, 14⟩,
   ⟨14, 1, 2, 13, 14, 1⟩,
   ⟨14, 1, 13, 13, 1, 14⟩,
   ⟨14, 1, 14, 1, 2, 1⟩,
   ⟨14, 2, 1, 14, 1, 1⟩,
   ⟨14, 2, 14, 14, 14, 14⟩,
   ⟨14, 13, 1, 1, 1, 14⟩,
   ⟨14, 13, 14, 1, 14, 1⟩,
   ⟨14, 14, 1, 14, 13, 1⟩,
   ⟨14, 14, 2, 2, 14, 14⟩,
   ⟨14, 14, 13, 2, 1, 1⟩,
   ⟨14, 14, 14, 14, 2, 14⟩ ]

theorem sourceOrbit15_closed (g : Generator) (z : SixMod 15)
    (hz : z ∈ sourceOrbit15) : stepMod g z ∈ sourceOrbit15 := by
  simp only [sourceOrbit15, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz
  all_goals subst z
  all_goals cases g <;> decide

theorem applyWord_sourceOrbit15 (word : List Generator) (z : Six)
    (hz : reduceMod 15 z ∈ sourceOrbit15) :
    reduceMod 15 (applyWord z word) ∈ sourceOrbit15 := by
  induction word generalizing z with
  | nil => exact hz
  | cons g gs ih =>
    apply ih
    rw [reduceMod_step]
    exact sourceOrbit15_closed g (reduceMod 15 z) hz

theorem source_mem_orbit15 : reduceMod 15 source ∈ sourceOrbit15 := by decide

theorem target_not_mem_orbit15 : reduceMod 15 target ∉ sourceOrbit15 := by decide

theorem source_target_not_reachable : ¬ Reachable source target := by
  rintro ⟨word, hw⟩
  apply target_not_mem_orbit15
  rw [← hw]
  exact applyWord_sourceOrbit15 word source source_mem_orbit15

theorem source_isSolution : isSolution source := family_isSolution 14 1

theorem target_isSolution : isSolution target := family_isSolution 11 4

theorem source_target_same_gcd : Int.gcd 14 1 = Int.gcd 11 4 := by decide

theorem source_target_same_square : (4 : ZMod 15) ^ 2 = (1 : ZMod 15) ^ 2 := by decide

theorem source_target_isometric : ∃ B : Mat4, B.det = 1 ∧
    Bᵀ * gram source * B = gram target := by
  simpa [source, target] using family_isometry_of_odd_square 15 (by decide) 1 4
    source_target_same_square

theorem composite_lattice_and_gcd_do_not_determine_mutation_orbit :
    (∃ B : Mat4, B.det = 1 ∧ Bᵀ * gram source * B = gram target) ∧
    Int.gcd 14 1 = Int.gcd 11 4 ∧ ¬ Reachable source target :=
  ⟨source_target_isometric, source_target_same_gcd, source_target_not_reachable⟩

/-- This is an identity in the residue ring, not an integral reachability claim. -/
theorem mod25_parameter_change :
    applyWordMod (reduceMod 25 (family 20 5)) [.m1, .i2, .i2, .m1, .m1, .m3] =
      reduceMod 25 (family 15 10) := by decide

theorem mod25_changed_parameter_not_a_sign :
    (10 : ZMod 25) ≠ (5 : ZMod 25) ∧ (10 : ZMod 25) ≠ -(5 : ZMod 25) := by decide

/-- A second such identity, with relatively prime family parameters. -/
theorem mod35_parameter_change :
    applyWordMod (reduceMod 35 (family 32 3)) [.m1, .m3, .i2, .m1, .m3] =
      reduceMod 35 (family 18 17) := by decide

theorem mod35_changed_parameter_not_a_sign :
    (17 : ZMod 35) ≠ (3 : ZMod 35) ∧ (17 : ZMod 35) ≠ -(3 : ZMod 35) := by decide

theorem sourceOrbit15_length : sourceOrbit15.length = 32 := rfl

theorem sourceOrbit15_nodup : sourceOrbit15.Nodup := by decide

/-- The eight coherent sign choices for the rank-one symmetric Gram form. -/
def rankOneStates15 : List (SixMod 15) :=
  [⟨13, 13, 13, 2, 2, 2⟩,
   ⟨13, 13, 2, 2, 13, 13⟩,
   ⟨13, 2, 13, 13, 2, 13⟩,
   ⟨13, 2, 2, 13, 13, 2⟩,
   ⟨2, 13, 13, 13, 13, 2⟩,
   ⟨2, 13, 2, 13, 2, 13⟩,
   ⟨2, 2, 13, 2, 13, 13⟩,
   ⟨2, 2, 2, 2, 2, 2⟩ ]

theorem rankOneStates15_closed (g : Generator) (z : SixMod 15)
    (hz : z ∈ rankOneStates15) : stepMod g z ∈ rankOneStates15 := by
  simp only [rankOneStates15, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with hz | hz | hz | hz | hz | hz | hz | hz
  all_goals subst z
  all_goals cases g <;> decide

theorem applyWord_rankOneStates15 (word : List Generator) (z : Six)
    (hz : reduceMod 15 z ∈ rankOneStates15) :
    reduceMod 15 (applyWord z word) ∈ rankOneStates15 := by
  induction word generalizing z with
  | nil => exact hz
  | cons g gs ih =>
    apply ih
    rw [reduceMod_step]
    exact rankOneStates15_closed g (reduceMod 15 z) hz

theorem total15_two_seven_not_reachable :
    ¬ Reachable (family 13 2) (family 8 7) := by
  rintro ⟨word, hw⟩
  have ht : reduceMod 15 (family 8 7) ∉ rankOneStates15 := by decide
  have hs : reduceMod 15 (family 13 2) ∈ rankOneStates15 := by decide
  apply ht
  rw [← hw]
  exact applyWord_rankOneStates15 word (family 13 2) hs

private theorem total15_square_options (y y' : ℤ)
    (hy : 0 ≤ y) (hy' : 0 ≤ y') (hb : 2 * y ≤ 15) (hb' : 2 * y' ≤ 15)
    (hs : (y' : ZMod 15) ^ 2 = (y : ZMod 15) ^ 2) :
    y = y' ∨ (y = 1 ∧ y' = 4) ∨ (y = 4 ∧ y' = 1) ∨
      (y = 2 ∧ y' = 7) ∨ (y = 7 ∧ y' = 2) := by
  have hy7 : y ≤ 7 := by omega
  have hy7' : y' ≤ 7 := by omega
  interval_cases y <;> interval_cases y'
  all_goals first | decide | (exfalso; revert hs; decide)

theorem normalized_total15_family_reachable_unique (y y' : ℤ)
    (hy : 0 ≤ y) (hy' : 0 ≤ y') (hb : 2 * y ≤ 15) (hb' : 2 * y' ≤ 15)
    (hr : Reachable (family (15-y) y) (family (15-y') y')) : y = y' := by
  obtain ⟨B, hd, hc⟩ := reachable_integral_congruence hr
  have hs := square_of_integer_congruences 15 y y'
    (family_divisibility_of_isometry 15 y y' (by norm_num) B hd hc)
  rcases total15_square_options y y' hy hy' hb hb' hs with heq | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact heq
  · exact False.elim (source_target_not_reachable hr)
  · exact False.elim (source_target_not_reachable (reachable_symm hr))
  · exact False.elim (total15_two_seven_not_reachable hr)
  · exact False.elim (total15_two_seven_not_reachable (reachable_symm hr))

theorem normalized_total15_family_reachable_iff (y y' : ℤ)
    (hy : 0 ≤ y) (hy' : 0 ≤ y') (hb : 2 * y ≤ 15) (hb' : 2 * y' ≤ 15) :
    Reachable (family (15-y) y) (family (15-y') y') ↔ y = y' := by
  constructor
  · exact normalized_total15_family_reachable_unique y y' hy hy' hb hb'
  · rintro rfl
    exact reachable_refl _

/-- The proposed modulo-total parameter rigidity already fails at modulus 25.
This statement concerns residue tuples, rather than integral mutation orbits. -/
theorem not_generic_mod25_parameter_rigidity :
    ¬ (∀ (y y' : ℤ) (word : List Generator),
      applyWordMod (reduceMod 25 (family (-y) y)) word =
        reduceMod 25 (family (-y') y') →
      (y' : ZMod 25) = (y : ZMod 25) ∨ (y' : ZMod 25) = -(y : ZMod 25)) := by
  intro h
  have hw : applyWordMod (reduceMod 25 (family (-5) 5))
      [.m1, .i2, .i2, .m1, .m1, .m3] = reduceMod 25 (family (-10) 10) := by decide
  rcases h 5 10 [.m1, .i2, .i2, .m1, .m1, .m3] hw with hp | hn
  · exact mod25_changed_parameter_not_a_sign.1 hp
  · exact mod25_changed_parameter_not_a_sign.2 hn

private theorem small_dvd_eq_zero (m : ℕ) (a : ℤ)
    (hlo : -(m : ℤ) < a) (hhi : a < m) (hd : (m : ℤ) ∣ a) : a = 0 := by
  obtain ⟨k, hk⟩ := hd
  have hk0 : k = 0 := by
    by_contra hn
    have hcases : k ≤ -1 ∨ 1 ≤ k := by omega
    rcases hcases with hn | hp
    · have hprod := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ (m : ℤ) by omega)
        (show k + 1 ≤ 0 by omega)
      nlinarith
    · have hprod := mul_nonneg (show 0 ≤ (m : ℤ) by omega)
        (show 0 ≤ k - 1 by omega)
      nlinarith
  simpa [hk0] using hk

private theorem small_intCast_injective (m : ℕ) (hm : 5 ≤ m) (a b : ℤ)
    (ha : -2 ≤ a ∧ a ≤ 2) (hb : -2 ≤ b ∧ b ≤ 2)
    (hcast : (a : ZMod m) = (b : ZMod m)) : a = b := by
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub a b m).mp hcast
  have hz := small_dvd_eq_zero m (b - a) (by omega) (by omega) hd
  omega

private theorem normalized_parameter_of_small_residue_sign (m : ℕ) (hm : 5 ≤ m)
    (k y : ℤ) (hk : k = 1 ∨ k = 2) (hy : 0 ≤ y) (hb : 2 * y ≤ m)
    (hs : (y : ZMod m) = (k : ZMod m) ∨ (y : ZMod m) = -(k : ZMod m)) : y = k := by
  have hkBounds : 1 ≤ k ∧ k ≤ 2 := by rcases hk with rfl | rfl <;> omega
  rcases hs with hp | hn
  · have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub y k m).mp hp
    have hz := small_dvd_eq_zero m (k - y) (by omega) (by omega) hd
    omega
  · have hcast : (y : ZMod m) = ((-k : ℤ) : ZMod m) := by simpa using hn
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub y (-k) m).mp hcast
    have hz := small_dvd_eq_zero m (-k - y) (by omega) (by omega) hd
    omega

private theorem reduceList_step_closed (m : ℕ) (states : List Six)
    (hc : ∀ g z, z ∈ states → step g z ∈ states) (g : Generator) (z : SixMod m)
    (hz : z ∈ states.map (reduceMod m)) : stepMod g z ∈ states.map (reduceMod m) := by
  rcases List.mem_map.mp hz with ⟨z0, hz0, rfl⟩
  rw [← reduceMod_step]
  exact List.mem_map.mpr ⟨step g z0, hc g z0 hz0, rfl⟩

private theorem reduceList_word_closed (m : ℕ) (states : List Six)
    (hc : ∀ g z, z ∈ states → step g z ∈ states) (z : Six) (word : List Generator)
    (hz : reduceMod m z ∈ states.map (reduceMod m)) :
    reduceMod m (applyWord z word) ∈ states.map (reduceMod m) := by
  induction word generalizing z with
  | nil => exact hz
  | cons g gs ih =>
    apply ih
    rw [reduceMod_step]
    exact reduceList_step_closed m states hc g (reduceMod m z) hz

private theorem reduced_family_parameter_sign (m : ℕ) (hm : 5 ≤ m) (k y : ℤ)
    (states : List Six)
    (hp : ∀ z, z ∈ states → (-2 ≤ z.c ∧ z.c ≤ 2) ∧ (-2 ≤ z.d ∧ z.d ≤ 2) ∧
      (z.c = -2 → z.d = 2 → z.e = k ∨ z.e = -k))
    (hz : reduceMod m (family ((m : ℤ) - y) y) ∈ states.map (reduceMod m)) :
    (y : ZMod m) = (k : ZMod m) ∨ (y : ZMod m) = -(k : ZMod m) := by
  rcases List.mem_map.mp hz with ⟨z0, hz0, heq⟩
  obtain ⟨hcB, hdB, heP⟩ := hp z0 hz0
  have hcCast : (z0.c : ZMod m) = ((-2 : ℤ) : ZMod m) := by
    simpa [reduceMod, family] using congrArg SixMod.c heq
  have hdCast : (z0.d : ZMod m) = ((2 : ℤ) : ZMod m) := by
    simpa [reduceMod, family] using congrArg SixMod.d heq
  have hc := small_intCast_injective m hm z0.c (-2) hcB (by omega) hcCast
  have hd := small_intCast_injective m hm z0.d 2 hdB (by omega) hdCast
  have heCast : (z0.e : ZMod m) = -(y : ZMod m) := by
    simpa [reduceMod, family] using congrArg SixMod.e heq
  rcases heP hc hd with he | he
  · rw [he] at heCast
    right
    have hn := congrArg Neg.neg heCast
    simpa using hn.symm
  · rw [he] at heCast
    left
    have hn := congrArg Neg.neg heCast
    simpa using hn.symm

/-- A finite integer set containing the mutation orbit for the parameter `1`. -/
def finiteAngleStates1 : List Six :=
  [⟨1, 1, 1, -1, 2, -1⟩,
   ⟨1, 1, 2, 2, 1, 1⟩,
   ⟨1, 1, -2, 2, -1, -1⟩,
   ⟨1, 1, -1, -1, -2, 1⟩,
   ⟨1, 2, 1, 1, -1, 1⟩,
   ⟨1, 2, -1, 1, 1, -1⟩,
   ⟨1, -2, 1, -1, -1, -1⟩,
   ⟨1, -2, -1, -1, 1, 1⟩,
   ⟨1, -1, 1, 1, 2, 1⟩,
   ⟨1, -1, 2, -2, 1, -1⟩,
   ⟨1, -1, -2, -2, -1, 1⟩,
   ⟨1, -1, -1, 1, -2, -1⟩,
   ⟨2, 1, 1, 1, 1, 2⟩,
   ⟨2, 1, -1, 1, -1, -2⟩,
   ⟨2, -1, 1, -1, 1, -2⟩,
   ⟨2, -1, -1, -1, -1, 2⟩,
   ⟨-2, 1, 1, -1, -1, 2⟩,
   ⟨-2, 1, -1, -1, 1, -2⟩,
   ⟨-2, -1, 1, 1, -1, -2⟩,
   ⟨-2, -1, -1, 1, 1, 2⟩,
   ⟨-1, 1, 1, 1, -2, -1⟩,
   ⟨-1, 1, 2, -2, -1, 1⟩,
   ⟨-1, 1, -2, -2, 1, -1⟩,
   ⟨-1, 1, -1, 1, 2, 1⟩,
   ⟨-1, 2, 1, -1, 1, 1⟩,
   ⟨-1, 2, -1, -1, -1, -1⟩,
   ⟨-1, -2, 1, 1, 1, -1⟩,
   ⟨-1, -2, -1, 1, -1, 1⟩,
   ⟨-1, -1, 1, -1, -2, 1⟩,
   ⟨-1, -1, 2, 2, -1, -1⟩,
   ⟨-1, -1, -2, 2, 1, 1⟩,
   ⟨-1, -1, -1, -1, 2, -1⟩ ]

theorem finiteAngleStates1_closed (g : Generator) (z : Six)
    (hz : z ∈ finiteAngleStates1) : step g z ∈ finiteAngleStates1 := by
  simp only [finiteAngleStates1, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz
  all_goals subst z
  all_goals cases g <;> decide

private theorem finiteAngleStates1_profile (z : Six) (hz : z ∈ finiteAngleStates1) :
    (-2 ≤ z.c ∧ z.c ≤ 2) ∧ (-2 ≤ z.d ∧ z.d ≤ 2) ∧
      (z.c = -2 → z.d = 2 → z.e = 1 ∨ z.e = -1) := by
  simp only [finiteAngleStates1, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz
  all_goals subst z
  all_goals decide

theorem normalized_parameter1_family_unique (m : ℕ) (hm : 5 ≤ m) (y : ℤ)
    (hy : 0 ≤ y) (hb : 2 * y ≤ m)
    (hr : Reachable (family ((m : ℤ)-1) 1) (family ((m : ℤ)-y) y)) : y = 1 := by
  obtain ⟨word, hw⟩ := hr
  have hsourceEq : reduceMod m (family ((m : ℤ)-1) 1) =
      reduceMod m (family (-1) 1) := by
    apply SixMod.ext <;> simp [reduceMod, family]
  have hsource : reduceMod m (family ((m : ℤ)-1) 1) ∈
      finiteAngleStates1.map (reduceMod m) := by
    rw [hsourceEq]
    exact List.mem_map.mpr ⟨family (-1) 1, by decide, rfl⟩
  have htarget := reduceList_word_closed m finiteAngleStates1 finiteAngleStates1_closed
    (family ((m : ℤ)-1) 1) word hsource
  rw [hw] at htarget
  have hsign := reduced_family_parameter_sign m hm 1 y finiteAngleStates1
    finiteAngleStates1_profile htarget
  exact normalized_parameter_of_small_residue_sign m hm 1 y (by decide) hy hb hsign

/-- A finite integer set containing the mutation orbit for the parameter `2`. -/
def finiteAngleStates2 : List Six :=
  [⟨-2, -2, -2, 2, 2, 2⟩,
   ⟨-2, -2, 2, 2, -2, -2⟩,
   ⟨-2, 2, -2, -2, 2, -2⟩,
   ⟨-2, 2, 2, -2, -2, 2⟩,
   ⟨2, -2, -2, -2, -2, 2⟩,
   ⟨2, -2, 2, -2, 2, -2⟩,
   ⟨2, 2, -2, 2, -2, -2⟩,
   ⟨2, 2, 2, 2, 2, 2⟩ ]

theorem finiteAngleStates2_closed (g : Generator) (z : Six)
    (hz : z ∈ finiteAngleStates2) : step g z ∈ finiteAngleStates2 := by
  simp only [finiteAngleStates2, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with hz | hz | hz | hz | hz | hz | hz | hz
  all_goals subst z
  all_goals cases g <;> decide

private theorem finiteAngleStates2_profile (z : Six) (hz : z ∈ finiteAngleStates2) :
    (-2 ≤ z.c ∧ z.c ≤ 2) ∧ (-2 ≤ z.d ∧ z.d ≤ 2) ∧
      (z.c = -2 → z.d = 2 → z.e = 2 ∨ z.e = -2) := by
  simp only [finiteAngleStates2, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with hz | hz | hz | hz | hz | hz | hz | hz
  all_goals subst z
  all_goals decide

theorem normalized_parameter2_family_unique (m : ℕ) (hm : 5 ≤ m) (y : ℤ)
    (hy : 0 ≤ y) (hb : 2 * y ≤ m)
    (hr : Reachable (family ((m : ℤ)-2) 2) (family ((m : ℤ)-y) y)) : y = 2 := by
  obtain ⟨word, hw⟩ := hr
  have hsourceEq : reduceMod m (family ((m : ℤ)-2) 2) =
      reduceMod m (family (-2) 2) := by
    apply SixMod.ext <;> simp [reduceMod, family]
  have hsource : reduceMod m (family ((m : ℤ)-2) 2) ∈
      finiteAngleStates2.map (reduceMod m) := by
    rw [hsourceEq]
    exact List.mem_map.mpr ⟨family (-2) 2, by decide, rfl⟩
  have htarget := reduceList_word_closed m finiteAngleStates2 finiteAngleStates2_closed
    (family ((m : ℤ)-2) 2) word hsource
  rw [hw] at htarget
  have hsign := reduced_family_parameter_sign m hm 2 y finiteAngleStates2
    finiteAngleStates2_profile htarget
  exact normalized_parameter_of_small_residue_sign m hm 2 y (by decide) hy hb hsign

end CompositeFamily
end SerreMarkov

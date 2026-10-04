import SerreMarkov.IndexTwelve
import Mathlib.Tactic

/-!
# Complete finite matching census: enumeration foundation

The recursive enumerator explores partners of the first unused vertex.  Its
coverage theorem below is a mathematical induction, independent of execution
of the finite census.  In particular, it never ranges over the 12^12 functions
on `Fin 12`.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace SerreMarkov.IndexTwelve

/-- Install a disjoint pair over an involution on the remaining vertices. -/
def installPair {V : Type*} [DecidableEq V] (x y : V) (a : V → V) : V → V :=
  fun z => if z = x then y else if z = y then x else a z

/-- Partner enumeration, with one unit of fuel per pair. -/
def enumerateInvolutions {V : Type*} [DecidableEq V] :
    Nat → List V → List (V → V)
  | 0, xs => if xs = [] then [id] else []
  | _ + 1, [] => [id]
  | n + 1, x :: xs =>
      xs.flatMap fun y =>
        (enumerateInvolutions n (xs.erase y)).map (installPair x y)

/-- Completeness of partner enumeration for every finite support and involution.
The empty support is represented by the identity function outside the support. -/
theorem enumerateInvolutions_complete {V : Type*} [DecidableEq V]
    (fuel : Nat) (xs : List V) (a : V → V)
    (hnd : xs.Nodup) (hlen : xs.length = 2 * fuel)
    (hinv : ∀ z, a (a z) = z)
    (hnofix : ∀ z ∈ xs, a z ≠ z)
    (hout : ∀ z, z ∉ xs → a z = z) :
    a ∈ enumerateInvolutions fuel xs := by
  induction fuel generalizing xs a with
  | zero =>
      have hnil : xs = [] := List.length_eq_zero_iff.mp (by omega)
      subst xs
      have ha : a = id := funext fun z => hout z (by simp)
      subst a
      simp [enumerateInvolutions]
  | succ n ih =>
      cases xs with
      | nil => simp at hlen
      | cons x xs =>
          have hxnot : x ∉ xs := (List.nodup_cons.mp hnd).1
          have hxsnd : xs.Nodup := (List.nodup_cons.mp hnd).2
          let y := a x
          have hyx : y ≠ x := hnofix x (by simp)
          have haxy : a x = y := rfl
          have hayx : a y = x := hinv x
          have hymemall : y ∈ x :: xs := by
            by_contra h
            have hyfixed := hout y h
            have hxy : x = y := by
              calc
                x = a y := hayx.symm
                _ = y := hyfixed
            exact hyx hxy.symm
          have hymem : y ∈ xs := by
            rcases List.mem_cons.mp hymemall with h | h
            · exact False.elim (hyx h)
            · exact h
          let b : V → V := fun z => if z = x ∨ z = y then z else a z
          have hb_inv : ∀ z, b (b z) = z := by
            intro z
            by_cases hzx : z = x
            · subst z; simp [b]
            by_cases hzy : z = y
            · subst z; simp [b]
            have hazx : a z ≠ x := by
              intro h
              have hh := congrArg a h
              rw [hinv z, haxy] at hh
              exact hzy hh
            have hazy : a z ≠ y := by
              intro h
              have hh := congrArg a h
              rw [hinv z, hayx] at hh
              exact hzx hh
            simp [b, hzx, hzy, hazx, hazy, hinv z]
          have hb_nofix : ∀ z ∈ xs.erase y, b z ≠ z := by
            intro z hz
            have hz' := (hxsnd.mem_erase_iff.mp hz)
            have hzx : z ≠ x := by
              intro h
              subst z
              exact hxnot hz'.2
            simp only [b, hzx, hz'.1, or_self, ↓reduceIte]
            exact hnofix z (List.mem_cons_of_mem x hz'.2)
          have hb_out : ∀ z, z ∉ xs.erase y → b z = z := by
            intro z hz
            by_cases hzx : z = x
            · simp [b, hzx]
            by_cases hzy : z = y
            · simp [b, hzy]
            have hzall : z ∉ x :: xs := by
              intro hall
              rcases List.mem_cons.mp hall with h | h
              · exact hzx h
              · exact hz (hxsnd.mem_erase_iff.mpr ⟨hzy, h⟩)
            simp [b, hzx, hzy, hout z hzall]
          have hrestlen : (xs.erase y).length = 2 * n := by
            rw [List.length_erase_of_mem hymem]
            simp only [List.length_cons] at hlen
            omega
          have hbmem : b ∈ enumerateInvolutions n (xs.erase y) :=
            ih (xs.erase y) b (List.Nodup.erase y hxsnd) hrestlen
              hb_inv hb_nofix hb_out
          rw [enumerateInvolutions]
          apply List.mem_flatMap.mpr
          refine ⟨y, hymem, List.mem_map.mpr ?_⟩
          refine ⟨b, hbmem, ?_⟩
          funext z
          by_cases hzx : z = x
          · simp [installPair, hzx, haxy]
          by_cases hzy : z = y
          · simp [installPair, hzy, hayx]
          simp [installPair, b, hzx, hzy]

/-- The 10,395 candidates generated from the twelve ordered vertices. -/
def allMatchingInvolutions : List VertexMap :=
  enumerateInvolutions 6 (List.finRange 12)

/-- Every fixed-point-free involution on the twelve vertices occurs in the
recursive list.  This theorem quantifies over all maps, without a search bound
on their coefficients and without enumerating all functions. -/
theorem allMatchingInvolutions_complete (a : VertexMap)
    (hinv : ∀ i, a (a i) = i) (hnofix : ∀ i, a i ≠ i) :
    a ∈ allMatchingInvolutions := by
  apply enumerateInvolutions_complete 6 (List.finRange 12) a
  · exact List.nodup_finRange 12
  · decide
  · exact hinv
  · intro i hi
    exact hnofix i
  · intro i hi
    exact False.elim (hi (List.mem_finRange i))

/-- The maps listed as representatives in the original finite table. -/
def representative (i : Fin 5) : VertexMap :=
  match i.val with
  | 0 => alphaOneEleven
  | 1 => alphaTwoTen
  | 2 => alphaThreeNine
  | 3 => alphaFourEight
  | _ => alphaSixSix

/-- Decode a list of twelve natural numbers as a finite map. -/
def vertexCode (code : List Nat) (i : Vertex) : Vertex :=
  ⟨code.getD i.val 0 % 12, Nat.mod_lt _ (by decide)⟩

def colorTwoCode (code : List Nat) (i : Vertex) : Fin 2 :=
  ⟨code.getD i.val 0 % 2, Nat.mod_lt _ (by decide)⟩

def colorFourCode (code : List Nat) (i : Vertex) : Fin 4 :=
  ⟨code.getD i.val 0 % 4, Nat.mod_lt _ (by decide)⟩

/-- Two cyclic orbits of a permutation cover the finite vertex set.
The theorem below only needs this at-most-two condition; requiring exactly two
orbits gives the usual two-cusp condition as an immediate special case. -/
def AtMostTwoCycles (p : VertexMap) : Prop :=
  ∃ x y : Vertex, ∀ z : Vertex,
    (∃ n : Nat, (p^[n]) x = z) ∨ (∃ n : Nat, (p^[n]) y = z)

/-- Simultaneous conjugacy with beta fixed. -/
def ConjugateFixedBeta (a b : VertexMap) : Prop :=
  ∃ g : VertexMap, Function.Bijective g ∧
    (∀ i, g (a i) = b (g i)) ∧ (∀ i, g (beta i) = beta (g i))

/-- A candidate has an explicit invariant bipartition, four invariant cusp
colors, or an actual simultaneous conjugacy to one of the five representatives. -/
inductive CensusWitness where
  | disconnected (colors : List Nat)
  | manyCycles (colors : List Nat)
  | conjugate (rep : Fin 5) (conjugator : List Nat)

def WitnessValid (a : VertexMap) : CensusWitness → Prop
  | .disconnected colors =>
      Function.Surjective (colorTwoCode colors) ∧
      (∀ i, colorTwoCode colors (a i) = colorTwoCode colors i) ∧
      (∀ i, colorTwoCode colors (beta i) = colorTwoCode colors i)
  | .manyCycles colors =>
      Function.Surjective (colorFourCode colors) ∧
      (∀ i, colorFourCode colors (cusp a i) = colorFourCode colors i)
  | .conjugate rep code =>
      Function.Bijective (vertexCode code) ∧
      (∀ i, vertexCode code (a i) = representative rep (vertexCode code i)) ∧
      (∀ i, vertexCode code (beta i) = beta (vertexCode code i))

/-- For an endomap of a finite set, surjectivity is enough to decide bijectivity.
The generic finite-set theorem supplies injectivity; the finite checker therefore
avoids a redundant quadratic injection test for every conjugator. -/
def vertexBijectiveDecidable (g : VertexMap) : Decidable (Function.Bijective g) := by
  letI : Decidable (Function.Surjective g) := by
    unfold Function.Surjective
    infer_instance
  exact decidable_of_iff (Function.Surjective g) Finite.surjective_iff_bijective

instance witnessValidDecidable (a : VertexMap) (w : CensusWitness) :
    Decidable (WitnessValid a w) := by
  cases w with
  | disconnected colors =>
      unfold WitnessValid Function.Surjective
      infer_instance
  | manyCycles colors =>
      unfold WitnessValid Function.Surjective
      infer_instance
  | conjugate rep code =>
      unfold WitnessValid
      letI : Decidable (Function.Bijective (vertexCode code)) :=
        vertexBijectiveDecidable (vertexCode code)
      infer_instance

/-- Invariant colors are preserved by every actual generator word. -/
theorem evalWord_preserves_color {C : Type*} (a : VertexMap) (c : Vertex → C)
    (ha : ∀ i, c (a i) = c i) (hb : ∀ i, c (beta i) = c i)
    (word : List Bool) (start : Vertex) :
    c (evalWord a word start) = c start := by
  induction word generalizing start with
  | nil => rfl
  | cons bit word ih =>
      cases bit
      · change c (evalWord a word (a start)) = c start
        rw [ih, ha]
      · change c (evalWord a word (beta start)) = c start
        rw [ih, hb]

/-- An invariant nonconstant coloring contradicts the full word transitivity. -/
theorem no_disconnected_witness (a : VertexMap) (colors : List Nat)
    (ht : TransitivePair a) : ¬ WitnessValid a (.disconnected colors) := by
  rintro ⟨hsurj, ha, hb⟩
  obtain ⟨x, hx⟩ := hsurj 0
  obtain ⟨y, hy⟩ := hsurj 1
  obtain ⟨word, hw⟩ := ht x y
  have hh := evalWord_preserves_color a (colorTwoCode colors) ha hb word x
  rw [hw, hx, hy] at hh
  exact (by decide : (1 : Fin 2) ≠ 0) hh

/-- A coloring invariant under one step is invariant under every iterate. -/
theorem iterate_preserves_color {C : Type*} (p : VertexMap) (c : Vertex → C)
    (hc : ∀ i, c (p i) = c i) (n : Nat) (i : Vertex) :
    c ((p^[n]) i) = c i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', hc, ih]

/-- A four-color invariant coloring contradicts coverage by two cyclic orbits. -/
theorem no_manyCycles_witness (a : VertexMap) (colors : List Nat)
    (htwo : AtMostTwoCycles (cusp a)) :
    ¬ WitnessValid a (.manyCycles colors) := by
  rintro ⟨hsurj, hc⟩
  obtain ⟨x, y, hcover⟩ := htwo
  have hcolors : ∀ u v : Fin 4, ∃ w : Fin 4, w ≠ u ∧ w ≠ v := by decide
  obtain ⟨w, hwx, hwy⟩ := hcolors (colorFourCode colors x) (colorFourCode colors y)
  obtain ⟨z, hz⟩ := hsurj w
  rcases hcover z with ⟨n, hn⟩ | ⟨n, hn⟩
  · have hh := iterate_preserves_color (cusp a) (colorFourCode colors) hc n x
    rw [hn, hz] at hh
    exact hwx hh
  · have hh := iterate_preserves_color (cusp a) (colorFourCode colors) hc n y
    rw [hn, hz] at hh
    exact hwy hh

/-- Every valid certificate in the transitive two-cusp case is a conjugacy. -/
theorem witness_gives_classification (a : VertexMap) (w : CensusWitness)
    (hw : WitnessValid a w) (ht : TransitivePair a)
    (htwo : AtMostTwoCycles (cusp a)) :
    ∃ r : Fin 5, ConjugateFixedBeta a (representative r) := by
  cases w with
  | disconnected colors => exact False.elim (no_disconnected_witness a colors ht hw)
  | manyCycles colors => exact False.elim (no_manyCycles_witness a colors htwo hw)
  | conjugate rep code => exact ⟨rep, vertexCode code, hw⟩

/-- One explicit map and its independently checked certificate. -/
structure CensusRow where
  alpha : List Nat
  witness : CensusWitness

def CensusRow.Valid (row : CensusRow) : Prop :=
  WitnessValid (vertexCode row.alpha) row.witness

instance rowValidDecidable (row : CensusRow) : Decidable row.Valid :=
  witnessValidDecidable (vertexCode row.alpha) row.witness

/-- Boolean-only surjectivity checker. Its correctness is proved separately. -/
def finiteSurjectiveCheck {n m : Nat} (g : Fin n → Fin m) : Bool :=
  (List.finRange m).all fun y => (List.finRange n).any fun x => decide (g x = y)

theorem finiteSurjectiveCheck_correct {n m : Nat} (g : Fin n → Fin m) :
    finiteSurjectiveCheck g = true ↔ Function.Surjective g := by
  simp [finiteSurjectiveCheck, List.all_eq_true, List.any_eq_true, Function.Surjective]

def finiteEqualityCheck {n m : Nat} (f g : Fin n → Fin m) : Bool :=
  (List.finRange n).all fun i => decide (f i = g i)

theorem finiteEqualityCheck_correct {n m : Nat} (f g : Fin n → Fin m) :
    finiteEqualityCheck f g = true ↔ ∀ i, f i = g i := by
  simp [finiteEqualityCheck, List.all_eq_true]

/-- A Boolean verifier avoids normalization of proof-valued finite decisions
for every row. All checked predicates retain their proved semantic meaning. -/
def WitnessCheck (a : VertexMap) : CensusWitness → Bool
  | .disconnected colors =>
      let c := colorTwoCode colors
      finiteSurjectiveCheck c && finiteEqualityCheck (c ∘ a) c &&
        finiteEqualityCheck (c ∘ beta) c
  | .manyCycles colors =>
      let c := colorFourCode colors
      finiteSurjectiveCheck c && finiteEqualityCheck (c ∘ cusp a) c
  | .conjugate rep code =>
      let g := vertexCode code
      finiteSurjectiveCheck g && finiteEqualityCheck (g ∘ a) (representative rep ∘ g) &&
        finiteEqualityCheck (g ∘ beta) (beta ∘ g)

theorem WitnessCheck_correct (a : VertexMap) (w : CensusWitness) :
    WitnessCheck a w = true ↔ WitnessValid a w := by
  cases w <;>
    simp only [WitnessCheck, WitnessValid, Bool.and_eq_true,
      finiteSurjectiveCheck_correct, finiteEqualityCheck_correct,
      Function.comp_apply, ← Finite.surjective_iff_bijective, and_assoc]

def CensusRow.Check (row : CensusRow) : Bool :=
  WitnessCheck (vertexCode row.alpha) row.witness

theorem CensusRow.check_correct (row : CensusRow) : row.Check = true ↔ row.Valid :=
  WitnessCheck_correct (vertexCode row.alpha) row.witness

end SerreMarkov.IndexTwelve

import SerreMarkov.PositiveBoundedTable

/-!
# A complete pruned enumeration of the bounded positive chamber

The recursive list enumerates all nonnegative offset tuples of a given length
and bounded sum. Five offsets determine five Gram coordinates; the exact
quadratic solution equation determines the remaining coordinate by division.
No unbounded height reduction is asserted.
-/

namespace SerreMarkov.PositiveBounded

open IntrinsicSigns

def Bounded (z : Six) : Prop :=
  isSolution z ∧ 3 ≤ z.a ∧ 3 ≤ z.b ∧ 3 ≤ z.c ∧ 3 ≤ z.d ∧ 3 ≤ z.e ∧ 3 ≤ z.f ∧
    0 < thirdMinorSum z ∧ z.a+z.b+z.c+z.d+z.e+z.f ≤ 37

instance (z : Six) : Decidable (Bounded z) := by unfold Bounded isSolution; infer_instance

def boundedTuples : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | k+1, B => (List.range (B+1)).flatMap
      (fun i => (boundedTuples k (B-i)).map (List.cons i))

theorem boundedTuples_complete (k B : ℕ) (xs : List ℕ)
    (hlen : xs.length = k) (hsum : xs.sum ≤ B) : xs ∈ boundedTuples k B := by
  induction k generalizing B xs with
  | zero =>
      have he : xs = [] := List.length_eq_zero_iff.mp hlen
      simp [he,boundedTuples]
  | succ k ih =>
      cases xs with
      | nil => simp at hlen
      | cons i xs =>
          have hi : i < B+1 := by simp only [List.sum_cons] at hsum; omega
          have htail : xs.sum ≤ B-i := by simp only [List.sum_cons] at hsum; omega
          have htail_len : xs.length = k := by simpa using hlen
          exact List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,
            List.mem_map.mpr ⟨xs,ih (B-i) xs htail_len htail,rfl⟩⟩

def fromOffsets (xs : List ℕ) (q : ℤ) : Six :=
  let a : ℤ := xs.getD 0 0 + 3
  let b : ℤ := xs.getD 1 0 + 3
  let c : ℤ := xs.getD 2 0 + 3
  let d : ℤ := xs.getD 3 0 + 3
  let f : ℤ := xs.getD 4 0 + 3
  ⟨a,b,c,d,(a*f+c*d-q)/b,f⟩

def candidateTuples (xs : List ℕ) : List Six := [fromOffsets xs 4,fromOffsets xs (-4)]

def allCandidates : List Six := (boundedTuples 5 19).flatMap candidateTuples

def allSolutions : List Six := allCandidates.filter (fun z => decide (Bounded z))

def blockCandidates (a b : ℕ) : List Six :=
  (boundedTuples 3 (19-a-b)).flatMap (fun xs => candidateTuples (a::b::xs))

def blockSolutions (a b : ℕ) : List Six :=
  (blockCandidates a b).filter (fun z => decide (Bounded z))

def blockCheck (a b : ℕ) : Bool :=
  (blockSolutions a b).all (fun z => decide (z ∈ PositiveBoundedTable.table))

theorem candidates_split : allCandidates = (List.range 20).flatMap (fun a =>
    (List.range (19-a+1)).flatMap (fun b => blockCandidates a b)) := by
  simp only [allCandidates,boundedTuples,List.flatMap_assoc,List.flatMap_map,
    blockCandidates]

theorem solutions_split : allSolutions = (List.range 20).flatMap (fun a =>
    (List.range (19-a+1)).flatMap (fun b => blockSolutions a b)) := by
  rw [allSolutions,candidates_split]
  simp only [List.filter_flatMap,blockSolutions]

/-- Every actual bounded solution occurs in the pruned list. Division is
justified from its exact equation, so no solution is lost by the pruning. -/
theorem bounded_mem_allSolutions (z : Six) (hz : Bounded z) : z ∈ allSolutions := by
  rcases hz with ⟨hsol,ha,hb,hc,hd,he,hf,hpos,hbound⟩
  let xs := [(z.a-3).toNat,(z.b-3).toNat,(z.c-3).toNat,(z.d-3).toNat,(z.f-3).toNat]
  have hca : ((z.a-3).toNat : ℤ) = z.a-3 := Int.toNat_of_nonneg (by omega)
  have hcb : ((z.b-3).toNat : ℤ) = z.b-3 := Int.toNat_of_nonneg (by omega)
  have hcc : ((z.c-3).toNat : ℤ) = z.c-3 := Int.toNat_of_nonneg (by omega)
  have hcd : ((z.d-3).toNat : ℤ) = z.d-3 := Int.toNat_of_nonneg (by omega)
  have hcf : ((z.f-3).toNat : ℤ) = z.f-3 := Int.toNat_of_nonneg (by omega)
  have hxsum : xs.sum ≤ 19 := by
    have hcast : (xs.sum : ℤ) = z.a+z.b+z.c+z.d+z.f-15 := by
      simp [xs,hca,hcb,hcc,hcd,hcf]
      ring
    have hi : (xs.sum : ℤ) ≤ 19 := by omega
    exact_mod_cast hi
  have hx : xs ∈ boundedTuples 5 19 := boundedTuples_complete 5 19 xs rfl hxsum
  have hdiv : (z.a*z.f+z.c*z.d-q2 z)/z.b = z.e := by
    have hn : z.a*z.f+z.c*z.d-q2 z = z.b*z.e := by unfold q2; ring
    rw [hn]
    exact Int.mul_ediv_cancel_left _ (by omega)
  have hfrom : fromOffsets xs (q2 z) = z := by
    ext <;> simp only [fromOffsets,xs,List.getD_cons_zero,List.getD_cons_succ,
      hca,hcb,hcc,hcd,hcf,sub_add_cancel,hdiv]
  have hq : q2 z = 4 ∨ q2 z = -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hsol.2)
  have hmem : z ∈ allCandidates := by
    apply List.mem_flatMap.mpr
    refine ⟨xs,hx,?_⟩
    rcases hq with hq | hq
    · rw [hq] at hfrom
      simp only [candidateTuples,List.mem_cons]
      exact Or.inl hfrom.symm
    · rw [hq] at hfrom
      simp only [candidateTuples,List.mem_cons]
      exact Or.inr (Or.inl hfrom.symm)
  apply List.mem_filter.mpr
  exact ⟨hmem,by simpa only [decide_eq_true_eq] using
    (show Bounded z from ⟨hsol,ha,hb,hc,hd,he,hf,hpos,hbound⟩)⟩

theorem blockCheck_correct (a b : ℕ) (h : blockCheck a b = true) :
    ∀ z ∈ blockSolutions a b, z ∈ PositiveBoundedTable.table := by
  intro z hz
  have hc := List.all_eq_true.mp h z hz
  exact of_decide_eq_true hc

end SerreMarkov.PositiveBounded

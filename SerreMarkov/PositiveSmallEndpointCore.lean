import SerreMarkov.PositiveSmallEndpointBase

/-! Structural completeness: every actual tuple within the proved endpoint
caps is encoded in a checked candidate block. -/

namespace SerreMarkov.PositiveSmallEndpointCensus

open PositiveChamber PositiveShortWord PositiveEndpointBounds PositiveBounded

theorem checked_small_endpoints_total_bound
    (hchecks : ∀ a f : Fin 3, ∀ b : Fin 52, blockCheck a.val f.val b.val=true)
    (z : Six) (hz : Chamber z) (ha5 : z.a ≤ 5) (hf5 : z.f ≤ 5)
    (ht : ShortTerminal z 2) : z.a+z.b+z.c+z.d+z.e+z.f ≤ 37 := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := hz.2.2
  let a := (z.a-3).toNat
  let f := (z.f-3).toNat
  let b := (z.b-3).toNat
  let xs := [(z.c-3).toNat,(z.d-3).toNat]
  have hca : (a : ℤ)=z.a-3 := Int.toNat_of_nonneg (by omega)
  have hcf : (f : ℤ)=z.f-3 := Int.toNat_of_nonneg (by omega)
  have hcb : (b : ℤ)=z.b-3 := Int.toNat_of_nonneg (by omega)
  have hcc : ((z.c-3).toNat : ℤ)=z.c-3 := Int.toNat_of_nonneg (by omega)
  have hcd : ((z.d-3).toNat : ℤ)=z.d-3 := Int.toNat_of_nonneg (by omega)
  have haN : a<3 := by omega
  have hfN : f<3 := by omega
  have hsum := small_endpoints_sum_bound z hz ha ha5 hf hf5
    (shortTerminal_mono (by decide : 1≤2) ht)
  have hcap : z.b+z.c+z.d+z.e ≤ (cap a f : ℤ) := by
    rw [cap_cast,hca,hcf]
    simpa only [sub_add_cancel] using hsum
  have h63 : (cap a f : ℤ) ≤ 63 := by exact_mod_cast cap_le_sixty_three a f
  have hbN : b<52 := by omega
  have hxsCast : (xs.sum : ℤ)=z.c+z.d-6 := by
    simp [xs,hcc,hcd]
    ring
  have hNbound : xs.sum+b+12 ≤ cap a f := by
    have hI : (xs.sum : ℤ)+(b : ℤ)+12 ≤ (cap a f : ℤ) := by omega
    exact_mod_cast hI
  have hx : xs ∈ boundedTuples 2 (cap a f-12-b) :=
    boundedTuples_complete 2 _ xs rfl (by omega)
  have hdiv : (z.a*z.f+z.c*z.d-q2 z)/z.b=z.e := by
    have hn : z.a*z.f+z.c*z.d-q2 z=z.b*z.e := by dsimp [q2]; ring
    rw [hn]
    exact Int.mul_ediv_cancel_left _ (by omega)
  have hfrom : candidate a f b xs (q2 z)=z := by
    ext <;> simp only [candidate,xs,List.getD_cons_zero,List.getD_cons_succ,
      hca,hcf,hcb,hcc,hcd,sub_add_cancel,hdiv]
  have hq : q2 z=4 ∨ q2 z=-4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.1.2)
  have hmem : z ∈ blockCandidates a f b := by
    apply List.mem_flatMap.mpr
    refine ⟨xs,hx,?_⟩
    rcases hq with hq | hq
    · rw [hq] at hfrom
      exact List.mem_cons.mpr (Or.inl hfrom.symm)
    · rw [hq] at hfrom
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl hfrom.symm)))
  have hcheck := List.all_eq_true.mp (hchecks ⟨a,haN⟩ ⟨f,hfN⟩ ⟨b,hbN⟩) z hmem
  exact caseCheck_correct _ z hcheck hz hcap (shortTerminal_balances z hz ht)

end SerreMarkov.PositiveSmallEndpointCensus

import SerreMarkov.PositiveFourFive
import SerreMarkov.PositiveFourFour

/-! # Complete conic-pruned finite candidates for the slice `a=4,d=5` -/
namespace SerreMarkov.PositiveFourFive
open PositiveChamber PositiveShortWord NegativeDescent
set_option maxHeartbeats 5000000

def computeBound (b : ℤ) : ℤ := if b=3 then 8 else sumBound b

/-- The two elementary guards already give a small box in the first branch. -/
theorem a_four_d_five_computation_bound (z : Six) (hz : Chamber z)
    (ha : z.a=4) (hd : z.d=5) (ht : ShortTerminal z 2) : z.c+z.f≤computeBound z.b := by
  obtain ⟨_,_,hcf⟩ := a_four_d_five_bounds z hz ha hd ht
  obtain ⟨_,_,hc,_,_,hf⟩ := hz.2.2
  by_cases hb : z.b=3
  · rw [computeBound,if_pos hb]
    obtain ⟨hm,_,_,hi,_,_,_,_⟩ := shortTerminal_balances z hz ht
    simp only [ha,hd,hb] at hm hi
    have hq : q2 z≤4 := by nlinarith only [hz.1.2]
    simp only [q2,ha,hd,hb] at hq
    omega
  · rw [computeBound,if_neg hb]
    exact hcf

def blockCount (b : ℤ) : ℕ := (computeBound b-6).toNat/10+1

def binaryConic (b c f q : ℤ) : ℤ :=
  -(20*b-b^2-25)*c^2-(20*b-b^2-16)*f^2+
    ((20-b)*b^2-41*b+40)*c*f+(4*b-10)*q*c+(5*b-8)*q*f+
    q^2+b^2*(b^2-20*b+33)

private theorem binaryConic_zero (b c e f q : ℤ)
    (hz : isSolution ⟨4,b,c,5,e,f⟩) (hq : q2 ⟨4,b,c,5,e,f⟩=q) :
    binaryConic b c f q=0 := by
  have h1 := hz.1
  dsimp [q1] at h1
  dsimp [q2] at hq
  dsimp [binaryConic]
  linear_combination b^2*h1-((4*b-5)*c+(5*b-4)*f-b*e+q)*hq

def candidate (b c f q : ℤ) : Six := ⟨4,b,c,5,(4*f+5*c-q)/b,f⟩

def blockCandidates (b : ℤ) (t : ℕ) : List Six :=
  (List.range 10).flatMap fun (j : ℕ) =>
    let c : ℤ := 10*(t : ℤ)+(j : ℤ)+3
    (List.range ((computeBound b-c-2).toNat)).flatMap fun (fi : ℕ) =>
      let f : ℤ := (fi : ℤ)+3
      (([4,-4] : List ℤ).filter (fun q => decide (binaryConic b c f q=0))).map
        (candidate b c f)

def blockSolutions (b : ℤ) (t : ℕ) : List Six :=
  (blockCandidates b t).filter PositiveFourFour.candidateCondition

private theorem shortTerminal_condition (z : Six) (hz : Chamber z)
    (ht : ShortTerminal z 2) : PositiveFourFour.candidateCondition z=true := by
  unfold PositiveFourFour.candidateCondition
  exact decide_eq_true ⟨hz.1,hz.2.1,hz.2.2,shortTerminal_balances z hz ht⟩

/-- Completeness is independent of the untrusted finite output table. -/
theorem a_four_d_five_mem_block (z : Six) (hz : Chamber z) (ha : z.a=4) (hd : z.d=5)
    (ht : ShortTerminal z 2) :
    ∃ bi t : ℕ, bi<14 ∧ t<blockCount (bi+3) ∧ z∈blockSolutions (bi+3) t := by
  obtain ⟨hb,hbHi,_,_,_,_,_,_⟩ := a_four_d_five_coordinate_bounds z hz ha hd ht
  have hcf := a_four_d_five_computation_bound z hz ha hd ht
  obtain ⟨_,_,hc,_,_,hf⟩ := hz.2.2
  let bi := (z.b-3).toNat
  let ci := (z.c-3).toNat
  let fi := (z.f-3).toNat
  let t := ci/10
  let j := ci%10
  have hbi : (bi : ℤ)=z.b-3 := Int.toNat_of_nonneg (by omega)
  have hci : (ci : ℤ)=z.c-3 := Int.toNat_of_nonneg (by omega)
  have hfi : (fi : ℤ)=z.f-3 := Int.toNat_of_nonneg (by omega)
  have hbshape : (bi : ℤ)+3=z.b := by omega
  have hcshape' : (10*(t : ℤ)+(j : ℤ)+3)=z.c := by
    have h := Nat.mod_add_div ci 10
    have hcast : ((ci%10 : ℕ) : ℤ)+10*((ci/10 : ℕ) : ℤ)=(ci : ℤ) := by exact_mod_cast h
    dsimp [t,j]
    omega
  have hcb : ci≤(computeBound z.b-6).toNat := by
    have hh : 0≤computeBound z.b-6 := by omega
    have hh' := Int.toNat_of_nonneg hh
    omega
  have htlt : t<blockCount z.b := by dsimp [t,blockCount]; omega
  have hjlt : j<10 := by dsimp [j]; omega
  have hfil : fi<(computeBound z.b-z.c-2).toNat := by
    have hh : 0≤computeBound z.b-z.c-2 := by omega
    have hh' := Int.toNat_of_nonneg hh
    omega
  have hshape : z=⟨4,z.b,z.c,5,z.e,z.f⟩ := by ext <;> simp [ha,hd]
  have hsol : isSolution ⟨4,z.b,z.c,5,z.e,z.f⟩ := hshape ▸ hz.1
  have hq : q2 ⟨4,z.b,z.c,5,z.e,z.f⟩=4 ∨ q2 ⟨4,z.b,z.c,5,z.e,z.f⟩= -4 := by
    have hh : (q2 ⟨4,z.b,z.c,5,z.e,z.f⟩-4)*(q2 ⟨4,z.b,z.c,5,z.e,z.f⟩+4)=0 := by
      nlinarith [hsol.2]
    rcases mul_eq_zero.mp hh with hh|hh <;> omega
  refine ⟨bi,t,by omega,by simpa only [hbshape] using htlt,?_⟩
  apply List.mem_filter.mpr
  refine ⟨?_,shortTerminal_condition z hz ht⟩
  rw [blockCandidates]
  apply List.mem_flatMap.mpr
  refine ⟨j,List.mem_range.mpr hjlt,?_⟩
  simp only [hbshape,hcshape']
  apply List.mem_flatMap.mpr
  refine ⟨fi,List.mem_range.mpr hfil,?_⟩
  have hfshape : (fi : ℤ)+3=z.f := by omega
  simp only [hfshape]
  apply List.mem_map.mpr
  rcases hq with hq|hq
  · refine ⟨4,List.mem_filter.mpr ⟨by simp,?_⟩,?_⟩
    · exact decide_eq_true (binaryConic_zero _ _ _ _ _ hsol hq)
    · have he : (4*z.f+5*z.c-4)/z.b=z.e := by
        dsimp [q2] at hq
        have heq : 4*z.f+5*z.c-4=z.e*z.b := by nlinarith only [hq]
        rw [heq,Int.mul_ediv_cancel _ (by omega)]
      ext <;> simp [candidate,ha,hd,he]
  · refine ⟨-4,List.mem_filter.mpr ⟨by simp,?_⟩,?_⟩
    · exact decide_eq_true (binaryConic_zero _ _ _ _ _ hsol hq)
    · have he : (4*z.f+5*z.c+4)/z.b=z.e := by
        dsimp [q2] at hq
        have heq : 4*z.f+5*z.c+4=z.e*z.b := by nlinarith only [hq]
        rw [heq,Int.mul_ediv_cancel _ (by omega)]
      ext <;> simp [candidate,ha,hd,he]

end SerreMarkov.PositiveFourFive

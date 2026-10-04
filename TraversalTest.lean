import Mathlib.Tactic
set_option maxHeartbeats 200000
/-- Consecutive list edges give forward-iterate paths from the first element. -/
theorem traversal_iterate {V : Type*} (p : V → V) (xs : List V) :
    ∀ (x : V) (suffix : List V),
      (∀ edge ∈ (x::xs).zip (xs++suffix), p edge.1=edge.2) →
      ∀ z ∈ x::xs, ∃ n : Nat, (p^[n]) x=z := by
  induction xs with
  | nil =>
    intro x suffix hedges z hz
    have hz' : z=x := by simpa using hz
    subst z
    exact ⟨0,rfl⟩
  | cons y ys ih =>
    intro x suffix hedges z hz
    have hxy : p x=y := by
      apply hedges (x,y)
      rw [List.cons_append, List.zip_cons_cons]
      exact List.mem_cons_self
    have htail : ∀ edge ∈ (y::ys).zip (ys++suffix), p edge.1=edge.2 := by
      intro edge he
      apply hedges edge
      rw [List.cons_append, List.zip_cons_cons]
      exact List.mem_cons_of_mem _ he
    rcases List.mem_cons.mp hz with hz | hz
    · subst z
      exact ⟨0,rfl⟩
    · obtain ⟨n, hn⟩ := ih y suffix htail z hz
      refine ⟨n+1, ?_⟩
      simpa only [Function.iterate_succ_apply, hxy] using hn


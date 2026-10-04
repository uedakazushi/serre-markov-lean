import SerreMarkov.Census
import Mathlib.Data.List.Zip

set_option maxHeartbeats 200000

/-! # Ordered cycle certificates imply the orbit-cover definition

This bridge proves that the explicit cycle lists in the finite certificates
really give at most two forward orbits. Its proof is list induction, without
bounded iteration or an assumed census result.
-/

namespace SerreMarkov.IndexTwelve

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

theorem formsCycle_exists_representative (p : VertexMap) (points : List Vertex)
    (h : FormsCycle p points) :
    ∃ x : Vertex, ∀ z ∈ points, ∃ n : Nat, (p^[n]) x=z := by
  rcases h with ⟨hne, _, hedges⟩
  cases points with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
    refine ⟨x, traversal_iterate p xs x [x] ?_⟩
    simpa [cycleEdges] using hedges

/-- A two-list cycle decomposition implies the census's intrinsic orbit condition. -/
theorem twoCycleDecomposition_atMostTwoCycles (p : VertexMap)
    (left right : List Vertex) (h : TwoCycleDecomposition p left right) :
    AtMostTwoCycles p := by
  rcases h with ⟨hl, hr, _, hcover⟩
  obtain ⟨x, hx⟩ := formsCycle_exists_representative p left hl
  obtain ⟨y, hy⟩ := formsCycle_exists_representative p right hr
  refine ⟨x,y,?_⟩
  intro z
  rcases List.mem_append.mp (hcover z) with hz | hz
  · exact Or.inl (hx z hz)
  · exact Or.inr (hy z hz)

end SerreMarkov.IndexTwelve

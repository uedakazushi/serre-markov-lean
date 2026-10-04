import SerreMarkov.NegativeSingleUnitDescent
import SerreMarkov.NegativeTwoEdge

/-! # Reflection of actual reachability and height reduction

Reversing the basis order reverses adjacent braid orientations. This gives
an exact operation on witness words and exchanges the two family parameters.
-/

namespace SerreMarkov.MirrorDescent
open NegativeDiagonalDescent NegativeSingleUnitDescent NegativeDescent NegativeTwoEdge

@[simp] theorem reverse_family (x y : ℤ) : reverse (family x y)=family y x := rfl

theorem reverse_reachable {z w : Six} (hr : Reachable z w) :
    Reachable (reverse z) (reverse w) := by
  obtain ⟨word,hword⟩ := hr
  refine ⟨word.map mirrorGenerator,?_⟩
  rw [←mirror_word,hword]

theorem reverse_reachable_iff (z w : Six) :
    Reachable (reverse z) (reverse w) ↔ Reachable z w := by
  constructor
  · intro h
    simpa only [reverse_reverse] using reverse_reachable h
  · exact reverse_reachable

theorem family_or_drop_reverse (z : Six) (h : FamilyOrDrop (reverse z)) : FamilyOrDrop z := by
  rcases h with ⟨x,y,hr⟩ | ⟨word,hdrop⟩
  · left
    refine ⟨y,x,?_⟩
    simpa only [reverse_reverse,reverse_family] using reverse_reachable hr
  · right
    refine ⟨word.map mirrorGenerator,?_⟩
    rw [mirror_word_height]
    simpa only [reverse_l1] using hdrop

theorem family_or_drop_reverse_iff (z : Six) : FamilyOrDrop (reverse z) ↔ FamilyOrDrop z := by
  constructor
  · exact family_or_drop_reverse z
  · intro h
    have ht := family_or_drop_reverse (reverse z)
    rw [reverse_reverse] at ht
    exact ht h

end SerreMarkov.MirrorDescent

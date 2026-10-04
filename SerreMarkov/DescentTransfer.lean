import SerreMarkov.NegativeTwoEdge

/-! # Actual path transfer through a nonincreasing intermediate point -/

namespace SerreMarkov.DescentTransfer
open NegativeDescent NegativeTwoEdge

theorem family_or_drop_of_nonincrease {z w : Six} (hr : Reachable z w)
    (hheight : l1 w≤l1 z) (hw : FamilyOrDrop w) : FamilyOrDrop z := by
  rcases hw with ⟨x,y,hxy⟩ | ⟨word,hdrop⟩
  · exact Or.inl ⟨x,y,reachable_trans hr hxy⟩
  · obtain ⟨path,hpath⟩ := hr
    refine Or.inr ⟨path++word,?_⟩
    rw [applyWord_append,hpath]
    exact lt_of_lt_of_le hdrop hheight

theorem family_or_drop_of_strict_path {z w : Six} (hr : Reachable z w)
    (hheight : l1 w<l1 z) : FamilyOrDrop z := by
  obtain ⟨word,hword⟩ := hr
  exact Or.inr ⟨word,by simpa only [hword] using hheight⟩

end SerreMarkov.DescentTransfer

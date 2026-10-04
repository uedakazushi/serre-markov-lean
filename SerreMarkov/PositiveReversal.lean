import SerreMarkov.PositiveAdjacentThrees
import SerreMarkov.PositiveShortWord

/-! Reversal transports actual short-word terminality at exactly the same length.
This is a braid-generator automorphism; no reachability of a tuple to its
reversal is asserted. -/
namespace SerreMarkov.PositiveReversal
open PositiveAdjacentThrees PositiveChamber PositiveShortWord NegativeDescent

def reverseGenerator : Generator → Generator
  | .m1 => .i3 | .m2 => .i2 | .m3 => .i1
  | .i1 => .m3 | .i2 => .m2 | .i3 => .m1
  | .s1 => .s4 | .s2 => .s3 | .s3 => .s2 | .s4 => .s1

theorem reverseSix_involutive (z : Six) : reverseSix (reverseSix z)=z := by
  rfl

theorem reverseGenerator_involutive (g : Generator) : reverseGenerator (reverseGenerator g)=g := by
  cases g <;> rfl

theorem reverseSix_step (g : Generator) (z : Six) :
    reverseSix (step g z)=step (reverseGenerator g) (reverseSix z) := by
  cases g <;> ext <;> dsimp [reverseSix,reverseGenerator,step,mu1,mu2,mu3,inv1,inv2,inv3,eps1,eps2,eps3,eps4] <;> ring

theorem reverseSix_applyWord (z : Six) (word : List Generator) :
    reverseSix (applyWord z word)=applyWord (reverseSix z) (word.map reverseGenerator) := by
  induction word generalizing z with
  | nil => rfl
  | cons g word ih =>
      simp only [applyWord,List.map_cons]
      rw [ih,reverseSix_step]

theorem reverseSix_height (z : Six) : l1 (reverseSix z)=l1 z := by
  dsimp [l1,reverseSix]
  omega

theorem reverseGenerator_mem_braidMoves {g : Generator} (hg : g ∈ braidMoves) :
    reverseGenerator g ∈ braidMoves := by
  cases g <;> simp_all [braidMoves,reverseGenerator]

theorem reverseWord_mem_braidWords {word : List Generator} {n : ℕ}
    (hw : word ∈ braidWords n) : word.map reverseGenerator ∈ braidWords n := by
  obtain ⟨hlen,hmove⟩ := (mem_braidWords_iff n word).mp hw
  apply (mem_braidWords_iff n _).mpr
  refine ⟨by simpa using hlen,?_⟩
  intro g hg
  obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
  exact reverseGenerator_mem_braidMoves (hmove h hh)

theorem reverseSix_shortTerminal (z : Six) (n : ℕ) (ht : ShortTerminal z n) :
    ShortTerminal (reverseSix z) n := by
  intro word hw
  have h := ht (word.map reverseGenerator) (reverseWord_mem_braidWords hw)
  rw [reverseSix_height z]
  have heq : reverseSix (applyWord z (word.map reverseGenerator))=
      applyWord (reverseSix z) word := by
    rw [reverseSix_applyWord,List.map_map]
    simp only [Function.comp_def,reverseGenerator_involutive]
    change applyWord (reverseSix z) (word.map id)=applyWord (reverseSix z) word
    rw [List.map_id]
  rw [← heq,reverseSix_height]
  exact h

theorem reverseSix_shortTerminal_iff (z : Six) (n : ℕ) :
    ShortTerminal (reverseSix z) n ↔ ShortTerminal z n := by
  constructor
  · intro h
    simpa only [reverseSix_involutive] using reverseSix_shortTerminal (reverseSix z) n h
  · exact reverseSix_shortTerminal z n

end SerreMarkov.PositiveReversal

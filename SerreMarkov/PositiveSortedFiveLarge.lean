import SerreMarkov.PositiveSortedFiveLargeMinus
import SerreMarkov.PositiveSortedFiveLargePlus

/-! The strict sorted first-edge-five region has no positive terminal solution. -/
namespace SerreMarkov.PositiveSortedFiveLarge
open PositiveChamber PositiveShortWord NegativeDescent

theorem a_five_sorted_large_impossible (z : Six) (hz : Chamber z) (ha : z.a=5)
    (hcd : z.d≤z.c) (hd : 6≤z.d) (hf : 6≤z.f)
    (ht : ShortTerminal z 3) : False := by
  let B := z.b-3
  let C := z.c-z.d
  let D := z.d-6
  let E := z.e-3
  let F := z.f-6
  have heq : z=⟨5,B+3,C+D+6,D+6,E+3,F+6⟩ := by
    ext <;> dsimp [B,C,D,E,F] <;> simp [ha] <;> omega
  have hw : Chamber ⟨5,B+3,C+D+6,D+6,E+3,F+6⟩ := heq ▸ hz
  have htw : ShortTerminal ⟨5,B+3,C+D+6,D+6,E+3,F+6⟩ 3 := heq ▸ ht
  have hB : 0≤B := by dsimp [B]; linarith [hz.2.2.2.1]
  have hC : 0≤C := by dsimp [C]; omega
  have hD : 0≤D := by dsimp [D]; omega
  have hE : 0≤E := by dsimp [E]; linarith [hz.2.2.2.2.2.2.1]
  have hF : 0≤F := by dsimp [F]; omega
  have hq : q2 ⟨5,B+3,C+D+6,D+6,E+3,F+6⟩=4 ∨
      q2 ⟨5,B+3,C+D+6,D+6,E+3,F+6⟩= -4 := by
    have hh := hw.1.2
    have hprod : (q2 ⟨5,B+3,C+D+6,D+6,E+3,F+6⟩-4)*
        (q2 ⟨5,B+3,C+D+6,D+6,E+3,F+6⟩+4)=0 := by nlinarith only [hh]
    rcases mul_eq_zero.mp hprod with h | h <;> [left;right] <;> omega
  rcases hq with hq | hq
  · exact PositiveSortedFiveLargePlus.certificate B C D E F hB hC hD hE hF hw htw hq
  · exact PositiveSortedFiveLargeMinus.certificate B C D E F hB hC hD hE hF hw htw hq

end SerreMarkov.PositiveSortedFiveLarge

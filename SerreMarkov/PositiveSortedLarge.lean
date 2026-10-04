import SerreMarkov.PositiveSortedLargeMinus
import SerreMarkov.PositiveSortedLargePlus

/-! The first outer edge of every sorted terminal positive chamber is at most
five. This is proved from actual finite-word guards by exact integer identities.
-/
namespace SerreMarkov.PositiveSortedLarge
open PositiveChamber PositiveShortWord PositiveSortedTerminal

theorem sorted_first_ge_six_impossible (z : Six) (hz : Chamber z)
    (hs : SortedOuter z) (ht : AllTerminal z) (ha : 6≤z.a) : False := by
  let A := z.a-6
  let B := z.b-3
  let C := z.c-z.d
  let D := z.d-z.a
  let E := z.e-3
  let F := z.f-z.a
  have heq : z=⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ := by
    ext <;> dsimp [A,B,C,D,E,F] <;> ring
  have hA : 0≤A := by dsimp [A]; omega
  have hB : 0≤B := by dsimp [B]; have h:=hz.2.2.2.1; omega
  have hC : 0≤C := by dsimp [C]; have h:=hs.2.2.2; omega
  have hD : 0≤D := by dsimp [D]; have h:=hs.2.1; omega
  have hE : 0≤E := by dsimp [E]; have h:=hz.2.2.2.2.2.2.1; omega
  have hF : 0≤F := by dsimp [F]; have h:=hs.2.2.1; omega
  have hw : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ := heq ▸ hz
  have htw : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ := heq ▸ ht
  have hq : q2 ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩=4 ∨
      q2 ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hw.1.2)
  rcases hq with hq|hq
  · exact certificate_plus A B C D E F hA hB hC hD hE hF hw htw hq
  · exact certificate_minus A B C D E F hA hB hC hD hE hF hw htw hq

theorem sorted_first_edge_le_five (z : Six) (hz : Chamber z)
    (hs : SortedOuter z) (ht : AllTerminal z) : z.a≤5 := by
  by_contra hn
  exact sorted_first_ge_six_impossible z hz hs ht (by omega)

end SerreMarkov.PositiveSortedLarge

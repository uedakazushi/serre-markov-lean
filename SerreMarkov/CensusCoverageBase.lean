import SerreMarkov.CensusData
import SerreMarkov.MapCode

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000

namespace SerreMarkov.IndexTwelve

theorem flatMap_list_blocks {T : Type*} (xs : List T) (n m : Nat) :
    (List.range n).flatMap (fun i => (xs.drop (m * i)).take m) = xs.take (m * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, ih]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.mul_succ,
        List.take_add]

theorem allCensusRows_length : allCensusRows.length = 10395 := by decide +kernel

def censusPartnerBlock (j : Nat) : List CensusRow :=
  (allCensusRows.drop (945 * j)).take 945

def matchingPartnerBlock (j : Nat) : List VertexMap :=
  (enumerateInvolutions 5 ((List.finRange 12).drop 1 |>.erase
    (⟨(j + 1) % 12, Nat.mod_lt _ (by decide)⟩ : Vertex))).map
      (installPair (0 : Vertex) ⟨(j + 1) % 12, Nat.mod_lt _ (by decide)⟩)

theorem censusPartnerBlocks_cover :
    (List.range 11).flatMap censusPartnerBlock = allCensusRows := by
  change (List.range 11).flatMap (fun j => (allCensusRows.drop (945 * j)).take 945) = _
  rw [flatMap_list_blocks]
  apply List.take_of_length_le
  rw [allCensusRows_length]

theorem matchingPartnerBlocks_cover :
    (List.range 11).flatMap matchingPartnerBlock = allMatchingInvolutions := by
  rfl

end SerreMarkov.IndexTwelve

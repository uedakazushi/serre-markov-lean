import SerreMarkov.Census
import Mathlib.Data.List.GetD

namespace SerreMarkov.IndexTwelve

def encodeMap (a : VertexMap) : List Nat :=
  (List.finRange 12).map fun i => (a i).val

theorem encodeMap_injective : Function.Injective encodeMap := by
  intro a b h
  funext i
  apply Fin.ext
  have ha := congrArg (fun l : List Nat => l.getD i.val 0) h
  have hi : i.val < (List.finRange 12).length := by simpa using i.isLt
  simpa [encodeMap, List.getD_eq_getElem, hi] using ha

end SerreMarkov.IndexTwelve

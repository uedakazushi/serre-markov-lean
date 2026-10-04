import SerreMarkov.PositiveBoundedPart19

namespace SerreMarkov.PositiveBounded

theorem all_blocks_checked (a b : Fin 20) (h : a.val+b.val ≤ 19) :
    blockCheck a.val b.val = true := by
  fin_cases a
  · exact checked_row_00 b h
  · exact checked_row_01 b h
  · exact checked_row_02 b h
  · exact checked_row_03 b h
  · exact checked_row_04 b h
  · exact checked_row_05 b h
  · exact checked_row_06 b h
  · exact checked_row_07 b h
  · exact checked_row_08 b h
  · exact checked_row_09 b h
  · exact checked_row_10 b h
  · exact checked_row_11 b h
  · exact checked_row_12 b h
  · exact checked_row_13 b h
  · exact checked_row_14 b h
  · exact checked_row_15 b h
  · exact checked_row_16 b h
  · exact checked_row_17 b h
  · exact checked_row_18 b h
  · exact checked_row_19 b h

end SerreMarkov.PositiveBounded

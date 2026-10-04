import SerreMarkov.PositiveFiveFive

/-! Every finite block is checked by the Lean kernel. -/
namespace SerreMarkov.PositiveFiveFiveChecks

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option Elab.async false

private theorem check_0 (t : Fin 20) : PositiveFiveFive.blockCheck 0 t.val=true := by
  fin_cases t <;> decide +kernel

private theorem check_1 (t : Fin 20) : PositiveFiveFive.blockCheck 1 t.val=true := by
  fin_cases t <;> decide +kernel

private theorem check_2 (t : Fin 20) : PositiveFiveFive.blockCheck 2 t.val=true := by
  fin_cases t <;> decide +kernel

private theorem check_3 (t : Fin 20) : PositiveFiveFive.blockCheck 3 t.val=true := by
  fin_cases t <;> decide +kernel

private theorem check_4 (t : Fin 20) : PositiveFiveFive.blockCheck 4 t.val=true := by
  fin_cases t <;> decide +kernel

private theorem check_5 (t : Fin 20) : PositiveFiveFive.blockCheck 5 t.val=true := by
  fin_cases t <;> decide +kernel

private theorem check_6 (t : Fin 20) : PositiveFiveFive.blockCheck 6 t.val=true := by
  fin_cases t <;> decide +kernel

private theorem check_7 (t : Fin 20) : PositiveFiveFive.blockCheck 7 t.val=true := by
  fin_cases t <;> decide +kernel

private theorem check_8 (t : Fin 20) : PositiveFiveFive.blockCheck 8 t.val=true := by
  fin_cases t <;> decide +kernel

private theorem check_9 (t : Fin 20) : PositiveFiveFive.blockCheck 9 t.val=true := by
  fin_cases t <;> decide +kernel

private theorem check_10 (t : Fin 20) : PositiveFiveFive.blockCheck 10 t.val=true := by
  fin_cases t <;> decide +kernel

private theorem check_11 (t : Fin 20) : PositiveFiveFive.blockCheck 11 t.val=true := by
  fin_cases t <;> decide +kernel

private theorem check_12 (t : Fin 20) : PositiveFiveFive.blockCheck 12 t.val=true := by
  fin_cases t <;> decide +kernel

private theorem check_13 (t : Fin 20) : PositiveFiveFive.blockCheck 13 t.val=true := by
  fin_cases t <;> decide +kernel

private theorem check_14 (t : Fin 20) : PositiveFiveFive.blockCheck 14 t.val=true := by
  fin_cases t <;> decide +kernel

private theorem check_15 (t : Fin 20) : PositiveFiveFive.blockCheck 15 t.val=true := by
  fin_cases t <;> decide +kernel

private theorem check_16 (t : Fin 20) : PositiveFiveFive.blockCheck 16 t.val=true := by
  fin_cases t <;> decide +kernel

private theorem check_17 (t : Fin 20) : PositiveFiveFive.blockCheck 17 t.val=true := by
  fin_cases t <;> decide +kernel

private theorem check_18 (t : Fin 20) : PositiveFiveFive.blockCheck 18 t.val=true := by
  fin_cases t <;> decide +kernel

private theorem check_19 (t : Fin 20) : PositiveFiveFive.blockCheck 19 t.val=true := by
  fin_cases t <;> decide +kernel

theorem block_checks (bi t : Fin 20) : PositiveFiveFive.blockCheck bi.val t.val=true := by
  fin_cases bi
  · exact check_0 t
  · exact check_1 t
  · exact check_2 t
  · exact check_3 t
  · exact check_4 t
  · exact check_5 t
  · exact check_6 t
  · exact check_7 t
  · exact check_8 t
  · exact check_9 t
  · exact check_10 t
  · exact check_11 t
  · exact check_12 t
  · exact check_13 t
  · exact check_14 t
  · exact check_15 t
  · exact check_16 t
  · exact check_17 t
  · exact check_18 t
  · exact check_19 t

end SerreMarkov.PositiveFiveFiveChecks

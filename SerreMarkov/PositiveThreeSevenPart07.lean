import SerreMarkov.PositiveThreeSevenBase
namespace SerreMarkov.PositiveThreeSeven
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_11_0 : blockCheck 11 0=true := by decide +kernel
theorem checked_11_1 : blockCheck 11 1=true := by decide +kernel
theorem checked_11_2 : blockCheck 11 2=true := by decide +kernel
theorem checked_11_3 : blockCheck 11 3=true := by decide +kernel
theorem checked_11_4 : blockCheck 11 4=true := by decide +kernel
theorem checked_11_5 : blockCheck 11 5=true := by decide +kernel
theorem checked_11_6 : blockCheck 11 6=true := by decide +kernel
theorem checked_11_7 : blockCheck 11 7=true := by decide +kernel
end SerreMarkov.PositiveThreeSeven

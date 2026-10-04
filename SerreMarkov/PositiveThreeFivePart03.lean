import SerreMarkov.PositiveThreeFiveBase
namespace SerreMarkov.PositiveThreeFive
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_7_0 : blockCheck 7 0=true := by decide +kernel
theorem checked_7_1 : blockCheck 7 1=true := by decide +kernel
theorem checked_7_2 : blockCheck 7 2=true := by decide +kernel
theorem checked_7_3 : blockCheck 7 3=true := by decide +kernel
theorem checked_7_4 : blockCheck 7 4=true := by decide +kernel
theorem checked_7_5 : blockCheck 7 5=true := by decide +kernel
end SerreMarkov.PositiveThreeFive

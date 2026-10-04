import SerreMarkov.PositiveThreeSixBase
namespace SerreMarkov.PositiveThreeSix
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_6_0 : blockCheck 6 0=true := by decide +kernel
theorem checked_6_1 : blockCheck 6 1=true := by decide +kernel
theorem checked_6_2 : blockCheck 6 2=true := by decide +kernel
theorem checked_6_3 : blockCheck 6 3=true := by decide +kernel
theorem checked_6_4 : blockCheck 6 4=true := by decide +kernel
theorem checked_6_5 : blockCheck 6 5=true := by decide +kernel
theorem checked_6_6 : blockCheck 6 6=true := by decide +kernel
theorem checked_6_7 : blockCheck 6 7=true := by decide +kernel
theorem checked_6_8 : blockCheck 6 8=true := by decide +kernel
theorem checked_6_9 : blockCheck 6 9=true := by decide +kernel
end SerreMarkov.PositiveThreeSix

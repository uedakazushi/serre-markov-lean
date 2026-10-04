import SerreMarkov.PositiveThreeSixBase
namespace SerreMarkov.PositiveThreeSix
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_10_0 : blockCheck 10 0=true := by decide +kernel
theorem checked_10_1 : blockCheck 10 1=true := by decide +kernel
theorem checked_10_2 : blockCheck 10 2=true := by decide +kernel
theorem checked_10_3 : blockCheck 10 3=true := by decide +kernel
theorem checked_10_4 : blockCheck 10 4=true := by decide +kernel
theorem checked_10_5 : blockCheck 10 5=true := by decide +kernel
end SerreMarkov.PositiveThreeSix

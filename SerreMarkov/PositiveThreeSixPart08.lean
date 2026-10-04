import SerreMarkov.PositiveThreeSixBase
namespace SerreMarkov.PositiveThreeSix
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_12_0 : blockCheck 12 0=true := by decide +kernel
theorem checked_12_1 : blockCheck 12 1=true := by decide +kernel
theorem checked_12_2 : blockCheck 12 2=true := by decide +kernel
theorem checked_12_3 : blockCheck 12 3=true := by decide +kernel
end SerreMarkov.PositiveThreeSix

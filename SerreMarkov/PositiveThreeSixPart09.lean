import SerreMarkov.PositiveThreeSixBase
namespace SerreMarkov.PositiveThreeSix
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_13_0 : blockCheck 13 0=true := by decide +kernel
theorem checked_13_1 : blockCheck 13 1=true := by decide +kernel
theorem checked_13_2 : blockCheck 13 2=true := by decide +kernel
end SerreMarkov.PositiveThreeSix

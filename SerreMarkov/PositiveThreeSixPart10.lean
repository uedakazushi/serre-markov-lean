import SerreMarkov.PositiveThreeSixBase
namespace SerreMarkov.PositiveThreeSix
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_14_0 : blockCheck 14 0=true := by decide +kernel
theorem checked_14_1 : blockCheck 14 1=true := by decide +kernel
end SerreMarkov.PositiveThreeSix

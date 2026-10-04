import SerreMarkov.PositiveThreeFiveBase
namespace SerreMarkov.PositiveThreeFive
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_11_0 : blockCheck 11 0=true := by decide +kernel
theorem checked_11_1 : blockCheck 11 1=true := by decide +kernel
end SerreMarkov.PositiveThreeFive

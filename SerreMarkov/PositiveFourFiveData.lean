import SerreMarkov.PositiveFourFiveCensusCore

/-! # Kernel-checked terminal classification in the actual slice `a=4,d=5`

The binary conic is tested before the positive tuple conditions. Completeness
of this finite table is proved in the separate census-core module, with no
height bound or small-edge cutpoint as input.
-/
namespace SerreMarkov.PositiveFourFive.CensusData
open PositiveChamber PositiveShortWord
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem verified_3_0 : blockSolutions 3 0=[] := by decide +kernel

#print axioms verified_3_0

theorem verified_4_0 : blockSolutions 4 0=[⟨4,4,4,5,11,5⟩] := by decide +kernel

theorem verified_4_1 : blockSolutions 4 1=[] := by decide +kernel

theorem verified_4_2 : blockSolutions 4 2=[] := by decide +kernel

theorem verified_4_3 : blockSolutions 4 3=[] := by decide +kernel

theorem verified_4_4 : blockSolutions 4 4=[] := by decide +kernel

theorem verified_4_5 : blockSolutions 4 5=[] := by decide +kernel

theorem verified_4_6 : blockSolutions 4 6=[] := by decide +kernel

theorem verified_4_7 : blockSolutions 4 7=[] := by decide +kernel

theorem verified_4_8 : blockSolutions 4 8=[] := by decide +kernel

theorem verified_4_9 : blockSolutions 4 9=[] := by decide +kernel

theorem verified_4_10 : blockSolutions 4 10=[] := by decide +kernel

theorem verified_4_11 : blockSolutions 4 11=[] := by decide +kernel

theorem verified_4_12 : blockSolutions 4 12=[] := by decide +kernel

theorem verified_4_13 : blockSolutions 4 13=[] := by decide +kernel

theorem verified_4_14 : blockSolutions 4 14=[] := by decide +kernel

theorem verified_4_15 : blockSolutions 4 15=[] := by decide +kernel

theorem verified_4_16 : blockSolutions 4 16=[] := by decide +kernel

#print axioms verified_4_16

theorem verified_5_0 : blockSolutions 5 0=[] := by decide +kernel

theorem verified_5_1 : blockSolutions 5 1=[] := by decide +kernel

theorem verified_5_2 : blockSolutions 5 2=[] := by decide +kernel

theorem verified_5_3 : blockSolutions 5 3=[] := by decide +kernel

theorem verified_5_4 : blockSolutions 5 4=[] := by decide +kernel

theorem verified_5_5 : blockSolutions 5 5=[] := by decide +kernel

theorem verified_5_6 : blockSolutions 5 6=[] := by decide +kernel

theorem verified_5_7 : blockSolutions 5 7=[] := by decide +kernel

theorem verified_5_8 : blockSolutions 5 8=[] := by decide +kernel

theorem verified_5_9 : blockSolutions 5 9=[] := by decide +kernel

theorem verified_5_10 : blockSolutions 5 10=[] := by decide +kernel

theorem verified_5_11 : blockSolutions 5 11=[] := by decide +kernel

theorem verified_5_12 : blockSolutions 5 12=[] := by decide +kernel

#print axioms verified_5_12

theorem verified_6_0 : blockSolutions 6 0=[] := by decide +kernel

theorem verified_6_1 : blockSolutions 6 1=[] := by decide +kernel

theorem verified_6_2 : blockSolutions 6 2=[] := by decide +kernel

theorem verified_6_3 : blockSolutions 6 3=[] := by decide +kernel

theorem verified_6_4 : blockSolutions 6 4=[] := by decide +kernel

theorem verified_6_5 : blockSolutions 6 5=[] := by decide +kernel

theorem verified_6_6 : blockSolutions 6 6=[] := by decide +kernel

theorem verified_6_7 : blockSolutions 6 7=[] := by decide +kernel

theorem verified_6_8 : blockSolutions 6 8=[] := by decide +kernel

theorem verified_6_9 : blockSolutions 6 9=[] := by decide +kernel

theorem verified_6_10 : blockSolutions 6 10=[] := by decide +kernel

#print axioms verified_6_10

theorem verified_7_0 : blockSolutions 7 0=[] := by decide +kernel

theorem verified_7_1 : blockSolutions 7 1=[] := by decide +kernel

theorem verified_7_2 : blockSolutions 7 2=[] := by decide +kernel

theorem verified_7_3 : blockSolutions 7 3=[] := by decide +kernel

theorem verified_7_4 : blockSolutions 7 4=[] := by decide +kernel

theorem verified_7_5 : blockSolutions 7 5=[] := by decide +kernel

theorem verified_7_6 : blockSolutions 7 6=[] := by decide +kernel

theorem verified_7_7 : blockSolutions 7 7=[] := by decide +kernel

theorem verified_7_8 : blockSolutions 7 8=[] := by decide +kernel

#print axioms verified_7_8

theorem verified_8_0 : blockSolutions 8 0=[] := by decide +kernel

theorem verified_8_1 : blockSolutions 8 1=[] := by decide +kernel

theorem verified_8_2 : blockSolutions 8 2=[] := by decide +kernel

theorem verified_8_3 : blockSolutions 8 3=[] := by decide +kernel

theorem verified_8_4 : blockSolutions 8 4=[] := by decide +kernel

theorem verified_8_5 : blockSolutions 8 5=[] := by decide +kernel

theorem verified_8_6 : blockSolutions 8 6=[] := by decide +kernel

theorem verified_8_7 : blockSolutions 8 7=[] := by decide +kernel

#print axioms verified_8_7

theorem verified_9_0 : blockSolutions 9 0=[] := by decide +kernel

theorem verified_9_1 : blockSolutions 9 1=[] := by decide +kernel

theorem verified_9_2 : blockSolutions 9 2=[] := by decide +kernel

theorem verified_9_3 : blockSolutions 9 3=[] := by decide +kernel

theorem verified_9_4 : blockSolutions 9 4=[] := by decide +kernel

theorem verified_9_5 : blockSolutions 9 5=[] := by decide +kernel

theorem verified_9_6 : blockSolutions 9 6=[] := by decide +kernel

#print axioms verified_9_6

theorem verified_10_0 : blockSolutions 10 0=[] := by decide +kernel

theorem verified_10_1 : blockSolutions 10 1=[] := by decide +kernel

theorem verified_10_2 : blockSolutions 10 2=[] := by decide +kernel

theorem verified_10_3 : blockSolutions 10 3=[] := by decide +kernel

theorem verified_10_4 : blockSolutions 10 4=[] := by decide +kernel

theorem verified_10_5 : blockSolutions 10 5=[] := by decide +kernel

#print axioms verified_10_5

theorem verified_11_0 : blockSolutions 11 0=[] := by decide +kernel

theorem verified_11_1 : blockSolutions 11 1=[] := by decide +kernel

theorem verified_11_2 : blockSolutions 11 2=[] := by decide +kernel

theorem verified_11_3 : blockSolutions 11 3=[] := by decide +kernel

theorem verified_11_4 : blockSolutions 11 4=[] := by decide +kernel

#print axioms verified_11_4

theorem verified_12_0 : blockSolutions 12 0=[] := by decide +kernel

theorem verified_12_1 : blockSolutions 12 1=[] := by decide +kernel

theorem verified_12_2 : blockSolutions 12 2=[] := by decide +kernel

theorem verified_12_3 : blockSolutions 12 3=[] := by decide +kernel

#print axioms verified_12_3

theorem verified_13_0 : blockSolutions 13 0=[] := by decide +kernel

theorem verified_13_1 : blockSolutions 13 1=[] := by decide +kernel

theorem verified_13_2 : blockSolutions 13 2=[] := by decide +kernel

#print axioms verified_13_2

theorem verified_14_0 : blockSolutions 14 0=[] := by decide +kernel

theorem verified_14_1 : blockSolutions 14 1=[] := by decide +kernel

theorem verified_14_2 : blockSolutions 14 2=[] := by decide +kernel

#print axioms verified_14_2

theorem verified_15_0 : blockSolutions 15 0=[] := by decide +kernel

theorem verified_15_1 : blockSolutions 15 1=[] := by decide +kernel

#print axioms verified_15_1

theorem verified_16_0 : blockSolutions 16 0=[] := by decide +kernel

#print axioms verified_16_0


end SerreMarkov.PositiveFourFive.CensusData

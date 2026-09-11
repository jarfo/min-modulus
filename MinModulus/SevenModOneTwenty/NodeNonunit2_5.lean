import MinModulus.SevenModOneTwenty.BlockNonunit274
import MinModulus.SevenModOneTwenty.BlockNonunit275
import MinModulus.SevenModOneTwenty.BlockNonunit276

namespace MinModulus.PrefixCertificate.Seven120

theorem nonunit_2_5_closed : ClosedMinimalPrefix false 120 2 4 [0,2,5] 6 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,6] 7 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,7] 8 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,8] 9 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,9] 10 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,10] 11 (.stop (.collision 200)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,11] 12 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,12] 13 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,13] 14 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_5_14_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,15] 16 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,16] 17 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,17] 18 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,18] 19 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,19] 20 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_5_20_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,21] 22 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,22] 23 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,23] 24 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,24] 25 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,25] 26 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_5_26_closed
  · exact nonunit_2_5_27_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,28] 29 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,29] 30 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_5_30_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,31] 32 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_5_32_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,33] 34 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,34] 35 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_5_35_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,36] 37 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,37] 38 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_5_38_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,39] 40 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_5_40_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,41] 42 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,42] 43 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,43] 44 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_5_44_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,45] 46 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,46] 47 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,47] 48 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,48] 49 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,49] 50 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_5_50_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,51] 52 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,52] 53 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,53] 54 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,54] 55 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,55] 56 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_5_56_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,57] 58 (.branch [.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.unitPair 2 4),.stop (.collision 9280),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 3 4),.stop (.unitPair 1 4),.stop (.unitPair 3 4),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 3 4),.stop (.unitPair 1 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 3 4),.stop (.unitPair 1 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 1 4),.stop (.unitPair 3 4),.stop (.collision 12416),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.collision 12304),.stop (.unitPair 0 4),.stop (.collision 12290),.stop (.unitPair 1 4),.stop (.unitPair 2 4),.stop (.collision 13312),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 3 4),.stop (.unitPair 1 4),.stop (.unitPair 3 4),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 3 4),.stop (.unitPair 1 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 3 4),.stop (.unitPair 1 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 1 4),.stop (.unitPair 3 4),.stop (.collision 8832),.stop (.unitPair 2 4),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,58] 59 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,59] 60 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_5_60_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,61] 62 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_5_62_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,63] 64 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,64] 65 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_5_65_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,66] 67 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,67] 68 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_5_68_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,69] 70 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_5_70_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,71] 72 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,72] 73 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,73] 74 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_5_74_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,75] 76 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,76] 77 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,77] 78 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,78] 79 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,79] 80 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_5_80_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,81] 82 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,82] 83 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,83] 84 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,84] 85 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,85] 86 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_5_86_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,87] 88 (.branch [.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.unitPair 2 4),.stop (.collision 1216),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 3 4),.stop (.unitPair 1 4),.stop (.unitPair 3 4),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 3 4),.stop (.unitPair 1 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 3 4),.stop (.unitPair 1 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 1 4),.stop (.unitPair 3 4),.stop (.collision 8832),.stop (.unitPair 2 4),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,88] 89 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,89] 90 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_5_90_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,91] 92 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_5_92_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,93] 94 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,94] 95 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,95] 96 (.branch [.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.unitPair 2 5),.stop (.unitPair 0 5),.stop (.unitPair 2 5),.stop (.unitPair 0 5),.stop (.collision 102409),.stop (.unitPair 1 5),.stop (.unitPair 2 5),.stop (.unitPair 0 5),.stop (.unitPair 2 5),.stop (.unitPair 1 5),.stop (.collision 73737),.stop (.unitPair 4 5),.stop (.unitPair 2 5),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.collision 12297),.stop (.unitPair 1 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 1 4),.branch [.stop (.unitPair 4 5),.stop (.unitPair 2 5),.stop (.unitPair 0 5)],.stop (.collision 8832),.stop (.unitPair 2 4),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,96] 97 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,97] 98 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,98] 99 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.unitPair 2 5),.stop (.unitPair 0 5),.stop (.unitPair 2 5),.stop (.unitPair 0 5),.stop (.collision 102465),.stop (.unitPair 1 5),.stop (.unitPair 2 5),.stop (.unitPair 0 5),.stop (.unitPair 2 5),.stop (.unitPair 1 5),.stop (.collision 73793),.stop (.unitPair 3 5),.stop (.unitPair 2 5),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 1 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 1 4),.branch [.stop (.unitPair 3 5),.stop (.unitPair 2 5),.stop (.unitPair 0 5)],.stop (.unitPair 3 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,99] 100 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,100] 101 (.branch [.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.unitPair 2 5),.stop (.unitPair 0 5),.stop (.unitPair 2 5),.stop (.unitPair 0 5),.stop (.collision 102472),.stop (.unitPair 1 5),.stop (.unitPair 2 5),.stop (.unitPair 0 5),.stop (.unitPair 2 5),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 3 5),.stop (.unitPair 2 5),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 1 4),.branch [.stop (.unitPair 3 5),.stop (.unitPair 2 5),.stop (.unitPair 0 5)],.stop (.unitPair 3 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,101] 102 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,102] 103 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,103] 104 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,104] 105 (.branch [.stop (.unitPair 1 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.unitPair 2 5),.stop (.unitPair 0 5),.stop (.unitPair 2 5),.stop (.unitPair 1 5),.stop (.collision 73793),.stop (.unitPair 3 5),.stop (.unitPair 2 5),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 1 4),.branch [.stop (.unitPair 3 5),.stop (.unitPair 2 5),.stop (.unitPair 0 5)],.stop (.unitPair 3 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,105] 106 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,106] 107 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,107] 108 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,108] 109 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,109] 110 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,110] 111 (.branch [.stop (.unitPair 1 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4),.stop (.unitPair 2 4),.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 3 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,111] 112 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,112] 113 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,113] 114 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,114] 115 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,115] 116 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,116] 117 (.branch [.stop (.unitPair 3 4),.stop (.unitPair 2 4),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,117] 118 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,118] 119 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,5,119] 120 (.stop (.unitPair 0 3)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

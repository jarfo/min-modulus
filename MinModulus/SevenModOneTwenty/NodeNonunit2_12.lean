import MinModulus.SevenModOneTwenty.BlockNonunit282
import MinModulus.SevenModOneTwenty.BlockNonunit283
import MinModulus.SevenModOneTwenty.BlockNonunit284

namespace MinModulus.PrefixCertificate.Seven120

theorem nonunit_2_12_closed : ClosedMinimalPrefix false 120 2 4 [0,2,12] 13 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,13] 14 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,14] 15 (.stop (.collision 144)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,15] 16 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_12_16_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,17] 18 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_18_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,19] 20 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_20_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,21] 22 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,22] 23 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,23] 24 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,24] 25 (.stop (.collision 200)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,25] 26 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_12_26_closed
  · exact nonunit_2_12_27_closed
  · exact nonunit_2_12_28_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,29] 30 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_30_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,31] 32 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_32_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,33] 34 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,34] 35 (.stop (.collision 256)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,35] 36 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_12_36_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,37] 38 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_38_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,39] 40 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_12_40_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,41] 42 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_42_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,43] 44 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_44_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,45] 46 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_12_46_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,47] 48 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_48_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,49] 50 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_50_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,51] 52 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_12_52_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,53] 54 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_54_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,55] 56 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_12_56_closed
  · exact nonunit_2_12_57_closed
  · exact nonunit_2_12_58_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,59] 60 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_60_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,61] 62 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_62_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,63] 64 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_12_64_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,65] 66 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,66] 67 (.stop (.collision 1544)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,67] 68 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_68_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,69] 70 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_12_70_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,71] 72 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_72_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,73] 74 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_74_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,75] 76 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_12_76_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,77] 78 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_78_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,79] 80 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_80_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,81] 82 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_12_82_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,83] 84 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_84_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,85] 86 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_12_86_closed
  · exact nonunit_2_12_87_closed
  · exact nonunit_2_12_88_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,89] 90 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_90_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,91] 92 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_12_92_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,93] 94 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,94] 95 (.branch [.stop (.unitPair 2 4),.stop (.collision 1104),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 12361),.stop (.unitPair 0 5),.stop (.collision 5249),.stop (.unitPair 1 5),.stop (.collision 5256),.stop (.unitPair 0 5),.stop (.collision 102465),.stop (.unitPair 0 5),.stop (.collision 70272),.stop (.unitPair 1 5),.stop (.collision 4633),.stop (.unitPair 0 5),.stop (.collision 66688),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 3 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 5249),.stop (.unitPair 1 5),.stop (.collision 5256),.stop (.unitPair 0 5),.stop (.collision 102465),.stop (.unitPair 0 5),.stop (.collision 70272),.stop (.unitPair 1 5),.stop (.collision 8840),.stop (.unitPair 0 5),.stop (.collision 73800),.stop (.unitPair 1 5),.stop (.collision 73793),.stop (.unitPair 3 5),.stop (.collision 4675),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 12416),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 537),.stop (.unitPair 0 4),.stop (.collision 544),.stop (.unitPair 1 4),.stop (.collision 1216),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,95] 96 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,96] 97 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 12361),.stop (.unitPair 1 5),.stop (.collision 5249),.stop (.unitPair 0 5),.stop (.collision 102472),.stop (.unitPair 0 5),.stop (.collision 70272),.stop (.unitPair 1 5),.stop (.collision 8840),.stop (.unitPair 0 5),.stop (.collision 102409),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 4 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 1 5),.stop (.collision 5249),.stop (.unitPair 0 5),.stop (.collision 102472),.stop (.unitPair 0 5),.stop (.collision 70272),.stop (.unitPair 1 5),.stop (.collision 98881),.stop (.unitPair 0 5),.stop (.collision 73800),.stop (.unitPair 1 5),.stop (.collision 73793),.stop (.collision 98825),.stop (.collision 4675),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 8216),.stop (.unitPair 1 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 537),.stop (.unitPair 0 4),.stop (.collision 12297),.stop (.unitPair 1 4),.stop (.collision 16392),.branch [.stop (.unitPair 4 5),.stop (.unitPair 0 5)],.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,97] 98 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,98] 99 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 1 5),.stop (.collision 12361),.stop (.unitPair 0 5),.stop (.collision 5249),.stop (.unitPair 0 5),.stop (.collision 70272),.stop (.unitPair 1 5),.stop (.collision 98881),.stop (.unitPair 0 5),.stop (.collision 8840),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 3 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 12416),.stop (.unitPair 1 4),.stop (.collision 8216),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 537),.stop (.unitPair 0 4),.stop (.collision 12304),.stop (.unitPair 1 4),.stop (.collision 12290),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,99] 100 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,100] 101 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 12361),.stop (.unitPair 0 5),.stop (.collision 70272),.stop (.unitPair 1 5),.stop (.collision 98888),.stop (.unitPair 0 5),.stop (.collision 8833),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 3 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.collision 516),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.collision 16448),.stop (.unitPair 1 4),.stop (.collision 12297),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,101] 102 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,102] 103 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 12416),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 12304),.stop (.collision 12297),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,103] 104 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,104] 105 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 3 4),.stop (.collision 12297),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,105] 106 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,106] 107 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,107] 108 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,108] 109 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,109] 110 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,110] 111 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,111] 112 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,112] 113 (.stop (.collision 25)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,113] 114 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,114] 115 (.stop (.collision 32)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,115] 116 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,116] 117 (.branch [.stop (.unitPair 3 4),.stop (.collision 12360),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,117] 118 (.branch [.stop (.unitPair 3 4),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,118] 119 (.stop (.collision 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,12,119] 120 (.stop (.unitPair 0 3)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

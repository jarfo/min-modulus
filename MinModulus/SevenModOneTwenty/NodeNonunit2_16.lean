import MinModulus.SevenModOneTwenty.BlockNonunit286
import MinModulus.SevenModOneTwenty.BlockNonunit287

namespace MinModulus.PrefixCertificate.Seven120

theorem nonunit_2_16_closed : ClosedMinimalPrefix false 120 2 4 [0,2,16] 17 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,17] 18 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,18] 19 (.stop (.collision 144)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,19] 20 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_16_20_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,21] 22 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_16_22_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,23] 24 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_16_24_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,25] 26 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_16_26_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,27] 28 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_16_28_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,29] 30 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,30] 31 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,31] 32 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,32] 33 (.stop (.collision 200)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,33] 34 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_16_34_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,35] 36 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_16_36_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,37] 38 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_16_38_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,39] 40 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_16_40_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,41] 42 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_16_42_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,43] 44 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_16_44_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,45] 46 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,46] 47 (.stop (.collision 2048)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,47] 48 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_16_48_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,49] 50 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_16_50_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,51] 52 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_16_52_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,53] 54 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_16_54_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,55] 56 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_16_56_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,57] 58 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_16_58_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,59] 60 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_16_60_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,61] 62 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_16_62_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,63] 64 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_16_64_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,65] 66 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_16_66_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,67] 68 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,68] 69 (.stop (.collision 1544)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,69] 70 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_16_70_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,71] 72 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_16_72_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,73] 74 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_16_74_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,75] 76 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_16_76_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,77] 78 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_16_78_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,79] 80 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_16_80_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,81] 82 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_16_82_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,83] 84 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_16_84_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,85] 86 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,86] 87 (.stop (.collision 2048)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,87] 88 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_16_88_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,89] 90 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_16_90_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,91] 92 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_16_92_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,93] 94 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,94] 95 (.branch [.stop (.unitPair 2 4),.stop (.collision 1104),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 12361),.stop (.unitPair 0 5),.stop (.collision 4619),.stop (.unitPair 1 5),.stop (.collision 70272),.stop (.unitPair 0 5),.stop (.collision 102465),.stop (.unitPair 0 5),.stop (.collision 5256),.stop (.unitPair 1 5),.stop (.collision 8833),.stop (.unitPair 0 5),.stop (.collision 8840),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 2 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.collision 12416),.stop (.unitPair 0 4),.stop (.collision 516),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 16448),.stop (.unitPair 0 4),.stop (.collision 12304),.stop (.unitPair 1 4),.stop (.collision 12290),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,95] 96 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,96] 97 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 12361),.stop (.unitPair 1 5),.stop (.collision 70272),.stop (.unitPair 0 5),.stop (.collision 102472),.stop (.unitPair 0 5),.stop (.collision 98888),.stop (.unitPair 1 5),.stop (.collision 5256),.stop (.unitPair 0 5),.stop (.collision 8833),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 2 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 516),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.collision 8195),.stop (.unitPair 1 4),.stop (.collision 12297),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,97] 98 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,98] 99 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 12416),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 537),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 1 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 12304),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,99] 100 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,100] 101 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 537),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.stop (.collision 8216),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 2 4),.stop (.collision 12297),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,101] 102 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,102] 103 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,103] 104 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,104] 105 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,105] 106 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,106] 107 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,107] 108 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,108] 109 (.stop (.collision 25)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,109] 110 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,110] 111 (.stop (.collision 32)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,111] 112 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,112] 113 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,113] 114 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,114] 115 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 2 4),.stop (.collision 12353),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,115] 116 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,116] 117 (.branch [.stop (.unitPair 2 4),.stop (.collision 12360),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,117] 118 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,118] 119 (.stop (.collision 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,16,119] 120 (.stop (.unitPair 0 3)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

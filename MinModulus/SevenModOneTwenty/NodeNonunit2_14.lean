import MinModulus.SevenModOneTwenty.BlockNonunit284
import MinModulus.SevenModOneTwenty.BlockNonunit285
import MinModulus.SevenModOneTwenty.BlockNonunit286

namespace MinModulus.PrefixCertificate.Seven120

theorem nonunit_2_14_closed : ClosedMinimalPrefix false 120 2 4 [0,2,14] 15 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,15] 16 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,16] 17 (.stop (.collision 144)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,17] 18 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_18_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,19] 20 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_20_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,21] 22 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_14_22_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,23] 24 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_24_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,25] 26 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,26] 27 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,27] 28 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,28] 29 (.stop (.collision 200)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,29] 30 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_30_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,31] 32 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_32_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,33] 34 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_14_34_closed
  · exact nonunit_2_14_35_closed
  · exact nonunit_2_14_36_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,37] 38 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_38_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,39] 40 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,40] 41 (.stop (.collision 256)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,41] 42 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_42_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,43] 44 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_44_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,45] 46 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_14_46_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,47] 48 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_48_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,49] 50 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_50_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,51] 52 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_14_52_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,53] 54 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_54_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,55] 56 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_14_56_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,57] 58 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_14_58_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,59] 60 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_60_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,61] 62 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_62_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,63] 64 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_14_64_closed
  · exact nonunit_2_14_65_closed
  · exact nonunit_2_14_66_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,67] 68 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,68] 69 (.stop (.collision 1537)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,69] 70 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_14_70_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,71] 72 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_72_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,73] 74 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_74_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,75] 76 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_14_76_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,77] 78 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_78_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,79] 80 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_80_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,81] 82 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_14_82_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,83] 84 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_84_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,85] 86 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_14_86_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,87] 88 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_14_88_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,89] 90 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_90_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,91] 92 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_14_92_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,93] 94 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_14_94_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,95] 96 (.branch [.stop (.unitPair 3 4),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5),.stop (.collision 1665),.stop (.unitPair 1 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5),.stop (.collision 98881),.stop (.unitPair 1 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5),.stop (.unitPair 3 5),.stop (.unitPair 1 5),.stop (.collision 98825),.stop (.unitPair 2 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5),.stop (.collision 98944),.stop (.unitPair 1 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5),.stop (.collision 98888),.stop (.unitPair 1 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5),.stop (.unitPair 3 5),.stop (.unitPair 1 5),.stop (.collision 98832),.stop (.unitPair 2 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.unitPair 3 4),.stop (.unitPair 0 4),.stop (.collision 516),.stop (.unitPair 1 4),.stop (.unitPair 3 4),.stop (.unitPair 0 4),.stop (.unitPair 3 4),.stop (.unitPair 0 4),.stop (.collision 537),.stop (.unitPair 1 4),.stop (.unitPair 3 4),.stop (.unitPair 0 4),.stop (.unitPair 3 4),.stop (.unitPair 1 4),.branch [.stop (.unitPair 2 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5)],.stop (.unitPair 2 4),.stop (.unitPair 3 4),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,96] 97 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 12361),.stop (.unitPair 1 5),.stop (.collision 4619),.stop (.unitPair 0 5),.stop (.collision 70272),.stop (.unitPair 0 5),.stop (.collision 98888),.stop (.unitPair 1 5),.stop (.collision 8833),.stop (.unitPair 0 5),.stop (.collision 8840),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 2 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 12416),.stop (.unitPair 0 4),.stop (.collision 516),.stop (.unitPair 1 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 544),.stop (.unitPair 0 4),.stop (.collision 12304),.stop (.unitPair 1 4),.stop (.collision 12290),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,97] 98 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,98] 99 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 1 5),.stop (.collision 12361),.stop (.unitPair 0 5),.stop (.collision 70272),.stop (.unitPair 0 5),.stop (.collision 102465),.stop (.unitPair 1 5),.stop (.collision 5256),.stop (.unitPair 0 5),.stop (.collision 8833),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 2 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 516),.stop (.unitPair 1 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.collision 8195),.stop (.unitPair 1 4),.stop (.collision 12297),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,99] 100 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,100] 101 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 12416),.stop (.unitPair 1 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 12304),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,101] 102 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,102] 103 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 537),.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 2 4),.stop (.collision 12297),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,103] 104 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,104] 105 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,105] 106 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,106] 107 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,107] 108 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,108] 109 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,109] 110 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,110] 111 (.stop (.collision 25)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,111] 112 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,112] 113 (.stop (.collision 32)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,113] 114 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,114] 115 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 2 4),.stop (.collision 12353),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,115] 116 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,116] 117 (.branch [.stop (.unitPair 2 4),.stop (.collision 12360),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,117] 118 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,118] 119 (.stop (.collision 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,14,119] 120 (.stop (.unitPair 0 3)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

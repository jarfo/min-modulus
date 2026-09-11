import MinModulus.SevenModOneTwenty.BlockNonunit287
import MinModulus.SevenModOneTwenty.BlockNonunit288
import MinModulus.SevenModOneTwenty.BlockNonunit289

namespace MinModulus.PrefixCertificate.Seven120

theorem nonunit_2_18_closed : ClosedMinimalPrefix false 120 2 4 [0,2,18] 19 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,19] 20 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,20] 21 (.stop (.collision 144)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,21] 22 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_18_22_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,23] 24 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_18_24_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,25] 26 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_18_26_closed
  · exact nonunit_2_18_27_closed
  · exact nonunit_2_18_28_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,29] 30 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_18_30_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,31] 32 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_18_32_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,33] 34 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,34] 35 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,35] 36 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,36] 37 (.stop (.collision 200)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,37] 38 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_18_38_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,39] 40 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_18_40_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,41] 42 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_18_42_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,43] 44 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_18_44_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,45] 46 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_18_46_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,47] 48 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_18_48_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,49] 50 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_18_50_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,51] 52 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,52] 53 (.stop (.collision 256)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,53] 54 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_18_54_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,55] 56 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_18_56_closed
  · exact nonunit_2_18_57_closed
  · exact nonunit_2_18_58_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,59] 60 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_18_60_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,61] 62 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_18_62_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,63] 64 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_18_64_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,65] 66 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_18_66_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,67] 68 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_18_68_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,69] 70 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,70] 71 (.stop (.collision 1537)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,71] 72 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_18_72_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,73] 74 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_18_74_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,75] 76 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_18_76_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,77] 78 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_18_78_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,79] 80 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_18_80_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,81] 82 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_18_82_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,83] 84 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_18_84_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,85] 86 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_18_86_closed
  · exact nonunit_2_18_87_closed
  · exact nonunit_2_18_88_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,89] 90 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_18_90_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,91] 92 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,92] 93 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 2 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 1 5),.stop (.collision 12361),.stop (.unitPair 0 5),.stop (.collision 4619),.stop (.unitPair 0 5),.stop (.collision 70272),.stop (.unitPair 1 5),.stop (.collision 102472),.stop (.unitPair 0 5),.stop (.collision 98888),.stop (.unitPair 0 5),.stop (.collision 5256),.stop (.unitPair 1 5),.stop (.collision 8833),.stop (.unitPair 0 5),.stop (.collision 8840),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.collision 98825),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 12416),.stop (.unitPair 1 4),.stop (.collision 516),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 8195),.stop (.unitPair 0 4),.stop (.collision 12304),.stop (.unitPair 1 4),.stop (.collision 12290),.branch [.stop (.unitPair 4 5),.stop (.unitPair 0 5)],.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,93] 94 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,94] 95 (.branch [.stop (.unitPair 2 4),.stop (.collision 1104),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 12361),.stop (.unitPair 0 5),.stop (.collision 70272),.stop (.unitPair 1 5),.stop (.collision 4633),.stop (.unitPair 0 5),.stop (.collision 102465),.stop (.unitPair 0 5),.stop (.collision 98881),.stop (.unitPair 1 5),.stop (.collision 5256),.stop (.unitPair 0 5),.stop (.collision 8833),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 3 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.collision 516),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 537),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.collision 8195),.stop (.unitPair 1 4),.stop (.collision 12297),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,95] 96 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,96] 97 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 12416),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 537),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 0 4),.stop (.collision 8216),.stop (.unitPair 1 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 12304),.stop (.collision 12297),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,97] 98 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,98] 99 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 537),.stop (.unitPair 0 4),.stop (.collision 544),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 1 4),.stop (.collision 8216),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 3 4),.stop (.collision 12297),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,99] 100 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,100] 101 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,101] 102 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,102] 103 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,103] 104 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,104] 105 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,105] 106 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,106] 107 (.stop (.collision 25)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,107] 108 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,108] 109 (.stop (.collision 32)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,109] 110 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,110] 111 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 19),.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,111] 112 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,112] 113 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.collision 12353),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,113] 114 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,114] 115 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.collision 12360),.stop (.collision 12353),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,115] 116 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,116] 117 (.branch [.stop (.unitPair 3 4),.stop (.collision 12360),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,117] 118 (.branch [.stop (.unitPair 3 4),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,118] 119 (.stop (.collision 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,18,119] 120 (.stop (.unitPair 0 3)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

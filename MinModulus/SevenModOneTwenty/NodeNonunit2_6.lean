import MinModulus.SevenModOneTwenty.BlockNonunit276
import MinModulus.SevenModOneTwenty.BlockNonunit277
import MinModulus.SevenModOneTwenty.BlockNonunit278
import MinModulus.SevenModOneTwenty.BlockNonunit279

namespace MinModulus.PrefixCertificate.Seven120

theorem nonunit_2_6_closed : ClosedMinimalPrefix false 120 2 4 [0,2,6] 7 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,7] 8 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,8] 9 (.stop (.collision 144)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,9] 10 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,10] 11 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,11] 12 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,12] 13 (.stop (.collision 200)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,13] 14 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_14_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,15] 16 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,16] 17 (.stop (.collision 256)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,17] 18 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_18_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,19] 20 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_20_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,21] 22 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_6_22_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,23] 24 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_24_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,25] 26 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_6_26_closed
  · exact nonunit_2_6_27_closed
  · exact nonunit_2_6_28_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,29] 30 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_30_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,31] 32 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_32_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,33] 34 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_6_34_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,35] 36 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_6_36_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,37] 38 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_38_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,39] 40 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_6_40_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,41] 42 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_42_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,43] 44 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_44_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,45] 46 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_6_46_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,47] 48 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_48_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,49] 50 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_50_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,51] 52 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_6_52_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,53] 54 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_54_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,55] 56 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_6_56_closed
  · exact nonunit_2_6_57_closed
  · exact nonunit_2_6_58_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,59] 60 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_60_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,61] 62 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_62_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,63] 64 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,64] 65 (.stop (.collision 1537)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,65] 66 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_6_66_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,67] 68 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_68_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,69] 70 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_6_70_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,71] 72 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_72_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,73] 74 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_74_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,75] 76 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_6_76_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,77] 78 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_78_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,79] 80 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_80_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,81] 82 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_6_82_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,83] 84 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_84_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,85] 86 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_6_86_closed
  · exact nonunit_2_6_87_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,88] 89 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 2 4),.stop (.collision 8195),.stop (.unitPair 0 4),.stop (.collision 1216),.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 102472),.stop (.unitPair 1 5),.stop (.collision 8840),.stop (.unitPair 0 5),.stop (.collision 73800),.stop (.unitPair 0 5),.stop (.collision 98888),.stop (.unitPair 1 5),.stop (.collision 12361),.stop (.unitPair 0 5),.stop (.collision 73737),.stop (.unitPair 1 5),.stop (.collision 70272),.stop (.unitPair 3 5),.stop (.collision 4633),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 12416),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.stop (.collision 12304),.stop (.unitPair 0 4),.stop (.collision 12290),.stop (.unitPair 0 4),.stop (.collision 16448),.stop (.unitPair 1 4),.stop (.collision 16385),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 3 4),.stop (.collision 537),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,89] 90 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_6_90_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,91] 92 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,92] 93 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 2 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 8195),.stop (.unitPair 0 4),.stop (.collision 1216),.stop (.unitPair 0 4),.stop (.collision 12416),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.unitPair 0 4),.stop (.collision 12304),.stop (.unitPair 0 4),.stop (.collision 12290),.stop (.unitPair 1 4),.stop (.collision 516),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 1 4),.stop (.collision 8832),.branch [.stop (.unitPair 4 5),.stop (.unitPair 0 5)],.stop (.collision 537),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,93] 94 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,94] 95 (.branch [.stop (.unitPair 2 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.collision 8195),.stop (.unitPair 0 4),.stop (.collision 1216),.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.collision 73800),.stop (.unitPair 0 5),.stop (.collision 73793),.stop (.unitPair 1 5),.stop (.collision 8840),.stop (.unitPair 0 5),.stop (.collision 98881),.stop (.unitPair 1 5),.stop (.collision 70272),.stop (.unitPair 3 5),.stop (.collision 12361),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 0 4),.stop (.collision 12297),.stop (.unitPair 1 4),.stop (.collision 16448),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 3 4),.stop (.collision 537),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,95] 96 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,96] 97 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.collision 8195),.stop (.unitPair 1 4),.stop (.collision 12416),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 0 4),.stop (.collision 12304),.stop (.unitPair 1 4),.stop (.collision 12290),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 1 4),.stop (.collision 8832),.branch [.stop (.unitPair 4 5),.stop (.unitPair 0 5)],.stop (.collision 537),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,97] 98 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,98] 99 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 8195),.stop (.unitPair 0 4),.stop (.collision 1216),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 1 4),.stop (.collision 12297),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 3 4),.stop (.collision 537),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,99] 100 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,100] 101 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.collision 12416),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.stop (.collision 12304),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 3 4),.stop (.collision 537),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,101] 102 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,102] 103 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.collision 8195),.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 0 4),.stop (.collision 12297),.stop (.unitPair 1 4),.stop (.collision 8832),.branch [.stop (.unitPair 4 5),.stop (.unitPair 0 5)],.stop (.collision 537),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,103] 104 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,104] 105 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 3 4),.stop (.collision 537),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,105] 106 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,106] 107 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 3 4),.stop (.collision 537),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,107] 108 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,108] 109 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.collision 12297),.stop (.collision 537),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,109] 110 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,110] 111 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 3 4),.stop (.collision 12297),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,111] 112 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,112] 113 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,113] 114 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,114] 115 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,115] 116 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,116] 117 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,117] 118 (.branch [.stop (.unitPair 3 4),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,118] 119 (.stop (.collision 25)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,6,119] 120 (.stop (.unitPair 0 3)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

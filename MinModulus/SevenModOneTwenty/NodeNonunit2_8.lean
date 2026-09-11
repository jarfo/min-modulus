import MinModulus.SevenModOneTwenty.BlockNonunit279
import MinModulus.SevenModOneTwenty.BlockNonunit280

namespace MinModulus.PrefixCertificate.Seven120

theorem nonunit_2_8_closed : ClosedMinimalPrefix false 120 2 4 [0,2,8] 9 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,9] 10 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,10] 11 (.stop (.collision 144)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,11] 12 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_12_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,13] 14 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,14] 15 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,15] 16 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,16] 17 (.stop (.collision 200)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,17] 18 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_18_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,19] 20 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_20_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,21] 22 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,22] 23 (.stop (.collision 256)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,23] 24 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_24_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,25] 26 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_8_26_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,27] 28 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_8_28_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,29] 30 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_30_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,31] 32 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_32_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,33] 34 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_8_34_closed
  · exact nonunit_2_8_35_closed
  · exact nonunit_2_8_36_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,37] 38 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_38_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,39] 40 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_8_40_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,41] 42 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_42_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,43] 44 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_44_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,45] 46 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_8_46_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,47] 48 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_48_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,49] 50 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_50_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,51] 52 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_8_52_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,53] 54 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_54_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,55] 56 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_8_56_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,57] 58 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_8_58_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,59] 60 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_60_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,61] 62 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_62_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,63] 64 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,64] 65 (.stop (.collision 1544)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,65] 66 (.stop (.collision 1537)) (by decide +kernel))
  · exact nonunit_2_8_66_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,67] 68 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_68_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,69] 70 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_8_70_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,71] 72 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_72_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,73] 74 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_74_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,75] 76 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_8_76_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,77] 78 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_78_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,79] 80 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_80_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,81] 82 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_8_82_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,83] 84 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_84_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,85] 86 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_8_86_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,87] 88 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,88] 89 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 8216),.stop (.unitPair 1 4),.stop (.collision 1153),.stop (.unitPair 3 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.collision 8195),.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 102472),.stop (.unitPair 1 5),.stop (.collision 8833),.stop (.unitPair 0 5),.stop (.collision 73800),.stop (.unitPair 0 5),.stop (.collision 98888),.stop (.unitPair 1 5),.stop (.collision 12361),.stop (.unitPair 0 5),.stop (.collision 70272),.stop (.unitPair 1 5),.stop (.collision 73737),.stop (.unitPair 2 5),.stop (.collision 4675),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 1216),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 73737),.stop (.unitPair 1 5),.stop (.collision 8833),.stop (.unitPair 0 5),.stop (.collision 70272),.stop (.unitPair 1 5),.stop (.collision 4633),.stop (.unitPair 2 5),.stop (.collision 4675),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 12297),.stop (.unitPair 0 4),.stop (.collision 16448),.stop (.unitPair 1 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 537),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,89] 90 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,90] 91 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 8216),.branch [.stop (.unitPair 4 5),.stop (.unitPair 0 5),.stop (.collision 5256),.stop (.unitPair 1 5),.stop (.collision 12361),.stop (.unitPair 0 5),.stop (.unitPair 4 5),.stop (.unitPair 0 5),.stop (.collision 5312),.stop (.unitPair 1 5),.stop (.unitPair 4 5),.stop (.unitPair 0 5),.stop (.unitPair 4 5),.stop (.unitPair 0 5),.stop (.collision 102402),.stop (.unitPair 1 5),.stop (.unitPair 4 5),.stop (.unitPair 0 5),.stop (.unitPair 4 5),.stop (.unitPair 1 5),.stop (.collision 4633),.stop (.unitPair 2 5),.stop (.unitPair 4 5),.stop (.unitPair 0 5)],.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 8195),.stop (.unitPair 0 4),.stop (.collision 12416),.stop (.unitPair 0 4),.stop (.collision 1216),.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 0 4),.stop (.collision 12304),.stop (.unitPair 0 4),.stop (.collision 12290),.stop (.unitPair 1 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 537),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,91] 92 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_8_92_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,93] 94 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,94] 95 (.branch [.stop (.unitPair 3 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 8216),.stop (.unitPair 1 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.collision 12416),.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.collision 73800),.stop (.unitPair 0 5),.stop (.collision 73793),.stop (.unitPair 1 5),.stop (.collision 8833),.stop (.unitPair 0 5),.stop (.collision 70272),.stop (.unitPair 1 5),.stop (.collision 73737),.stop (.unitPair 2 5),.stop (.collision 12361),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 0 4),.stop (.collision 12304),.stop (.unitPair 1 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 537),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact nonunit_2_8_95_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,96] 97 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 8216),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 8195),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 0 4),.stop (.collision 1216),.stop (.unitPair 1 4),.stop (.collision 12297),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 537),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,97] 98 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,98] 99 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 8216),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.collision 8195),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 1 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 537),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,99] 100 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,100] 101 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 8216),.stop (.unitPair 1 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 537),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,101] 102 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,102] 103 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 8216),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 537),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,103] 104 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,104] 105 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 8216),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 12297),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,105] 106 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,106] 107 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 12416),.stop (.unitPair 1 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 537),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,107] 108 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,108] 109 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 2 4),.stop (.collision 12297),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,109] 110 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,110] 111 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,111] 112 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,112] 113 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,113] 114 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,114] 115 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,115] 116 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,116] 117 (.stop (.collision 25)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,117] 118 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,118] 119 (.stop (.collision 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,8,119] 120 (.stop (.unitPair 0 3)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

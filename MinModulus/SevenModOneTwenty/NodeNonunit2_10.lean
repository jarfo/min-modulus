import MinModulus.SevenModOneTwenty.BlockNonunit281
import MinModulus.SevenModOneTwenty.BlockNonunit282

namespace MinModulus.PrefixCertificate.Seven120

theorem nonunit_2_10_closed : ClosedMinimalPrefix false 120 2 4 [0,2,10] 11 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,11] 12 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,12] 13 (.stop (.collision 144)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,13] 14 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_10_14_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,15] 16 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_10_16_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,17] 18 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,18] 19 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,19] 20 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,20] 21 (.stop (.collision 200)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,21] 22 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_10_22_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,23] 24 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_10_24_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,25] 26 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_10_26_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,27] 28 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,28] 29 (.stop (.collision 256)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,29] 30 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_10_30_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,31] 32 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_10_32_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,33] 34 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_10_34_closed
  · exact nonunit_2_10_35_closed
  · exact nonunit_2_10_36_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,37] 38 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_10_38_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,39] 40 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_10_40_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,41] 42 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_10_42_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,43] 44 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,44] 45 (.stop (.collision 2048)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,45] 46 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_10_46_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,47] 48 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_10_48_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,49] 50 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_10_50_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,51] 52 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_10_52_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,53] 54 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_10_54_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,55] 56 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_10_56_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,57] 58 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_10_58_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,59] 60 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_10_60_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,61] 62 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_10_62_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,63] 64 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_10_64_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,65] 66 (.stop (.collision 1544)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,66] 67 (.stop (.collision 1537)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,67] 68 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_10_68_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,69] 70 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_10_70_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,71] 72 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_10_72_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,73] 74 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_10_74_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,75] 76 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_10_76_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,77] 78 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_10_78_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,79] 80 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_10_80_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,81] 82 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_10_82_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,83] 84 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,84] 85 (.stop (.collision 2048)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,85] 86 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_10_86_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,87] 88 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_10_88_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,89] 90 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_10_90_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,91] 92 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_10_92_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,93] 94 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,94] 95 (.branch [.stop (.unitPair 3 4),.stop (.collision 1104),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 5249),.stop (.unitPair 0 5),.stop (.collision 5256),.stop (.unitPair 1 5),.stop (.collision 8833),.stop (.unitPair 0 5),.stop (.collision 8840),.stop (.unitPair 0 5),.stop (.collision 98881),.stop (.unitPair 1 5),.stop (.collision 70272),.stop (.unitPair 0 5),.stop (.collision 98825),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 2 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.collision 8216),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 8195),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 537),.stop (.unitPair 1 4),.stop (.collision 544),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact nonunit_2_10_95_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,96] 97 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 5249),.stop (.unitPair 1 5),.stop (.collision 5256),.stop (.unitPair 0 5),.stop (.collision 102472),.stop (.unitPair 0 5),.stop (.collision 98888),.stop (.unitPair 1 5),.stop (.collision 70272),.stop (.unitPair 0 5),.stop (.collision 4633),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 2 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 8216),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 537),.stop (.unitPair 1 4),.stop (.collision 544),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,97] 98 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,98] 99 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 1 5),.stop (.collision 5249),.stop (.unitPair 0 5),.stop (.collision 5256),.stop (.unitPair 0 5),.stop (.collision 102465),.stop (.unitPair 1 5),.stop (.collision 70272),.stop (.unitPair 0 5),.stop (.collision 102409),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 2 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 8216),.stop (.unitPair 1 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 12297),.stop (.unitPair 1 4),.stop (.collision 1216),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,99] 100 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,100] 101 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 5249),.stop (.unitPair 0 5),.stop (.collision 102472),.stop (.unitPair 1 5),.stop (.collision 70272),.stop (.unitPair 0 5),.stop (.collision 8840),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 2 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.collision 12416),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 537),.stop (.unitPair 1 4),.stop (.collision 544),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,101] 102 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,102] 103 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 5249),.stop (.unitPair 1 5),.stop (.collision 70272),.stop (.unitPair 0 5),.stop (.collision 98881),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 2 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 8216),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 537),.stop (.unitPair 1 4),.stop (.collision 12297),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,103] 104 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,104] 105 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 12416),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 12304),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,105] 106 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,106] 107 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 2 4),.stop (.collision 12297),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,107] 108 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,108] 109 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,109] 110 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,110] 111 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,111] 112 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,112] 113 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,113] 114 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,114] 115 (.stop (.collision 25)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,115] 116 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,116] 117 (.stop (.collision 32)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,117] 118 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,118] 119 (.stop (.collision 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,10,119] 120 (.stop (.unitPair 0 3)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

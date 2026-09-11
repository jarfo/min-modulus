import MinModulus.SevenModOneTwenty.BlockNonunit291
import MinModulus.SevenModOneTwenty.BlockNonunit292

namespace MinModulus.PrefixCertificate.Seven120

theorem nonunit_2_22_closed : ClosedMinimalPrefix false 120 2 4 [0,2,22] 23 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,23] 24 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,24] 25 (.stop (.collision 144)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,25] 26 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_22_26_closed
  · exact nonunit_2_22_27_closed
  · exact nonunit_2_22_28_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,29] 30 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_22_30_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,31] 32 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_22_32_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,33] 34 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_22_34_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,35] 36 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_22_36_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,37] 38 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_22_38_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,39] 40 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_22_40_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,41] 42 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,42] 43 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,43] 44 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,44] 45 (.stop (.collision 200)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,45] 46 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_22_46_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,47] 48 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,48] 49 (.stop (.collision 2048)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,49] 50 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_22_50_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,51] 52 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_22_52_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,53] 54 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_22_54_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,55] 56 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_22_56_closed
  · exact nonunit_2_22_57_closed
  · exact nonunit_2_22_58_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,59] 60 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_22_60_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,61] 62 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_22_62_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,63] 64 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,64] 65 (.stop (.collision 256)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,65] 66 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_22_66_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,67] 68 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_22_68_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,69] 70 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_22_70_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,71] 72 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,72] 73 (.stop (.collision 1537)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,73] 74 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_22_74_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,75] 76 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_22_76_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,77] 78 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_22_78_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,79] 80 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_22_80_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,81] 82 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_22_82_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,83] 84 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,84] 85 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.collision 20480),.stop (.collision 16896),.stop (.unitPair 0 4),.stop (.collision 13312),.stop (.unitPair 0 4),.stop (.collision 12416),.stop (.unitPair 1 4),.branch [.stop (.unitPair 2 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 4619),.stop (.unitPair 1 5),.stop (.collision 70272),.stop (.unitPair 0 5),.stop (.collision 102472),.stop (.unitPair 0 5),.stop (.collision 5249),.stop (.unitPair 1 5),.stop (.collision 5256),.stop (.unitPair 0 5),.stop (.collision 98881),.stop (.unitPair 0 5),.stop (.collision 73800),.stop (.unitPair 1 5),.stop (.collision 73793),.stop (.unitPair 0 5),.stop (.collision 8833),.stop (.unitPair 1 5),.stop (.collision 8840),.stop (.unitPair 4 5),.stop (.collision 98825),.stop (.unitPair 0 5)],.stop (.unitPair 2 4),.stop (.collision 9728),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.collision 2049),.stop (.unitPair 0 4),.stop (.collision 2056),.stop (.unitPair 1 4),.stop (.collision 12304),.stop (.unitPair 0 4),.stop (.collision 12290),.stop (.unitPair 1 4),.stop (.collision 16385),.stop (.collision 20480),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,85] 86 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_22_86_closed
  · exact nonunit_2_22_87_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,88] 89 (.stop (.collision 2048)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,89] 90 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,90] 91 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 257),.stop (.unitPair 2 4),.stop (.collision 264),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 537),.stop (.unitPair 0 4),.stop (.collision 544),.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 0 4),.stop (.collision 8216),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.collision 8195),.stop (.unitPair 1 4),.stop (.collision 12297),.stop (.collision 12290),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,91] 92 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,92] 93 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 2 4),.stop (.collision 12416),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 537),.stop (.unitPair 0 4),.stop (.collision 544),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.unitPair 0 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 1 5),.stop (.collision 5249),.stop (.unitPair 0 5),.stop (.collision 98888),.stop (.unitPair 1 5),.stop (.collision 12928),.stop (.collision 102409),.stop (.collision 4675),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 8216),.stop (.unitPair 1 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 12304),.stop (.collision 12297),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,93] 94 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,94] 95 (.branch [.stop (.unitPair 2 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 523),.stop (.unitPair 1 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 537),.stop (.unitPair 0 4),.stop (.collision 544),.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.collision 73800),.stop (.unitPair 0 5),.stop (.collision 73793),.stop (.unitPair 1 5),.stop (.collision 135232),.stop (.unitPair 0 5),.stop (.collision 98881),.stop (.unitPair 1 5),.stop (.collision 5256),.stop (.unitPair 3 5),.stop (.collision 102409),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 5249),.stop (.unitPair 1 5),.stop (.collision 5256),.stop (.unitPair 3 5),.stop (.collision 102409),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.collision 16448),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 3 4),.stop (.collision 12297),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,95] 96 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,96] 97 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,97] 98 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,98] 99 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,99] 100 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,100] 101 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,101] 102 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,102] 103 (.stop (.collision 25)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,103] 104 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,104] 105 (.stop (.collision 32)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,105] 106 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,106] 107 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 5),.stop (.unitPair 1 4),.stop (.collision 1664),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 1 4),.stop (.collision 16448),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,107] 108 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,108] 109 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 19),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.stop (.collision 1664),.branch [.stop (.unitPair 4 5),.stop (.unitPair 0 5)],.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,109] 110 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,110] 111 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 33),.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,111] 112 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,112] 113 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.collision 12353),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,113] 114 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,114] 115 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.collision 12360),.stop (.collision 12353),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,115] 116 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,116] 117 (.branch [.stop (.unitPair 3 4),.stop (.collision 12360),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,117] 118 (.branch [.stop (.unitPair 3 4),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,118] 119 (.stop (.collision 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,22,119] 120 (.stop (.unitPair 0 3)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

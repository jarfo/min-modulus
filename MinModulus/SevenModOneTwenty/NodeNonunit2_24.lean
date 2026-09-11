import MinModulus.SevenModOneTwenty.BlockNonunit292
import MinModulus.SevenModOneTwenty.BlockNonunit293

namespace MinModulus.PrefixCertificate.Seven120

theorem nonunit_2_24_closed : ClosedMinimalPrefix false 120 2 4 [0,2,24] 25 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,25] 26 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,26] 27 (.stop (.collision 144)) (by decide +kernel))
  · exact nonunit_2_24_27_closed
  · exact nonunit_2_24_28_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,29] 30 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_24_30_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,31] 32 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_24_32_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,33] 34 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_24_34_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,35] 36 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_24_36_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,37] 38 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_24_38_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,39] 40 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_24_40_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,41] 42 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_24_42_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,43] 44 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_24_44_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,45] 46 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,46] 47 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,47] 48 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,48] 49 (.stop (.collision 200)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,49] 50 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_24_50_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,51] 52 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_24_52_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,53] 54 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_24_54_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,55] 56 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_24_56_closed
  · exact nonunit_2_24_57_closed
  · exact nonunit_2_24_58_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,59] 60 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_24_60_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,61] 62 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_24_62_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,63] 64 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_24_64_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,65] 66 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_24_66_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,67] 68 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_24_68_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,69] 70 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,70] 71 (.stop (.collision 256)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,71] 72 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,72] 73 (.stop (.collision 1544)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,73] 74 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_24_74_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,75] 76 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_24_76_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,77] 78 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_24_78_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,79] 80 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_24_80_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,81] 82 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,82] 83 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 201),.stop (.collision 20480),.stop (.collision 208),.stop (.unitPair 0 4),.stop (.collision 12416),.stop (.unitPair 0 4),.stop (.collision 13312),.stop (.unitPair 1 4),.stop (.collision 516),.stop (.unitPair 2 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 537),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 0 4),.stop (.collision 16448),.stop (.unitPair 0 4),.stop (.collision 264),.stop (.unitPair 1 4),.stop (.collision 12304),.stop (.unitPair 0 4),.stop (.collision 12290),.stop (.unitPair 1 4),.stop (.collision 16385),.stop (.collision 20480),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,83] 84 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_24_84_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,85] 86 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,86] 87 (.branch [.stop (.unitPair 3 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 13312),.stop (.unitPair 0 4),.stop (.collision 12416),.stop (.unitPair 1 4),.stop (.collision 9728),.stop (.unitPair 2 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 537),.stop (.unitPair 0 4),.stop (.collision 544),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 1 4),.stop (.collision 264),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 2049),.stop (.unitPair 0 4),.stop (.collision 2056),.stop (.unitPair 1 4),.stop (.collision 12290),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact nonunit_2_24_87_closed
  · exact nonunit_2_24_88_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,89] 90 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,90] 91 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 12416),.stop (.unitPair 2 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 537),.stop (.unitPair 0 4),.stop (.collision 264),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 0 5),.stop (.collision 73793),.stop (.unitPair 0 5),.stop (.collision 12928),.stop (.unitPair 1 5),.stop (.collision 98888),.stop (.unitPair 0 5),.stop (.collision 5256),.stop (.unitPair 1 5),.stop (.collision 102416),.stop (.unitPair 4 5),.stop (.collision 12361),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 0 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 1 5),.stop (.collision 5249),.stop (.unitPair 0 5),.stop (.collision 98888),.stop (.unitPair 1 5),.stop (.collision 77888),.stop (.collision 102409),.stop (.collision 4675),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 8216),.stop (.unitPair 1 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 12304),.stop (.collision 12297),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,91] 92 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,92] 93 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 2 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 1 4),.stop (.collision 537),.stop (.unitPair 0 4),.stop (.collision 544),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.collision 102472),.stop (.unitPair 0 5),.stop (.collision 73800),.stop (.unitPair 0 5),.stop (.collision 73793),.stop (.unitPair 1 5),.stop (.collision 98888),.stop (.unitPair 0 5),.stop (.collision 5249),.stop (.unitPair 1 5),.stop (.collision 5256),.stop (.unitPair 4 5),.stop (.collision 102409),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.unitPair 0 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 1 5),.stop (.collision 16456),.stop (.unitPair 0 5),.stop (.collision 98888),.stop (.unitPair 1 5),.stop (.collision 5256),.stop (.collision 102416),.stop (.collision 102409),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 5249),.stop (.unitPair 1 5),.stop (.collision 5256),.stop (.unitPair 4 5),.stop (.collision 102409),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.collision 8216),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.collision 12304),.stop (.collision 12297),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,93] 94 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,94] 95 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,95] 96 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,96] 97 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,97] 98 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,98] 99 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,99] 100 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,100] 101 (.stop (.collision 25)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,101] 102 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,102] 103 (.stop (.collision 32)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,103] 104 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,104] 105 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 1 5),.stop (.collision 102472),.stop (.unitPair 0 5),.stop (.collision 98888),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 3 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 1664),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.unitPair 0 4),.stop (.collision 19),.stop (.unitPair 1 4),.stop (.collision 26),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,105] 106 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,106] 107 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 12),.stop (.unitPair 1 4),.stop (.collision 19),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 1 4),.stop (.collision 16448),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,107] 108 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,108] 109 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 26),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.stop (.collision 40),.branch [.stop (.unitPair 4 5),.stop (.unitPair 0 5)],.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,109] 110 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,110] 111 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 40),.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,111] 112 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,112] 113 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.collision 12353),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,113] 114 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,114] 115 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.collision 12360),.stop (.collision 12353),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,115] 116 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,116] 117 (.branch [.stop (.unitPair 3 4),.stop (.collision 12360),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,117] 118 (.branch [.stop (.unitPair 3 4),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,118] 119 (.stop (.collision 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,24,119] 120 (.stop (.unitPair 0 3)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

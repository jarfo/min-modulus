import MinModulus.SevenModOneTwenty.BlockNonunit298
import MinModulus.SevenModOneTwenty.BlockNonunit299

namespace MinModulus.PrefixCertificate.Seven120

theorem nonunit_2_32_closed : ClosedMinimalPrefix false 120 2 4 [0,2,32] 33 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,33] 34 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,34] 35 (.stop (.collision 144)) (by decide +kernel))
  · exact nonunit_2_32_35_closed
  · exact nonunit_2_32_36_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,37] 38 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_32_38_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,39] 40 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_32_40_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,41] 42 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_32_42_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,43] 44 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_32_44_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,45] 46 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_32_46_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,47] 48 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_32_48_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,49] 50 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_32_50_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,51] 52 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_32_52_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,53] 54 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_32_54_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,55] 56 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_32_56_closed
  · exact nonunit_2_32_57_closed
  · exact nonunit_2_32_58_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,59] 60 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_32_60_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,61] 62 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,62] 63 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,63] 64 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,64] 65 (.stop (.collision 200)) (by decide +kernel))
  · exact nonunit_2_32_65_closed
  · exact nonunit_2_32_66_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,67] 68 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_32_68_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,69] 70 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_32_70_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,71] 72 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_32_72_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,73] 74 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_32_74_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,75] 76 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,76] 77 (.stop (.collision 1544)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,77] 78 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_32_78_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,79] 80 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_32_80_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,81] 82 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_32_82_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,83] 84 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_32_84_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,85] 86 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,86] 87 (.stop (.collision 4)) (by decide +kernel))
  · exact nonunit_2_32_87_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,88] 89 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,89] 90 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,90] 91 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,91] 92 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,92] 93 (.stop (.collision 25)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,93] 94 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,94] 95 (.stop (.collision 256)) (by decide +kernel))
  · exact nonunit_2_32_95_closed
  · exact nonunit_2_32_96_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,97] 98 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,98] 99 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 1 5),.stop (.collision 12361),.stop (.unitPair 0 5),.stop (.collision 12368),.stop (.unitPair 0 5),.stop (.collision 102465),.stop (.unitPair 1 5),.stop (.collision 98881),.stop (.unitPair 0 5),.stop (.collision 12928),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 3 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 131137),.stop (.unitPair 0 5),.stop (.collision 102465),.stop (.unitPair 1 5),.stop (.collision 98888),.stop (.unitPair 0 5),.stop (.collision 73800),.stop (.unitPair 1 5),.stop (.collision 73793),.stop (.unitPair 3 5),.stop (.collision 4675),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.collision 1664),.stop (.unitPair 0 4),.stop (.collision 5),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 1 4),.stop (.collision 19),.stop (.unitPair 0 4),.stop (.collision 26),.stop (.unitPair 1 4),.stop (.collision 257),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,99] 100 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,100] 101 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 12361),.stop (.unitPair 0 5),.stop (.collision 102472),.stop (.unitPair 1 5),.stop (.collision 98888),.stop (.unitPair 0 5),.stop (.collision 135232),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 3 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.collision 5),.stop (.unitPair 0 4),.stop (.collision 12),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.stop (.collision 26),.stop (.unitPair 0 4),.stop (.collision 16448),.stop (.unitPair 1 4),.stop (.collision 264),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,101] 102 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,102] 103 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 12),.stop (.unitPair 0 4),.stop (.collision 19),.stop (.unitPair 0 4),.stop (.collision 26),.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 0 4),.stop (.collision 1664),.stop (.unitPair 1 4),.branch [.stop (.unitPair 4 5),.stop (.collision 98888),.stop (.unitPair 0 5)],.branch [.stop (.unitPair 4 5),.stop (.unitPair 0 5)],.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,103] 104 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,104] 105 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 26),.stop (.unitPair 0 4),.stop (.collision 257),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.collision 8784),.stop (.unitPair 3 5),.stop (.collision 98881),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.branch [.stop (.unitPair 3 5),.stop (.collision 98888),.stop (.unitPair 0 5)],.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,105] 106 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,106] 107 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 264),.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.collision 73800),.stop (.unitPair 1 5),.stop (.collision 98888),.stop (.unitPair 3 5),.stop (.collision 12361),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 1 4),.stop (.collision 16448),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,107] 108 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,108] 109 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.collision 102472),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.collision 98881),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.branch [.stop (.unitPair 4 5),.stop (.collision 98888),.stop (.unitPair 0 5)],.branch [.stop (.unitPair 4 5),.stop (.unitPair 0 5)],.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,109] 110 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,110] 111 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 3 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,111] 112 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,112] 113 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.collision 12353),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,113] 114 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,114] 115 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.collision 12360),.stop (.collision 12353),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,115] 116 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,116] 117 (.branch [.stop (.unitPair 3 4),.stop (.collision 12360),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,117] 118 (.branch [.stop (.unitPair 3 4),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,118] 119 (.stop (.collision 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,32,119] 120 (.stop (.unitPair 0 3)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

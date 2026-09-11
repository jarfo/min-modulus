import MinModulus.SevenModOneTwenty.BlockNonunit296
import MinModulus.SevenModOneTwenty.BlockNonunit297
import MinModulus.SevenModOneTwenty.BlockNonunit298

namespace MinModulus.PrefixCertificate.Seven120

theorem nonunit_2_30_closed : ClosedMinimalPrefix false 120 2 4 [0,2,30] 31 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,31] 32 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,32] 33 (.stop (.collision 144)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,33] 34 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_30_34_closed
  · exact nonunit_2_30_35_closed
  · exact nonunit_2_30_36_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,37] 38 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_30_38_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,39] 40 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_30_40_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,41] 42 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_30_42_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,43] 44 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_30_44_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,45] 46 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_30_46_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,47] 48 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_30_48_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,49] 50 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_30_50_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,51] 52 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_30_52_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,53] 54 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_30_54_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,55] 56 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_30_56_closed
  · exact nonunit_2_30_57_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,58] 59 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,59] 60 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,60] 61 (.stop (.collision 200)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,61] 62 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_30_62_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,63] 64 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_30_64_closed
  · exact nonunit_2_30_65_closed
  · exact nonunit_2_30_66_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,67] 68 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_30_68_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,69] 70 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_30_70_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,71] 72 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_30_72_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,73] 74 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_30_74_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,75] 76 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,76] 77 (.stop (.collision 1537)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,77] 78 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_30_78_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,79] 80 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_30_80_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,81] 82 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_30_82_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,83] 84 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_30_84_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,85] 86 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_30_86_closed
  · exact nonunit_2_30_87_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,88] 89 (.stop (.collision 256)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,89] 90 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,90] 91 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,91] 92 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,92] 93 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,93] 94 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,94] 95 (.stop (.collision 25)) (by decide +kernel))
  · exact nonunit_2_30_95_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,96] 97 (.stop (.collision 32)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,97] 98 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,98] 99 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 1 5),.stop (.collision 12361),.stop (.unitPair 0 5),.stop (.collision 9344),.stop (.unitPair 0 5),.stop (.collision 102465),.stop (.unitPair 1 5),.stop (.collision 98881),.stop (.unitPair 0 5),.stop (.collision 98321),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 3 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 1664),.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 102465),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 0 5),.stop (.collision 73793),.stop (.unitPair 1 5),.stop (.collision 131648),.stop (.unitPair 3 5),.stop (.collision 4675),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.branch [.stop (.unitPair 0 5),.stop (.collision 73800),.stop (.unitPair 1 5),.stop (.collision 73793),.stop (.unitPair 0 5),.stop (.collision 98888),.stop (.unitPair 1 5),.stop (.collision 106560),.stop (.unitPair 3 5),.stop (.collision 12361),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 1 4),.stop (.collision 264),.stop (.unitPair 0 4),.stop (.collision 19),.stop (.unitPair 1 4),.stop (.collision 26),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,99] 100 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,100] 101 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 12361),.stop (.unitPair 0 5),.stop (.collision 102472),.stop (.unitPair 1 5),.stop (.collision 98888),.stop (.unitPair 0 5),.stop (.collision 135232),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 3 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 102472),.stop (.unitPair 1 5),.stop (.collision 12361),.stop (.unitPair 0 5),.stop (.collision 73800),.stop (.unitPair 1 5),.stop (.collision 73793),.stop (.unitPair 3 5),.stop (.collision 4675),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 1664),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.stop (.collision 19),.stop (.unitPair 0 4),.stop (.collision 16448),.stop (.unitPair 1 4),.stop (.collision 33),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,101] 102 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,102] 103 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 257),.stop (.unitPair 0 4),.stop (.collision 264),.stop (.unitPair 0 4),.stop (.collision 19),.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 0 4),.stop (.collision 33),.stop (.unitPair 1 4),.stop (.collision 40),.branch [.stop (.unitPair 4 5),.stop (.unitPair 0 5)],.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,103] 104 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,104] 105 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 19),.stop (.unitPair 0 4),.stop (.collision 26),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.unitPair 0 4),.stop (.collision 40),.stop (.unitPair 1 4),.stop (.collision 1664),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,105] 106 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,106] 107 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 33),.stop (.unitPair 1 4),.stop (.collision 40),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 1 4),.stop (.collision 16448),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,107] 108 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,108] 109 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.collision 102472),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.collision 98881),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.branch [.stop (.unitPair 4 5),.stop (.collision 98888),.stop (.unitPair 0 5)],.branch [.stop (.unitPair 4 5),.stop (.unitPair 0 5)],.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,109] 110 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,110] 111 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 3 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 3 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,111] 112 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,112] 113 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.collision 12353),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,113] 114 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,114] 115 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.collision 12360),.stop (.collision 12353),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,115] 116 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,116] 117 (.branch [.stop (.unitPair 3 4),.stop (.collision 12360),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,117] 118 (.branch [.stop (.unitPair 3 4),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,118] 119 (.stop (.collision 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,30,119] 120 (.stop (.unitPair 0 3)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

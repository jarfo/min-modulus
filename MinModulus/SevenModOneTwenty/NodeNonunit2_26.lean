import MinModulus.SevenModOneTwenty.BlockNonunit293
import MinModulus.SevenModOneTwenty.BlockNonunit294

namespace MinModulus.PrefixCertificate.Seven120

theorem nonunit_2_26_closed : ClosedMinimalPrefix false 120 2 4 [0,2,26] 27 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,27] 28 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,28] 29 (.stop (.collision 144)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,29] 30 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_26_30_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,31] 32 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_26_32_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,33] 34 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_26_34_closed
  · exact nonunit_2_26_35_closed
  · exact nonunit_2_26_36_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,37] 38 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_26_38_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,39] 40 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_26_40_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,41] 42 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_26_42_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,43] 44 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_26_44_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,45] 46 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_26_46_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,47] 48 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_26_48_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,49] 50 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,50] 51 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,51] 52 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,52] 53 (.stop (.collision 200)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,53] 54 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_26_54_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,55] 56 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_26_56_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,57] 58 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_26_58_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,59] 60 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_26_60_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,61] 62 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_26_62_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,63] 64 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_26_64_closed
  · exact nonunit_2_26_65_closed
  · exact nonunit_2_26_66_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,67] 68 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_26_68_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,69] 70 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_26_70_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,71] 72 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_26_72_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,73] 74 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,74] 75 (.stop (.collision 1537)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,75] 76 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,76] 77 (.stop (.collision 256)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,77] 78 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_26_78_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,79] 80 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_26_80_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,81] 82 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_26_82_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,83] 84 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,84] 85 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 2 4),.stop (.collision 201),.stop (.unitPair 0 4),.stop (.collision 12416),.stop (.unitPair 0 4),.stop (.collision 13312),.stop (.unitPair 1 4),.stop (.collision 523),.stop (.unitPair 3 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 537),.stop (.unitPair 1 4),.stop (.collision 9728),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 0 4),.stop (.collision 2049),.stop (.unitPair 1 4),.stop (.collision 2056),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 257),.stop (.unitPair 0 4),.stop (.collision 264),.stop (.unitPair 1 4),.stop (.collision 12290),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,85] 86 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_26_86_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,87] 88 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,88] 89 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 9728),.stop (.unitPair 1 4),.stop (.collision 523),.stop (.unitPair 3 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 537),.stop (.unitPair 1 4),.stop (.collision 544),.stop (.unitPair 0 4),.branch [.stop (.unitPair 0 5),.stop (.collision 102472),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 0 5),.stop (.collision 73793),.stop (.unitPair 0 5),.stop (.collision 135232),.stop (.unitPair 1 5),.stop (.collision 98881),.stop (.unitPair 0 5),.stop (.collision 5256),.stop (.unitPair 1 5),.stop (.collision 12361),.stop (.unitPair 2 5),.stop (.collision 4675),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 135232),.stop (.unitPair 1 5),.stop (.collision 5249),.stop (.unitPair 0 5),.stop (.collision 5256),.stop (.unitPair 1 5),.stop (.collision 131648),.stop (.unitPair 2 5),.stop (.collision 4675),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 257),.stop (.unitPair 0 4),.stop (.collision 16448),.stop (.unitPair 1 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 12304),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,89] 90 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_26_90_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,91] 92 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,92] 93 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,93] 94 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,94] 95 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,95] 96 (.branch [.stop (.unitPair 3 4),.stop (.unitPair 0 4),.stop (.collision 537),.stop (.unitPair 1 4),.stop (.collision 544),.stop (.unitPair 0 4),.stop (.unitPair 3 4),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5),.stop (.collision 1665),.stop (.unitPair 1 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5),.stop (.unitPair 3 5),.stop (.unitPair 1 5),.stop (.collision 545),.stop (.unitPair 2 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.unitPair 3 4),.stop (.unitPair 0 4),.stop (.unitPair 3 4),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5),.stop (.unitPair 3 5),.stop (.unitPair 1 5),.stop (.collision 98881),.stop (.unitPair 2 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.unitPair 3 4),.stop (.unitPair 0 4),.stop (.unitPair 3 4),.stop (.unitPair 1 4),.branch [.stop (.unitPair 2 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5)],.stop (.unitPair 2 4),.stop (.unitPair 3 4),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,96] 97 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,97] 98 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,98] 99 (.stop (.collision 25)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,99] 100 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,100] 101 (.stop (.collision 32)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,101] 102 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,102] 103 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.branch [.stop (.unitPair 0 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 12361),.stop (.unitPair 1 5),.stop (.collision 102465),.stop (.unitPair 0 5),.stop (.collision 98881),.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 2 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 0 4),.stop (.collision 1664),.stop (.unitPair 0 4),.stop (.collision 5),.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 0 4),.stop (.collision 19),.stop (.unitPair 1 4),.stop (.collision 26),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,103] 104 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,104] 105 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 5),.stop (.unitPair 0 4),.stop (.collision 12),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.unitPair 0 4),.stop (.collision 26),.stop (.unitPair 1 4),.stop (.collision 33),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,105] 106 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,106] 107 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 19),.stop (.unitPair 1 4),.stop (.collision 26),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 1 4),.stop (.collision 16448),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,107] 108 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,108] 109 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 33),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.branch [.stop (.unitPair 2 5),.stop (.collision 98888),.stop (.unitPair 0 5)],.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,109] 110 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,110] 111 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.collision 73800),.stop (.unitPair 2 5),.stop (.collision 73793),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,111] 112 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,112] 113 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,113] 114 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,114] 115 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 2 4),.stop (.collision 12353),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,115] 116 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,116] 117 (.branch [.stop (.unitPair 2 4),.stop (.collision 12360),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,117] 118 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,118] 119 (.stop (.collision 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,26,119] 120 (.stop (.unitPair 0 3)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

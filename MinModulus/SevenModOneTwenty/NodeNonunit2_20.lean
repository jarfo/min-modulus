import MinModulus.SevenModOneTwenty.BlockNonunit289
import MinModulus.SevenModOneTwenty.BlockNonunit290

namespace MinModulus.PrefixCertificate.Seven120

theorem nonunit_2_20_closed : ClosedMinimalPrefix false 120 2 4 [0,2,20] 21 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,21] 22 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,22] 23 (.stop (.collision 144)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,23] 24 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_20_24_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,25] 26 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_20_26_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,27] 28 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_20_28_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,29] 30 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_20_30_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,31] 32 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_20_32_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,33] 34 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_20_34_closed
  · exact nonunit_2_20_35_closed
  · exact nonunit_2_20_36_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,37] 38 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,38] 39 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,39] 40 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,40] 41 (.stop (.collision 200)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,41] 42 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_20_42_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,43] 44 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_20_44_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,45] 46 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_20_46_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,47] 48 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_20_48_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,49] 50 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_20_50_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,51] 52 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_20_52_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,53] 54 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_20_54_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,55] 56 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_20_56_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,57] 58 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,58] 59 (.stop (.collision 256)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,59] 60 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_20_60_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,61] 62 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_20_62_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,63] 64 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_20_64_closed
  · exact nonunit_2_20_65_closed
  · exact nonunit_2_20_66_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,67] 68 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_20_68_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,69] 70 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,70] 71 (.stop (.collision 1544)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,71] 72 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_20_72_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,73] 74 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_20_74_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,75] 76 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_20_76_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,77] 78 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_20_78_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,79] 80 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_20_80_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,81] 82 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_20_82_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,83] 84 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_20_84_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,85] 86 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact nonunit_2_20_86_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,87] 88 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact nonunit_2_20_88_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,89] 90 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_20_90_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,91] 92 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact nonunit_2_20_92_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,93] 94 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,94] 95 (.branch [.stop (.unitPair 3 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 12416),.stop (.unitPair 1 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 537),.stop (.unitPair 1 4),.stop (.collision 544),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 0 4),.stop (.collision 8216),.stop (.unitPair 1 4),.stop (.collision 1153),.stop (.unitPair 0 4),.stop (.collision 1160),.stop (.unitPair 1 4),.stop (.collision 12304),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,95] 96 (.branch [.stop (.unitPair 3 4),.stop (.unitPair 0 4),.stop (.collision 516),.stop (.unitPair 1 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.unitPair 3 4),.stop (.unitPair 0 4),.stop (.collision 537),.stop (.unitPair 1 4),.stop (.unitPair 3 4),.stop (.unitPair 0 4),.stop (.unitPair 3 4),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5),.stop (.unitPair 3 5),.stop (.unitPair 1 5),.stop (.collision 98881),.stop (.unitPair 2 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.unitPair 3 4),.stop (.unitPair 0 4),.stop (.unitPair 3 4),.stop (.unitPair 1 4),.branch [.stop (.unitPair 2 5),.stop (.unitPair 3 5),.stop (.unitPair 0 5)],.stop (.unitPair 2 4),.stop (.unitPair 3 4),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,96] 97 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 523),.stop (.unitPair 0 4),.stop (.collision 8832),.stop (.unitPair 0 4),.stop (.collision 537),.stop (.unitPair 1 4),.stop (.collision 544),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 0 4),.branch [.stop (.unitPair 1 5),.stop (.collision 8784),.stop (.unitPair 0 5),.stop (.collision 5249),.stop (.unitPair 1 5),.stop (.collision 5256),.stop (.unitPair 2 5),.stop (.collision 102409),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.collision 8216),.stop (.unitPair 0 4),.stop (.collision 1153),.stop (.unitPair 1 4),.stop (.collision 1160),.stop (.unitPair 2 4),.stop (.collision 12297),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,97] 98 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,98] 99 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,99] 100 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,100] 101 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,101] 102 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,102] 103 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,103] 104 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,104] 105 (.stop (.collision 25)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,105] 106 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,106] 107 (.stop (.collision 32)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,107] 108 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,108] 109 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 12),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.stop (.collision 26),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,109] 110 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,110] 111 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 26),.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,111] 112 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,112] 113 (.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,113] 114 (.stop (.unitPair 0 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,114] 115 (.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 2 4),.stop (.collision 12353),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,115] 116 (.stop (.unitPair 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,116] 117 (.branch [.stop (.unitPair 2 4),.stop (.collision 12360),.stop (.unitPair 0 4)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,117] 118 (.stop (.unitPair 2 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,118] 119 (.stop (.collision 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 3 [0,2,20,119] 120 (.stop (.unitPair 0 3)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

import MinModulus.SevenModOneTwenty.BlockNonunit295
import MinModulus.SevenModOneTwenty.BlockNonunit296
import MinModulus.SevenModOneTwenty.BlockNonunit299
import MinModulus.SevenModOneTwenty.BlockNonunit300
import MinModulus.SevenModOneTwenty.BlockNonunit301
import MinModulus.SevenModOneTwenty.BlockNonunit302
import MinModulus.SevenModOneTwenty.BlockNonunit303
import MinModulus.SevenModOneTwenty.BlockNonunit304
import MinModulus.SevenModOneTwenty.BlockNonunit305
import MinModulus.SevenModOneTwenty.BlockNonunit306
import MinModulus.SevenModOneTwenty.BlockNonunit307
import MinModulus.SevenModOneTwenty.BlockNonunit308
import MinModulus.SevenModOneTwenty.BlockNonunit309
import MinModulus.SevenModOneTwenty.BlockNonunit310
import MinModulus.SevenModOneTwenty.BlockNonunit311
import MinModulus.SevenModOneTwenty.BlockNonunit312
import MinModulus.SevenModOneTwenty.NodeNonunit2_10
import MinModulus.SevenModOneTwenty.NodeNonunit2_12
import MinModulus.SevenModOneTwenty.NodeNonunit2_14
import MinModulus.SevenModOneTwenty.NodeNonunit2_16
import MinModulus.SevenModOneTwenty.NodeNonunit2_18
import MinModulus.SevenModOneTwenty.NodeNonunit2_20
import MinModulus.SevenModOneTwenty.NodeNonunit2_22
import MinModulus.SevenModOneTwenty.NodeNonunit2_24
import MinModulus.SevenModOneTwenty.NodeNonunit2_26
import MinModulus.SevenModOneTwenty.NodeNonunit2_30
import MinModulus.SevenModOneTwenty.NodeNonunit2_32
import MinModulus.SevenModOneTwenty.NodeNonunit2_5
import MinModulus.SevenModOneTwenty.NodeNonunit2_6
import MinModulus.SevenModOneTwenty.NodeNonunit2_8

namespace MinModulus.PrefixCertificate.Seven120

theorem nonunit_2_closed : ClosedMinimalPrefix false 120 2 5 [0,2] 3 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,3] 4 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,4] 5 (.stop (.collision 24)) (by decide +kernel))
  · exact nonunit_2_5_closed
  · exact nonunit_2_6_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,7] 8 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_8_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,9] 10 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_2_10_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,11] 12 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_12_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,13] 14 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_14_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,15] 16 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_2_16_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,17] 18 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_18_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,19] 20 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_20_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,21] 22 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_2_22_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,23] 24 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_24_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,25] 26 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_2_26_closed
  · exact nonunit_2_27_closed
  · exact nonunit_2_28_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,29] 30 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_30_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,31] 32 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_32_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,33] 34 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_2_34_closed
  · exact nonunit_2_35_closed
  · exact nonunit_2_36_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,37] 38 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_38_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,39] 40 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_2_40_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,41] 42 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_42_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,43] 44 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_44_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,45] 46 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_2_46_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,47] 48 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_48_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,49] 50 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_50_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,51] 52 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_2_52_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,53] 54 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_54_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,55] 56 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_2_56_closed
  · exact nonunit_2_57_closed
  · exact nonunit_2_58_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,59] 60 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_60_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,61] 62 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_62_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,63] 64 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_2_64_closed
  · exact nonunit_2_65_closed
  · exact nonunit_2_66_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,67] 68 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_68_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,69] 70 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_2_70_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,71] 72 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_72_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,73] 74 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_74_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,75] 76 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_2_76_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,77] 78 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_78_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,79] 80 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_80_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,81] 82 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_2_82_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,83] 84 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_84_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,85] 86 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_2_86_closed
  · exact nonunit_2_87_closed
  · exact nonunit_2_88_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,89] 90 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_90_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,91] 92 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_92_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,93] 94 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_2_94_closed
  · exact nonunit_2_95_closed
  · exact nonunit_2_96_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,97] 98 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_2_98_closed
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,99] 100 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,100] 101 (.branch [.stop (.unitPair 0 3),.stop (.collision 144),.stop (.unitPair 0 3),.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 1545),.stop (.unitPair 0 4),.stop (.collision 12808),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.unitPair 0 4),.stop (.collision 16896),.stop (.unitPair 1 4),.stop (.collision 9224),.stop (.unitPair 2 4),.stop (.collision 9217),.stop (.unitPair 0 4)],.stop (.unitPair 1 3),.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 12808),.stop (.unitPair 1 4),.stop (.collision 1545),.stop (.unitPair 0 4),.stop (.collision 9224),.stop (.unitPair 1 4),.stop (.collision 9217),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)],.stop (.unitPair 0 3),.branch [.stop (.unitPair 0 4),.stop (.collision 12808),.stop (.unitPair 1 4),.stop (.collision 9224),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.stop (.collision 1545),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)],.stop (.unitPair 0 3),.stop (.collision 1544),.stop (.unitPair 1 3),.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)],.stop (.unitPair 0 3),.stop (.collision 2048),.stop (.unitPair 1 3),.branch [.stop (.unitPair 2 4),.stop (.collision 12360),.stop (.unitPair 0 4)],.stop (.unitPair 2 3),.stop (.collision 67),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,101] 102 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,102] 103 (.branch [.stop (.unitPair 0 3),.stop (.collision 144),.stop (.unitPair 1 3),.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 1545),.stop (.unitPair 1 4),.stop (.collision 12801),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 1 4),.stop (.collision 9224),.stop (.unitPair 3 4),.stop (.collision 9217),.stop (.unitPair 0 4)],.stop (.unitPair 0 3),.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 12801),.stop (.unitPair 0 4),.stop (.collision 9224),.stop (.unitPair 1 4),.stop (.collision 9217),.branch [.stop (.unitPair 4 5),.stop (.unitPair 0 5)],.stop (.collision 579),.stop (.unitPair 0 4)],.stop (.unitPair 0 3),.branch [.stop (.unitPair 1 4),.stop (.collision 9224),.stop (.unitPair 0 4),.stop (.collision 9217),.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 3 4),.stop (.collision 1545),.stop (.unitPair 0 4)],.stop (.unitPair 1 3),.stop (.collision 1537),.stop (.unitPair 0 3),.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.collision 12360),.stop (.collision 12353),.stop (.unitPair 0 4)],.stop (.unitPair 1 3),.branch [.stop (.unitPair 3 4),.stop (.collision 12360),.stop (.unitPair 0 4)],.branch [.stop (.unitPair 3 4),.stop (.unitPair 0 4)],.stop (.collision 67),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,103] 104 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,104] 105 (.branch [.stop (.unitPair 1 3),.stop (.collision 144),.stop (.unitPair 0 3),.branch [.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.collision 12808),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 1 4),.stop (.collision 9224),.stop (.unitPair 2 4),.stop (.collision 9217),.stop (.unitPair 0 4)],.stop (.unitPair 0 3),.branch [.stop (.unitPair 1 4),.stop (.collision 12808),.stop (.unitPair 0 4),.stop (.collision 9224),.stop (.unitPair 1 4),.stop (.collision 9217),.stop (.unitPair 2 4),.stop (.collision 579),.stop (.unitPair 0 4)],.stop (.unitPair 1 3),.stop (.collision 1544),.stop (.unitPair 0 3),.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 2 4),.stop (.collision 12353),.stop (.unitPair 0 4)],.stop (.unitPair 1 3),.branch [.stop (.unitPair 2 4),.stop (.collision 12360),.stop (.unitPair 0 4)],.stop (.unitPair 2 3),.stop (.collision 67),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,105] 106 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,106] 107 (.branch [.stop (.unitPair 0 3),.stop (.collision 144),.stop (.unitPair 0 3),.branch [.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.collision 12801),.stop (.unitPair 1 4),.stop (.collision 9224),.stop (.unitPair 2 4),.stop (.collision 9217),.stop (.unitPair 0 4)],.stop (.unitPair 1 3),.branch [.stop (.unitPair 0 4),.stop (.collision 9224),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.unitPair 2 4),.stop (.collision 1545),.stop (.unitPair 0 4)],.stop (.unitPair 0 3),.stop (.collision 1537),.stop (.unitPair 1 3),.stop (.collision 2048),.stop (.unitPair 2 3),.stop (.collision 67),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,107] 108 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,108] 109 (.branch [.stop (.unitPair 0 3),.stop (.collision 144),.stop (.unitPair 1 3),.branch [.stop (.unitPair 0 4),.stop (.collision 12808),.stop (.unitPair 1 4),.stop (.collision 9224),.stop (.collision 12353),.stop (.collision 9217),.stop (.unitPair 0 4)],.stop (.unitPair 0 3),.stop (.collision 1544),.stop (.unitPair 1 3),.branch [.stop (.unitPair 3 4),.stop (.collision 12360),.stop (.unitPair 0 4)],.branch [.stop (.unitPair 3 4),.stop (.unitPair 0 4)],.stop (.collision 67),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,109] 110 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,110] 111 (.branch [.stop (.unitPair 1 3),.stop (.collision 144),.stop (.unitPair 0 3),.branch [.stop (.unitPair 1 4),.stop (.collision 9224),.stop (.unitPair 2 4),.stop (.collision 9217),.stop (.unitPair 0 4)],.stop (.unitPair 1 3),.stop (.collision 1537),.stop (.unitPair 2 3),.stop (.collision 67),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,111] 112 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,112] 113 (.branch [.stop (.unitPair 0 3),.stop (.collision 144),.stop (.unitPair 1 3),.stop (.collision 1544),.stop (.collision 1537),.stop (.collision 67),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,113] 114 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,114] 115 (.branch [.stop (.unitPair 1 3),.stop (.collision 144),.stop (.collision 1544),.stop (.collision 1537),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,115] 116 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,116] 117 (.branch [.stop (.unitPair 2 3),.stop (.collision 1544),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,117] 118 (.branch [.stop (.unitPair 2 3),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,118] 119 (.stop (.collision 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 2 4 [0,2,119] 120 (.stop (.unitPair 0 2)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

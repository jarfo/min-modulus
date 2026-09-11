import MinModulus.SevenModOneTwenty.BlockNonunit313
import MinModulus.SevenModOneTwenty.BlockNonunit314
import MinModulus.SevenModOneTwenty.BlockNonunit315
import MinModulus.SevenModOneTwenty.BlockNonunit316
import MinModulus.SevenModOneTwenty.BlockNonunit317
import MinModulus.SevenModOneTwenty.BlockNonunit318
import MinModulus.SevenModOneTwenty.BlockNonunit319
import MinModulus.SevenModOneTwenty.BlockNonunit320

namespace MinModulus.PrefixCertificate.Seven120

theorem nonunit_3_closed : ClosedMinimalPrefix false 120 3 5 [0,3] 4 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,4] 5 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,5] 6 (.stop (.pair 1 2 1 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,6] 7 (.stop (.collision 24)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,7] 8 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_3_8_closed
  · exact nonunit_3_9_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,10] 11 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,11] 12 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_3_12_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,13] 14 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,14] 15 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_3_15_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,16] 17 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,17] 18 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_3_18_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,19] 20 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,20] 21 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_3_21_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,22] 23 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,23] 24 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_3_24_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,25] 26 (.stop (.pair 1 2 11 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,26] 27 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_3_27_closed
  · exact nonunit_3_28_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,29] 30 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_3_30_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,31] 32 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,32] 33 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_3_33_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,34] 35 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_3_35_closed
  · exact nonunit_3_36_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,37] 38 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,38] 39 (.stop (.pair 0 2 19 19)) (by decide +kernel))
  · exact nonunit_3_39_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,40] 41 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,41] 42 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_3_42_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,43] 44 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,44] 45 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_3_45_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,46] 47 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,47] 48 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_3_48_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,49] 50 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,50] 51 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_3_51_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,52] 53 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,53] 54 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_3_54_closed
  · exact nonunit_3_55_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,56] 57 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_3_57_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,58] 59 (.stop (.pair 0 2 29 29)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,59] 60 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_3_60_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,61] 62 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,62] 63 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_3_63_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,64] 65 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,65] 66 (.stop (.pair 1 2 31 31)) (by decide +kernel))
  · exact nonunit_3_66_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,67] 68 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_3_68_closed
  · exact nonunit_3_69_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,70] 71 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,71] 72 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_3_72_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,73] 74 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,74] 75 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_3_75_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,76] 77 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,77] 78 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_3_78_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,79] 80 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,80] 81 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_3_81_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,82] 83 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,83] 84 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_3_84_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,85] 86 (.stop (.pair 1 2 41 41)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,86] 87 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_3_87_closed
  · exact nonunit_3_88_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,89] 90 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_3_90_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,91] 92 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,92] 93 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_3_93_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,94] 95 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_3_95_closed
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,96] 97 (.branch [.stop (.unitPair 0 3),.stop (.pair 0 3 49 49),.stop (.collision 144),.stop (.unitPair 1 3),.stop (.unitPair 0 3),.branch [.stop (.unitPair 0 4),.stop (.unitPair 1 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.unitPair 0 4),.stop (.collision 12808),.stop (.unitPair 0 4),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.unitPair 1 4),.stop (.unitPair 0 4),.stop (.collision 9224),.stop (.unitPair 2 4),.stop (.unitPair 1 4),.stop (.collision 9217),.stop (.pair 0 4 59 59),.stop (.unitPair 0 4)],.stop (.unitPair 0 3),.stop (.unitPair 1 3),.branch [.stop (.unitPair 1 4),.stop (.unitPair 0 4),.stop (.collision 12808),.stop (.unitPair 0 4),.stop (.unitPair 1 4),.stop (.collision 9224),.stop (.unitPair 1 4),.stop (.unitPair 0 4),.stop (.collision 9217),.stop (.unitPair 2 4),.stop (.unitPair 1 4),.stop (.collision 579),.stop (.unitPair 3 4),.stop (.unitPair 0 4)],.stop (.unitPair 1 3),.stop (.unitPair 0 3),.stop (.collision 1544),.stop (.unitPair 0 3),.stop (.unitPair 1 3),.branch [.stop (.unitPair 1 4),.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 2 4),.stop (.unitPair 1 4),.stop (.collision 12353),.stop (.unitPair 3 4),.stop (.unitPair 0 4)],.stop (.unitPair 1 3),.stop (.unitPair 0 3),.branch [.stop (.unitPair 2 4),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.pair 0 4 59 59),.stop (.unitPair 0 4)],.stop (.unitPair 2 3),.stop (.unitPair 1 3),.stop (.collision 67),.stop (.pair 0 3 59 59),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,97] 98 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,98] 99 (.stop (.pair 0 2 49 49)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,99] 100 (.branch [.stop (.unitPair 1 3),.stop (.unitPair 0 3),.stop (.collision 144),.stop (.unitPair 0 3),.stop (.unitPair 1 3),.branch [.stop (.unitPair 1 4),.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 0 4),.stop (.unitPair 1 4),.stop (.collision 12801),.stop (.unitPair 1 4),.stop (.unitPair 0 4),.stop (.collision 9224),.branch [.stop (.unitPair 1 5),.stop (.pair 4 5 1 1),.stop (.unitPair 2 5),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.collision 9217),.stop (.unitPair 2 4),.stop (.unitPair 0 4)],.stop (.unitPair 1 3),.stop (.unitPair 0 3),.branch [.stop (.unitPair 0 4),.stop (.unitPair 1 4),.stop (.collision 9224),.stop (.unitPair 1 4),.stop (.unitPair 0 4),.stop (.collision 12360),.stop (.unitPair 3 4),.stop (.unitPair 1 4),.stop (.collision 1545),.stop (.unitPair 2 4),.stop (.unitPair 0 4)],.stop (.unitPair 0 3),.stop (.unitPair 1 3),.stop (.collision 1537),.stop (.unitPair 1 3),.stop (.unitPair 0 3),.stop (.collision 2048),.branch [.stop (.unitPair 1 4),.stop (.pair 3 4 1 1),.stop (.unitPair 2 4),.stop (.unitPair 0 4)],.stop (.unitPair 1 3),.stop (.collision 67),.stop (.unitPair 2 3),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,100] 101 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,101] 102 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,102] 103 (.branch [.stop (.unitPair 0 3),.stop (.unitPair 1 3),.stop (.collision 144),.stop (.unitPair 1 3),.stop (.unitPair 0 3),.branch [.stop (.unitPair 0 4),.stop (.unitPair 1 4),.stop (.collision 12808),.stop (.unitPair 1 4),.stop (.unitPair 0 4),.stop (.collision 9224),.stop (.unitPair 2 4),.stop (.unitPair 1 4),.stop (.collision 9217),.stop (.pair 0 4 59 59),.stop (.unitPair 0 4)],.stop (.unitPair 0 3),.stop (.unitPair 1 3),.stop (.collision 1544),.stop (.unitPair 1 3),.stop (.unitPair 0 3),.branch [.stop (.unitPair 2 4),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.pair 0 4 59 59),.stop (.unitPair 0 4)],.stop (.unitPair 2 3),.stop (.unitPair 1 3),.stop (.collision 67),.stop (.pair 0 3 59 59),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,103] 104 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,104] 105 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,105] 106 (.branch [.stop (.unitPair 1 3),.stop (.unitPair 0 3),.stop (.collision 144),.stop (.unitPair 0 3),.stop (.unitPair 1 3),.branch [.stop (.unitPair 1 4),.stop (.unitPair 0 4),.stop (.collision 9224),.branch [.stop (.unitPair 1 5),.stop (.pair 4 5 1 1),.stop (.unitPair 2 5),.stop (.unitPair 0 5)],.stop (.unitPair 1 4),.stop (.collision 9217),.stop (.unitPair 2 4),.stop (.unitPair 0 4)],.stop (.unitPair 1 3),.stop (.unitPair 0 3),.stop (.collision 1537),.branch [.stop (.unitPair 1 4),.stop (.pair 3 4 1 1),.stop (.unitPair 2 4),.stop (.unitPair 0 4)],.stop (.unitPair 1 3),.stop (.collision 67),.stop (.unitPair 2 3),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,106] 107 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,107] 108 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,108] 109 (.branch [.stop (.unitPair 0 3),.stop (.unitPair 1 3),.stop (.collision 144),.stop (.unitPair 1 3),.stop (.unitPair 0 3),.stop (.collision 1544),.stop (.unitPair 2 3),.stop (.unitPair 1 3),.stop (.collision 67),.stop (.pair 0 3 59 59),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,109] 110 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,110] 111 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,111] 112 (.branch [.stop (.unitPair 1 3),.stop (.unitPair 0 3),.stop (.collision 144),.branch [.stop (.unitPair 1 4),.stop (.pair 3 4 1 1),.stop (.unitPair 2 4),.stop (.unitPair 0 4)],.stop (.unitPair 1 3),.stop (.collision 1537),.stop (.unitPair 2 3),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,112] 113 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,113] 114 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,114] 115 (.branch [.stop (.unitPair 2 3),.stop (.unitPair 1 3),.stop (.collision 1544),.stop (.pair 0 3 59 59),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,115] 116 (.branch [.stop (.unitPair 1 3),.stop (.pair 2 3 1 1),.stop (.pair 0 3 59 59),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,116] 117 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,117] 118 (.stop (.collision 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,118] 119 (.stop (.pair 0 2 59 59)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 3 4 [0,3,119] 120 (.stop (.unitPair 0 2)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

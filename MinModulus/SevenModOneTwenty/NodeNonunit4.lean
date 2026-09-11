import MinModulus.SevenModOneTwenty.BlockNonunit320
import MinModulus.SevenModOneTwenty.BlockNonunit321
import MinModulus.SevenModOneTwenty.BlockNonunit322

namespace MinModulus.PrefixCertificate.Seven120

theorem nonunit_4_closed : ClosedMinimalPrefix false 120 4 5 [0,4] 5 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,5] 6 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,6] 7 (.stop (.pair 1 2 1 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,7] 8 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,8] 9 (.stop (.collision 24)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,9] 10 (.stop (.pair 0 2 67 43)) (by decide +kernel))
  · exact nonunit_4_10_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,11] 12 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_4_12_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,13] 14 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,14] 15 (.stop (.pair 0 2 43 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,15] 16 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_4_16_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,17] 18 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,18] 19 (.stop (.pair 1 2 43 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,19] 20 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_4_20_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,21] 22 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,22] 23 (.stop (.pair 0 2 11 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,23] 24 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_4_24_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,25] 26 (.stop (.pair 1 2 23 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,26] 27 (.stop (.pair 0 2 37 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,27] 28 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_4_28_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,29] 30 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,30] 31 (.stop (.pair 1 2 37 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,31] 32 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_4_32_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,33] 34 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,34] 35 (.stop (.pair 0 2 53 77)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,35] 36 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_4_36_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,37] 38 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,38] 39 (.stop (.pair 0 2 19 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,39] 40 (.stop (.pair 0 2 37 13)) (by decide +kernel))
  · exact nonunit_4_40_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,41] 42 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,42] 43 (.stop (.pair 1 2 19 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,43] 44 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_4_44_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,45] 46 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,46] 47 (.stop (.pair 0 2 47 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,47] 48 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_4_48_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,49] 50 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,50] 51 (.stop (.pair 1 2 47 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,51] 52 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_4_52_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,53] 54 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_4_54_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,55] 56 (.stop (.pair 1 2 73 97)) (by decide +kernel))
  · exact nonunit_4_56_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,57] 58 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,58] 59 (.stop (.pair 0 2 29 29)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,59] 60 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_4_60_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,61] 62 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,62] 63 (.stop (.pair 0 2 31 31)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,63] 64 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_4_64_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,65] 66 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,66] 67 (.stop (.pair 1 2 31 31)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,67] 68 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_4_68_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,69] 70 (.stop (.pair 0 2 7 103)) (by decide +kernel))
  · exact nonunit_4_70_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,71] 72 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_4_72_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,73] 74 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,74] 75 (.stop (.pair 0 2 13 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,75] 76 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_4_76_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,77] 78 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,78] 79 (.stop (.pair 1 2 13 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,79] 80 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_4_80_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,81] 82 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,82] 83 (.stop (.pair 0 2 41 41)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,83] 84 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact nonunit_4_84_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,85] 86 (.stop (.pair 1 2 43 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,86] 87 (.stop (.pair 0 2 7 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,87] 88 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact nonunit_4_88_closed
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,89] 90 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,90] 91 (.stop (.pair 1 2 7 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,91] 92 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,92] 93 (.branch [.stop (.unitPair 1 3),.stop (.pair 0 3 23 47),.stop (.unitPair 1 3),.stop (.collision 144),.stop (.unitPair 0 3),.stop (.pair 0 3 49 49),.stop (.unitPair 2 3),.branch [.stop (.unitPair 0 4),.stop (.pair 1 4 49 49),.stop (.unitPair 0 4),.stop (.collision 1104),.stop (.unitPair 1 4),.stop (.pair 0 4 17 113),.stop (.unitPair 0 4),.stop (.collision 12801),.stop (.unitPair 0 4),.stop (.pair 1 4 17 113),.stop (.unitPair 1 4),.stop (.collision 9224),.stop (.unitPair 0 4),.stop (.pair 2 4 11 11),.stop (.unitPair 2 4),.stop (.collision 9217),.stop (.unitPair 1 4),.stop (.pair 0 4 59 59),.stop (.unitPair 0 4)],.stop (.unitPair 0 3),.stop (.pair 1 3 49 49),.stop (.unitPair 0 3),.branch [.stop (.unitPair 1 4),.stop (.pair 0 4 17 113),.stop (.unitPair 0 4),.stop (.collision 9224),.stop (.unitPair 0 4),.stop (.pair 1 4 17 113),.stop (.unitPair 1 4),.stop (.collision 12360),.stop (.unitPair 0 4),.stop (.pair 2 4 11 11),.stop (.unitPair 2 4),.stop (.collision 1545),.stop (.unitPair 1 4),.stop (.pair 0 4 59 59),.stop (.unitPair 0 4)],.stop (.unitPair 1 3),.stop (.pair 0 3 17 113),.stop (.unitPair 0 3),.stop (.collision 1537),.stop (.unitPair 0 3),.stop (.pair 1 3 17 113),.stop (.unitPair 1 3),.stop (.collision 2048),.stop (.unitPair 0 3),.stop (.pair 2 3 11 11),.stop (.unitPair 2 3),.stop (.collision 67),.stop (.unitPair 1 3),.stop (.pair 0 3 59 59),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,93] 94 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,94] 95 (.stop (.pair 0 2 23 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,95] 96 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,96] 97 (.branch [.stop (.unitPair 0 3),.stop (.pair 0 3 49 49),.stop (.pair 0 3 17 113),.stop (.collision 144),.stop (.unitPair 0 3),.stop (.pair 1 3 49 49),.stop (.unitPair 0 3),.branch [.stop (.unitPair 1 4),.stop (.pair 0 4 17 113),.stop (.unitPair 0 4),.stop (.collision 12808),.stop (.unitPair 0 4),.stop (.pair 1 4 17 113),.stop (.unitPair 1 4),.stop (.collision 9224),.stop (.unitPair 0 4),.stop (.collision 12353),.stop (.unitPair 2 4),.stop (.collision 9217),.stop (.unitPair 1 4),.stop (.pair 0 4 59 59),.stop (.unitPair 0 4)],.stop (.unitPair 1 3),.stop (.pair 0 3 17 113),.stop (.unitPair 0 3),.stop (.collision 1544),.stop (.unitPair 0 3),.stop (.pair 1 3 17 113),.stop (.unitPair 1 3),.branch [.stop (.unitPair 0 4),.stop (.pair 3 4 1 1),.stop (.unitPair 2 4),.stop (.collision 12360),.stop (.unitPair 1 4),.stop (.pair 0 4 59 59),.stop (.unitPair 0 4)],.stop (.unitPair 0 3),.branch [.stop (.unitPair 2 4),.stop (.pair 3 4 1 1),.stop (.unitPair 1 4),.stop (.pair 0 4 59 59),.stop (.unitPair 0 4)],.stop (.unitPair 2 3),.stop (.collision 67),.stop (.unitPair 1 3),.stop (.pair 0 3 59 59),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,97] 98 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,98] 99 (.stop (.pair 0 2 49 49)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,99] 100 (.stop (.pair 0 2 17 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,100] 101 (.branch [.stop (.unitPair 0 3),.stop (.pair 1 3 49 49),.stop (.unitPair 0 3),.stop (.collision 144),.stop (.unitPair 1 3),.stop (.pair 0 3 17 113),.stop (.unitPair 0 3),.branch [.stop (.unitPair 0 4),.stop (.pair 1 4 17 113),.stop (.unitPair 1 4),.stop (.collision 9224),.stop (.unitPair 0 4),.stop (.pair 2 4 43 67),.stop (.unitPair 3 4),.stop (.collision 9217),.stop (.unitPair 1 4),.stop (.pair 0 4 59 59),.stop (.unitPair 0 4)],.stop (.unitPair 0 3),.stop (.pair 1 3 17 113),.stop (.unitPair 1 3),.stop (.collision 1537),.stop (.unitPair 0 3),.stop (.pair 2 3 43 67),.stop (.pair 1 3 13 37),.stop (.collision 67),.stop (.unitPair 1 3),.stop (.pair 0 3 59 59),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,101] 102 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,102] 103 (.stop (.pair 1 2 49 49)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,103] 104 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,104] 105 (.branch [.stop (.unitPair 1 3),.stop (.pair 0 3 17 113),.stop (.unitPair 0 3),.stop (.collision 144),.stop (.unitPair 0 3),.stop (.pair 1 3 17 113),.stop (.unitPair 1 3),.stop (.collision 1544),.stop (.unitPair 0 3),.stop (.collision 1537),.stop (.unitPair 2 3),.stop (.collision 67),.stop (.unitPair 1 3),.stop (.pair 0 3 59 59),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,105] 106 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,106] 107 (.stop (.pair 0 2 17 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,107] 108 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,108] 109 (.branch [.stop (.unitPair 0 3),.stop (.pair 1 3 17 113),.stop (.unitPair 1 3),.stop (.collision 144),.stop (.unitPair 0 3),.stop (.collision 1544),.stop (.unitPair 2 3),.stop (.collision 1537),.stop (.unitPair 1 3),.stop (.pair 0 3 59 59),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,109] 110 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,110] 111 (.stop (.pair 1 2 17 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,111] 112 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,112] 113 (.branch [.stop (.unitPair 0 3),.stop (.pair 2 3 1 1),.stop (.pair 1 3 13 37),.stop (.collision 1544),.stop (.unitPair 1 3),.stop (.pair 0 3 59 59),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,113] 114 (.stop (.unitPair 0 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,114] 115 (.branch [.stop (.unitPair 2 3),.stop (.pair 2 3 1 1),.stop (.unitPair 1 3),.stop (.pair 0 3 59 59),.stop (.unitPair 0 3)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,115] 116 (.stop (.pair 1 2 13 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,116] 117 (.stop (.collision 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,117] 118 (.stop (.unitPair 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,118] 119 (.stop (.pair 0 2 59 59)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 4 4 [0,4,119] 120 (.stop (.unitPair 0 2)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

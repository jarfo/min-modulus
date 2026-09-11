import MinModulus.SevenModOneTwenty.BlockUnit249
import MinModulus.SevenModOneTwenty.BlockUnit250
import MinModulus.SevenModOneTwenty.BlockUnit251
import MinModulus.SevenModOneTwenty.BlockUnit252
import MinModulus.SevenModOneTwenty.BlockUnit253

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_22_closed : ClosedMinimalPrefix true 120 22 4 [0,1,22] 23 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,23] 24 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_22_24_closed
  · exact unit_22_25_closed
  · exact unit_22_26_closed
  · exact unit_22_27_closed
  · exact unit_22_28_closed
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,29] 30 (.stop (.third 2 3 0 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,30] 31 (.stop (.third 1 3 2 29)) (by decide +kernel))
  · exact unit_22_31_closed
  · exact unit_22_32_closed
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,33] 34 (.stop (.third 2 3 1 11)) (by decide +kernel))
  · exact unit_22_34_closed
  · exact unit_22_35_closed
  · exact unit_22_36_closed
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,37] 38 (.stop (.third 0 3 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,38] 39 (.stop (.third 3 1 0 107)) (by decide +kernel))
  · exact unit_22_39_closed
  · exact unit_22_40_closed
  · exact unit_22_41_closed
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,42] 43 (.stop (.third 1 3 2 41)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,43] 44 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,44] 45 (.stop (.collision 200)) (by decide +kernel))
  · exact unit_22_45_closed
  · exact unit_22_46_closed
  · exact unit_22_47_closed
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,48] 49 (.stop (.third 1 3 2 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,49] 50 (.stop (.third 3 0 2 71)) (by decide +kernel))
  · exact unit_22_50_closed
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,51] 52 (.stop (.third 3 2 1 91)) (by decide +kernel))
  · exact unit_22_52_closed
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,53] 54 (.stop (.third 0 3 2 77)) (by decide +kernel))
  · exact unit_22_54_closed
  · exact unit_22_55_closed
  · exact unit_22_56_closed
  · exact unit_22_57_closed
  · exact unit_22_58_closed
  · exact unit_22_59_closed
  · exact unit_22_60_closed
  · exact unit_22_61_closed
  · exact unit_22_62_closed
  · exact unit_22_63_closed
  · exact unit_22_64_closed
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,65] 66 (.stop (.collision 256)) (by decide +kernel))
  · exact unit_22_66_closed
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,67] 68 (.stop (.third 3 0 2 77)) (by decide +kernel))
  · exact unit_22_68_closed
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,69] 70 (.stop (.third 3 2 1 97)) (by decide +kernel))
  · exact unit_22_70_closed
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,71] 72 (.stop (.third 0 3 2 71)) (by decide +kernel))
  · exact unit_22_72_closed
  · exact unit_22_73_closed
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,74] 75 (.stop (.third 3 1 2 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,75] 76 (.stop (.third 3 2 0 43)) (by decide +kernel))
  · exact unit_22_76_closed
  · exact unit_22_77_closed
  · exact unit_22_78_closed
  · exact unit_22_79_closed
  · exact unit_22_80_closed
  · exact unit_22_81_closed
  · exact unit_22_82_closed
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,83] 84 (.stop (.third 3 0 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,84] 85 (.stop (.third 1 3 0 107)) (by decide +kernel))
  · exact unit_22_85_closed
  · exact unit_22_86_closed
  · exact unit_22_87_closed
  · exact unit_22_88_closed
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,89] 90 (.stop (.third 2 3 0 43)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,90] 91 (.branch [.stop (.collision 1104),.stop (.third 4 1 2 29),.stop (.third 4 2 0 49),.stop (.third 3 1 4 31),.stop (.third 2 4 1 97),.stop (.collision 264),.stop (.collision 516),.stop (.third 1 4 3 73),.stop (.third 2 4 3 53),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,91] 92 (.branch [.stop (.third 4 1 2 29),.stop (.third 4 2 0 49),.stop (.collision 257),.stop (.third 0 3 4 91),.branch [.stop (.third 5 4 3 119),.stop (.third 5 3 0 17),.stop (.third 0 3 5 91),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 3 5 91),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 3 5 91),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 3 5 91),.stop (.third 1 0 5 119),.stop (.third 0 5 1 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 516),.stop (.third 4 3 0 17),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,92] 93 (.stop (.third 3 1 2 29)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,93] 94 (.stop (.third 3 2 0 49)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,94] 95 (.branch [.stop (.third 2 4 1 97),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 0 5 3 101),.stop (.third 1 0 5 119),.stop (.third 0 5 1 7),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 3 83),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 1 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 516),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 0 4 3 101),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 83),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,95] 96 (.stop (.third 2 3 1 97)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,96] 97 (.branch [.stop (.collision 1104),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,97] 98 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,98] 99 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,99] 100 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,100] 101 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,101] 102 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,102] 103 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,104] 105 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,105] 106 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,106] 107 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,107] 108 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,108] 109 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,109] 110 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,110] 111 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,111] 112 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,112] 113 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,113] 114 (.stop (.third 0 3 1 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,114] 115 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 22 3 [0,1,22,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

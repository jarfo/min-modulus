import MinModulus.SevenModOneTwenty.BlockUnit259
import MinModulus.SevenModOneTwenty.BlockUnit260
import MinModulus.SevenModOneTwenty.BlockUnit261

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_26_closed : ClosedMinimalPrefix true 120 26 4 [0,1,26] 27 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,27] 28 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_26_28_closed
  · exact unit_26_29_closed
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,30] 31 (.stop (.third 1 3 2 29)) (by decide +kernel))
  · exact unit_26_31_closed
  · exact unit_26_32_closed
  · exact unit_26_33_closed
  · exact unit_26_34_closed
  · exact unit_26_35_closed
  · exact unit_26_36_closed
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,37] 38 (.stop (.third 0 3 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,38] 39 (.stop (.third 3 1 0 107)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,39] 40 (.stop (.third 3 2 0 83)) (by decide +kernel))
  · exact unit_26_40_closed
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,41] 42 (.stop (.third 3 0 2 79)) (by decide +kernel))
  · exact unit_26_42_closed
  · exact unit_26_43_closed
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,44] 45 (.stop (.third 3 1 2 53)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,45] 46 (.stop (.third 2 3 1 19)) (by decide +kernel))
  · exact unit_26_46_closed
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,47] 48 (.stop (.third 0 3 1 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,48] 49 (.stop (.third 3 1 0 97)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,49] 50 (.stop (.third 2 3 1 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,50] 51 (.stop (.third 1 3 2 49)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,51] 52 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,52] 53 (.stop (.collision 200)) (by decide +kernel))
  · exact unit_26_53_closed
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,54] 55 (.stop (.third 1 3 2 77)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,55] 56 (.stop (.third 3 2 1 91)) (by decide +kernel))
  · exact unit_26_56_closed
  · exact unit_26_57_closed
  · exact unit_26_58_closed
  · exact unit_26_59_closed
  · exact unit_26_60_closed
  · exact unit_26_61_closed
  · exact unit_26_62_closed
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,63] 64 (.stop (.third 2 3 0 13)) (by decide +kernel))
  · exact unit_26_64_closed
  · exact unit_26_65_closed
  · exact unit_26_66_closed
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,67] 68 (.stop (.third 2 3 0 41)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,68] 69 (.stop (.third 3 1 2 77)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,69] 70 (.stop (.third 2 3 1 67)) (by decide +kernel))
  · exact unit_26_70_closed
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,71] 72 (.branch [.stop (.collision 1104),.stop (.third 0 3 4 71),.stop (.third 1 4 0 97),.stop (.collision 9224),.stop (.third 3 0 4 49),.stop (.collision 768),.stop (.third 0 3 4 71),.stop (.third 0 4 2 79),.stop (.third 1 4 3 79),.stop (.third 3 0 4 49),.stop (.third 4 3 2 109),.stop (.third 0 3 4 71),.stop (.third 1 4 0 107),.stop (.third 2 4 3 59),.stop (.third 3 0 4 49),.stop (.third 4 2 3 59),.stop (.third 0 3 4 71),.stop (.collision 16896),.stop (.third 4 1 3 31),.stop (.third 3 0 4 49),.stop (.third 1 4 3 91),.stop (.third 0 3 4 71),.stop (.third 3 4 0 47),.stop (.third 0 3 4 71),.stop (.third 1 0 4 119),.stop (.third 0 4 3 73),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 71),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 0 3 4 71),.stop (.third 1 0 4 119),.stop (.third 0 4 3 83),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 71),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 0 3 4 71),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact unit_26_72_closed
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,73] 74 (.stop (.third 0 3 2 97)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,74] 75 (.stop (.third 1 3 0 97)) (by decide +kernel))
  · exact unit_26_75_closed
  · exact unit_26_76_closed
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,77] 78 (.stop (.collision 256)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,78] 79 (.stop (.third 1 3 2 53)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,79] 80 (.stop (.third 0 3 2 79)) (by decide +kernel))
  · exact unit_26_80_closed
  · exact unit_26_81_closed
  · exact unit_26_82_closed
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,83] 84 (.stop (.third 0 3 2 107)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,84] 85 (.stop (.third 1 3 0 107)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,85] 86 (.branch [.stop (.collision 1104),.stop (.third 3 2 4 61),.stop (.collision 208),.stop (.third 0 4 3 89),.stop (.collision 12416),.stop (.third 3 2 4 61),.stop (.third 3 4 0 103),.stop (.third 2 4 1 43),.stop (.collision 523),.stop (.third 3 2 4 61),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 109),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact unit_26_86_closed
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,87] 88 (.branch [.stop (.collision 1104),.stop (.third 2 3 4 61),.stop (.collision 13312),.stop (.third 2 3 4 61),.stop (.third 4 1 2 29),.stop (.third 2 3 4 61),.stop (.third 3 4 1 103),.stop (.third 2 3 4 61),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 83),.stop (.third 1 0 4 119),.stop (.third 0 4 3 109),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,88] 89 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.third 5 1 2 29),.stop (.third 2 5 1 43),.stop (.third 4 1 5 31),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 3 101),.stop (.third 1 0 5 119),.stop (.third 0 5 1 7),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 1 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 9728),.stop (.third 4 1 2 29),.stop (.third 2 4 1 43),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 101),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,89] 90 (.stop (.collision 2048)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,90] 91 (.branch [.stop (.collision 1104),.stop (.third 4 1 2 29),.stop (.third 2 4 1 43),.stop (.third 3 1 4 31),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,91] 92 (.branch [.stop (.third 4 1 2 29),.stop (.third 2 4 1 43),.stop (.collision 523),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,92] 93 (.stop (.third 3 1 2 29)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,93] 94 (.stop (.third 2 3 1 43)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,94] 95 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,95] 96 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,96] 97 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,97] 98 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,98] 99 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,99] 100 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,100] 101 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,101] 102 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,102] 103 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,104] 105 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,105] 106 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,106] 107 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,107] 108 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,108] 109 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,109] 110 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,110] 111 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,111] 112 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,112] 113 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,113] 114 (.stop (.third 0 3 1 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,114] 115 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 26 3 [0,1,26,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

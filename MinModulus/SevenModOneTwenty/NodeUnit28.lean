import MinModulus.SevenModOneTwenty.BlockUnit262
import MinModulus.SevenModOneTwenty.BlockUnit263
import MinModulus.SevenModOneTwenty.BlockUnit264

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_28_closed : ClosedMinimalPrefix true 120 28 4 [0,1,28] 29 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,29] 30 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_28_30_closed
  · exact unit_28_31_closed
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,32] 33 (.stop (.third 3 1 2 89)) (by decide +kernel))
  · exact unit_28_33_closed
  · exact unit_28_34_closed
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,35] 36 (.stop (.third 3 2 0 17)) (by decide +kernel))
  · exact unit_28_36_closed
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,37] 38 (.stop (.third 0 3 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,38] 39 (.stop (.third 3 1 0 107)) (by decide +kernel))
  · exact unit_28_39_closed
  · exact unit_28_40_closed
  · exact unit_28_41_closed
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,42] 43 (.stop (.third 1 3 2 41)) (by decide +kernel))
  · exact unit_28_43_closed
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,44] 45 (.stop (.third 1 3 2 67)) (by decide +kernel))
  · exact unit_28_45_closed
  · exact unit_28_46_closed
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,47] 48 (.stop (.third 0 3 1 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,48] 49 (.stop (.third 1 3 2 23)) (by decide +kernel))
  · exact unit_28_49_closed
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,50] 51 (.stop (.third 1 3 2 49)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,51] 52 (.stop (.third 2 3 0 47)) (by decide +kernel))
  · exact unit_28_52_closed
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,53] 54 (.stop (.third 3 0 2 43)) (by decide +kernel))
  · exact unit_28_54_closed
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,55] 56 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,56] 57 (.stop (.collision 200)) (by decide +kernel))
  · exact unit_28_57_closed
  · exact unit_28_58_closed
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,59] 60 (.stop (.third 2 3 1 31)) (by decide +kernel))
  · exact unit_28_60_closed
  · exact unit_28_61_closed
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,62] 63 (.branch [.stop (.collision 1104),.stop (.third 1 3 4 61),.stop (.third 2 4 1 13),.stop (.third 1 3 4 61),.stop (.third 0 4 2 43),.stop (.third 1 3 4 61),.stop (.third 4 3 0 17),.stop (.third 1 3 4 61),.stop (.third 4 2 1 53),.stop (.third 1 3 4 61),.stop (.third 0 4 3 97),.stop (.third 1 3 4 61),.stop (.third 3 4 1 37),.stop (.third 1 3 4 61),.stop (.third 4 2 1 71),.stop (.third 1 3 4 61),.stop (.third 4 0 3 41),.stop (.third 1 3 4 61),.stop (.third 2 4 0 77),.stop (.third 1 3 4 61),.stop (.third 4 0 1 13),.stop (.third 1 3 4 61),.stop (.third 3 4 1 47),.stop (.third 1 3 4 61),.stop (.collision 9217),.stop (.third 1 3 4 61),.stop (.third 4 0 3 31),.stop (.third 1 4 2 89),.stop (.third 0 4 3 91),.stop (.collision 523),.stop (.third 3 4 2 31),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 2 73),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 101),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact unit_28_63_closed
  · exact unit_28_64_closed
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,65] 66 (.stop (.third 2 3 1 13)) (by decide +kernel))
  · exact unit_28_66_closed
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,67] 68 (.stop (.third 0 3 2 43)) (by decide +kernel))
  · exact unit_28_68_closed
  · exact unit_28_69_closed
  · exact unit_28_70_closed
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,71] 72 (.stop (.third 3 2 1 53)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,72] 73 (.stop (.third 3 1 2 49)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,73] 74 (.stop (.third 3 0 1 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,74] 75 (.stop (.third 1 3 0 97)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,75] 76 (.stop (.third 3 2 1 97)) (by decide +kernel))
  · exact unit_28_76_closed
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,77] 78 (.stop (.third 3 2 1 71)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,78] 79 (.stop (.third 3 1 2 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,79] 80 (.branch [.stop (.collision 1104),.stop (.third 2 4 0 77),.stop (.third 3 0 4 41),.stop (.third 4 0 1 13),.stop (.third 1 4 0 107),.stop (.third 3 0 4 41),.stop (.third 3 4 0 103),.stop (.third 2 4 3 59),.stop (.third 3 0 4 41),.stop (.third 4 2 3 59),.stop (.third 1 4 2 89),.stop (.third 3 0 4 41),.stop (.third 1 4 3 91),.stop (.third 0 3 4 79),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 79),.stop (.third 0 4 2 73),.stop (.third 1 0 4 119),.stop (.third 0 3 4 79),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 79),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 0 3 4 79),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 79),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 79),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 0 3 4 79),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 79),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact unit_28_80_closed
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,81] 82 (.stop (.third 2 3 0 77)) (by decide +kernel))
  · exact unit_28_82_closed
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,83] 84 (.stop (.third 3 0 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,84] 85 (.stop (.third 1 3 0 107)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,85] 86 (.branch [.stop (.collision 1104),.stop (.third 2 4 3 59),.branch [.stop (.third 0 5 3 89),.stop (.third 1 5 2 89),.stop (.collision 12361),.stop (.third 3 5 0 103),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 2 73),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 4 101),.stop (.third 1 0 5 119),.stop (.third 0 5 1 7),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 3 109),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 1 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 0 4 3 89),.stop (.third 1 4 2 89),.stop (.collision 201),.stop (.third 3 4 0 103),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 2 73),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 109),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,86] 87 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 0 3 31),.stop (.third 1 5 2 89),.stop (.third 0 5 3 91),.stop (.third 5 1 4 29),.stop (.third 3 5 0 103),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 2 73),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 4 101),.stop (.third 1 0 5 119),.stop (.third 0 5 1 7),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 3 109),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 1 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 4 0 3 31),.stop (.third 1 4 2 89),.stop (.third 0 4 3 91),.stop (.collision 523),.stop (.third 3 4 0 103),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 2 73),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 109),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,87] 88 (.branch [.stop (.collision 1104),.stop (.third 3 2 4 61),.stop (.third 1 4 2 89),.stop (.third 3 2 4 61),.stop (.third 1 4 3 91),.stop (.third 3 2 4 61),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 2 73),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 101),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 83),.stop (.third 1 0 4 119),.stop (.third 0 4 3 109),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,88] 89 (.branch [.stop (.collision 1104),.stop (.third 1 4 2 89),.stop (.collision 516),.stop (.third 4 1 3 29),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 2 73),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 101),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,89] 90 (.branch [.stop (.third 1 4 2 89),.stop (.third 2 3 4 61),.stop (.collision 523),.stop (.third 2 3 4 61),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 89),.stop (.third 0 4 2 73),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 89),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 0 3 4 89),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 89),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 89),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 89),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,90] 91 (.stop (.third 1 3 2 89)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,91] 92 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,92] 93 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,93] 94 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,94] 95 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,95] 96 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,96] 97 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,97] 98 (.stop (.third 0 3 2 73)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,98] 99 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,99] 100 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,100] 101 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,101] 102 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,102] 103 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,104] 105 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,105] 106 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,106] 107 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,107] 108 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,108] 109 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,109] 110 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,110] 111 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,111] 112 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,112] 113 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,113] 114 (.stop (.third 0 3 1 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,114] 115 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 28 3 [0,1,28,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

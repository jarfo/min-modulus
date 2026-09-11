import MinModulus.SevenModOneTwenty.BlockUnit257
import MinModulus.SevenModOneTwenty.BlockUnit258
import MinModulus.SevenModOneTwenty.BlockUnit259

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_25_closed : ClosedMinimalPrefix true 120 25 4 [0,1,25] 26 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,26] 27 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_25_27_closed
  · exact unit_25_28_closed
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,29] 30 (.stop (.third 0 3 2 29)) (by decide +kernel))
  · exact unit_25_30_closed
  · exact unit_25_31_closed
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,32] 33 (.stop (.third 1 3 2 31)) (by decide +kernel))
  · exact unit_25_33_closed
  · exact unit_25_34_closed
  · exact unit_25_35_closed
  · exact unit_25_36_closed
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,37] 38 (.stop (.third 0 3 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,38] 39 (.stop (.third 3 1 0 107)) (by decide +kernel))
  · exact unit_25_39_closed
  · exact unit_25_40_closed
  · exact unit_25_41_closed
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,42] 43 (.stop (.third 1 3 2 41)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,43] 44 (.stop (.third 3 0 2 53)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,44] 45 (.stop (.third 2 3 0 19)) (by decide +kernel))
  · exact unit_25_45_closed
  · exact unit_25_46_closed
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,47] 48 (.stop (.third 0 3 1 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,48] 49 (.stop (.third 3 1 0 97)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,49] 50 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,50] 51 (.stop (.collision 200)) (by decide +kernel))
  · exact unit_25_51_closed
  · exact unit_25_52_closed
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,53] 54 (.stop (.third 0 3 2 77)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,54] 55 (.stop (.third 2 3 1 29)) (by decide +kernel))
  · exact unit_25_55_closed
  · exact unit_25_56_closed
  · exact unit_25_57_closed
  · exact unit_25_58_closed
  · exact unit_25_59_closed
  · exact unit_25_60_closed
  · exact unit_25_61_closed
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,62] 63 (.stop (.third 1 3 2 61)) (by decide +kernel))
  · exact unit_25_63_closed
  · exact unit_25_64_closed
  · exact unit_25_65_closed
  · exact unit_25_66_closed
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,67] 68 (.stop (.third 3 0 2 77)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,68] 69 (.stop (.third 2 3 0 67)) (by decide +kernel))
  · exact unit_25_69_closed
  · exact unit_25_70_closed
  · exact unit_25_71_closed
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,72] 73 (.stop (.third 1 3 2 71)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,73] 74 (.stop (.third 3 0 1 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,74] 75 (.stop (.third 1 3 0 97)) (by decide +kernel))
  · exact unit_25_75_closed
  · exact unit_25_76_closed
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,77] 78 (.stop (.third 0 3 2 53)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,78] 79 (.stop (.third 3 2 0 43)) (by decide +kernel))
  · exact unit_25_79_closed
  · exact unit_25_80_closed
  · exact unit_25_81_closed
  · exact unit_25_82_closed
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,83] 84 (.stop (.third 3 0 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,84] 85 (.stop (.third 1 3 0 107)) (by decide +kernel))
  · exact unit_25_85_closed
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,86] 87 (.branch [.stop (.collision 1104),.stop (.third 2 3 4 61),.branch [.stop (.third 1 5 3 89),.stop (.third 5 0 2 29),.stop (.third 1 5 2 91),.stop (.third 3 5 0 103),.stop (.third 2 3 5 61),.stop (.collision 4619),.stop (.third 0 4 5 89),.stop (.third 0 5 4 73),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 4 5 89),.stop (.third 0 5 2 101),.stop (.third 1 0 5 119),.stop (.third 0 5 1 7),.stop (.third 0 4 5 89),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 4 5 89),.stop (.third 0 5 3 109),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 4 5 89),.stop (.third 0 5 1 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 4 5 89),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 1 4 3 89),.stop (.third 4 0 2 29),.stop (.third 1 4 2 91),.stop (.third 3 4 0 103),.stop (.third 2 3 4 61),.stop (.collision 523),.stop (.third 2 3 4 61),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 2 101),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 109),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact unit_25_87_closed
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,88] 89 (.branch [.stop (.collision 1104),.stop (.collision 9728),.stop (.third 4 0 2 29),.stop (.third 1 4 2 91),.branch [.stop (.third 5 4 3 119),.stop (.third 5 3 2 17),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 2 101),.stop (.third 1 0 5 119),.stop (.third 0 5 1 7),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 1 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 516),.stop (.third 4 3 2 17),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 2 101),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,89] 90 (.branch [.stop (.collision 1104),.stop (.third 4 0 2 29),.stop (.third 1 4 2 91),.stop (.third 3 0 4 31),.stop (.collision 516),.stop (.collision 523),.stop (.third 0 3 4 89),.stop (.third 0 4 3 73),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 89),.stop (.third 0 4 2 101),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 0 3 4 89),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 89),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 89),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 89),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,90] 91 (.branch [.stop (.third 4 0 2 29),.stop (.third 1 4 2 91),.stop (.collision 12416),.stop (.third 3 1 4 31),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 2 101),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,91] 92 (.stop (.third 3 0 2 29)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,92] 93 (.stop (.third 1 3 2 91)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,93] 94 (.branch [.stop (.collision 1104),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 2 101),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,94] 95 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,95] 96 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,96] 97 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,97] 98 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,98] 99 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,99] 100 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,100] 101 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,101] 102 (.stop (.third 0 3 2 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,102] 103 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,104] 105 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,105] 106 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,106] 107 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,107] 108 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,108] 109 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,109] 110 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,110] 111 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,111] 112 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,112] 113 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,113] 114 (.stop (.third 0 3 1 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,114] 115 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 25 3 [0,1,25,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

import MinModulus.SevenModOneTwenty.BlockUnit244
import MinModulus.SevenModOneTwenty.BlockUnit245
import MinModulus.SevenModOneTwenty.BlockUnit246
import MinModulus.SevenModOneTwenty.BlockUnit247
import MinModulus.SevenModOneTwenty.BlockUnit248
import MinModulus.SevenModOneTwenty.BlockUnit249

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_21_closed : ClosedMinimalPrefix true 120 21 4 [0,1,21] 22 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,22] 23 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_21_23_closed
  · exact unit_21_24_closed
  · exact unit_21_25_closed
  · exact unit_21_26_closed
  · exact unit_21_27_closed
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,28] 29 (.stop (.third 3 2 0 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,29] 30 (.stop (.third 0 3 2 29)) (by decide +kernel))
  · exact unit_21_30_closed
  · exact unit_21_31_closed
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,32] 33 (.stop (.third 1 3 2 31)) (by decide +kernel))
  · exact unit_21_33_closed
  · exact unit_21_34_closed
  · exact unit_21_35_closed
  · exact unit_21_36_closed
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,37] 38 (.stop (.third 0 3 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,38] 39 (.stop (.third 1 3 2 13)) (by decide +kernel))
  · exact unit_21_39_closed
  · exact unit_21_40_closed
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,41] 42 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,42] 43 (.stop (.collision 200)) (by decide +kernel))
  · exact unit_21_43_closed
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,44] 45 (.stop (.third 1 3 2 67)) (by decide +kernel))
  · exact unit_21_45_closed
  · exact unit_21_46_closed
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,47] 48 (.stop (.third 0 3 2 23)) (by decide +kernel))
  · exact unit_21_48_closed
  · exact unit_21_49_closed
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,50] 51 (.stop (.third 1 3 2 49)) (by decide +kernel))
  · exact unit_21_51_closed
  · exact unit_21_52_closed
  · exact unit_21_53_closed
  · exact unit_21_54_closed
  · exact unit_21_55_closed
  · exact unit_21_56_closed
  · exact unit_21_57_closed
  · exact unit_21_58_closed
  · exact unit_21_59_closed
  · exact unit_21_60_closed
  · exact unit_21_61_closed
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,62] 63 (.stop (.third 1 3 2 61)) (by decide +kernel))
  · exact unit_21_63_closed
  · exact unit_21_64_closed
  · exact unit_21_65_closed
  · exact unit_21_66_closed
  · exact unit_21_67_closed
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,68] 69 (.stop (.third 1 3 2 43)) (by decide +kernel))
  · exact unit_21_69_closed
  · exact unit_21_70_closed
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,71] 72 (.stop (.collision 1537)) (by decide +kernel))
  · exact unit_21_72_closed
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,73] 74 (.stop (.third 3 0 2 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,74] 75 (.stop (.third 1 3 2 97)) (by decide +kernel))
  · exact unit_21_75_closed
  · exact unit_21_76_closed
  · exact unit_21_77_closed
  · exact unit_21_78_closed
  · exact unit_21_79_closed
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,80] 81 (.stop (.third 1 3 2 79)) (by decide +kernel))
  · exact unit_21_81_closed
  · exact unit_21_82_closed
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,83] 84 (.stop (.third 3 0 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,84] 85 (.stop (.third 1 3 0 107)) (by decide +kernel))
  · exact unit_21_85_closed
  · exact unit_21_86_closed
  · exact unit_21_87_closed
  · exact unit_21_88_closed
  · exact unit_21_89_closed
  · exact unit_21_90_closed
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,91] 92 (.stop (.third 3 0 2 29)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,92] 93 (.stop (.third 1 3 2 91)) (by decide +kernel))
  · exact unit_21_93_closed
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,94] 95 (.stop (.third 2 3 0 97)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,95] 96 (.branch [.stop (.collision 1104),.branch [.stop (.third 1 5 2 73),.stop (.collision 12361),.stop (.third 2 5 4 79),.stop (.third 1 0 5 119),.stop (.third 0 4 5 73),.stop (.third 0 5 1 7),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 4 5 73),.stop (.third 1 0 5 119),.stop (.third 0 5 2 109),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 4 5 73),.stop (.third 0 5 1 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 1 4 2 73),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 2 109),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,96] 97 (.branch [.stop (.collision 1104),.stop (.third 1 4 2 73),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 2 109),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,97] 98 (.branch [.stop (.third 1 4 2 73),.stop (.collision 523),.stop (.third 2 4 3 79),.stop (.third 1 0 4 119),.stop (.third 0 3 4 73),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 73),.stop (.third 1 0 4 119),.stop (.third 0 4 2 109),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 73),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,98] 99 (.stop (.third 1 3 2 73)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,99] 100 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,100] 101 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,101] 102 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,102] 103 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,104] 105 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,105] 106 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,106] 107 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,107] 108 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,108] 109 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,109] 110 (.stop (.third 0 3 2 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,110] 111 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,111] 112 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,112] 113 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,113] 114 (.stop (.third 0 3 1 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,114] 115 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 21 3 [0,1,21,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

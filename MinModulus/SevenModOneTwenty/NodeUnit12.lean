import MinModulus.SevenModOneTwenty.BlockUnit204
import MinModulus.SevenModOneTwenty.BlockUnit205
import MinModulus.SevenModOneTwenty.BlockUnit206
import MinModulus.SevenModOneTwenty.BlockUnit207
import MinModulus.SevenModOneTwenty.BlockUnit208
import MinModulus.SevenModOneTwenty.BlockUnit209
import MinModulus.SevenModOneTwenty.BlockUnit210
import MinModulus.SevenModOneTwenty.BlockUnit211

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_12_closed : ClosedMinimalPrefix true 120 12 4 [0,1,12] 13 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,13] 14 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_12_14_closed
  · exact unit_12_15_closed
  · exact unit_12_16_closed
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,17] 18 (.stop (.third 3 0 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,18] 19 (.stop (.third 1 3 0 113)) (by decide +kernel))
  · exact unit_12_19_closed
  · exact unit_12_20_closed
  · exact unit_12_21_closed
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,22] 23 (.stop (.third 2 1 3 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,23] 24 (.stop (.third 1 2 3 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,24] 25 (.stop (.collision 200)) (by decide +kernel))
  · exact unit_12_25_closed
  · exact unit_12_26_closed
  · exact unit_12_27_closed
  · exact unit_12_28_closed
  · exact unit_12_29_closed
  · exact unit_12_30_closed
  · exact unit_12_31_closed
  · exact unit_12_32_closed
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,33] 34 (.stop (.third 2 1 3 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,34] 35 (.stop (.third 1 2 3 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,35] 36 (.stop (.collision 256)) (by decide +kernel))
  · exact unit_12_36_closed
  · exact unit_12_37_closed
  · exact unit_12_38_closed
  · exact unit_12_39_closed
  · exact unit_12_40_closed
  · exact unit_12_41_closed
  · exact unit_12_42_closed
  · exact unit_12_43_closed
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,44] 45 (.stop (.third 2 1 3 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,45] 46 (.stop (.third 1 2 3 11)) (by decide +kernel))
  · exact unit_12_46_closed
  · exact unit_12_47_closed
  · exact unit_12_48_closed
  · exact unit_12_49_closed
  · exact unit_12_50_closed
  · exact unit_12_51_closed
  · exact unit_12_52_closed
  · exact unit_12_53_closed
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,54] 55 (.stop (.third 1 3 2 77)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,55] 56 (.stop (.third 2 1 3 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,56] 57 (.stop (.third 1 2 3 11)) (by decide +kernel))
  · exact unit_12_57_closed
  · exact unit_12_58_closed
  · exact unit_12_59_closed
  · exact unit_12_60_closed
  · exact unit_12_61_closed
  · exact unit_12_62_closed
  · exact unit_12_63_closed
  · exact unit_12_64_closed
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,65] 66 (.stop (.third 3 2 1 43)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,66] 67 (.stop (.third 2 1 3 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,67] 68 (.stop (.third 1 2 3 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,68] 69 (.stop (.third 3 1 2 77)) (by decide +kernel))
  · exact unit_12_69_closed
  · exact unit_12_70_closed
  · exact unit_12_71_closed
  · exact unit_12_72_closed
  · exact unit_12_73_closed
  · exact unit_12_74_closed
  · exact unit_12_75_closed
  · exact unit_12_76_closed
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,77] 78 (.stop (.third 2 1 3 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,78] 79 (.stop (.third 1 2 3 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,79] 80 (.stop (.third 2 3 1 43)) (by decide +kernel))
  · exact unit_12_80_closed
  · exact unit_12_81_closed
  · exact unit_12_82_closed
  · exact unit_12_83_closed
  · exact unit_12_84_closed
  · exact unit_12_85_closed
  · exact unit_12_86_closed
  · exact unit_12_87_closed
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,88] 89 (.stop (.third 2 1 3 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,89] 90 (.stop (.third 1 2 3 11)) (by decide +kernel))
  · exact unit_12_90_closed
  · exact unit_12_91_closed
  · exact unit_12_92_closed
  · exact unit_12_93_closed
  · exact unit_12_94_closed
  · exact unit_12_95_closed
  · exact unit_12_96_closed
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,97] 98 (.branch [.stop (.collision 1104),.stop (.third 2 1 4 109),.stop (.third 1 2 4 11),.stop (.third 2 4 3 89),.stop (.third 0 3 4 73),.stop (.third 0 4 1 7),.stop (.third 3 4 2 103),.branch [.stop (.third 5 4 3 119),.stop (.third 0 3 5 73),.stop (.third 5 1 4 37),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 0 3 5 73),.stop (.collision 5249),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 0 3 4 73),.stop (.collision 1153),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact unit_12_98_closed
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,99] 100 (.stop (.third 2 1 3 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,100] 101 (.stop (.third 1 2 3 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,101] 102 (.branch [.stop (.collision 1104),.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.stop (.third 3 2 4 31),.branch [.stop (.third 0 3 5 101),.stop (.collision 4619),.stop (.third 3 2 5 31),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 0 3 4 101),.stop (.collision 523),.stop (.third 3 2 4 31),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,102] 103 (.branch [.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.branch [.stop (.third 5 4 3 119),.stop (.collision 98944),.stop (.third 1 3 5 101),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.third 1 3 5 101),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 516),.stop (.third 1 3 4 101),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,104] 105 (.stop (.third 3 1 0 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,105] 106 (.branch [.stop (.collision 1104),.stop (.collision 12416),.stop (.third 4 1 3 37),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,106] 107 (.branch [.stop (.collision 1104),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,107] 108 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,108] 109 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,109] 110 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,110] 111 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,111] 112 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,112] 113 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,113] 114 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,114] 115 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 12 3 [0,1,12,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

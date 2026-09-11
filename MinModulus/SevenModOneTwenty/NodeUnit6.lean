import MinModulus.SevenModOneTwenty.BlockUnit112
import MinModulus.SevenModOneTwenty.BlockUnit113
import MinModulus.SevenModOneTwenty.BlockUnit114
import MinModulus.SevenModOneTwenty.BlockUnit115
import MinModulus.SevenModOneTwenty.BlockUnit116
import MinModulus.SevenModOneTwenty.BlockUnit118
import MinModulus.SevenModOneTwenty.BlockUnit119
import MinModulus.SevenModOneTwenty.BlockUnit120
import MinModulus.SevenModOneTwenty.BlockUnit121
import MinModulus.SevenModOneTwenty.BlockUnit122
import MinModulus.SevenModOneTwenty.BlockUnit123
import MinModulus.SevenModOneTwenty.BlockUnit124
import MinModulus.SevenModOneTwenty.BlockUnit125
import MinModulus.SevenModOneTwenty.BlockUnit126
import MinModulus.SevenModOneTwenty.BlockUnit127
import MinModulus.SevenModOneTwenty.BlockUnit128
import MinModulus.SevenModOneTwenty.BlockUnit129
import MinModulus.SevenModOneTwenty.BlockUnit130
import MinModulus.SevenModOneTwenty.BlockUnit131
import MinModulus.SevenModOneTwenty.BlockUnit132
import MinModulus.SevenModOneTwenty.BlockUnit133
import MinModulus.SevenModOneTwenty.BlockUnit134
import MinModulus.SevenModOneTwenty.BlockUnit135
import MinModulus.SevenModOneTwenty.BlockUnit136
import MinModulus.SevenModOneTwenty.NodeUnit6_16
import MinModulus.SevenModOneTwenty.NodeUnit6_8

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_6_closed : ClosedMinimalPrefix true 120 6 4 [0,1,6] 7 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,7] 8 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_6_8_closed
  · exact unit_6_9_closed
  · exact unit_6_10_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,11] 12 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,12] 13 (.stop (.collision 200)) (by decide +kernel))
  · exact unit_6_13_closed
  · exact unit_6_14_closed
  · exact unit_6_15_closed
  · exact unit_6_16_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,17] 18 (.stop (.collision 256)) (by decide +kernel))
  · exact unit_6_18_closed
  · exact unit_6_19_closed
  · exact unit_6_20_closed
  · exact unit_6_21_closed
  · exact unit_6_22_closed
  · exact unit_6_23_closed
  · exact unit_6_24_closed
  · exact unit_6_25_closed
  · exact unit_6_26_closed
  · exact unit_6_27_closed
  · exact unit_6_28_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,29] 30 (.stop (.third 2 3 1 47)) (by decide +kernel))
  · exact unit_6_30_closed
  · exact unit_6_31_closed
  · exact unit_6_32_closed
  · exact unit_6_33_closed
  · exact unit_6_34_closed
  · exact unit_6_35_closed
  · exact unit_6_36_closed
  · exact unit_6_37_closed
  · exact unit_6_38_closed
  · exact unit_6_39_closed
  · exact unit_6_40_closed
  · exact unit_6_41_closed
  · exact unit_6_42_closed
  · exact unit_6_43_closed
  · exact unit_6_44_closed
  · exact unit_6_45_closed
  · exact unit_6_46_closed
  · exact unit_6_47_closed
  · exact unit_6_48_closed
  · exact unit_6_49_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,50] 51 (.stop (.third 1 3 2 49)) (by decide +kernel))
  · exact unit_6_51_closed
  · exact unit_6_52_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,53] 54 (.stop (.third 2 3 1 23)) (by decide +kernel))
  · exact unit_6_54_closed
  · exact unit_6_55_closed
  · exact unit_6_56_closed
  · exact unit_6_57_closed
  · exact unit_6_58_closed
  · exact unit_6_59_closed
  · exact unit_6_60_closed
  · exact unit_6_61_closed
  · exact unit_6_62_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,63] 64 (.stop (.collision 1544)) (by decide +kernel))
  · exact unit_6_64_closed
  · exact unit_6_65_closed
  · exact unit_6_66_closed
  · exact unit_6_67_closed
  · exact unit_6_68_closed
  · exact unit_6_69_closed
  · exact unit_6_70_closed
  · exact unit_6_71_closed
  · exact unit_6_72_closed
  · exact unit_6_73_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,74] 75 (.stop (.third 1 3 2 97)) (by decide +kernel))
  · exact unit_6_75_closed
  · exact unit_6_76_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,77] 78 (.stop (.third 2 3 1 71)) (by decide +kernel))
  · exact unit_6_78_closed
  · exact unit_6_79_closed
  · exact unit_6_80_closed
  · exact unit_6_81_closed
  · exact unit_6_82_closed
  · exact unit_6_83_closed
  · exact unit_6_84_closed
  · exact unit_6_85_closed
  · exact unit_6_86_closed
  · exact unit_6_87_closed
  · exact unit_6_88_closed
  · exact unit_6_89_closed
  · exact unit_6_90_closed
  · exact unit_6_91_closed
  · exact unit_6_92_closed
  · exact unit_6_93_closed
  · exact unit_6_94_closed
  · exact unit_6_95_closed
  · exact unit_6_96_closed
  · exact unit_6_97_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,98] 99 (.stop (.third 1 3 2 73)) (by decide +kernel))
  · exact unit_6_99_closed
  · exact unit_6_100_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,101] 102 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 12417),.stop (.collision 102465),.stop (.collision 98881),.stop (.collision 73856),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 102528),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 102465),.stop (.collision 98888),.stop (.collision 12424),.stop (.collision 4619),.stop (.third 2 5 4 109),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 12416),.branch [.stop (.collision 8784),.stop (.collision 102465),.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 8833),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 102416),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12353),.stop (.collision 1216),.stop (.collision 12304),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,102] 103 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 102472),.stop (.collision 98888),.stop (.collision 73856),.stop (.collision 102409),.stop (.third 2 5 4 109),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 131144),.stop (.collision 8833),.stop (.collision 102472),.stop (.third 4 5 2 103),.stop (.collision 98881),.stop (.collision 102409),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.branch [.stop (.collision 102472),.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 102409),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12360),.branch [.stop (.collision 8784),.stop (.collision 102409),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 1216),.stop (.collision 12297),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,103] 104 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 8833),.stop (.collision 8840),.stop (.third 4 5 2 103),.stop (.collision 98881),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 12368),.stop (.collision 8833),.stop (.collision 8840),.stop (.third 0 5 4 17),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.branch [.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12353),.stop (.collision 516),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,104] 105 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 8833),.stop (.collision 102472),.stop (.third 0 5 4 17),.stop (.collision 4619),.stop (.third 2 5 3 109),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 98944),.stop (.collision 102472),.stop (.collision 8840),.stop (.third 1 5 4 17),.stop (.third 2 5 3 109),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.collision 12360),.stop (.collision 516),.stop (.collision 523),.stop (.third 2 4 3 109),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,105] 106 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.collision 5249),.stop (.collision 5256),.stop (.third 3 5 2 103),.stop (.collision 8840),.stop (.third 1 5 4 17),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 5256),.stop (.third 3 5 2 103),.stop (.collision 102465),.stop (.collision 98888),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.third 3 4 2 103),.stop (.collision 12353),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,106] 107 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.collision 5249),.stop (.collision 5256),.stop (.third 0 5 3 17),.stop (.collision 98888),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 5256),.stop (.third 0 5 3 17),.stop (.collision 8833),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.third 0 4 3 17),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,107] 108 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.collision 5249),.stop (.collision 5256),.stop (.third 1 5 3 17),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 5256),.stop (.third 1 5 3 17),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12416),.stop (.collision 1153),.stop (.collision 1160),.stop (.third 1 4 3 17),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,108] 109 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.collision 5249),.stop (.collision 102472),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 102472),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 12360),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,109] 110 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.collision 5249),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12416),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,110] 111 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 516),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,111] 112 (.branch [.stop (.collision 1104),.stop (.collision 12416),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,112] 113 (.branch [.stop (.collision 1104),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,113] 114 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,114] 115 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,115] 116 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 3 [0,1,6,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

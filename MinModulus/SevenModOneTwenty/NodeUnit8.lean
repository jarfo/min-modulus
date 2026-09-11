import MinModulus.SevenModOneTwenty.BlockUnit155
import MinModulus.SevenModOneTwenty.BlockUnit156
import MinModulus.SevenModOneTwenty.BlockUnit157
import MinModulus.SevenModOneTwenty.BlockUnit158
import MinModulus.SevenModOneTwenty.BlockUnit159
import MinModulus.SevenModOneTwenty.BlockUnit160
import MinModulus.SevenModOneTwenty.BlockUnit161
import MinModulus.SevenModOneTwenty.BlockUnit162
import MinModulus.SevenModOneTwenty.BlockUnit163
import MinModulus.SevenModOneTwenty.BlockUnit164
import MinModulus.SevenModOneTwenty.BlockUnit165
import MinModulus.SevenModOneTwenty.BlockUnit166
import MinModulus.SevenModOneTwenty.BlockUnit167
import MinModulus.SevenModOneTwenty.BlockUnit168
import MinModulus.SevenModOneTwenty.BlockUnit169
import MinModulus.SevenModOneTwenty.BlockUnit170

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_8_closed : ClosedMinimalPrefix true 120 8 4 [0,1,8] 9 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,9] 10 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_8_10_closed
  · exact unit_8_11_closed
  · exact unit_8_12_closed
  · exact unit_8_13_closed
  · exact unit_8_14_closed
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,15] 16 (.stop (.third 1 2 3 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,16] 17 (.stop (.collision 200)) (by decide +kernel))
  · exact unit_8_17_closed
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,18] 19 (.stop (.third 1 3 0 113)) (by decide +kernel))
  · exact unit_8_19_closed
  · exact unit_8_20_closed
  · exact unit_8_21_closed
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,22] 23 (.stop (.third 1 2 3 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,23] 24 (.stop (.collision 256)) (by decide +kernel))
  · exact unit_8_24_closed
  · exact unit_8_25_closed
  · exact unit_8_26_closed
  · exact unit_8_27_closed
  · exact unit_8_28_closed
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,29] 30 (.stop (.third 1 2 3 103)) (by decide +kernel))
  · exact unit_8_30_closed
  · exact unit_8_31_closed
  · exact unit_8_32_closed
  · exact unit_8_33_closed
  · exact unit_8_34_closed
  · exact unit_8_35_closed
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,36] 37 (.stop (.third 1 2 3 103)) (by decide +kernel))
  · exact unit_8_37_closed
  · exact unit_8_38_closed
  · exact unit_8_39_closed
  · exact unit_8_40_closed
  · exact unit_8_41_closed
  · exact unit_8_42_closed
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,43] 44 (.stop (.third 1 2 3 103)) (by decide +kernel))
  · exact unit_8_44_closed
  · exact unit_8_45_closed
  · exact unit_8_46_closed
  · exact unit_8_47_closed
  · exact unit_8_48_closed
  · exact unit_8_49_closed
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,50] 51 (.stop (.third 1 2 3 103)) (by decide +kernel))
  · exact unit_8_51_closed
  · exact unit_8_52_closed
  · exact unit_8_53_closed
  · exact unit_8_54_closed
  · exact unit_8_55_closed
  · exact unit_8_56_closed
  · exact unit_8_57_closed
  · exact unit_8_58_closed
  · exact unit_8_59_closed
  · exact unit_8_60_closed
  · exact unit_8_61_closed
  · exact unit_8_62_closed
  · exact unit_8_63_closed
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,64] 65 (.stop (.collision 1544)) (by decide +kernel))
  · exact unit_8_65_closed
  · exact unit_8_66_closed
  · exact unit_8_67_closed
  · exact unit_8_68_closed
  · exact unit_8_69_closed
  · exact unit_8_70_closed
  · exact unit_8_71_closed
  · exact unit_8_72_closed
  · exact unit_8_73_closed
  · exact unit_8_74_closed
  · exact unit_8_75_closed
  · exact unit_8_76_closed
  · exact unit_8_77_closed
  · exact unit_8_78_closed
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,79] 80 (.stop (.third 2 1 3 17)) (by decide +kernel))
  · exact unit_8_80_closed
  · exact unit_8_81_closed
  · exact unit_8_82_closed
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,83] 84 (.stop (.collision 2048)) (by decide +kernel))
  · exact unit_8_84_closed
  · exact unit_8_85_closed
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,86] 87 (.stop (.third 2 1 3 17)) (by decide +kernel))
  · exact unit_8_87_closed
  · exact unit_8_88_closed
  · exact unit_8_89_closed
  · exact unit_8_90_closed
  · exact unit_8_91_closed
  · exact unit_8_92_closed
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,93] 94 (.stop (.third 2 1 3 17)) (by decide +kernel))
  · exact unit_8_94_closed
  · exact unit_8_95_closed
  · exact unit_8_96_closed
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,97] 98 (.branch [.stop (.collision 1104),.branch [.stop (.third 2 1 5 17),.stop (.third 3 2 5 31),.stop (.third 0 3 5 73),.stop (.third 0 5 1 7),.stop (.collision 5249),.stop (.collision 5256),.stop (.third 4 5 0 103),.stop (.third 2 1 5 17),.stop (.collision 12417),.stop (.collision 102465),.stop (.third 1 5 4 109),.stop (.collision 73856),.stop (.collision 4619),.stop (.third 0 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 2 1 4 17),.stop (.third 3 2 4 31),.stop (.third 0 3 4 73),.stop (.third 0 4 1 7),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.third 2 1 4 17),.branch [.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 1112),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12353),.branch [.stop (.third 5 2 4 113),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 516),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact unit_8_98_closed
  · exact unit_8_99_closed
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,100] 101 (.stop (.third 2 1 3 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,101] 102 (.branch [.stop (.collision 1104),.stop (.third 0 4 1 7),.branch [.stop (.third 5 4 3 119),.stop (.collision 1672),.stop (.third 0 3 5 101),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 73856),.stop (.collision 102465),.stop (.collision 98888),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.third 0 3 5 101),.stop (.collision 5249),.stop (.collision 5256),.stop (.third 2 4 5 73),.stop (.collision 102465),.stop (.collision 8833),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 0 3 5 101),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 12354),.stop (.collision 102465),.stop (.collision 4619),.stop (.third 0 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 0 3 4 101),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.collision 12353),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,102] 103 (.branch [.stop (.third 0 4 1 7),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.third 2 1 5 17),.stop (.third 1 3 5 101),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 102472),.stop (.collision 98888),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.third 2 1 5 17),.stop (.third 1 3 5 101),.stop (.collision 5249),.stop (.third 2 4 5 73),.stop (.collision 102472),.stop (.collision 8833),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 2 1 5 17),.stop (.third 1 3 5 101),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 102472),.stop (.collision 4619),.stop (.third 0 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 2 1 4 17),.stop (.third 1 3 4 101),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 12360),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,104] 105 (.branch [.stop (.collision 1104),.branch [.stop (.third 2 1 5 17),.stop (.collision 12361),.stop (.collision 12368),.stop (.collision 131144),.stop (.collision 5249),.stop (.collision 102472),.stop (.third 0 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 2 1 4 17),.branch [.stop (.third 5 4 3 119),.stop (.collision 69656),.stop (.collision 5249),.stop (.collision 102472),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 102472),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 12360),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,105] 106 (.branch [.stop (.collision 1104),.stop (.third 2 1 4 17),.branch [.stop (.third 5 4 3 119),.stop (.third 2 3 5 73),.stop (.collision 12361),.stop (.collision 5249),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12416),.stop (.third 2 3 4 73),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,106] 107 (.branch [.stop (.third 2 1 4 17),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.collision 73856),.stop (.collision 4619),.stop (.third 0 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.collision 98944),.stop (.collision 12361),.stop (.third 0 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 2 4 113),.stop (.collision 4619),.stop (.third 0 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 516),.stop (.collision 523),.stop (.third 0 4 3 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,107] 108 (.stop (.third 2 1 3 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,108] 109 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 2 4 113),.stop (.collision 12361),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 516),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,109] 110 (.branch [.stop (.collision 1104),.stop (.collision 12416),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,110] 111 (.branch [.stop (.third 4 2 3 113),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,111] 112 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,112] 113 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,113] 114 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,114] 115 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 8 3 [0,1,8,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

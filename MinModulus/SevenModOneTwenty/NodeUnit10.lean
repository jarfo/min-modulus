import MinModulus.SevenModOneTwenty.BlockUnit186
import MinModulus.SevenModOneTwenty.BlockUnit187
import MinModulus.SevenModOneTwenty.BlockUnit188
import MinModulus.SevenModOneTwenty.BlockUnit189
import MinModulus.SevenModOneTwenty.BlockUnit190
import MinModulus.SevenModOneTwenty.BlockUnit191
import MinModulus.SevenModOneTwenty.BlockUnit192
import MinModulus.SevenModOneTwenty.BlockUnit193
import MinModulus.SevenModOneTwenty.BlockUnit194
import MinModulus.SevenModOneTwenty.BlockUnit195
import MinModulus.SevenModOneTwenty.BlockUnit196
import MinModulus.SevenModOneTwenty.BlockUnit197

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_10_closed : ClosedMinimalPrefix true 120 10 4 [0,1,10] 11 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,11] 12 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_10_12_closed
  · exact unit_10_13_closed
  · exact unit_10_14_closed
  · exact unit_10_15_closed
  · exact unit_10_16_closed
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,17] 18 (.stop (.third 3 0 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,18] 19 (.stop (.third 1 3 0 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,19] 20 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,20] 21 (.stop (.collision 200)) (by decide +kernel))
  · exact unit_10_21_closed
  · exact unit_10_22_closed
  · exact unit_10_23_closed
  · exact unit_10_24_closed
  · exact unit_10_25_closed
  · exact unit_10_26_closed
  · exact unit_10_27_closed
  · exact unit_10_28_closed
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,29] 30 (.stop (.collision 256)) (by decide +kernel))
  · exact unit_10_30_closed
  · exact unit_10_31_closed
  · exact unit_10_32_closed
  · exact unit_10_33_closed
  · exact unit_10_34_closed
  · exact unit_10_35_closed
  · exact unit_10_36_closed
  · exact unit_10_37_closed
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,38] 39 (.stop (.third 3 1 2 107)) (by decide +kernel))
  · exact unit_10_39_closed
  · exact unit_10_40_closed
  · exact unit_10_41_closed
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,42] 43 (.stop (.third 1 3 2 41)) (by decide +kernel))
  · exact unit_10_43_closed
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,44] 45 (.stop (.third 1 3 2 67)) (by decide +kernel))
  · exact unit_10_45_closed
  · exact unit_10_46_closed
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,47] 48 (.stop (.third 2 3 1 13)) (by decide +kernel))
  · exact unit_10_48_closed
  · exact unit_10_49_closed
  · exact unit_10_50_closed
  · exact unit_10_51_closed
  · exact unit_10_52_closed
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,53] 54 (.stop (.third 3 2 1 53)) (by decide +kernel))
  · exact unit_10_54_closed
  · exact unit_10_55_closed
  · exact unit_10_56_closed
  · exact unit_10_57_closed
  · exact unit_10_58_closed
  · exact unit_10_59_closed
  · exact unit_10_60_closed
  · exact unit_10_61_closed
  · exact unit_10_62_closed
  · exact unit_10_63_closed
  · exact unit_10_64_closed
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,65] 66 (.stop (.collision 1544)) (by decide +kernel))
  · exact unit_10_66_closed
  · exact unit_10_67_closed
  · exact unit_10_68_closed
  · exact unit_10_69_closed
  · exact unit_10_70_closed
  · exact unit_10_71_closed
  · exact unit_10_72_closed
  · exact unit_10_73_closed
  · exact unit_10_74_closed
  · exact unit_10_75_closed
  · exact unit_10_76_closed
  · exact unit_10_77_closed
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,78] 79 (.stop (.third 3 1 2 67)) (by decide +kernel))
  · exact unit_10_79_closed
  · exact unit_10_80_closed
  · exact unit_10_81_closed
  · exact unit_10_82_closed
  · exact unit_10_83_closed
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,84] 85 (.stop (.third 1 3 2 107)) (by decide +kernel))
  · exact unit_10_85_closed
  · exact unit_10_86_closed
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,87] 88 (.stop (.third 2 3 1 53)) (by decide +kernel))
  · exact unit_10_88_closed
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,89] 90 (.stop (.third 2 3 1 79)) (by decide +kernel))
  · exact unit_10_90_closed
  · exact unit_10_91_closed
  · exact unit_10_92_closed
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,93] 94 (.stop (.third 3 2 1 13)) (by decide +kernel))
  · exact unit_10_94_closed
  · exact unit_10_95_closed
  · exact unit_10_96_closed
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,97] 98 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.third 5 2 3 29),.stop (.third 0 3 5 73),.stop (.third 0 5 1 7),.stop (.third 5 1 0 113),.stop (.collision 98944),.stop (.third 4 5 0 103),.stop (.third 4 2 5 31),.stop (.third 3 5 2 11),.stop (.collision 8840),.stop (.third 1 5 4 109),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 0 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 2 3 29),.stop (.third 0 3 5 73),.stop (.third 0 5 1 7),.stop (.third 5 1 0 113),.stop (.collision 69656),.stop (.collision 5249),.stop (.third 4 5 1 103),.stop (.third 3 5 2 11),.stop (.collision 102465),.stop (.collision 98888),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 4 2 3 29),.stop (.third 0 3 4 73),.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.third 3 4 2 11),.stop (.collision 12353),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact unit_10_98_closed
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,99] 100 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.third 0 5 1 7),.stop (.third 5 1 0 113),.stop (.third 2 4 5 91),.stop (.third 3 5 0 103),.stop (.third 0 4 5 101),.stop (.collision 5249),.stop (.third 2 4 5 91),.stop (.third 1 5 3 109),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 0 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 0 5 1 7),.stop (.third 5 1 0 113),.stop (.collision 12361),.stop (.third 3 5 0 103),.stop (.third 3 2 5 31),.stop (.third 1 4 5 101),.stop (.third 4 5 2 103),.stop (.third 1 5 3 109),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 0 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.stop (.collision 12416),.stop (.third 3 4 0 103),.stop (.third 3 2 4 31),.stop (.collision 1153),.stop (.collision 1160),.stop (.third 1 4 3 109),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 0 4 3 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,100] 101 (.branch [.stop (.collision 1104),.branch [.stop (.third 0 5 1 7),.stop (.third 5 1 0 113),.stop (.collision 12368),.stop (.collision 98314),.stop (.third 3 5 1 103),.stop (.third 1 4 5 101),.stop (.third 4 5 2 103),.stop (.collision 102472),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.branch [.stop (.third 5 4 3 119),.stop (.third 3 5 1 103),.stop (.third 5 1 4 37),.stop (.collision 5249),.stop (.collision 102472),.stop (.third 5 2 4 19),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 3 5 1 103),.stop (.collision 69656),.stop (.collision 5249),.stop (.collision 102472),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 0 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 3 4 1 103),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 12360),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,101] 102 (.branch [.stop (.collision 1104),.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.stop (.third 2 3 4 91),.stop (.collision 12416),.stop (.third 0 3 4 101),.branch [.stop (.third 2 3 5 91),.stop (.collision 5249),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 2 3 4 91),.stop (.collision 1153),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,102] 103 (.branch [.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.branch [.stop (.third 5 4 3 119),.stop (.third 5 2 3 47),.stop (.third 1 3 5 101),.stop (.third 3 5 2 103),.stop (.collision 4619),.stop (.third 5 2 4 19),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 2 3 47),.stop (.third 1 3 5 101),.stop (.third 3 5 2 103),.stop (.collision 12361),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 0 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 4 2 3 47),.stop (.third 1 3 4 101),.stop (.third 3 4 2 103),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,104] 105 (.stop (.third 3 1 0 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,105] 106 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 1 3 37),.stop (.collision 12361),.stop (.collision 4619),.stop (.third 5 2 3 19),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 4 1 3 37),.stop (.collision 516),.stop (.collision 523),.stop (.third 4 2 3 19),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,106] 107 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 0 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 516),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 0 4 3 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,107] 108 (.branch [.stop (.collision 1104),.stop (.collision 12416),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,108] 109 (.branch [.stop (.collision 1104),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,109] 110 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,110] 111 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,111] 112 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,112] 113 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,113] 114 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,114] 115 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 10 3 [0,1,10,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

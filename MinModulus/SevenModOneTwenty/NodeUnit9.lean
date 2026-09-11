import MinModulus.SevenModOneTwenty.BlockUnit171
import MinModulus.SevenModOneTwenty.BlockUnit172
import MinModulus.SevenModOneTwenty.BlockUnit173
import MinModulus.SevenModOneTwenty.BlockUnit174
import MinModulus.SevenModOneTwenty.BlockUnit175
import MinModulus.SevenModOneTwenty.BlockUnit176
import MinModulus.SevenModOneTwenty.BlockUnit177
import MinModulus.SevenModOneTwenty.BlockUnit178
import MinModulus.SevenModOneTwenty.BlockUnit179
import MinModulus.SevenModOneTwenty.BlockUnit180
import MinModulus.SevenModOneTwenty.BlockUnit181
import MinModulus.SevenModOneTwenty.BlockUnit182
import MinModulus.SevenModOneTwenty.BlockUnit183
import MinModulus.SevenModOneTwenty.BlockUnit184
import MinModulus.SevenModOneTwenty.BlockUnit185

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_9_closed : ClosedMinimalPrefix true 120 9 4 [0,1,9] 10 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,10] 11 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_9_11_closed
  · exact unit_9_12_closed
  · exact unit_9_13_closed
  · exact unit_9_14_closed
  · exact unit_9_15_closed
  · exact unit_9_16_closed
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,17] 18 (.stop (.third 3 0 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,18] 19 (.stop (.third 1 3 0 113)) (by decide +kernel))
  · exact unit_9_19_closed
  · exact unit_9_20_closed
  · exact unit_9_21_closed
  · exact unit_9_22_closed
  · exact unit_9_23_closed
  · exact unit_9_24_closed
  · exact unit_9_25_closed
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,26] 27 (.stop (.collision 256)) (by decide +kernel))
  · exact unit_9_27_closed
  · exact unit_9_28_closed
  · exact unit_9_29_closed
  · exact unit_9_30_closed
  · exact unit_9_31_closed
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,32] 33 (.stop (.third 1 3 2 31)) (by decide +kernel))
  · exact unit_9_33_closed
  · exact unit_9_34_closed
  · exact unit_9_35_closed
  · exact unit_9_36_closed
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,37] 38 (.stop (.third 3 0 2 107)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,38] 39 (.stop (.third 2 3 1 29)) (by decide +kernel))
  · exact unit_9_39_closed
  · exact unit_9_40_closed
  · exact unit_9_41_closed
  · exact unit_9_42_closed
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,43] 44 (.stop (.third 0 3 2 67)) (by decide +kernel))
  · exact unit_9_44_closed
  · exact unit_9_45_closed
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,46] 47 (.stop (.third 2 3 0 13)) (by decide +kernel))
  · exact unit_9_47_closed
  · exact unit_9_48_closed
  · exact unit_9_49_closed
  · exact unit_9_50_closed
  · exact unit_9_51_closed
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,52] 53 (.stop (.third 3 2 0 53)) (by decide +kernel))
  · exact unit_9_53_closed
  · exact unit_9_54_closed
  · exact unit_9_55_closed
  · exact unit_9_56_closed
  · exact unit_9_57_closed
  · exact unit_9_58_closed
  · exact unit_9_59_closed
  · exact unit_9_60_closed
  · exact unit_9_61_closed
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,62] 63 (.stop (.third 1 3 2 61)) (by decide +kernel))
  · exact unit_9_63_closed
  · exact unit_9_64_closed
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,65] 66 (.stop (.collision 1537)) (by decide +kernel))
  · exact unit_9_66_closed
  · exact unit_9_67_closed
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,68] 69 (.stop (.third 2 3 1 59)) (by decide +kernel))
  · exact unit_9_69_closed
  · exact unit_9_70_closed
  · exact unit_9_71_closed
  · exact unit_9_72_closed
  · exact unit_9_73_closed
  · exact unit_9_74_closed
  · exact unit_9_75_closed
  · exact unit_9_76_closed
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,77] 78 (.stop (.third 3 0 2 67)) (by decide +kernel))
  · exact unit_9_78_closed
  · exact unit_9_79_closed
  · exact unit_9_80_closed
  · exact unit_9_81_closed
  · exact unit_9_82_closed
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,83] 84 (.stop (.third 0 3 2 107)) (by decide +kernel))
  · exact unit_9_84_closed
  · exact unit_9_85_closed
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,86] 87 (.stop (.third 2 3 0 53)) (by decide +kernel))
  · exact unit_9_87_closed
  · exact unit_9_88_closed
  · exact unit_9_89_closed
  · exact unit_9_90_closed
  · exact unit_9_91_closed
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,92] 93 (.stop (.third 1 3 2 91)) (by decide +kernel))
  · exact unit_9_93_closed
  · exact unit_9_94_closed
  · exact unit_9_95_closed
  · exact unit_9_96_closed
  · exact unit_9_97_closed
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,98] 99 (.stop (.third 2 3 1 89)) (by decide +kernel))
  · exact unit_9_99_closed
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,100] 101 (.branch [.stop (.collision 1104),.branch [.stop (.third 0 5 1 7),.stop (.third 2 3 5 91),.stop (.collision 12368),.stop (.collision 102528),.stop (.third 3 5 1 103),.stop (.third 1 4 5 101),.stop (.collision 5256),.stop (.collision 102472),.stop (.collision 98888),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 0 4 1 7),.stop (.third 2 3 4 91),.branch [.stop (.third 5 4 3 119),.stop (.third 3 5 1 103),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 102472),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12416),.stop (.third 3 4 1 103),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 12360),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,101] 102 (.branch [.stop (.collision 1104),.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.branch [.stop (.third 5 2 3 47),.stop (.third 0 3 5 101),.stop (.third 3 5 2 103),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 102465),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 4 2 3 47),.stop (.third 0 3 4 101),.stop (.third 3 4 2 103),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 12353),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,102] 103 (.branch [.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.branch [.stop (.third 5 4 3 119),.stop (.collision 102528),.stop (.third 1 3 5 101),.stop (.collision 73856),.stop (.collision 5249),.stop (.collision 102472),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.third 1 3 5 101),.stop (.collision 98944),.stop (.collision 5249),.stop (.third 2 4 5 73),.stop (.collision 70272),.stop (.third 0 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12416),.stop (.third 1 3 4 101),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 12360),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,104] 105 (.stop (.third 3 1 0 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,105] 106 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.collision 73856),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.collision 98944),.stop (.collision 12361),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 516),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,106] 107 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.third 2 3 5 73),.stop (.collision 70272),.stop (.third 0 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12416),.stop (.collision 516),.stop (.third 2 3 4 73),.stop (.collision 8832),.stop (.third 0 4 3 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,107] 108 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 516),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,108] 109 (.branch [.stop (.collision 1104),.stop (.collision 12416),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,109] 110 (.branch [.stop (.collision 1104),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,110] 111 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,111] 112 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,112] 113 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,113] 114 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,114] 115 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 9 3 [0,1,9,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

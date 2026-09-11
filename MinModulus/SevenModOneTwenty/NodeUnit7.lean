import MinModulus.SevenModOneTwenty.BlockUnit137
import MinModulus.SevenModOneTwenty.BlockUnit138
import MinModulus.SevenModOneTwenty.BlockUnit139
import MinModulus.SevenModOneTwenty.BlockUnit140
import MinModulus.SevenModOneTwenty.BlockUnit141
import MinModulus.SevenModOneTwenty.BlockUnit142
import MinModulus.SevenModOneTwenty.BlockUnit143
import MinModulus.SevenModOneTwenty.BlockUnit144
import MinModulus.SevenModOneTwenty.BlockUnit145
import MinModulus.SevenModOneTwenty.BlockUnit146
import MinModulus.SevenModOneTwenty.BlockUnit147
import MinModulus.SevenModOneTwenty.BlockUnit148
import MinModulus.SevenModOneTwenty.BlockUnit149
import MinModulus.SevenModOneTwenty.BlockUnit150
import MinModulus.SevenModOneTwenty.BlockUnit151
import MinModulus.SevenModOneTwenty.BlockUnit152
import MinModulus.SevenModOneTwenty.BlockUnit153
import MinModulus.SevenModOneTwenty.BlockUnit154
import MinModulus.SevenModOneTwenty.BlockUnit155
import MinModulus.SevenModOneTwenty.NodeUnit7_15

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_7_closed : ClosedMinimalPrefix true 120 7 4 [0,1,7] 8 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,8] 9 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_7_9_closed
  · exact unit_7_10_closed
  · exact unit_7_11_closed
  · exact unit_7_12_closed
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,13] 14 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,14] 15 (.stop (.third 0 2 3 103)) (by decide +kernel))
  · exact unit_7_15_closed
  · exact unit_7_16_closed
  · exact unit_7_17_closed
  · exact unit_7_18_closed
  · exact unit_7_19_closed
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,20] 21 (.stop (.collision 256)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,21] 22 (.stop (.third 0 2 3 103)) (by decide +kernel))
  · exact unit_7_22_closed
  · exact unit_7_23_closed
  · exact unit_7_24_closed
  · exact unit_7_25_closed
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,26] 27 (.stop (.third 2 3 1 19)) (by decide +kernel))
  · exact unit_7_27_closed
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,28] 29 (.stop (.third 0 2 3 103)) (by decide +kernel))
  · exact unit_7_29_closed
  · exact unit_7_30_closed
  · exact unit_7_31_closed
  · exact unit_7_32_closed
  · exact unit_7_33_closed
  · exact unit_7_34_closed
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,35] 36 (.stop (.third 0 2 3 103)) (by decide +kernel))
  · exact unit_7_36_closed
  · exact unit_7_37_closed
  · exact unit_7_38_closed
  · exact unit_7_39_closed
  · exact unit_7_40_closed
  · exact unit_7_41_closed
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,42] 43 (.stop (.third 0 2 3 103)) (by decide +kernel))
  · exact unit_7_43_closed
  · exact unit_7_44_closed
  · exact unit_7_45_closed
  · exact unit_7_46_closed
  · exact unit_7_47_closed
  · exact unit_7_48_closed
  · exact unit_7_49_closed
  · exact unit_7_50_closed
  · exact unit_7_51_closed
  · exact unit_7_52_closed
  · exact unit_7_53_closed
  · exact unit_7_54_closed
  · exact unit_7_55_closed
  · exact unit_7_56_closed
  · exact unit_7_57_closed
  · exact unit_7_58_closed
  · exact unit_7_59_closed
  · exact unit_7_60_closed
  · exact unit_7_61_closed
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,62] 63 (.stop (.third 1 3 2 61)) (by decide +kernel))
  · exact unit_7_63_closed
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,64] 65 (.stop (.collision 1537)) (by decide +kernel))
  · exact unit_7_65_closed
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,66] 67 (.stop (.third 2 3 1 59)) (by decide +kernel))
  · exact unit_7_67_closed
  · exact unit_7_68_closed
  · exact unit_7_69_closed
  · exact unit_7_70_closed
  · exact unit_7_71_closed
  · exact unit_7_72_closed
  · exact unit_7_73_closed
  · exact unit_7_74_closed
  · exact unit_7_75_closed
  · exact unit_7_76_closed
  · exact unit_7_77_closed
  · exact unit_7_78_closed
  · exact unit_7_79_closed
  · exact unit_7_80_closed
  · exact unit_7_81_closed
  · exact unit_7_82_closed
  · exact unit_7_83_closed
  · exact unit_7_84_closed
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,85] 86 (.stop (.third 2 0 3 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,86] 87 (.stop (.third 2 3 1 79)) (by decide +kernel))
  · exact unit_7_87_closed
  · exact unit_7_88_closed
  · exact unit_7_89_closed
  · exact unit_7_90_closed
  · exact unit_7_91_closed
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,92] 93 (.stop (.third 2 0 3 17)) (by decide +kernel))
  · exact unit_7_93_closed
  · exact unit_7_94_closed
  · exact unit_7_95_closed
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,96] 97 (.branch [.stop (.collision 1104),.branch [.stop (.third 2 0 5 17),.stop (.third 3 2 5 31),.stop (.collision 1672),.stop (.third 1 5 2 101),.stop (.third 1 4 5 73),.stop (.collision 8833),.stop (.collision 8840),.stop (.third 2 0 5 17),.stop (.collision 12424),.stop (.collision 102472),.stop (.third 0 5 4 109),.stop (.collision 1028),.stop (.collision 8896),.stop (.collision 73856),.stop (.third 2 0 5 17),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 2 0 4 17),.stop (.third 3 2 4 31),.stop (.collision 8216),.stop (.third 1 4 2 101),.stop (.collision 1160),.stop (.collision 8195),.stop (.collision 12416),.stop (.third 2 0 4 17),.branch [.stop (.collision 102472),.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 102416),.stop (.collision 66072),.stop (.third 2 0 5 17),.stop (.third 1 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12360),.stop (.collision 1216),.branch [.stop (.collision 8784),.stop (.collision 98944),.stop (.third 2 0 5 17),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12304),.stop (.collision 12290),.stop (.third 2 0 4 17),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact unit_7_97_closed
  · exact unit_7_98_closed
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,99] 100 (.stop (.third 2 0 3 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,100] 101 (.branch [.stop (.collision 1104),.stop (.third 1 4 2 101),.branch [.stop (.third 5 4 3 119),.stop (.collision 69656),.stop (.third 2 0 5 17),.stop (.third 3 5 1 103),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 102472),.stop (.collision 73856),.stop (.collision 98881),.stop (.third 2 0 5 17),.stop (.third 1 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.third 2 0 5 17),.stop (.third 3 5 1 103),.stop (.collision 12361),.stop (.third 2 4 5 73),.stop (.collision 102472),.stop (.collision 8840),.stop (.collision 98888),.stop (.third 2 0 5 17),.stop (.third 1 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.third 2 0 4 17),.stop (.third 3 4 1 103),.stop (.collision 8195),.branch [.stop (.collision 102472),.stop (.collision 73800),.stop (.collision 73793),.stop (.third 2 0 5 17),.stop (.third 1 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12360),.branch [.stop (.collision 8784),.stop (.third 2 0 5 17),.stop (.third 1 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 516),.stop (.third 2 0 4 17),.stop (.third 1 4 3 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact unit_7_101_closed
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,102] 103 (.stop (.third 1 3 2 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,103] 104 (.branch [.stop (.collision 1104),.branch [.stop (.third 2 0 5 17),.stop (.collision 12361),.stop (.collision 1672),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 8833),.stop (.collision 8840),.stop (.third 2 0 5 17),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 2 0 4 17),.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 12361),.stop (.collision 102465),.stop (.third 2 0 5 17),.stop (.third 1 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.collision 12353),.stop (.third 2 0 4 17),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,104] 105 (.branch [.stop (.collision 1104),.stop (.third 2 0 4 17),.branch [.stop (.third 5 4 3 119),.stop (.third 2 3 5 73),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 102472),.stop (.third 2 0 5 17),.stop (.third 1 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 2 3 5 73),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 102472),.stop (.third 2 0 5 17),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 2 3 4 73),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 12360),.stop (.third 2 0 4 17),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,105] 106 (.branch [.stop (.third 2 0 4 17),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.collision 1672),.stop (.collision 5249),.stop (.collision 5256),.stop (.third 2 0 5 17),.stop (.third 1 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.collision 69656),.stop (.collision 5249),.stop (.collision 5256),.stop (.third 2 0 5 17),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 5256),.stop (.third 2 0 5 17),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.third 2 0 4 17),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,106] 107 (.stop (.third 2 0 3 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,107] 108 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.collision 73856),.stop (.third 2 0 5 17),.stop (.third 1 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.collision 98944),.stop (.third 2 0 5 17),.stop (.third 1 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.third 2 0 5 17),.stop (.third 1 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.third 2 0 4 17),.stop (.third 1 4 3 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,108] 109 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.third 2 0 5 17),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12416),.stop (.collision 516),.stop (.third 2 0 4 17),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,109] 110 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.third 2 0 5 17),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 516),.stop (.third 2 0 4 17),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,110] 111 (.branch [.stop (.collision 1104),.stop (.collision 12416),.stop (.third 2 0 4 17),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,111] 112 (.branch [.stop (.collision 1104),.stop (.third 2 0 4 17),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,112] 113 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,113] 114 (.stop (.third 2 0 3 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,114] 115 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 7 3 [0,1,7,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

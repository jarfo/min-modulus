import MinModulus.SevenModOneTwenty.BlockUnit100
import MinModulus.SevenModOneTwenty.BlockUnit101
import MinModulus.SevenModOneTwenty.BlockUnit102
import MinModulus.SevenModOneTwenty.BlockUnit103
import MinModulus.SevenModOneTwenty.BlockUnit104
import MinModulus.SevenModOneTwenty.BlockUnit105
import MinModulus.SevenModOneTwenty.BlockUnit106
import MinModulus.SevenModOneTwenty.BlockUnit107
import MinModulus.SevenModOneTwenty.BlockUnit108
import MinModulus.SevenModOneTwenty.BlockUnit109
import MinModulus.SevenModOneTwenty.BlockUnit110
import MinModulus.SevenModOneTwenty.BlockUnit87
import MinModulus.SevenModOneTwenty.BlockUnit89
import MinModulus.SevenModOneTwenty.BlockUnit90
import MinModulus.SevenModOneTwenty.BlockUnit91
import MinModulus.SevenModOneTwenty.BlockUnit92
import MinModulus.SevenModOneTwenty.BlockUnit93
import MinModulus.SevenModOneTwenty.BlockUnit94
import MinModulus.SevenModOneTwenty.BlockUnit95
import MinModulus.SevenModOneTwenty.BlockUnit96
import MinModulus.SevenModOneTwenty.BlockUnit97
import MinModulus.SevenModOneTwenty.BlockUnit98
import MinModulus.SevenModOneTwenty.BlockUnit99
import MinModulus.SevenModOneTwenty.NodeUnit5_11
import MinModulus.SevenModOneTwenty.NodeUnit5_13
import MinModulus.SevenModOneTwenty.NodeUnit5_7
import MinModulus.SevenModOneTwenty.NodeUnit5_8

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_5_closed : ClosedMinimalPrefix true 120 5 4 [0,1,5] 6 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,6] 7 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_5_7_closed
  · exact unit_5_8_closed
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,9] 10 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,10] 11 (.stop (.collision 200)) (by decide +kernel))
  · exact unit_5_11_closed
  · exact unit_5_12_closed
  · exact unit_5_13_closed
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,14] 15 (.stop (.collision 256)) (by decide +kernel))
  · exact unit_5_15_closed
  · exact unit_5_16_closed
  · exact unit_5_17_closed
  · exact unit_5_18_closed
  · exact unit_5_19_closed
  · exact unit_5_20_closed
  · exact unit_5_21_closed
  · exact unit_5_22_closed
  · exact unit_5_23_closed
  · exact unit_5_24_closed
  · exact unit_5_25_closed
  · exact unit_5_26_closed
  · exact unit_5_27_closed
  · exact unit_5_28_closed
  · exact unit_5_29_closed
  · exact unit_5_30_closed
  · exact unit_5_31_closed
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,32] 33 (.stop (.third 1 3 2 31)) (by decide +kernel))
  · exact unit_5_33_closed
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,34] 35 (.stop (.third 2 3 1 29)) (by decide +kernel))
  · exact unit_5_35_closed
  · exact unit_5_36_closed
  · exact unit_5_37_closed
  · exact unit_5_38_closed
  · exact unit_5_39_closed
  · exact unit_5_40_closed
  · exact unit_5_41_closed
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,42] 43 (.stop (.collision 2048)) (by decide +kernel))
  · exact unit_5_43_closed
  · exact unit_5_44_closed
  · exact unit_5_45_closed
  · exact unit_5_46_closed
  · exact unit_5_47_closed
  · exact unit_5_48_closed
  · exact unit_5_49_closed
  · exact unit_5_50_closed
  · exact unit_5_51_closed
  · exact unit_5_52_closed
  · exact unit_5_53_closed
  · exact unit_5_54_closed
  · exact unit_5_55_closed
  · exact unit_5_56_closed
  · exact unit_5_57_closed
  · exact unit_5_58_closed
  · exact unit_5_59_closed
  · exact unit_5_60_closed
  · exact unit_5_61_closed
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,62] 63 (.stop (.third 1 3 2 61)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,63] 64 (.stop (.collision 1537)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,64] 65 (.stop (.third 2 3 1 59)) (by decide +kernel))
  · exact unit_5_65_closed
  · exact unit_5_66_closed
  · exact unit_5_67_closed
  · exact unit_5_68_closed
  · exact unit_5_69_closed
  · exact unit_5_70_closed
  · exact unit_5_71_closed
  · exact unit_5_72_closed
  · exact unit_5_73_closed
  · exact unit_5_74_closed
  · exact unit_5_75_closed
  · exact unit_5_76_closed
  · exact unit_5_77_closed
  · exact unit_5_78_closed
  · exact unit_5_79_closed
  · exact unit_5_80_closed
  · exact unit_5_81_closed
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,82] 83 (.stop (.collision 2048)) (by decide +kernel))
  · exact unit_5_83_closed
  · exact unit_5_84_closed
  · exact unit_5_85_closed
  · exact unit_5_86_closed
  · exact unit_5_87_closed
  · exact unit_5_88_closed
  · exact unit_5_89_closed
  · exact unit_5_90_closed
  · exact unit_5_91_closed
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,92] 93 (.stop (.third 1 3 2 91)) (by decide +kernel))
  · exact unit_5_93_closed
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,94] 95 (.stop (.third 2 3 1 89)) (by decide +kernel))
  · exact unit_5_95_closed
  · exact unit_5_96_closed
  · exact unit_5_97_closed
  · exact unit_5_98_closed
  · exact unit_5_99_closed
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,100] 101 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 8833),.stop (.third 3 5 1 103),.stop (.collision 102528),.stop (.collision 98944),.stop (.collision 102472),.stop (.collision 98888),.stop (.collision 102416),.stop (.collision 98832),.stop (.third 1 5 3 17),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.third 3 4 1 103),.stop (.collision 12416),.stop (.collision 1216),.stop (.collision 12360),.branch [.stop (.collision 8784),.stop (.collision 16456),.stop (.third 1 5 3 17),.stop (.collision 8833),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12304),.stop (.collision 12290),.stop (.third 1 4 3 17),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,101] 102 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 12417),.stop (.collision 5312),.stop (.collision 102465),.stop (.collision 98881),.stop (.collision 102409),.stop (.third 2 5 4 109),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.branch [.stop (.collision 8784),.stop (.collision 5312),.stop (.collision 102465),.stop (.collision 8833),.stop (.collision 73800),.stop (.collision 98888),.stop (.third 3 4 5 103),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.collision 8784),.stop (.collision 102465),.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 8840),.stop (.collision 98881),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 1216),.stop (.collision 12353),.branch [.stop (.collision 8784),.stop (.collision 73737),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12297),.stop (.collision 16448),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,102] 103 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 98944),.stop (.third 4 5 2 103),.stop (.collision 98888),.stop (.collision 8896),.stop (.collision 73856),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.collision 12416),.branch [.stop (.collision 102472),.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 8833),.stop (.collision 98888),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12360),.branch [.stop (.collision 8784),.stop (.collision 98944),.stop (.collision 73737),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12304),.stop (.collision 12290),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,103] 104 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 12417),.stop (.collision 102465),.stop (.collision 98881),.stop (.third 2 5 3 109),.stop (.collision 98825),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.branch [.stop (.collision 8784),.stop (.collision 102465),.stop (.collision 73800),.stop (.third 2 5 3 109),.stop (.collision 98888),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.collision 73800),.stop (.collision 73793),.stop (.third 2 5 3 109),.stop (.collision 8833),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12353),.branch [.stop (.third 2 5 3 109),.stop (.collision 73737),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 2 4 3 109),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,104] 105 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 8833),.stop (.third 3 5 2 103),.stop (.collision 102472),.stop (.third 0 5 4 17),.stop (.collision 73856),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 12416),.stop (.third 3 4 2 103),.stop (.collision 12360),.stop (.collision 1216),.stop (.collision 12304),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,105] 106 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 102465),.stop (.third 1 5 4 17),.stop (.collision 102409),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.branch [.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 102409),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12353),.stop (.collision 1216),.stop (.collision 12297),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,106] 107 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 8833),.stop (.third 0 5 3 17),.stop (.collision 98888),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.third 0 4 3 17),.stop (.collision 516),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,107] 108 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 8833),.stop (.third 1 5 3 17),.stop (.collision 98881),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.third 1 4 3 17),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,108] 109 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 102472),.stop (.collision 98888),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 12360),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,109] 110 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 5256),.stop (.collision 102465),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 12353),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,110] 111 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 102472),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12416),.stop (.collision 1153),.stop (.collision 12360),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,111] 112 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.collision 5249),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,112] 113 (.branch [.stop (.collision 1104),.stop (.collision 12416),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,113] 114 (.branch [.stop (.collision 1104),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,114] 115 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,115] 116 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,116] 117 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 5 3 [0,1,5,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

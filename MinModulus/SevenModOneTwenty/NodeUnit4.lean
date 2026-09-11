import MinModulus.SevenModOneTwenty.BlockUnit56
import MinModulus.SevenModOneTwenty.BlockUnit57
import MinModulus.SevenModOneTwenty.BlockUnit58
import MinModulus.SevenModOneTwenty.BlockUnit60
import MinModulus.SevenModOneTwenty.BlockUnit61
import MinModulus.SevenModOneTwenty.BlockUnit62
import MinModulus.SevenModOneTwenty.BlockUnit63
import MinModulus.SevenModOneTwenty.BlockUnit64
import MinModulus.SevenModOneTwenty.BlockUnit65
import MinModulus.SevenModOneTwenty.BlockUnit66
import MinModulus.SevenModOneTwenty.BlockUnit67
import MinModulus.SevenModOneTwenty.BlockUnit68
import MinModulus.SevenModOneTwenty.BlockUnit69
import MinModulus.SevenModOneTwenty.BlockUnit70
import MinModulus.SevenModOneTwenty.BlockUnit71
import MinModulus.SevenModOneTwenty.BlockUnit72
import MinModulus.SevenModOneTwenty.BlockUnit73
import MinModulus.SevenModOneTwenty.BlockUnit74
import MinModulus.SevenModOneTwenty.BlockUnit75
import MinModulus.SevenModOneTwenty.BlockUnit76
import MinModulus.SevenModOneTwenty.BlockUnit77
import MinModulus.SevenModOneTwenty.BlockUnit78
import MinModulus.SevenModOneTwenty.BlockUnit79
import MinModulus.SevenModOneTwenty.BlockUnit80
import MinModulus.SevenModOneTwenty.BlockUnit81
import MinModulus.SevenModOneTwenty.BlockUnit82
import MinModulus.SevenModOneTwenty.BlockUnit83
import MinModulus.SevenModOneTwenty.NodeUnit4_10
import MinModulus.SevenModOneTwenty.NodeUnit4_12
import MinModulus.SevenModOneTwenty.NodeUnit4_16
import MinModulus.SevenModOneTwenty.NodeUnit4_6
import MinModulus.SevenModOneTwenty.NodeUnit4_9

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_4_closed : ClosedMinimalPrefix true 120 4 4 [0,1,4] 5 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,5] 6 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_4_6_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,7] 8 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,8] 9 (.stop (.collision 200)) (by decide +kernel))
  · exact unit_4_9_closed
  · exact unit_4_10_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,11] 12 (.stop (.collision 256)) (by decide +kernel))
  · exact unit_4_12_closed
  · exact unit_4_13_closed
  · exact unit_4_14_closed
  · exact unit_4_15_closed
  · exact unit_4_16_closed
  · exact unit_4_17_closed
  · exact unit_4_18_closed
  · exact unit_4_19_closed
  · exact unit_4_20_closed
  · exact unit_4_21_closed
  · exact unit_4_22_closed
  · exact unit_4_23_closed
  · exact unit_4_24_closed
  · exact unit_4_25_closed
  · exact unit_4_26_closed
  · exact unit_4_27_closed
  · exact unit_4_28_closed
  · exact unit_4_29_closed
  · exact unit_4_30_closed
  · exact unit_4_31_closed
  · exact unit_4_32_closed
  · exact unit_4_33_closed
  · exact unit_4_34_closed
  · exact unit_4_35_closed
  · exact unit_4_36_closed
  · exact unit_4_37_closed
  · exact unit_4_38_closed
  · exact unit_4_39_closed
  · exact unit_4_40_closed
  · exact unit_4_41_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,42] 43 (.stop (.third 1 3 2 41)) (by decide +kernel))
  · exact unit_4_43_closed
  · exact unit_4_44_closed
  · exact unit_4_45_closed
  · exact unit_4_46_closed
  · exact unit_4_47_closed
  · exact unit_4_48_closed
  · exact unit_4_49_closed
  · exact unit_4_50_closed
  · exact unit_4_51_closed
  · exact unit_4_52_closed
  · exact unit_4_53_closed
  · exact unit_4_54_closed
  · exact unit_4_55_closed
  · exact unit_4_56_closed
  · exact unit_4_57_closed
  · exact unit_4_58_closed
  · exact unit_4_59_closed
  · exact unit_4_60_closed
  · exact unit_4_61_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,62] 63 (.stop (.collision 1544)) (by decide +kernel))
  · exact unit_4_63_closed
  · exact unit_4_64_closed
  · exact unit_4_65_closed
  · exact unit_4_66_closed
  · exact unit_4_67_closed
  · exact unit_4_68_closed
  · exact unit_4_69_closed
  · exact unit_4_70_closed
  · exact unit_4_71_closed
  · exact unit_4_72_closed
  · exact unit_4_73_closed
  · exact unit_4_74_closed
  · exact unit_4_75_closed
  · exact unit_4_76_closed
  · exact unit_4_77_closed
  · exact unit_4_78_closed
  · exact unit_4_79_closed
  · exact unit_4_80_closed
  · exact unit_4_81_closed
  · exact unit_4_82_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,83] 84 (.stop (.third 2 3 1 79)) (by decide +kernel))
  · exact unit_4_84_closed
  · exact unit_4_85_closed
  · exact unit_4_86_closed
  · exact unit_4_87_closed
  · exact unit_4_88_closed
  · exact unit_4_89_closed
  · exact unit_4_90_closed
  · exact unit_4_91_closed
  · exact unit_4_92_closed
  · exact unit_4_93_closed
  · exact unit_4_94_closed
  · exact unit_4_95_closed
  · exact unit_4_96_closed
  · exact unit_4_97_closed
  · exact unit_4_98_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,99] 100 (.branch [.stop (.collision 1104),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.branch [.stop (.third 3 5 0 103),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.third 1 5 3 109),.stop (.collision 12361),.stop (.collision 8896),.stop (.third 0 5 3 17),.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 3 4 0 103),.branch [.stop (.collision 8784),.stop (.collision 73856),.stop (.third 1 5 3 109),.stop (.collision 8840),.stop (.collision 73800),.stop (.third 0 5 3 17),.stop (.third 1 5 4 17),.stop (.collision 12361),.stop (.collision 73737),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12416),.branch [.stop (.third 1 5 3 109),.stop (.collision 73793),.stop (.collision 8833),.stop (.third 0 5 3 17),.stop (.collision 73737),.stop (.collision 98881),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 1 4 3 109),.stop (.collision 12304),.stop (.collision 12290),.stop (.third 0 4 3 17),.branch [.stop (.collision 8784),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 516),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,100] 101 (.branch [.stop (.collision 1104),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.branch [.stop (.third 3 5 1 103),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 102472),.stop (.collision 73856),.stop (.collision 102409),.stop (.third 0 5 4 17),.stop (.third 1 5 3 17),.stop (.collision 73793),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 3 4 1 103),.branch [.stop (.collision 8784),.stop (.collision 102472),.stop (.collision 8833),.stop (.collision 73800),.stop (.collision 73793),.stop (.third 1 5 3 17),.stop (.collision 8896),.stop (.collision 73737),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.collision 102472),.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 8840),.stop (.third 1 5 3 17),.stop (.collision 98881),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12360),.branch [.stop (.collision 8784),.stop (.collision 73737),.stop (.third 1 5 3 17),.stop (.collision 8840),.stop (.collision 98881),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12297),.branch [.stop (.third 1 5 3 17),.stop (.collision 77888),.stop (.collision 8833),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 1 4 3 17),.stop (.collision 16385),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,101] 102 (.branch [.stop (.collision 1104),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.branch [.stop (.collision 8784),.stop (.collision 102528),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 98944),.stop (.collision 12361),.stop (.third 1 5 4 17),.stop (.collision 73793),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 1216),.stop (.collision 12416),.branch [.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 98888),.stop (.collision 4619),.stop (.third 2 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12353),.stop (.collision 12304),.stop (.collision 12290),.stop (.collision 16448),.stop (.collision 16392),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,102] 103 (.branch [.stop (.collision 1104),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.branch [.stop (.collision 8784),.stop (.collision 131144),.stop (.collision 102472),.stop (.collision 8840),.stop (.third 2 5 3 109),.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 98825),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 1216),.branch [.stop (.collision 102472),.stop (.collision 73800),.stop (.third 2 5 3 109),.stop (.collision 8840),.stop (.collision 98888),.stop (.collision 73737),.stop (.third 2 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12360),.branch [.stop (.third 2 5 3 109),.stop (.collision 73737),.stop (.collision 8833),.stop (.collision 98888),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 2 4 3 109),.branch [.stop (.collision 8784),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 516),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,103] 104 (.branch [.stop (.collision 1104),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.branch [.stop (.third 3 5 2 103),.stop (.collision 73856),.stop (.collision 102465),.stop (.collision 8840),.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 4619),.stop (.third 2 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 3 4 2 103),.branch [.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 98881),.stop (.third 2 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12353),.stop (.collision 12304),.stop (.collision 12290),.stop (.collision 516),.stop (.collision 523),.stop (.third 2 4 3 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,104] 105 (.branch [.stop (.collision 1104),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.branch [.stop (.collision 8784),.stop (.collision 102472),.stop (.collision 8833),.stop (.collision 73800),.stop (.collision 98888),.stop (.collision 12361),.stop (.third 2 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 1216),.stop (.collision 12360),.branch [.stop (.collision 8784),.stop (.collision 73737),.stop (.collision 8833),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12297),.stop (.collision 16448),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,105] 106 (.branch [.stop (.collision 1104),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.collision 12416),.stop (.collision 1216),.stop (.collision 12353),.stop (.collision 12304),.stop (.collision 12290),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,106] 107 (.branch [.stop (.collision 1104),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.branch [.stop (.third 0 5 3 17),.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 98888),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 0 4 3 17),.branch [.stop (.collision 8784),.stop (.collision 73737),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12297),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,107] 108 (.branch [.stop (.collision 1104),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 12416),.branch [.stop (.third 1 5 3 17),.stop (.collision 73793),.stop (.collision 8833),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 1 4 3 17),.stop (.collision 12304),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,108] 109 (.branch [.stop (.collision 1104),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.collision 12360),.stop (.collision 1216),.stop (.collision 12297),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,109] 110 (.branch [.stop (.collision 1104),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.collision 12353),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,110] 111 (.branch [.stop (.collision 1104),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 12360),.stop (.collision 523),.stop (.third 2 4 3 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,111] 112 (.branch [.stop (.collision 1104),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 12353),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,112] 113 (.branch [.stop (.collision 1104),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 12360),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,113] 114 (.branch [.stop (.collision 1104),.stop (.collision 12416),.stop (.collision 1153),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,114] 115 (.branch [.stop (.collision 1104),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,115] 116 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,116] 117 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,117] 118 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 3 [0,1,4,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

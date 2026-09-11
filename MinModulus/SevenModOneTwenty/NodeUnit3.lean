import MinModulus.SevenModOneTwenty.BlockUnit10
import MinModulus.SevenModOneTwenty.BlockUnit13
import MinModulus.SevenModOneTwenty.BlockUnit15
import MinModulus.SevenModOneTwenty.BlockUnit17
import MinModulus.SevenModOneTwenty.BlockUnit18
import MinModulus.SevenModOneTwenty.BlockUnit19
import MinModulus.SevenModOneTwenty.BlockUnit20
import MinModulus.SevenModOneTwenty.BlockUnit21
import MinModulus.SevenModOneTwenty.BlockUnit22
import MinModulus.SevenModOneTwenty.BlockUnit23
import MinModulus.SevenModOneTwenty.BlockUnit24
import MinModulus.SevenModOneTwenty.BlockUnit25
import MinModulus.SevenModOneTwenty.BlockUnit26
import MinModulus.SevenModOneTwenty.BlockUnit27
import MinModulus.SevenModOneTwenty.BlockUnit28
import MinModulus.SevenModOneTwenty.BlockUnit29
import MinModulus.SevenModOneTwenty.BlockUnit30
import MinModulus.SevenModOneTwenty.BlockUnit31
import MinModulus.SevenModOneTwenty.BlockUnit32
import MinModulus.SevenModOneTwenty.BlockUnit33
import MinModulus.SevenModOneTwenty.BlockUnit34
import MinModulus.SevenModOneTwenty.BlockUnit35
import MinModulus.SevenModOneTwenty.BlockUnit36
import MinModulus.SevenModOneTwenty.BlockUnit37
import MinModulus.SevenModOneTwenty.BlockUnit38
import MinModulus.SevenModOneTwenty.BlockUnit39
import MinModulus.SevenModOneTwenty.BlockUnit40
import MinModulus.SevenModOneTwenty.BlockUnit41
import MinModulus.SevenModOneTwenty.BlockUnit42
import MinModulus.SevenModOneTwenty.BlockUnit43
import MinModulus.SevenModOneTwenty.BlockUnit44
import MinModulus.SevenModOneTwenty.BlockUnit45
import MinModulus.SevenModOneTwenty.BlockUnit46
import MinModulus.SevenModOneTwenty.BlockUnit47
import MinModulus.SevenModOneTwenty.BlockUnit48
import MinModulus.SevenModOneTwenty.NodeUnit3_10
import MinModulus.SevenModOneTwenty.NodeUnit3_11
import MinModulus.SevenModOneTwenty.NodeUnit3_12
import MinModulus.SevenModOneTwenty.NodeUnit3_13
import MinModulus.SevenModOneTwenty.NodeUnit3_15
import MinModulus.SevenModOneTwenty.NodeUnit3_17
import MinModulus.SevenModOneTwenty.NodeUnit3_19
import MinModulus.SevenModOneTwenty.NodeUnit3_7
import MinModulus.SevenModOneTwenty.NodeUnit3_9

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_3_closed : ClosedMinimalPrefix true 120 3 4 [0,1,3] 4 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,4] 5 (.stop (.collision 144)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,5] 6 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,6] 7 (.stop (.collision 200)) (by decide +kernel))
  · exact unit_3_7_closed
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,8] 9 (.stop (.collision 256)) (by decide +kernel))
  · exact unit_3_9_closed
  · exact unit_3_10_closed
  · exact unit_3_11_closed
  · exact unit_3_12_closed
  · exact unit_3_13_closed
  · exact unit_3_14_closed
  · exact unit_3_15_closed
  · exact unit_3_16_closed
  · exact unit_3_17_closed
  · exact unit_3_18_closed
  · exact unit_3_19_closed
  · exact unit_3_20_closed
  · exact unit_3_21_closed
  · exact unit_3_22_closed
  · exact unit_3_23_closed
  · exact unit_3_24_closed
  · exact unit_3_25_closed
  · exact unit_3_26_closed
  · exact unit_3_27_closed
  · exact unit_3_28_closed
  · exact unit_3_29_closed
  · exact unit_3_30_closed
  · exact unit_3_31_closed
  · exact unit_3_32_closed
  · exact unit_3_33_closed
  · exact unit_3_34_closed
  · exact unit_3_35_closed
  · exact unit_3_36_closed
  · exact unit_3_37_closed
  · exact unit_3_38_closed
  · exact unit_3_39_closed
  · exact unit_3_40_closed
  · exact unit_3_41_closed
  · exact unit_3_42_closed
  · exact unit_3_43_closed
  · exact unit_3_44_closed
  · exact unit_3_45_closed
  · exact unit_3_46_closed
  · exact unit_3_47_closed
  · exact unit_3_48_closed
  · exact unit_3_49_closed
  · exact unit_3_50_closed
  · exact unit_3_51_closed
  · exact unit_3_52_closed
  · exact unit_3_53_closed
  · exact unit_3_54_closed
  · exact unit_3_55_closed
  · exact unit_3_56_closed
  · exact unit_3_57_closed
  · exact unit_3_58_closed
  · exact unit_3_59_closed
  · exact unit_3_60_closed
  · exact unit_3_61_closed
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,62] 63 (.stop (.third 1 3 2 61)) (by decide +kernel))
  · exact unit_3_63_closed
  · exact unit_3_64_closed
  · exact unit_3_65_closed
  · exact unit_3_66_closed
  · exact unit_3_67_closed
  · exact unit_3_68_closed
  · exact unit_3_69_closed
  · exact unit_3_70_closed
  · exact unit_3_71_closed
  · exact unit_3_72_closed
  · exact unit_3_73_closed
  · exact unit_3_74_closed
  · exact unit_3_75_closed
  · exact unit_3_76_closed
  · exact unit_3_77_closed
  · exact unit_3_78_closed
  · exact unit_3_79_closed
  · exact unit_3_80_closed
  · exact unit_3_81_closed
  · exact unit_3_82_closed
  · exact unit_3_83_closed
  · exact unit_3_84_closed
  · exact unit_3_85_closed
  · exact unit_3_86_closed
  · exact unit_3_87_closed
  · exact unit_3_88_closed
  · exact unit_3_89_closed
  · exact unit_3_90_closed
  · exact unit_3_91_closed
  · exact unit_3_92_closed
  · exact unit_3_93_closed
  · exact unit_3_94_closed
  · exact unit_3_95_closed
  · exact unit_3_96_closed
  · exact unit_3_97_closed
  · exact unit_3_98_closed
  · exact unit_3_99_closed
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,100] 101 (.branch [.stop (.collision 1104),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.collision 1216),.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 102472),.stop (.collision 8896),.stop (.collision 12361),.stop (.third 0 5 4 17),.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 73744),.stop (.collision 73737),.stop (.collision 70272),.stop (.third 1 0 5 119)],.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 102472),.stop (.collision 73856),.stop (.collision 8896),.stop (.collision 73800),.stop (.third 1 5 4 17),.stop (.collision 98825),.stop (.collision 73737),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119)],.branch [.stop (.collision 8784),.stop (.collision 102472),.stop (.collision 8840),.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 98888),.stop (.collision 73737),.stop (.collision 12361),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119)],.stop (.collision 12416),.stop (.collision 12360),.stop (.collision 12304),.stop (.collision 12290),.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 98881),.stop (.collision 70272),.stop (.third 1 0 5 119)],.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 98888),.stop (.collision 70272),.stop (.third 1 0 5 119)],.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 70272),.stop (.third 1 0 5 119)],.stop (.collision 516),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,101] 102 (.branch [.stop (.collision 1104),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.collision 1216),.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 102465),.stop (.third 2 5 3 109),.stop (.collision 12361),.stop (.third 1 5 4 17),.stop (.collision 73793),.stop (.collision 131648),.stop (.collision 73737),.stop (.collision 70272),.stop (.third 1 0 5 119)],.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.third 2 5 3 109),.stop (.collision 73800),.stop (.collision 98888),.stop (.third 3 4 5 103),.stop (.collision 73737),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119)],.branch [.stop (.collision 8784),.stop (.collision 102465),.stop (.third 2 5 3 109),.stop (.collision 73793),.stop (.collision 135232),.stop (.collision 98881),.stop (.third 2 5 4 17),.stop (.collision 12361),.stop (.collision 70272),.stop (.third 1 0 5 119)],.branch [.stop (.collision 73800),.stop (.third 2 5 3 109),.stop (.collision 8840),.stop (.collision 73737),.stop (.collision 98888),.stop (.collision 106560),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119)],.stop (.collision 12353),.stop (.third 2 4 3 109),.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 98881),.stop (.collision 70272),.stop (.third 1 0 5 119)],.stop (.collision 16448),.stop (.collision 16385),.stop (.collision 516),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,102] 103 (.branch [.stop (.collision 1104),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.collision 1216),.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 102472),.stop (.collision 73856),.stop (.collision 98944),.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 73744),.stop (.collision 73737),.stop (.collision 70272),.stop (.third 1 0 5 119)],.branch [.stop (.collision 8784),.stop (.collision 102472),.stop (.collision 8840),.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 98881),.stop (.third 2 5 4 17),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119)],.stop (.collision 12416),.stop (.collision 12360),.stop (.collision 12304),.stop (.collision 12290),.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 98888),.stop (.collision 70272),.stop (.third 1 0 5 119)],.stop (.collision 16392),.stop (.collision 516),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,103] 104 (.branch [.stop (.collision 1104),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.collision 1216),.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 102409),.stop (.collision 73800),.stop (.collision 73793),.stop (.third 2 5 4 17),.stop (.collision 73737),.stop (.collision 70272),.stop (.third 1 0 5 119)],.branch [.stop (.collision 8784),.stop (.collision 102465),.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 98888),.stop (.collision 73737),.stop (.third 3 4 5 103),.stop (.collision 70272),.stop (.third 1 0 5 119)],.branch [.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 8840),.stop (.collision 73737),.stop (.collision 98881),.stop (.collision 98825),.stop (.collision 70272),.stop (.third 1 0 5 119)],.stop (.collision 12353),.stop (.collision 12297),.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 98888),.stop (.collision 70272),.stop (.third 1 0 5 119)],.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 70272),.stop (.third 1 0 5 119)],.stop (.collision 516),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,104] 105 (.branch [.stop (.collision 1104),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.collision 1216),.branch [.stop (.collision 8784),.stop (.collision 102472),.stop (.collision 8840),.stop (.collision 73800),.stop (.collision 98888),.stop (.collision 12361),.stop (.collision 73737),.stop (.collision 70272),.stop (.third 1 0 5 119)],.stop (.collision 12416),.stop (.collision 12360),.stop (.collision 12304),.stop (.collision 12290),.stop (.collision 16448),.stop (.collision 16385),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,105] 106 (.branch [.stop (.collision 1104),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.collision 1216),.branch [.stop (.collision 8784),.stop (.collision 102465),.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 98881),.stop (.collision 73737),.stop (.collision 70272),.stop (.third 1 0 5 119)],.branch [.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 8840),.stop (.collision 98888),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119)],.stop (.collision 12353),.stop (.collision 12297),.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 70272),.stop (.third 1 0 5 119)],.stop (.collision 16392),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,106] 107 (.branch [.stop (.collision 1104),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.collision 1216),.stop (.collision 12416),.stop (.third 0 4 3 17),.stop (.collision 12304),.stop (.collision 12290),.stop (.collision 516),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,107] 108 (.branch [.stop (.collision 1104),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.collision 1216),.branch [.stop (.third 1 5 3 17),.stop (.collision 73793),.stop (.collision 8840),.stop (.collision 98881),.stop (.collision 70272),.stop (.third 1 0 5 119)],.stop (.third 1 4 3 17),.stop (.collision 12297),.stop (.collision 16448),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,108] 109 (.branch [.stop (.collision 1104),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.collision 12416),.stop (.collision 12360),.stop (.collision 12304),.stop (.collision 12290),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,109] 110 (.branch [.stop (.collision 1104),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.collision 1216),.stop (.collision 12353),.stop (.third 2 4 3 17),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,110] 111 (.branch [.stop (.collision 1104),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 12416),.stop (.collision 12360),.stop (.collision 12304),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,111] 112 (.branch [.stop (.collision 1104),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 8195),.stop (.collision 12353),.stop (.collision 12297),.stop (.collision 8832),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,112] 113 (.branch [.stop (.collision 1104),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 12360),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,113] 114 (.branch [.stop (.collision 1104),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 12353),.stop (.collision 8832),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,114] 115 (.branch [.stop (.collision 1104),.stop (.collision 1153),.stop (.collision 12360),.stop (.collision 8832),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,115] 116 (.branch [.stop (.collision 1104),.stop (.collision 1153),.stop (.collision 8832),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,116] 117 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,117] 118 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,118] 119 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 3 [0,1,3,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

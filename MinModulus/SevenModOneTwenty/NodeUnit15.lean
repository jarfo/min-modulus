import MinModulus.SevenModOneTwenty.BlockUnit223
import MinModulus.SevenModOneTwenty.BlockUnit224
import MinModulus.SevenModOneTwenty.BlockUnit225
import MinModulus.SevenModOneTwenty.BlockUnit226
import MinModulus.SevenModOneTwenty.BlockUnit227
import MinModulus.SevenModOneTwenty.BlockUnit228
import MinModulus.SevenModOneTwenty.BlockUnit229
import MinModulus.SevenModOneTwenty.BlockUnit230
import MinModulus.SevenModOneTwenty.BlockUnit231

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_15_closed : ClosedMinimalPrefix true 120 15 4 [0,1,15] 16 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,16] 17 (.stop (.collision 144)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,17] 18 (.stop (.third 3 0 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,18] 19 (.stop (.third 1 3 0 113)) (by decide +kernel))
  · exact unit_15_19_closed
  · exact unit_15_20_closed
  · exact unit_15_21_closed
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,22] 23 (.stop (.third 3 2 1 17)) (by decide +kernel))
  · exact unit_15_23_closed
  · exact unit_15_24_closed
  · exact unit_15_25_closed
  · exact unit_15_26_closed
  · exact unit_15_27_closed
  · exact unit_15_28_closed
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,29] 30 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,30] 31 (.stop (.collision 200)) (by decide +kernel))
  · exact unit_15_31_closed
  · exact unit_15_32_closed
  · exact unit_15_33_closed
  · exact unit_15_34_closed
  · exact unit_15_35_closed
  · exact unit_15_36_closed
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,37] 38 (.stop (.third 0 3 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,38] 39 (.stop (.third 3 1 0 107)) (by decide +kernel))
  · exact unit_15_39_closed
  · exact unit_15_40_closed
  · exact unit_15_41_closed
  · exact unit_15_42_closed
  · exact unit_15_43_closed
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,44] 45 (.stop (.collision 256)) (by decide +kernel))
  · exact unit_15_45_closed
  · exact unit_15_46_closed
  · exact unit_15_47_closed
  · exact unit_15_48_closed
  · exact unit_15_49_closed
  · exact unit_15_50_closed
  · exact unit_15_51_closed
  · exact unit_15_52_closed
  · exact unit_15_53_closed
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,54] 55 (.stop (.third 3 1 2 43)) (by decide +kernel))
  · exact unit_15_55_closed
  · exact unit_15_56_closed
  · exact unit_15_57_closed
  · exact unit_15_58_closed
  · exact unit_15_59_closed
  · exact unit_15_60_closed
  · exact unit_15_61_closed
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,62] 63 (.stop (.third 1 3 2 61)) (by decide +kernel))
  · exact unit_15_63_closed
  · exact unit_15_64_closed
  · exact unit_15_65_closed
  · exact unit_15_66_closed
  · exact unit_15_67_closed
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,68] 69 (.stop (.third 1 3 2 43)) (by decide +kernel))
  · exact unit_15_69_closed
  · exact unit_15_70_closed
  · exact unit_15_71_closed
  · exact unit_15_72_closed
  · exact unit_15_73_closed
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,74] 75 (.stop (.third 2 3 1 59)) (by decide +kernel))
  · exact unit_15_75_closed
  · exact unit_15_76_closed
  · exact unit_15_77_closed
  · exact unit_15_78_closed
  · exact unit_15_79_closed
  · exact unit_15_80_closed
  · exact unit_15_81_closed
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,82] 83 (.stop (.third 3 2 1 77)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,83] 84 (.stop (.third 3 0 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,84] 85 (.stop (.third 1 3 0 107)) (by decide +kernel))
  · exact unit_15_85_closed
  · exact unit_15_86_closed
  · exact unit_15_87_closed
  · exact unit_15_88_closed
  · exact unit_15_89_closed
  · exact unit_15_90_closed
  · exact unit_15_91_closed
  · exact unit_15_92_closed
  · exact unit_15_93_closed
  · exact unit_15_94_closed
  · exact unit_15_95_closed
  · exact unit_15_96_closed
  · exact unit_15_97_closed
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,98] 99 (.branch [.stop (.third 3 2 4 13),.branch [.stop (.third 5 4 3 119),.stop (.collision 12361),.stop (.third 0 5 1 7),.stop (.third 2 5 4 89),.stop (.collision 4619),.stop (.third 5 2 3 29),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 3 109),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.third 0 5 1 7),.stop (.third 5 1 0 113),.stop (.collision 4619),.stop (.third 5 2 3 29),.stop (.third 0 4 5 101),.stop (.third 1 0 5 119),.stop (.third 0 5 3 109),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 4 5 101),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12416),.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.stop (.collision 523),.stop (.third 4 2 3 29),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 109),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,99] 100 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 4 3 119),.stop (.third 0 5 1 7),.stop (.third 5 1 0 113),.stop (.collision 4619),.stop (.third 3 5 0 103),.stop (.third 0 4 5 101),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 4 5 101),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 0 5 1 7),.stop (.third 5 1 0 113),.stop (.collision 12361),.stop (.third 3 5 0 103),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.stop (.collision 523),.stop (.third 3 4 0 103),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,100] 101 (.branch [.stop (.collision 1104),.branch [.stop (.third 0 5 1 7),.stop (.third 2 5 3 89),.stop (.collision 4619),.stop (.third 5 2 4 29),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 0 4 1 7),.stop (.third 2 4 3 89),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,101] 102 (.branch [.stop (.collision 1104),.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.stop (.collision 523),.stop (.collision 8832),.stop (.third 0 3 4 101),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 101),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,102] 103 (.branch [.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.stop (.collision 523),.stop (.third 4 2 3 29),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,104] 105 (.stop (.third 3 1 0 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,105] 106 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,106] 107 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,107] 108 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,108] 109 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,109] 110 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,110] 111 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,111] 112 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,112] 113 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,113] 114 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,114] 115 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 15 3 [0,1,15,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

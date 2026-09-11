import MinModulus.SevenModOneTwenty.BlockUnit232
import MinModulus.SevenModOneTwenty.BlockUnit233
import MinModulus.SevenModOneTwenty.BlockUnit234
import MinModulus.SevenModOneTwenty.BlockUnit235
import MinModulus.SevenModOneTwenty.BlockUnit236
import MinModulus.SevenModOneTwenty.BlockUnit237
import MinModulus.SevenModOneTwenty.BlockUnit238

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_16_closed : ClosedMinimalPrefix true 120 16 4 [0,1,16] 17 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,17] 18 (.stop (.third 0 3 2 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,18] 19 (.stop (.third 1 3 0 113)) (by decide +kernel))
  · exact unit_16_19_closed
  · exact unit_16_20_closed
  · exact unit_16_21_closed
  · exact unit_16_22_closed
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,23] 24 (.stop (.third 2 3 1 103)) (by decide +kernel))
  · exact unit_16_24_closed
  · exact unit_16_25_closed
  · exact unit_16_26_closed
  · exact unit_16_27_closed
  · exact unit_16_28_closed
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,29] 30 (.stop (.third 2 3 0 37)) (by decide +kernel))
  · exact unit_16_30_closed
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,31] 32 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,32] 33 (.stop (.collision 200)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,33] 34 (.stop (.third 3 2 0 7)) (by decide +kernel))
  · exact unit_16_34_closed
  · exact unit_16_35_closed
  · exact unit_16_36_closed
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,37] 38 (.stop (.third 0 3 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,38] 39 (.stop (.third 3 1 0 107)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,39] 40 (.stop (.third 2 3 1 47)) (by decide +kernel))
  · exact unit_16_40_closed
  · exact unit_16_41_closed
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,42] 43 (.stop (.third 1 3 2 41)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,43] 44 (.stop (.third 3 0 2 53)) (by decide +kernel))
  · exact unit_16_44_closed
  · exact unit_16_45_closed
  · exact unit_16_46_closed
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,47] 48 (.stop (.third 0 3 2 23)) (by decide +kernel))
  · exact unit_16_48_closed
  · exact unit_16_49_closed
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,50] 51 (.stop (.third 1 3 2 49)) (by decide +kernel))
  · exact unit_16_51_closed
  · exact unit_16_52_closed
  · exact unit_16_53_closed
  · exact unit_16_54_closed
  · exact unit_16_55_closed
  · exact unit_16_56_closed
  · exact unit_16_57_closed
  · exact unit_16_58_closed
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,59] 60 (.stop (.third 2 3 0 67)) (by decide +kernel))
  · exact unit_16_60_closed
  · exact unit_16_61_closed
  · exact unit_16_62_closed
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,63] 64 (.stop (.third 2 3 1 23)) (by decide +kernel))
  · exact unit_16_64_closed
  · exact unit_16_65_closed
  · exact unit_16_66_closed
  · exact unit_16_67_closed
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,68] 69 (.stop (.collision 1544)) (by decide +kernel))
  · exact unit_16_69_closed
  · exact unit_16_70_closed
  · exact unit_16_71_closed
  · exact unit_16_72_closed
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,73] 74 (.stop (.third 3 0 2 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,74] 75 (.stop (.third 1 3 2 97)) (by decide +kernel))
  · exact unit_16_75_closed
  · exact unit_16_76_closed
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,77] 78 (.stop (.third 0 3 2 53)) (by decide +kernel))
  · exact unit_16_78_closed
  · exact unit_16_79_closed
  · exact unit_16_80_closed
  · exact unit_16_81_closed
  · exact unit_16_82_closed
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,83] 84 (.stop (.third 3 0 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,84] 85 (.stop (.third 1 3 0 107)) (by decide +kernel))
  · exact unit_16_85_closed
  · exact unit_16_86_closed
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,87] 88 (.stop (.third 2 3 1 71)) (by decide +kernel))
  · exact unit_16_88_closed
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,89] 90 (.stop (.third 2 3 0 97)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,90] 91 (.stop (.third 1 3 2 89)) (by decide +kernel))
  · exact unit_16_91_closed
  · exact unit_16_92_closed
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,93] 94 (.stop (.third 3 2 0 67)) (by decide +kernel))
  · exact unit_16_94_closed
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,95] 96 (.stop (.third 2 3 1 79)) (by decide +kernel))
  · exact unit_16_96_closed
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,97] 98 (.branch [.stop (.third 1 4 2 73),.branch [.stop (.third 4 2 5 13),.stop (.collision 12361),.stop (.third 0 3 5 73),.stop (.third 0 5 1 7),.stop (.third 5 1 0 113),.stop (.third 2 5 3 89),.stop (.third 1 0 5 119),.stop (.third 0 3 5 73),.stop (.third 1 0 5 119),.stop (.third 0 5 3 109),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 5 4 3 119),.stop (.third 0 3 5 73),.stop (.third 0 5 1 7),.stop (.third 5 1 0 113),.stop (.third 2 5 3 89),.stop (.third 1 0 5 119),.stop (.third 0 3 5 73),.stop (.third 1 0 5 119),.stop (.third 0 5 3 109),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12416),.stop (.third 0 3 4 73),.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.stop (.third 2 4 3 89),.stop (.third 1 0 4 119),.stop (.third 0 3 4 73),.stop (.third 1 0 4 119),.stop (.third 0 4 3 109),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,98] 99 (.stop (.third 1 3 2 73)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,99] 100 (.branch [.stop (.third 3 2 4 13),.branch [.stop (.third 5 4 3 119),.stop (.third 0 5 1 7),.stop (.third 5 1 0 113),.stop (.third 2 5 4 89),.stop (.third 1 0 5 119),.stop (.third 0 4 5 101),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 4 5 101),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 12416),.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 0 4 2 83),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,100] 101 (.branch [.stop (.collision 1104),.branch [.stop (.third 0 5 1 7),.stop (.third 5 1 0 113),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 0 5 2 83),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 0 4 2 83),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,101] 102 (.branch [.stop (.collision 1104),.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.stop (.third 2 4 3 89),.stop (.third 1 0 4 119),.stop (.third 0 3 4 101),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 101),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,102] 103 (.branch [.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 0 4 2 83),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,104] 105 (.stop (.third 3 1 0 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,105] 106 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,106] 107 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,107] 108 (.stop (.third 0 3 2 83)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,108] 109 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,109] 110 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,110] 111 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,111] 112 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,112] 113 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,113] 114 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,114] 115 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 16 3 [0,1,16,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

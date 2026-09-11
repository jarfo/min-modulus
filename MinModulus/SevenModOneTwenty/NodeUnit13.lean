import MinModulus.SevenModOneTwenty.BlockUnit211
import MinModulus.SevenModOneTwenty.BlockUnit212
import MinModulus.SevenModOneTwenty.BlockUnit213
import MinModulus.SevenModOneTwenty.BlockUnit214
import MinModulus.SevenModOneTwenty.BlockUnit215
import MinModulus.SevenModOneTwenty.BlockUnit216
import MinModulus.SevenModOneTwenty.BlockUnit217

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_13_closed : ClosedMinimalPrefix true 120 13 4 [0,1,13] 14 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,14] 15 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_13_15_closed
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,16] 17 (.stop (.third 2 0 3 83)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,17] 18 (.stop (.third 3 0 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,18] 19 (.stop (.third 1 3 0 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,19] 20 (.stop (.third 0 3 2 19)) (by decide +kernel))
  · exact unit_13_20_closed
  · exact unit_13_21_closed
  · exact unit_13_22_closed
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,23] 24 (.stop (.third 0 2 3 37)) (by decide +kernel))
  · exact unit_13_24_closed
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,25] 26 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,26] 27 (.stop (.third 0 2 3 37)) (by decide +kernel))
  · exact unit_13_27_closed
  · exact unit_13_28_closed
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,29] 30 (.stop (.third 2 0 3 83)) (by decide +kernel))
  · exact unit_13_30_closed
  · exact unit_13_31_closed
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,32] 33 (.stop (.third 1 3 2 31)) (by decide +kernel))
  · exact unit_13_33_closed
  · exact unit_13_34_closed
  · exact unit_13_35_closed
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,36] 37 (.stop (.third 0 2 3 37)) (by decide +kernel))
  · exact unit_13_37_closed
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,38] 39 (.stop (.collision 256)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,39] 40 (.stop (.third 0 2 3 37)) (by decide +kernel))
  · exact unit_13_40_closed
  · exact unit_13_41_closed
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,42] 43 (.stop (.third 1 3 2 41)) (by decide +kernel))
  · exact unit_13_43_closed
  · exact unit_13_44_closed
  · exact unit_13_45_closed
  · exact unit_13_46_closed
  · exact unit_13_47_closed
  · exact unit_13_48_closed
  · exact unit_13_49_closed
  · exact unit_13_50_closed
  · exact unit_13_51_closed
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,52] 53 (.stop (.third 0 2 3 37)) (by decide +kernel))
  · exact unit_13_53_closed
  · exact unit_13_54_closed
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,55] 56 (.stop (.third 2 0 3 83)) (by decide +kernel))
  · exact unit_13_56_closed
  · exact unit_13_57_closed
  · exact unit_13_58_closed
  · exact unit_13_59_closed
  · exact unit_13_60_closed
  · exact unit_13_61_closed
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,62] 63 (.stop (.third 1 3 2 61)) (by decide +kernel))
  · exact unit_13_63_closed
  · exact unit_13_64_closed
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,65] 66 (.stop (.third 0 2 3 37)) (by decide +kernel))
  · exact unit_13_66_closed
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,67] 68 (.stop (.collision 1537)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,68] 69 (.stop (.third 2 0 3 83)) (by decide +kernel))
  · exact unit_13_69_closed
  · exact unit_13_70_closed
  · exact unit_13_71_closed
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,72] 73 (.stop (.third 1 3 2 71)) (by decide +kernel))
  · exact unit_13_73_closed
  · exact unit_13_74_closed
  · exact unit_13_75_closed
  · exact unit_13_76_closed
  · exact unit_13_77_closed
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,78] 79 (.stop (.third 0 2 3 37)) (by decide +kernel))
  · exact unit_13_79_closed
  · exact unit_13_80_closed
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,81] 82 (.stop (.third 2 0 3 83)) (by decide +kernel))
  · exact unit_13_82_closed
  · exact unit_13_83_closed
  · exact unit_13_84_closed
  · exact unit_13_85_closed
  · exact unit_13_86_closed
  · exact unit_13_87_closed
  · exact unit_13_88_closed
  · exact unit_13_89_closed
  · exact unit_13_90_closed
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,91] 92 (.stop (.third 0 2 3 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,92] 93 (.stop (.third 1 3 2 91)) (by decide +kernel))
  · exact unit_13_93_closed
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,94] 95 (.stop (.third 2 0 3 83)) (by decide +kernel))
  · exact unit_13_95_closed
  · exact unit_13_96_closed
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,97] 98 (.stop (.third 2 0 3 83)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,98] 99 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 0 2 19),.stop (.third 1 5 2 101),.stop (.third 0 5 1 7),.stop (.third 0 2 5 37),.stop (.third 3 5 2 103),.stop (.collision 73856),.stop (.third 2 0 5 83),.stop (.third 1 3 5 73),.stop (.third 0 5 3 109),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 2 5 37),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 4 0 2 19),.stop (.third 1 4 2 101),.stop (.third 0 4 1 7),.stop (.third 0 2 4 37),.stop (.third 3 4 2 103),.stop (.collision 516),.stop (.third 2 0 4 83),.stop (.third 1 3 4 73),.stop (.third 0 4 3 109),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 2 4 37),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,99] 100 (.branch [.stop (.collision 1104),.stop (.third 4 0 2 19),.stop (.third 1 4 2 101),.stop (.third 0 4 1 7),.stop (.third 0 2 4 37),.branch [.stop (.third 3 5 0 103),.stop (.third 2 0 5 83),.stop (.third 5 1 4 37),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 2 5 37),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 3 4 0 103),.stop (.third 2 0 4 83),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 2 4 37),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,100] 101 (.branch [.stop (.third 4 0 2 19),.stop (.third 1 4 2 101),.stop (.third 0 4 1 7),.stop (.third 0 2 4 37),.branch [.stop (.third 5 4 3 119),.stop (.third 2 0 5 83),.stop (.third 5 1 4 37),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 2 5 37),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 516),.stop (.third 2 0 4 83),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 2 4 37),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,101] 102 (.stop (.third 3 0 2 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,102] 103 (.stop (.third 1 3 2 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,104] 105 (.stop (.third 0 2 3 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,105] 106 (.branch [.stop (.collision 1104),.stop (.third 2 0 4 83),.stop (.third 4 1 3 37),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 2 4 37),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,106] 107 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,107] 108 (.stop (.third 2 0 3 83)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,108] 109 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,109] 110 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,110] 111 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,111] 112 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,112] 113 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,113] 114 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,114] 115 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,117] 118 (.stop (.third 0 2 3 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 13 3 [0,1,13,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

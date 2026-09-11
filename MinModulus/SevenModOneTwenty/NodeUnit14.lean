import MinModulus.SevenModOneTwenty.BlockUnit218
import MinModulus.SevenModOneTwenty.BlockUnit219
import MinModulus.SevenModOneTwenty.BlockUnit220
import MinModulus.SevenModOneTwenty.BlockUnit221
import MinModulus.SevenModOneTwenty.BlockUnit222

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_14_closed : ClosedMinimalPrefix true 120 14 4 [0,1,14] 15 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,15] 16 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_14_16_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,17] 18 (.stop (.third 2 1 3 83)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,18] 19 (.stop (.third 1 3 0 113)) (by decide +kernel))
  · exact unit_14_19_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,20] 21 (.stop (.third 1 3 2 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,21] 22 (.stop (.third 3 2 0 17)) (by decide +kernel))
  · exact unit_14_22_closed
  · exact unit_14_23_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,24] 25 (.stop (.third 1 2 3 37)) (by decide +kernel))
  · exact unit_14_25_closed
  · exact unit_14_26_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,27] 28 (.stop (.third 1 2 3 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,28] 29 (.stop (.collision 200)) (by decide +kernel))
  · exact unit_14_29_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,30] 31 (.stop (.third 2 1 3 83)) (by decide +kernel))
  · exact unit_14_31_closed
  · exact unit_14_32_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,33] 34 (.stop (.third 3 2 1 101)) (by decide +kernel))
  · exact unit_14_34_closed
  · exact unit_14_35_closed
  · exact unit_14_36_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,37] 38 (.stop (.third 0 3 1 13)) (by decide +kernel))
  · exact unit_14_38_closed
  · exact unit_14_39_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,40] 41 (.stop (.third 1 2 3 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,41] 42 (.stop (.collision 256)) (by decide +kernel))
  · exact unit_14_42_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,43] 44 (.stop (.third 2 1 3 83)) (by decide +kernel))
  · exact unit_14_44_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,45] 46 (.stop (.collision 2048)) (by decide +kernel))
  · exact unit_14_46_closed
  · exact unit_14_47_closed
  · exact unit_14_48_closed
  · exact unit_14_49_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,50] 51 (.stop (.third 1 2 3 37)) (by decide +kernel))
  · exact unit_14_51_closed
  · exact unit_14_52_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,53] 54 (.stop (.third 1 2 3 37)) (by decide +kernel))
  · exact unit_14_54_closed
  · exact unit_14_55_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,56] 57 (.stop (.third 2 1 3 83)) (by decide +kernel))
  · exact unit_14_57_closed
  · exact unit_14_58_closed
  · exact unit_14_59_closed
  · exact unit_14_60_closed
  · exact unit_14_61_closed
  · exact unit_14_62_closed
  · exact unit_14_63_closed
  · exact unit_14_64_closed
  · exact unit_14_65_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,66] 67 (.stop (.third 1 2 3 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,67] 68 (.stop (.third 0 3 2 43)) (by decide +kernel))
  · exact unit_14_68_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,69] 70 (.stop (.third 2 1 3 83)) (by decide +kernel))
  · exact unit_14_70_closed
  · exact unit_14_71_closed
  · exact unit_14_72_closed
  · exact unit_14_73_closed
  · exact unit_14_74_closed
  · exact unit_14_75_closed
  · exact unit_14_76_closed
  · exact unit_14_77_closed
  · exact unit_14_78_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,79] 80 (.stop (.third 1 2 3 37)) (by decide +kernel))
  · exact unit_14_80_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,81] 82 (.stop (.third 3 2 0 77)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,82] 83 (.stop (.third 2 1 3 83)) (by decide +kernel))
  · exact unit_14_83_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,84] 85 (.stop (.third 1 3 0 107)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,85] 86 (.stop (.third 2 1 3 83)) (by decide +kernel))
  · exact unit_14_86_closed
  · exact unit_14_87_closed
  · exact unit_14_88_closed
  · exact unit_14_89_closed
  · exact unit_14_90_closed
  · exact unit_14_91_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,92] 93 (.stop (.third 1 2 3 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,93] 94 (.branch [.stop (.collision 1104),.stop (.third 2 1 4 83),.stop (.third 3 2 4 41),.branch [.stop (.third 2 1 5 83),.stop (.third 3 2 5 41),.stop (.third 3 5 1 103),.stop (.collision 12361),.stop (.third 0 4 5 73),.stop (.third 0 5 1 7),.stop (.third 5 1 0 113),.stop (.third 1 2 5 37),.stop (.third 2 4 5 107),.stop (.third 0 4 5 73),.stop (.third 1 0 5 119),.stop (.third 0 5 4 109),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 2 1 4 83),.stop (.third 3 2 4 41),.stop (.third 3 4 1 103),.branch [.stop (.third 3 2 5 41),.stop (.third 0 5 1 7),.stop (.third 5 1 0 113),.stop (.third 1 2 5 37),.stop (.collision 5249),.stop (.third 0 4 5 101),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 4 5 101),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 3 2 4 41),.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.stop (.third 1 2 4 37),.stop (.collision 1153),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact unit_14_94_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,95] 96 (.stop (.third 2 1 3 83)) (by decide +kernel))
  · exact unit_14_96_closed
  · exact unit_14_97_closed
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,98] 99 (.stop (.third 2 1 3 83)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,99] 100 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 1 2 19),.stop (.third 0 5 1 7),.stop (.third 5 1 0 113),.stop (.third 1 2 5 37),.stop (.third 3 5 0 103),.stop (.third 0 4 5 101),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 4 5 101),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 4 1 2 19),.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.stop (.third 1 2 4 37),.stop (.third 3 4 0 103),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,100] 101 (.branch [.stop (.collision 1104),.stop (.third 4 1 2 19),.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.stop (.third 1 2 4 37),.stop (.collision 523),.stop (.third 3 4 1 103),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,101] 102 (.branch [.stop (.third 4 1 2 19),.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.stop (.third 1 2 4 37),.stop (.collision 523),.stop (.third 0 3 4 101),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 101),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,102] 103 (.stop (.third 3 1 2 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,104] 105 (.stop (.third 3 1 0 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,105] 106 (.stop (.third 1 2 3 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,106] 107 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,107] 108 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,108] 109 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,109] 110 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,110] 111 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,111] 112 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,112] 113 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,113] 114 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,114] 115 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 14 3 [0,1,14,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

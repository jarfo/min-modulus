import MinModulus.SevenModOneTwenty.BlockUnit241
import MinModulus.SevenModOneTwenty.BlockUnit242
import MinModulus.SevenModOneTwenty.BlockUnit243
import MinModulus.SevenModOneTwenty.BlockUnit244

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_20_closed : ClosedMinimalPrefix true 120 20 4 [0,1,20] 21 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,21] 22 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_20_22_closed
  · exact unit_20_23_closed
  · exact unit_20_24_closed
  · exact unit_20_25_closed
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,26] 27 (.stop (.third 2 1 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,27] 28 (.stop (.third 1 2 3 19)) (by decide +kernel))
  · exact unit_20_28_closed
  · exact unit_20_29_closed
  · exact unit_20_30_closed
  · exact unit_20_31_closed
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,32] 33 (.stop (.third 2 1 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,33] 34 (.stop (.third 1 2 3 19)) (by decide +kernel))
  · exact unit_20_34_closed
  · exact unit_20_35_closed
  · exact unit_20_36_closed
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,37] 38 (.stop (.third 0 3 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,38] 39 (.stop (.third 1 3 2 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,39] 40 (.stop (.third 1 2 3 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,40] 41 (.stop (.collision 200)) (by decide +kernel))
  · exact unit_20_41_closed
  · exact unit_20_42_closed
  · exact unit_20_43_closed
  · exact unit_20_44_closed
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,45] 46 (.stop (.third 2 1 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,46] 47 (.stop (.third 1 2 3 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,47] 48 (.stop (.collision 2048)) (by decide +kernel))
  · exact unit_20_48_closed
  · exact unit_20_49_closed
  · exact unit_20_50_closed
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,51] 52 (.stop (.third 2 1 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,52] 53 (.stop (.third 1 2 3 19)) (by decide +kernel))
  · exact unit_20_53_closed
  · exact unit_20_54_closed
  · exact unit_20_55_closed
  · exact unit_20_56_closed
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,57] 58 (.stop (.third 2 1 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,58] 59 (.stop (.third 1 2 3 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,59] 60 (.stop (.collision 256)) (by decide +kernel))
  · exact unit_20_60_closed
  · exact unit_20_61_closed
  · exact unit_20_62_closed
  · exact unit_20_63_closed
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,64] 65 (.stop (.third 2 1 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,65] 66 (.stop (.third 1 2 3 19)) (by decide +kernel))
  · exact unit_20_66_closed
  · exact unit_20_67_closed
  · exact unit_20_68_closed
  · exact unit_20_69_closed
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,70] 71 (.stop (.third 2 1 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,71] 72 (.stop (.third 1 2 3 19)) (by decide +kernel))
  · exact unit_20_72_closed
  · exact unit_20_73_closed
  · exact unit_20_74_closed
  · exact unit_20_75_closed
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,76] 77 (.stop (.third 2 1 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,77] 78 (.stop (.third 1 2 3 19)) (by decide +kernel))
  · exact unit_20_78_closed
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,79] 80 (.branch [.stop (.collision 1104),.stop (.third 3 2 4 61),.stop (.third 3 0 4 41),.stop (.third 2 1 4 101),.stop (.third 1 2 4 19),.stop (.third 3 0 4 41),.stop (.third 3 4 1 103),.stop (.third 2 4 3 43),.stop (.third 3 0 4 41),.stop (.third 2 1 4 101),.stop (.third 1 2 4 19),.stop (.third 3 0 4 41),.stop (.third 1 4 3 91),.stop (.third 3 2 4 61),.stop (.third 3 0 4 41),.stop (.third 2 1 4 101),.stop (.third 1 2 4 19),.stop (.third 0 4 3 73),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 12353),.stop (.collision 8832),.stop (.third 0 3 4 79),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 0 3 4 79),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 79),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 79),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 0 3 4 79),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 79),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact unit_20_80_closed
  · exact unit_20_81_closed
  · exact unit_20_82_closed
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,83] 84 (.stop (.third 2 1 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,84] 85 (.stop (.third 1 2 3 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,85] 86 (.branch [.stop (.collision 1104),.stop (.collision 16896),.stop (.collision 13312),.stop (.third 0 4 3 89),.stop (.third 1 2 4 19),.stop (.collision 9728),.stop (.third 3 4 0 103),.stop (.collision 12416),.stop (.collision 257),.stop (.third 2 1 4 101),.stop (.third 1 2 4 19),.branch [.stop (.third 1 5 3 73),.stop (.third 4 2 5 67),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 0 4 5 73),.stop (.third 0 5 1 7),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 4 5 73),.stop (.third 1 0 5 119),.stop (.third 0 5 4 109),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 4 5 73),.stop (.third 0 5 1 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 1 4 3 73),.stop (.collision 516),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact unit_20_86_closed
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,87] 88 (.stop (.collision 2048)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,88] 89 (.branch [.stop (.third 2 1 4 101),.stop (.third 1 2 4 19),.stop (.collision 257),.stop (.third 4 1 3 29),.stop (.third 4 2 3 23),.branch [.stop (.third 2 1 5 101),.stop (.third 1 2 5 19),.stop (.third 2 5 3 53),.stop (.third 5 1 3 47),.stop (.third 3 5 1 11),.stop (.collision 12361),.stop (.third 0 5 3 101),.stop (.third 1 0 5 119),.stop (.third 0 5 1 7),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 4 83),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 1 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 2 1 4 101),.stop (.third 1 2 4 19),.stop (.third 2 4 3 53),.stop (.third 4 1 3 47),.stop (.third 3 4 1 11),.stop (.collision 523),.stop (.third 0 4 3 101),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,89] 90 (.stop (.third 2 1 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,90] 91 (.stop (.third 1 2 3 19)) (by decide +kernel))
  · exact unit_20_91_closed
  · exact unit_20_92_closed
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,93] 94 (.branch [.stop (.collision 1104),.stop (.third 2 1 4 101),.stop (.third 1 2 4 19),.stop (.collision 12416),.stop (.third 2 3 4 97),.stop (.third 2 4 3 79),.stop (.third 3 4 1 103),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact unit_20_94_closed
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,95] 96 (.stop (.third 2 1 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,96] 97 (.stop (.third 1 2 3 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,97] 98 (.branch [.stop (.collision 1104),.stop (.third 3 2 4 67),.stop (.collision 523),.stop (.collision 8832),.stop (.third 0 3 4 73),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 73),.stop (.third 1 0 4 119),.stop (.third 0 4 3 109),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 73),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,98] 99 (.branch [.stop (.collision 1104),.stop (.collision 523),.stop (.collision 8832),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 109),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,99] 100 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,100] 101 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,101] 102 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,102] 103 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,104] 105 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,105] 106 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,106] 107 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,107] 108 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,108] 109 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,109] 110 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,110] 111 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,111] 112 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,112] 113 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,113] 114 (.stop (.third 0 3 1 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,114] 115 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 20 3 [0,1,20,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

import MinModulus.SevenModOneTwenty.BlockUnit238
import MinModulus.SevenModOneTwenty.BlockUnit239
import MinModulus.SevenModOneTwenty.BlockUnit240
import MinModulus.SevenModOneTwenty.BlockUnit241

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_19_closed : ClosedMinimalPrefix true 120 19 4 [0,1,19] 20 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,20] 21 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_19_21_closed
  · exact unit_19_22_closed
  · exact unit_19_23_closed
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,24] 25 (.stop (.third 1 3 2 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,25] 26 (.stop (.third 2 0 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,26] 27 (.stop (.third 0 2 3 19)) (by decide +kernel))
  · exact unit_19_27_closed
  · exact unit_19_28_closed
  · exact unit_19_29_closed
  · exact unit_19_30_closed
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,31] 32 (.stop (.third 2 0 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,32] 33 (.stop (.third 0 2 3 19)) (by decide +kernel))
  · exact unit_19_33_closed
  · exact unit_19_34_closed
  · exact unit_19_35_closed
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,36] 37 (.stop (.third 2 3 0 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,37] 38 (.stop (.third 0 3 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,38] 39 (.stop (.third 0 2 3 19)) (by decide +kernel))
  · exact unit_19_39_closed
  · exact unit_19_40_closed
  · exact unit_19_41_closed
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,42] 43 (.stop (.third 1 3 2 41)) (by decide +kernel))
  · exact unit_19_43_closed
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,44] 45 (.stop (.third 1 3 2 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,45] 46 (.stop (.third 0 2 3 19)) (by decide +kernel))
  · exact unit_19_46_closed
  · exact unit_19_47_closed
  · exact unit_19_48_closed
  · exact unit_19_49_closed
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,50] 51 (.stop (.third 2 0 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,51] 52 (.stop (.third 0 2 3 19)) (by decide +kernel))
  · exact unit_19_52_closed
  · exact unit_19_53_closed
  · exact unit_19_54_closed
  · exact unit_19_55_closed
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,56] 57 (.stop (.third 2 0 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,57] 58 (.stop (.third 0 2 3 19)) (by decide +kernel))
  · exact unit_19_58_closed
  · exact unit_19_59_closed
  · exact unit_19_60_closed
  · exact unit_19_61_closed
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,62] 63 (.stop (.third 1 3 2 61)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,63] 64 (.stop (.third 2 0 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,64] 65 (.stop (.third 0 2 3 19)) (by decide +kernel))
  · exact unit_19_65_closed
  · exact unit_19_66_closed
  · exact unit_19_67_closed
  · exact unit_19_68_closed
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,69] 70 (.stop (.third 2 0 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,70] 71 (.stop (.third 0 2 3 19)) (by decide +kernel))
  · exact unit_19_71_closed
  · exact unit_19_72_closed
  · exact unit_19_73_closed
  · exact unit_19_74_closed
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,75] 76 (.stop (.third 2 0 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,76] 77 (.stop (.third 0 2 3 19)) (by decide +kernel))
  · exact unit_19_77_closed
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,78] 79 (.stop (.third 2 3 1 59)) (by decide +kernel))
  · exact unit_19_79_closed
  · exact unit_19_80_closed
  · exact unit_19_81_closed
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,82] 83 (.stop (.third 2 0 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,83] 84 (.stop (.third 0 2 3 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,84] 85 (.stop (.third 1 3 0 107)) (by decide +kernel))
  · exact unit_19_85_closed
  · exact unit_19_86_closed
  · exact unit_19_87_closed
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,88] 89 (.stop (.third 2 0 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,89] 90 (.stop (.third 0 2 3 19)) (by decide +kernel))
  · exact unit_19_90_closed
  · exact unit_19_91_closed
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,92] 93 (.branch [.stop (.collision 1104),.stop (.third 2 0 4 101),.stop (.third 0 2 4 19),.stop (.third 1 3 4 91),.stop (.third 2 3 4 97),.stop (.third 2 4 1 79),.stop (.third 3 4 0 103),.stop (.third 1 3 4 91),.stop (.third 2 0 4 101),.stop (.third 0 2 4 19),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 2 83),.stop (.third 0 2 4 19),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 0 2 4 19),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact unit_19_93_closed
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,94] 95 (.stop (.third 2 0 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,95] 96 (.stop (.third 0 2 3 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,96] 97 (.stop (.third 2 3 1 53)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,97] 98 (.branch [.stop (.third 2 4 1 79),.branch [.stop (.third 5 4 3 119),.stop (.third 2 0 5 101),.stop (.third 0 2 5 19),.stop (.third 0 5 1 7),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 3 5 73),.stop (.third 0 2 5 19),.stop (.third 0 5 3 109),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 3 5 73),.stop (.third 0 5 1 17),.stop (.third 0 2 5 19),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.collision 516),.stop (.third 2 0 4 101),.stop (.third 0 2 4 19),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 73),.stop (.third 0 2 4 19),.stop (.third 0 4 3 109),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 73),.stop (.third 0 4 1 17),.stop (.third 0 2 4 19),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,98] 99 (.stop (.third 2 3 1 79)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,99] 100 (.branch [.stop (.collision 1104),.stop (.third 2 0 4 101),.stop (.third 0 2 4 19),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 2 83),.stop (.third 0 2 4 19),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 0 2 4 19),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,100] 101 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,101] 102 (.stop (.third 2 0 3 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,102] 103 (.stop (.third 0 2 3 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,104] 105 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,105] 106 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,106] 107 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,107] 108 (.stop (.third 0 3 2 83)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,108] 109 (.stop (.third 0 2 3 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,109] 110 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,110] 111 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,111] 112 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,112] 113 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,113] 114 (.stop (.third 0 3 1 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,114] 115 (.stop (.third 0 2 3 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 19 3 [0,1,19,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

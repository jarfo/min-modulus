import MinModulus.SevenModOneTwenty.BlockUnit198
import MinModulus.SevenModOneTwenty.BlockUnit199
import MinModulus.SevenModOneTwenty.BlockUnit200
import MinModulus.SevenModOneTwenty.BlockUnit201
import MinModulus.SevenModOneTwenty.BlockUnit202
import MinModulus.SevenModOneTwenty.BlockUnit203

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_11_closed : ClosedMinimalPrefix true 120 11 4 [0,1,11] 12 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,12] 13 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_11_13_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,14] 15 (.stop (.third 1 3 2 37)) (by decide +kernel))
  · exact unit_11_15_closed
  · exact unit_11_16_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,17] 18 (.stop (.third 3 0 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,18] 19 (.stop (.third 1 3 0 113)) (by decide +kernel))
  · exact unit_11_19_closed
  · exact unit_11_20_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,21] 22 (.stop (.third 2 0 3 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,22] 23 (.stop (.third 0 2 3 11)) (by decide +kernel))
  · exact unit_11_23_closed
  · exact unit_11_24_closed
  · exact unit_11_25_closed
  · exact unit_11_26_closed
  · exact unit_11_27_closed
  · exact unit_11_28_closed
  · exact unit_11_29_closed
  · exact unit_11_30_closed
  · exact unit_11_31_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,32] 33 (.stop (.third 2 0 3 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,33] 34 (.stop (.third 0 2 3 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,34] 35 (.stop (.third 2 3 1 47)) (by decide +kernel))
  · exact unit_11_35_closed
  · exact unit_11_36_closed
  · exact unit_11_37_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,38] 39 (.stop (.third 1 3 2 13)) (by decide +kernel))
  · exact unit_11_39_closed
  · exact unit_11_40_closed
  · exact unit_11_41_closed
  · exact unit_11_42_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,43] 44 (.stop (.third 2 0 3 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,44] 45 (.stop (.third 0 2 3 11)) (by decide +kernel))
  · exact unit_11_45_closed
  · exact unit_11_46_closed
  · exact unit_11_47_closed
  · exact unit_11_48_closed
  · exact unit_11_49_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,50] 51 (.stop (.third 1 3 2 49)) (by decide +kernel))
  · exact unit_11_51_closed
  · exact unit_11_52_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,53] 54 (.stop (.third 0 3 2 77)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,54] 55 (.stop (.third 2 0 3 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,55] 56 (.stop (.third 0 2 3 11)) (by decide +kernel))
  · exact unit_11_56_closed
  · exact unit_11_57_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,58] 59 (.stop (.third 2 3 1 23)) (by decide +kernel))
  · exact unit_11_59_closed
  · exact unit_11_60_closed
  · exact unit_11_61_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,62] 63 (.stop (.third 1 3 2 61)) (by decide +kernel))
  · exact unit_11_63_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,64] 65 (.stop (.third 3 2 0 43)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,65] 66 (.stop (.third 2 0 3 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,66] 67 (.stop (.third 0 2 3 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,67] 68 (.stop (.third 3 0 2 77)) (by decide +kernel))
  · exact unit_11_68_closed
  · exact unit_11_69_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,70] 71 (.stop (.third 2 3 1 59)) (by decide +kernel))
  · exact unit_11_71_closed
  · exact unit_11_72_closed
  · exact unit_11_73_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,74] 75 (.stop (.third 1 3 2 97)) (by decide +kernel))
  · exact unit_11_75_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,76] 77 (.stop (.third 2 0 3 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,77] 78 (.stop (.third 0 2 3 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,78] 79 (.stop (.third 2 3 0 43)) (by decide +kernel))
  · exact unit_11_79_closed
  · exact unit_11_80_closed
  · exact unit_11_81_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,82] 83 (.stop (.third 2 3 1 71)) (by decide +kernel))
  · exact unit_11_83_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,84] 85 (.stop (.collision 2048)) (by decide +kernel))
  · exact unit_11_85_closed
  · exact unit_11_86_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,87] 88 (.stop (.third 2 0 3 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,88] 89 (.stop (.third 0 2 3 11)) (by decide +kernel))
  · exact unit_11_89_closed
  · exact unit_11_90_closed
  · exact unit_11_91_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,92] 93 (.branch [.stop (.collision 1104),.stop (.third 2 4 1 107),.branch [.stop (.third 1 3 5 91),.stop (.third 5 0 3 47),.stop (.third 1 5 2 73),.stop (.third 0 2 5 11),.stop (.third 1 3 5 91),.stop (.third 5 0 4 19),.stop (.collision 5249),.stop (.third 0 5 1 7),.stop (.third 5 1 0 113),.stop (.third 3 5 2 37),.stop (.collision 102472),.stop (.collision 73856),.stop (.third 1 5 4 83),.stop (.third 2 0 5 109),.stop (.third 0 2 5 11),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 1 3 4 91),.stop (.third 4 0 3 47),.stop (.third 1 4 2 73),.stop (.third 0 2 4 11),.stop (.third 1 3 4 91),.stop (.collision 12416),.stop (.collision 1153),.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.stop (.third 3 4 2 37),.stop (.collision 12360),.branch [.stop (.third 5 1 3 37),.stop (.third 2 0 5 109),.stop (.third 0 2 5 11),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 3 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 4 1 3 37),.stop (.third 2 0 4 109),.stop (.third 0 2 4 11),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact unit_11_93_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,94] 95 (.stop (.third 2 3 1 107)) (by decide +kernel))
  · exact unit_11_95_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,96] 97 (.branch [.stop (.collision 1104),.stop (.third 1 4 2 73),.stop (.third 0 2 4 11),.stop (.third 2 4 3 89),.branch [.stop (.third 5 1 3 19),.stop (.third 0 5 1 7),.stop (.third 5 1 0 113),.stop (.collision 73856),.stop (.collision 5249),.stop (.third 0 4 5 101),.stop (.collision 102472),.stop (.third 2 0 5 109),.stop (.third 0 2 5 11),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 4 1 3 19),.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.stop (.collision 8216),.stop (.collision 1153),.stop (.collision 1160),.stop (.collision 12360),.stop (.third 2 0 4 109),.stop (.third 0 2 4 11),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact unit_11_97_closed
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,98] 99 (.stop (.third 1 3 2 73)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,99] 100 (.stop (.third 0 2 3 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,100] 101 (.branch [.stop (.collision 1104),.branch [.stop (.third 0 5 1 7),.stop (.third 3 2 5 31),.stop (.collision 102528),.stop (.third 2 4 5 91),.stop (.third 3 5 1 103),.stop (.third 1 4 5 101),.stop (.third 2 0 5 109),.stop (.third 0 2 5 11),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 0 4 1 7),.stop (.third 3 2 4 31),.stop (.collision 12416),.branch [.stop (.third 3 5 1 103),.stop (.third 3 2 5 31),.stop (.third 2 0 5 109),.stop (.third 0 2 5 11),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 3 4 1 103),.stop (.third 3 2 4 31),.stop (.third 2 0 4 109),.stop (.third 0 2 4 11),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,101] 102 (.branch [.stop (.collision 1104),.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.branch [.stop (.third 5 4 3 119),.stop (.third 0 3 5 101),.stop (.third 5 1 4 37),.stop (.third 2 0 5 109),.stop (.third 0 2 5 11),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.branch [.stop (.third 0 3 5 101),.stop (.collision 98944),.stop (.third 2 0 5 109),.stop (.third 0 2 5 11),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 0 3 4 101),.stop (.collision 516),.stop (.third 2 0 4 109),.stop (.third 0 2 4 11),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,102] 103 (.branch [.stop (.third 0 4 1 7),.stop (.third 4 1 0 113),.branch [.stop (.third 2 3 5 91),.stop (.collision 73856),.stop (.third 1 3 5 101),.stop (.third 2 0 5 109),.stop (.third 0 2 5 11),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 2 3 4 91),.branch [.stop (.third 1 3 5 101),.stop (.third 2 0 5 109),.stop (.third 0 2 5 11),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 1 3 4 101),.stop (.third 2 0 4 109),.stop (.third 0 2 4 11),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,104] 105 (.stop (.third 3 1 0 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,105] 106 (.branch [.stop (.collision 1104),.branch [.stop (.third 5 1 3 37),.stop (.third 2 0 5 109),.stop (.third 0 2 5 11),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 4 1 3 37),.stop (.third 2 0 4 109),.stop (.third 0 2 4 11),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,106] 107 (.branch [.stop (.collision 1104),.stop (.collision 12416),.stop (.third 2 0 4 109),.stop (.third 0 2 4 11),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,107] 108 (.branch [.stop (.collision 1104),.stop (.third 2 0 4 109),.stop (.third 0 2 4 11),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,108] 109 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,109] 110 (.stop (.third 2 0 3 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,110] 111 (.stop (.third 0 2 3 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,111] 112 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,112] 113 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,113] 114 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,114] 115 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 11 3 [0,1,11,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

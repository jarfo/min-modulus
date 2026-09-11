import MinModulus.SevenModOneTwenty.BlockUnit253
import MinModulus.SevenModOneTwenty.BlockUnit254

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_23_closed : ClosedMinimalPrefix true 120 23 4 [0,1,23] 24 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,24] 25 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_23_25_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,26] 27 (.stop (.third 0 2 3 47)) (by decide +kernel))
  · exact unit_23_27_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,28] 29 (.stop (.third 2 0 3 73)) (by decide +kernel))
  · exact unit_23_29_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,30] 31 (.stop (.third 2 3 1 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,31] 32 (.stop (.third 0 2 3 47)) (by decide +kernel))
  · exact unit_23_32_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,33] 34 (.stop (.third 2 0 3 73)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,34] 35 (.stop (.third 3 2 0 109)) (by decide +kernel))
  · exact unit_23_35_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,36] 37 (.stop (.third 0 2 3 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,37] 38 (.stop (.third 0 3 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,38] 39 (.stop (.third 2 0 3 73)) (by decide +kernel))
  · exact unit_23_39_closed
  · exact unit_23_40_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,41] 42 (.stop (.third 0 2 3 47)) (by decide +kernel))
  · exact unit_23_42_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,43] 44 (.stop (.third 2 0 3 73)) (by decide +kernel))
  · exact unit_23_44_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,45] 46 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,46] 47 (.stop (.third 0 2 3 47)) (by decide +kernel))
  · exact unit_23_47_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,48] 49 (.stop (.collision 2048)) (by decide +kernel))
  · exact unit_23_49_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,50] 51 (.stop (.third 3 1 2 71)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,51] 52 (.stop (.third 2 0 3 73)) (by decide +kernel))
  · exact unit_23_52_closed
  · exact unit_23_53_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,54] 55 (.stop (.third 0 2 3 47)) (by decide +kernel))
  · exact unit_23_55_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,56] 57 (.stop (.third 2 0 3 73)) (by decide +kernel))
  · exact unit_23_57_closed
  · exact unit_23_58_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,59] 60 (.stop (.third 0 2 3 47)) (by decide +kernel))
  · exact unit_23_60_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,61] 62 (.stop (.third 2 0 3 73)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,62] 63 (.stop (.third 1 3 2 61)) (by decide +kernel))
  · exact unit_23_63_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,64] 65 (.stop (.third 0 2 3 47)) (by decide +kernel))
  · exact unit_23_65_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,66] 67 (.stop (.third 2 0 3 73)) (by decide +kernel))
  · exact unit_23_67_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,68] 69 (.stop (.third 3 1 2 77)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,69] 70 (.stop (.third 0 2 3 47)) (by decide +kernel))
  · exact unit_23_70_closed
  · exact unit_23_71_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,72] 73 (.stop (.third 1 3 2 71)) (by decide +kernel))
  · exact unit_23_73_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,74] 75 (.stop (.third 2 0 3 73)) (by decide +kernel))
  · exact unit_23_75_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,76] 77 (.stop (.third 3 2 1 43)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,77] 78 (.stop (.third 0 2 3 47)) (by decide +kernel))
  · exact unit_23_78_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,79] 80 (.stop (.third 0 3 2 79)) (by decide +kernel))
  · exact unit_23_80_closed
  · exact unit_23_81_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,82] 83 (.stop (.third 0 2 3 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,83] 84 (.stop (.third 3 0 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,84] 85 (.stop (.third 1 3 0 107)) (by decide +kernel))
  · exact unit_23_85_closed
  · exact unit_23_86_closed
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,87] 88 (.stop (.third 0 2 3 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,88] 89 (.stop (.collision 2048)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,89] 90 (.stop (.third 0 3 2 89)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,90] 91 (.stop (.third 2 3 1 43)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,91] 92 (.branch [.stop (.third 0 2 4 47),.branch [.stop (.third 5 2 1 49),.stop (.third 0 3 5 91),.stop (.third 5 2 3 23),.stop (.third 2 0 5 73),.stop (.third 5 1 4 47),.stop (.third 0 3 5 91),.stop (.third 0 2 5 47),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 3 5 91),.stop (.third 1 0 5 119),.stop (.third 0 2 5 47),.stop (.third 1 0 5 119),.stop (.third 0 3 5 91),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 2 5 47),.stop (.third 0 3 5 91),.stop (.third 1 0 5 119),.stop (.third 0 5 1 17),.stop (.third 1 0 5 119),.stop (.third 0 2 5 47),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 4 2 1 49),.stop (.third 0 3 4 91),.stop (.third 4 2 3 23),.stop (.third 2 0 4 73),.stop (.third 4 3 0 17),.stop (.third 0 3 4 91),.stop (.third 0 2 4 47),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 0 2 4 47),.stop (.third 1 0 4 119),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 2 4 47),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 0 2 4 47),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,92] 93 (.stop (.third 0 2 3 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,93] 94 (.branch [.stop (.third 4 2 1 49),.stop (.collision 257),.stop (.collision 264),.stop (.third 2 0 4 73),.stop (.third 4 1 3 47),.stop (.third 1 0 4 119),.stop (.third 0 2 4 47),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 0 2 4 47),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 2 4 47),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 0 2 4 47),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,94] 95 (.stop (.third 3 2 1 49)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,95] 96 (.branch [.stop (.collision 1104),.stop (.third 2 0 4 73),.stop (.third 1 4 3 73),.stop (.third 1 0 4 119),.stop (.third 0 2 4 47),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 0 2 4 47),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 2 4 47),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 0 2 4 47),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,96] 97 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,97] 98 (.stop (.third 2 0 3 73)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,98] 99 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,99] 100 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,100] 101 (.stop (.third 0 2 3 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,101] 102 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,102] 103 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,104] 105 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,105] 106 (.stop (.third 0 2 3 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,106] 107 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,107] 108 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,108] 109 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,109] 110 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,110] 111 (.stop (.third 0 2 3 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,111] 112 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,112] 113 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,113] 114 (.stop (.third 0 3 1 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,114] 115 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,115] 116 (.stop (.third 0 2 3 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 23 3 [0,1,23,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

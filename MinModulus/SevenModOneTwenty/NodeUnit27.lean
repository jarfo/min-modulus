import MinModulus.SevenModOneTwenty.BlockUnit261
import MinModulus.SevenModOneTwenty.BlockUnit262

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_27_closed : ClosedMinimalPrefix true 120 27 4 [0,1,27] 28 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,28] 29 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_27_29_closed
  · exact unit_27_30_closed
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,31] 32 (.stop (.third 3 0 2 89)) (by decide +kernel))
  · exact unit_27_32_closed
  · exact unit_27_33_closed
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,34] 35 (.stop (.third 3 2 0 17)) (by decide +kernel))
  · exact unit_27_35_closed
  · exact unit_27_36_closed
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,37] 38 (.stop (.third 0 3 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,38] 39 (.stop (.third 3 1 0 107)) (by decide +kernel))
  · exact unit_27_39_closed
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,40] 41 (.stop (.third 3 2 1 83)) (by decide +kernel))
  · exact unit_27_41_closed
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,42] 43 (.stop (.third 3 1 2 79)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,43] 44 (.stop (.third 0 3 2 67)) (by decide +kernel))
  · exact unit_27_44_closed
  · exact unit_27_45_closed
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,46] 47 (.stop (.third 3 2 1 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,47] 48 (.stop (.third 0 3 1 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,48] 49 (.stop (.third 3 1 0 97)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,49] 50 (.stop (.third 0 3 2 49)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,50] 51 (.stop (.third 3 2 1 73)) (by decide +kernel))
  · exact unit_27_51_closed
  · exact unit_27_52_closed
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,53] 54 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,54] 55 (.stop (.collision 200)) (by decide +kernel))
  · exact unit_27_55_closed
  · exact unit_27_56_closed
  · exact unit_27_57_closed
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,58] 59 (.stop (.third 2 3 0 31)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,59] 60 (.branch [.stop (.collision 1104),.stop (.third 3 0 4 61),.stop (.third 1 4 2 61),.stop (.third 3 0 4 61),.stop (.third 2 4 0 13),.stop (.third 3 0 4 61),.stop (.third 3 4 1 103),.stop (.third 0 4 3 43),.stop (.third 2 4 1 41),.stop (.third 3 0 4 61),.stop (.third 3 4 2 11),.stop (.third 3 0 4 61),.stop (.third 3 4 1 37),.stop (.third 3 0 4 61),.stop (.third 1 4 0 97),.stop (.third 3 0 4 61),.stop (.third 2 4 3 49),.stop (.third 0 4 3 53),.stop (.third 4 3 1 101),.stop (.third 3 0 4 61),.stop (.third 1 4 2 79),.stop (.third 3 0 4 61),.stop (.third 4 3 0 73),.stop (.third 0 4 2 107),.stop (.third 1 4 0 107),.stop (.third 3 0 4 61),.stop (.third 2 4 1 59),.stop (.collision 8195),.stop (.third 4 3 1 91),.stop (.third 0 4 2 89),.stop (.third 1 4 3 89),.stop (.collision 1545),.stop (.third 4 1 3 29),.stop (.collision 523),.stop (.third 0 3 4 59),.stop (.third 1 0 4 119),.stop (.third 0 3 4 59),.stop (.third 1 0 4 119),.stop (.third 0 3 4 59),.stop (.third 1 0 4 119),.stop (.third 0 3 4 59),.stop (.third 1 0 4 119),.stop (.third 0 3 4 59),.stop (.third 0 4 1 7),.stop (.third 0 3 4 59),.stop (.third 1 0 4 119),.stop (.third 0 3 4 59),.stop (.third 1 0 4 119),.stop (.third 0 3 4 59),.stop (.third 1 0 4 119),.stop (.third 0 3 4 59),.stop (.third 1 0 4 119),.stop (.third 0 3 4 59),.stop (.third 0 4 1 17),.stop (.third 0 3 4 59),.stop (.third 1 0 4 119),.stop (.third 0 3 4 59),.stop (.third 1 0 4 119),.stop (.third 0 3 4 59),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact unit_27_60_closed
  · exact unit_27_61_closed
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,62] 63 (.stop (.third 1 3 2 61)) (by decide +kernel))
  · exact unit_27_63_closed
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,64] 65 (.stop (.third 2 3 0 13)) (by decide +kernel))
  · exact unit_27_65_closed
  · exact unit_27_66_closed
  · exact unit_27_67_closed
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,68] 69 (.stop (.third 2 3 1 41)) (by decide +kernel))
  · exact unit_27_69_closed
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,70] 71 (.stop (.third 3 2 0 53)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,71] 72 (.stop (.third 3 0 2 49)) (by decide +kernel))
  · exact unit_27_72_closed
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,73] 74 (.stop (.third 3 0 1 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,74] 75 (.stop (.third 1 3 0 97)) (by decide +kernel))
  · exact unit_27_75_closed
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,76] 77 (.stop (.third 3 2 0 71)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,77] 78 (.stop (.third 3 0 2 67)) (by decide +kernel))
  · exact unit_27_78_closed
  · exact unit_27_79_closed
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,80] 81 (.stop (.third 1 3 2 79)) (by decide +kernel))
  · exact unit_27_81_closed
  · exact unit_27_82_closed
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,83] 84 (.stop (.third 0 3 2 107)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,84] 85 (.stop (.third 1 3 0 107)) (by decide +kernel))
  · exact unit_27_85_closed
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,86] 87 (.stop (.third 2 3 1 59)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,87] 88 (.branch [.stop (.collision 1104),.stop (.third 0 4 2 89),.branch [.stop (.third 5 0 3 29),.stop (.third 1 5 3 91),.stop (.collision 12361),.stop (.third 3 5 1 103),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 1 7),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 3 83),.stop (.third 1 0 5 119),.stop (.third 0 5 3 109),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 1 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 4 0 3 29),.stop (.third 1 4 3 91),.stop (.collision 523),.stop (.third 3 4 1 103),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 83),.stop (.third 1 0 4 119),.stop (.third 0 4 3 109),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,88] 89 (.branch [.stop (.third 0 4 2 89),.stop (.third 2 3 4 61),.stop (.collision 12416),.stop (.third 2 3 4 61),.stop (.collision 523),.stop (.third 2 3 4 61),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 101),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,89] 90 (.stop (.third 0 3 2 89)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,90] 91 (.branch [.stop (.collision 1104),.stop (.collision 12416),.stop (.collision 523),.stop (.third 3 1 4 31),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,91] 92 (.branch [.stop (.collision 1104),.stop (.collision 523),.stop (.third 4 2 3 77),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,92] 93 (.stop (.collision 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,93] 94 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,94] 95 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,95] 96 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,96] 97 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,97] 98 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,98] 99 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,99] 100 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,100] 101 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,101] 102 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,102] 103 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,104] 105 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,105] 106 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,106] 107 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,107] 108 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,108] 109 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,109] 110 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,110] 111 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,111] 112 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,112] 113 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,113] 114 (.stop (.third 0 3 1 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,114] 115 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 27 3 [0,1,27,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

import MinModulus.SevenModOneTwenty.BlockUnit266
import MinModulus.SevenModOneTwenty.BlockUnit267

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_33_closed : ClosedMinimalPrefix true 120 33 4 [0,1,33] 34 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,34] 35 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_33_35_closed
  · exact unit_33_36_closed
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,37] 38 (.stop (.third 0 3 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,38] 39 (.stop (.third 3 1 0 107)) (by decide +kernel))
  · exact unit_33_39_closed
  · exact unit_33_40_closed
  · exact unit_33_41_closed
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,42] 43 (.stop (.third 3 1 2 79)) (by decide +kernel))
  · exact unit_33_43_closed
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,44] 45 (.stop (.third 2 3 1 11)) (by decide +kernel))
  · exact unit_33_45_closed
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,46] 47 (.stop (.third 2 3 1 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,47] 48 (.stop (.third 0 3 1 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,48] 49 (.stop (.third 1 3 2 23)) (by decide +kernel))
  · exact unit_33_49_closed
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,50] 51 (.stop (.third 1 3 2 49)) (by decide +kernel))
  · exact unit_33_51_closed
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,52] 53 (.stop (.third 3 2 0 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,53] 54 (.stop (.third 0 3 2 77)) (by decide +kernel))
  · exact unit_33_54_closed
  · exact unit_33_55_closed
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,56] 57 (.stop (.third 2 3 0 47)) (by decide +kernel))
  · exact unit_33_57_closed
  · exact unit_33_58_closed
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,59] 60 (.stop (.third 0 3 2 59)) (by decide +kernel))
  · exact unit_33_60_closed
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,61] 62 (.stop (.third 3 0 2 59)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,62] 63 (.stop (.third 1 3 2 61)) (by decide +kernel))
  · exact unit_33_63_closed
  · exact unit_33_64_closed
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,65] 66 (.stop (.collision 193)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,66] 67 (.stop (.collision 200)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,67] 68 (.stop (.third 3 0 2 77)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,68] 69 (.branch [.stop (.collision 1104),.stop (.third 4 2 3 107),.stop (.third 0 4 3 71),.stop (.third 4 1 2 49),.stop (.third 3 1 4 77),.stop (.third 1 3 4 43),.stop (.third 4 3 2 17),.stop (.third 2 4 1 67),.stop (.third 0 4 3 53),.stop (.third 1 4 2 53),.stop (.third 3 1 4 77),.stop (.third 1 4 2 79),.stop (.third 3 4 0 37),.stop (.third 1 3 4 43),.stop (.third 4 0 1 13),.stop (.third 1 4 0 107),.stop (.third 1 3 4 43),.stop (.third 4 2 0 43),.stop (.third 3 1 4 77),.stop (.third 1 3 4 43),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 2 91),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 2 73),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 101),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 83),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact unit_33_69_closed
  · exact unit_33_70_closed
  · exact unit_33_71_closed
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,72] 73 (.stop (.third 3 1 2 49)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,73] 74 (.stop (.third 3 0 1 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,74] 75 (.stop (.third 1 3 0 97)) (by decide +kernel))
  · exact unit_33_75_closed
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,76] 77 (.stop (.third 2 3 1 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,77] 78 (.stop (.collision 1537)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,78] 79 (.stop (.third 1 3 2 53)) (by decide +kernel))
  · exact unit_33_79_closed
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,80] 81 (.stop (.third 1 3 2 79)) (by decide +kernel))
  · exact unit_33_81_closed
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,82] 83 (.stop (.third 3 2 1 71)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,83] 84 (.stop (.third 3 0 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,84] 85 (.stop (.third 1 3 0 107)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,85] 86 (.branch [.stop (.third 4 2 0 43),.stop (.collision 523),.stop (.collision 8832),.stop (.third 0 4 3 89),.stop (.third 1 0 4 119),.stop (.third 0 4 2 91),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 2 73),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 109),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,86] 87 (.stop (.third 3 2 0 43)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,87] 88 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,88] 89 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,89] 90 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,90] 91 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,91] 92 (.stop (.third 0 3 2 91)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,92] 93 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,93] 94 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,94] 95 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,95] 96 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,96] 97 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,97] 98 (.stop (.third 0 3 2 73)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,98] 99 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,99] 100 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,100] 101 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,101] 102 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,102] 103 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,104] 105 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,105] 106 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,106] 107 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,107] 108 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,108] 109 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,109] 110 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,110] 111 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,111] 112 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,112] 113 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,113] 114 (.stop (.third 0 3 1 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,114] 115 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 33 3 [0,1,33,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

import MinModulus.SevenModOneTwenty.BlockUnit254
import MinModulus.SevenModOneTwenty.BlockUnit255
import MinModulus.SevenModOneTwenty.BlockUnit256

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_24_closed : ClosedMinimalPrefix true 120 24 4 [0,1,24] 25 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,25] 26 (.stop (.collision 144)) (by decide +kernel))
  · exact unit_24_26_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,27] 28 (.stop (.third 1 2 3 47)) (by decide +kernel))
  · exact unit_24_28_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,29] 30 (.stop (.third 2 1 3 73)) (by decide +kernel))
  · exact unit_24_30_closed
  · exact unit_24_31_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,32] 33 (.stop (.third 1 2 3 47)) (by decide +kernel))
  · exact unit_24_33_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,34] 35 (.stop (.third 2 1 3 73)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,35] 36 (.stop (.third 3 2 1 109)) (by decide +kernel))
  · exact unit_24_36_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,37] 38 (.stop (.third 0 3 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,38] 39 (.stop (.third 3 1 0 107)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,39] 40 (.stop (.third 2 1 3 73)) (by decide +kernel))
  · exact unit_24_40_closed
  · exact unit_24_41_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,42] 43 (.stop (.third 1 2 3 47)) (by decide +kernel))
  · exact unit_24_43_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,44] 45 (.stop (.third 2 1 3 73)) (by decide +kernel))
  · exact unit_24_45_closed
  · exact unit_24_46_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,47] 48 (.stop (.third 0 3 1 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,48] 49 (.stop (.collision 200)) (by decide +kernel))
  · exact unit_24_49_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,50] 51 (.stop (.third 1 2 3 47)) (by decide +kernel))
  · exact unit_24_51_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,52] 53 (.stop (.third 2 1 3 73)) (by decide +kernel))
  · exact unit_24_53_closed
  · exact unit_24_54_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,55] 56 (.stop (.third 1 2 3 47)) (by decide +kernel))
  · exact unit_24_56_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,57] 58 (.stop (.third 2 1 3 73)) (by decide +kernel))
  · exact unit_24_58_closed
  · exact unit_24_59_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,60] 61 (.stop (.third 1 2 3 47)) (by decide +kernel))
  · exact unit_24_61_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,62] 63 (.stop (.third 2 1 3 73)) (by decide +kernel))
  · exact unit_24_63_closed
  · exact unit_24_64_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,65] 66 (.stop (.third 1 2 3 47)) (by decide +kernel))
  · exact unit_24_66_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,67] 68 (.stop (.third 2 1 3 73)) (by decide +kernel))
  · exact unit_24_68_closed
  · exact unit_24_69_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,70] 71 (.stop (.third 1 2 3 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,71] 72 (.stop (.collision 256)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,72] 73 (.stop (.collision 1544)) (by decide +kernel))
  · exact unit_24_73_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,74] 75 (.stop (.third 1 3 0 97)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,75] 76 (.stop (.third 2 1 3 73)) (by decide +kernel))
  · exact unit_24_76_closed
  · exact unit_24_77_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,78] 79 (.stop (.third 1 2 3 47)) (by decide +kernel))
  · exact unit_24_79_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,80] 81 (.stop (.third 1 3 2 79)) (by decide +kernel))
  · exact unit_24_81_closed
  · exact unit_24_82_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,83] 84 (.stop (.third 1 2 3 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,84] 85 (.stop (.third 1 3 0 107)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,85] 86 (.stop (.third 2 1 3 73)) (by decide +kernel))
  · exact unit_24_86_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,87] 88 (.branch [.stop (.third 1 2 4 47),.stop (.collision 13312),.stop (.third 1 4 2 89),.stop (.third 4 0 3 29),.stop (.collision 12416),.stop (.third 1 2 4 47),.stop (.third 3 4 1 103),.stop (.third 2 1 4 73),.stop (.collision 523),.stop (.third 4 0 3 47),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 83),.stop (.third 1 0 4 119),.stop (.third 0 4 3 109),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,88] 89 (.stop (.third 1 2 3 47)) (by decide +kernel))
  · exact unit_24_89_closed
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,90] 91 (.stop (.third 1 3 2 89)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,91] 92 (.branch [.stop (.collision 1104),.stop (.third 1 2 4 47),.stop (.third 2 3 4 43),.stop (.third 0 3 4 91),.stop (.collision 523),.stop (.third 2 3 4 43),.stop (.third 1 0 4 119),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 3 4 91),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,92] 93 (.branch [.stop (.third 1 2 4 47),.branch [.stop (.third 2 1 5 73),.stop (.third 1 3 5 91),.stop (.third 0 5 4 73),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 4 101),.stop (.third 1 0 5 119),.stop (.third 0 5 1 7),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 4 83),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 0 5 1 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)],.stop (.third 2 1 4 73),.stop (.third 1 3 4 91),.stop (.third 4 0 3 47),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,93] 94 (.stop (.third 1 2 3 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,94] 95 (.branch [.stop (.third 2 1 4 73),.stop (.collision 523),.stop (.third 0 4 3 73),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 101),.stop (.third 1 0 4 119),.stop (.third 0 4 1 7),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 3 83),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 0 4 1 17),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119),.stop (.third 1 0 4 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,95] 96 (.stop (.third 2 1 3 73)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,96] 97 (.stop (.collision 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,97] 98 (.stop (.collision 1152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,98] 99 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,99] 100 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,100] 101 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,101] 102 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,102] 103 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,103] 104 (.stop (.third 0 3 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,104] 105 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,105] 106 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,106] 107 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,107] 108 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,108] 109 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,109] 110 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,110] 111 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,111] 112 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,112] 113 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,113] 114 (.stop (.third 0 3 1 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,114] 115 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,115] 116 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,116] 117 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,117] 118 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,118] 119 (.stop (.third 1 0 3 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 24 3 [0,1,24,119] 120 (.stop (.third 1 0 3 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

import MinModulus.SevenModOneTwenty.BlockNonunit322
import MinModulus.SevenModOneTwenty.BlockNonunit323
import MinModulus.SevenModOneTwenty.BlockUnit264
import MinModulus.SevenModOneTwenty.BlockUnit265
import MinModulus.SevenModOneTwenty.BlockUnit266
import MinModulus.SevenModOneTwenty.BlockUnit268
import MinModulus.SevenModOneTwenty.BlockUnit269
import MinModulus.SevenModOneTwenty.BlockUnit270
import MinModulus.SevenModOneTwenty.BlockUnit271
import MinModulus.SevenModOneTwenty.BlockUnit272
import MinModulus.SevenModOneTwenty.BlockUnit273
import MinModulus.SevenModOneTwenty.NodeNonunit2
import MinModulus.SevenModOneTwenty.NodeNonunit3
import MinModulus.SevenModOneTwenty.NodeNonunit4
import MinModulus.SevenModOneTwenty.NodeUnit10
import MinModulus.SevenModOneTwenty.NodeUnit11
import MinModulus.SevenModOneTwenty.NodeUnit12
import MinModulus.SevenModOneTwenty.NodeUnit13
import MinModulus.SevenModOneTwenty.NodeUnit14
import MinModulus.SevenModOneTwenty.NodeUnit15
import MinModulus.SevenModOneTwenty.NodeUnit16
import MinModulus.SevenModOneTwenty.NodeUnit19
import MinModulus.SevenModOneTwenty.NodeUnit20
import MinModulus.SevenModOneTwenty.NodeUnit21
import MinModulus.SevenModOneTwenty.NodeUnit22
import MinModulus.SevenModOneTwenty.NodeUnit23
import MinModulus.SevenModOneTwenty.NodeUnit24
import MinModulus.SevenModOneTwenty.NodeUnit25
import MinModulus.SevenModOneTwenty.NodeUnit26
import MinModulus.SevenModOneTwenty.NodeUnit27
import MinModulus.SevenModOneTwenty.NodeUnit28
import MinModulus.SevenModOneTwenty.NodeUnit3
import MinModulus.SevenModOneTwenty.NodeUnit33
import MinModulus.SevenModOneTwenty.NodeUnit4
import MinModulus.SevenModOneTwenty.NodeUnit5
import MinModulus.SevenModOneTwenty.NodeUnit6
import MinModulus.SevenModOneTwenty.NodeUnit7
import MinModulus.SevenModOneTwenty.NodeUnit8
import MinModulus.SevenModOneTwenty.NodeUnit9

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_closed (a : ℕ) (hlo : 2 ≤ a) (hhi : a < 120) :
    ClosedMinimalPrefix true 120 a 4 [0,1,a] (a+1) := by
  interval_cases a
  · exact (closedMinimalPrefix_of_verify true 120 2 4 [0,1,2] 3 (.stop (.collision 24)) (by decide +kernel))
  · exact unit_3_closed
  · exact unit_4_closed
  · exact unit_5_closed
  · exact unit_6_closed
  · exact unit_7_closed
  · exact unit_8_closed
  · exact unit_9_closed
  · exact unit_10_closed
  · exact unit_11_closed
  · exact unit_12_closed
  · exact unit_13_closed
  · exact unit_14_closed
  · exact unit_15_closed
  · exact unit_16_closed
  · exact (closedMinimalPrefix_of_verify true 120 17 4 [0,1,17] 18 (.stop (.third 2 0 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 18 4 [0,1,18] 19 (.stop (.third 1 2 0 113)) (by decide +kernel))
  · exact unit_19_closed
  · exact unit_20_closed
  · exact unit_21_closed
  · exact unit_22_closed
  · exact unit_23_closed
  · exact unit_24_closed
  · exact unit_25_closed
  · exact unit_26_closed
  · exact unit_27_closed
  · exact unit_28_closed
  · exact unit_29_closed
  · exact unit_30_closed
  · exact unit_31_closed
  · exact unit_32_closed
  · exact unit_33_closed
  · exact unit_34_closed
  · exact unit_35_closed
  · exact unit_36_closed
  · exact (closedMinimalPrefix_of_verify true 120 37 4 [0,1,37] 38 (.stop (.third 0 2 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 38 4 [0,1,38] 39 (.stop (.third 2 1 0 107)) (by decide +kernel))
  · exact unit_39_closed
  · exact unit_40_closed
  · exact unit_41_closed
  · exact unit_42_closed
  · exact unit_43_closed
  · exact unit_44_closed
  · exact unit_45_closed
  · exact unit_46_closed
  · exact (closedMinimalPrefix_of_verify true 120 47 4 [0,1,47] 48 (.stop (.third 0 2 1 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 48 4 [0,1,48] 49 (.stop (.third 2 1 0 97)) (by decide +kernel))
  · exact unit_49_closed
  · exact unit_50_closed
  · exact unit_51_closed
  · exact unit_52_closed
  · exact (closedMinimalPrefix_of_verify true 120 53 4 [0,1,53] 54 (.stop (.third 2 0 1 43)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 54 4 [0,1,54] 55 (.stop (.third 1 2 0 77)) (by decide +kernel))
  · exact unit_55_closed
  · exact unit_56_closed
  · exact unit_57_closed
  · exact (closedMinimalPrefix_of_verify true 120 58 4 [0,1,58] 59 (.branch [.stop (.collision 144),.stop (.third 1 3 2 59),.stop (.collision 4),.stop (.third 3 1 2 59),.stop (.collision 1152),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 0 3 1 43),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 0 3 2 71),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 0 3 1 53),.stop (.third 1 0 3 119),.stop (.third 0 3 2 79),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 0 3 2 89),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 0 3 2 73),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 0 3 1 7),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 0 3 2 83),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 0 3 1 17),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 59 4 [0,1,59] 60 (.branch [.stop (.collision 144),.stop (.third 2 0 3 61),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 0 3 1 43),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 0 3 1 53),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 0 3 1 7),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 0 3 1 17),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119),.stop (.third 0 2 3 59),.stop (.third 1 0 3 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 60 4 [0,1,60] 61 (.branch [.stop (.collision 1152),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 0 3 1 43),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 0 3 1 53),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 0 3 1 7),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 0 3 1 17),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119),.stop (.third 1 0 3 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 61 4 [0,1,61] 62 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 62 4 [0,1,62] 63 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 63 4 [0,1,63] 64 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 64 4 [0,1,64] 65 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 65 4 [0,1,65] 66 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 66 4 [0,1,66] 67 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 67 4 [0,1,67] 68 (.stop (.third 0 2 1 43)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 68 4 [0,1,68] 69 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 69 4 [0,1,69] 70 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 70 4 [0,1,70] 71 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 71 4 [0,1,71] 72 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 72 4 [0,1,72] 73 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 73 4 [0,1,73] 74 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 74 4 [0,1,74] 75 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 75 4 [0,1,75] 76 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 76 4 [0,1,76] 77 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 77 4 [0,1,77] 78 (.stop (.third 0 2 1 53)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 78 4 [0,1,78] 79 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 79 4 [0,1,79] 80 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 80 4 [0,1,80] 81 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 81 4 [0,1,81] 82 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 82 4 [0,1,82] 83 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 83 4 [0,1,83] 84 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 84 4 [0,1,84] 85 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 85 4 [0,1,85] 86 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 86 4 [0,1,86] 87 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 87 4 [0,1,87] 88 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 88 4 [0,1,88] 89 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 89 4 [0,1,89] 90 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 90 4 [0,1,90] 91 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 91 4 [0,1,91] 92 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 92 4 [0,1,92] 93 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 93 4 [0,1,93] 94 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 94 4 [0,1,94] 95 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 95 4 [0,1,95] 96 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 96 4 [0,1,96] 97 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 97 4 [0,1,97] 98 (.stop (.third 0 2 1 73)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 98 4 [0,1,98] 99 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 99 4 [0,1,99] 100 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 100 4 [0,1,100] 101 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 101 4 [0,1,101] 102 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 102 4 [0,1,102] 103 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 103 4 [0,1,103] 104 (.stop (.third 0 2 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 104 4 [0,1,104] 105 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 105 4 [0,1,105] 106 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 106 4 [0,1,106] 107 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 107 4 [0,1,107] 108 (.stop (.third 0 2 1 83)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 108 4 [0,1,108] 109 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 109 4 [0,1,109] 110 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 110 4 [0,1,110] 111 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 111 4 [0,1,111] 112 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 112 4 [0,1,112] 113 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 113 4 [0,1,113] 114 (.stop (.third 0 2 1 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 114 4 [0,1,114] 115 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 115 4 [0,1,115] 116 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 116 4 [0,1,116] 117 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 117 4 [0,1,117] 118 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 118 4 [0,1,118] 119 (.stop (.third 1 0 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 119 4 [0,1,119] 120 (.stop (.third 1 0 2 119)) (by decide +kernel))

theorem nonunit_closed (a : ℕ) (hlo : 1 ≤ a) (hhi : a < 120) :
    ClosedMinimalPrefix false 120 a 5 [0,a] (a+1) := by
  interval_cases a
  · exact (closedMinimalPrefix_of_verify false 120 1 5 [0,1] 2 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact nonunit_2_closed
  · exact nonunit_3_closed
  · exact nonunit_4_closed
  · exact nonunit_5_closed
  · exact nonunit_6_closed
  · exact (closedMinimalPrefix_of_verify false 120 7 5 [0,7] 8 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact nonunit_8_closed
  · exact (closedMinimalPrefix_of_verify false 120 9 5 [0,9] 10 (.stop (.pair 0 1 67 43)) (by decide +kernel))
  · exact nonunit_10_closed
  · exact (closedMinimalPrefix_of_verify false 120 11 5 [0,11] 12 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact nonunit_12_closed
  · exact (closedMinimalPrefix_of_verify false 120 13 5 [0,13] 14 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 14 5 [0,14] 15 (.stop (.pair 0 1 43 67)) (by decide +kernel))
  · exact nonunit_15_closed
  · exact (closedMinimalPrefix_of_verify false 120 16 5 [0,16] 17 (.stop (.pair 0 1 23 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 17 5 [0,17] 18 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 18 5 [0,18] 19 (.stop (.pair 0 1 7 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 19 5 [0,19] 20 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact nonunit_20_closed
  · exact (closedMinimalPrefix_of_verify false 120 21 5 [0,21] 22 (.stop (.pair 0 1 23 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 22 5 [0,22] 23 (.stop (.pair 0 1 11 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 23 5 [0,23] 24 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact nonunit_24_closed
  · exact (closedMinimalPrefix_of_verify false 120 25 5 [0,25] 26 (.stop (.pair 0 1 29 29)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 26 5 [0,26] 27 (.stop (.pair 0 1 37 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 27 5 [0,27] 28 (.stop (.pair 0 1 49 49)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 28 5 [0,28] 29 (.stop (.pair 0 1 13 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 29 5 [0,29] 30 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact nonunit_30_closed
  · exact (closedMinimalPrefix_of_verify false 120 31 5 [0,31] 32 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 32 5 [0,32] 33 (.stop (.pair 0 1 19 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 33 5 [0,33] 34 (.stop (.pair 0 1 11 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 34 5 [0,34] 35 (.stop (.pair 0 1 53 77)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 35 5 [0,35] 36 (.stop (.pair 0 1 7 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 36 5 [0,36] 37 (.stop (.pair 0 1 7 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 37 5 [0,37] 38 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 38 5 [0,38] 39 (.stop (.pair 0 1 19 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 39 5 [0,39] 40 (.stop (.pair 0 1 37 13)) (by decide +kernel))
  · exact nonunit_40_closed
  · exact (closedMinimalPrefix_of_verify false 120 41 5 [0,41] 42 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 42 5 [0,42] 43 (.stop (.pair 0 1 23 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 43 5 [0,43] 44 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 44 5 [0,44] 45 (.stop (.pair 0 1 11 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 45 5 [0,45] 46 (.stop (.pair 0 1 11 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 46 5 [0,46] 47 (.stop (.pair 0 1 47 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 47 5 [0,47] 48 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 48 5 [0,48] 49 (.stop (.pair 0 1 13 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 49 5 [0,49] 50 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 50 5 [0,50] 51 (.stop (.pair 0 1 17 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 51 5 [0,51] 52 (.stop (.pair 0 1 73 97)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 52 5 [0,52] 53 (.stop (.pair 0 1 7 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 53 5 [0,53] 54 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 54 5 [0,54] 55 (.stop (.pair 0 1 29 29)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 55 5 [0,55] 56 (.stop (.pair 0 1 11 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 56 5 [0,56] 57 (.stop (.pair 0 1 13 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 57 5 [0,57] 58 (.stop (.pair 0 1 19 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 58 5 [0,58] 59 (.stop (.pair 0 1 29 29)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 59 5 [0,59] 60 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 60 5 [0,60] 61 (.branch [.stop (.unitPair 0 2),.stop (.pair 0 2 31 31),.stop (.pair 0 2 61 61),.stop (.pair 0 2 17 113),.stop (.pair 0 2 13 37),.stop (.pair 0 2 11 11),.stop (.unitPair 0 2),.stop (.pair 0 2 23 47),.stop (.pair 0 2 7 103),.stop (.pair 0 2 7 103),.stop (.unitPair 0 2),.stop (.pair 0 2 7 103),.stop (.unitPair 0 2),.stop (.pair 0 2 13 37),.stop (.pair 0 2 13 37),.stop (.pair 0 2 19 19),.stop (.unitPair 0 2),.stop (.pair 0 2 17 113),.stop (.unitPair 0 2),.stop (.pair 0 2 11 11),.stop (.pair 0 2 43 67),.stop (.pair 0 2 41 41),.stop (.unitPair 0 2),.stop (.pair 0 2 13 37),.stop (.pair 0 2 17 113),.stop (.pair 0 2 7 103),.stop (.pair 0 2 29 29),.stop (.pair 0 2 11 11),.stop (.unitPair 0 2),.stop (.pair 0 2 7 103),.stop (.unitPair 0 2),.stop (.pair 0 2 17 113),.stop (.pair 0 2 31 31),.stop (.pair 0 2 23 47),.stop (.pair 0 2 19 19),.stop (.pair 0 2 19 19),.stop (.unitPair 0 2),.stop (.pair 0 2 49 49),.stop (.pair 0 2 17 113),.stop (.pair 0 2 11 11),.stop (.unitPair 0 2),.stop (.pair 0 2 13 37),.stop (.unitPair 0 2),.stop (.pair 0 2 7 103),.stop (.pair 0 2 7 103),.stop (.pair 0 2 17 113),.stop (.unitPair 0 2),.stop (.pair 0 2 19 19),.stop (.unitPair 0 2),.stop (.pair 0 2 11 11),.stop (.pair 0 2 13 37),.stop (.pair 0 2 29 29),.stop (.unitPair 0 2),.stop (.pair 0 2 19 19),.stop (.pair 0 2 23 47),.stop (.pair 0 2 29 29),.stop (.pair 0 2 79 79),.stop (.pair 0 2 59 59),.stop (.unitPair 0 2)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 61 5 [0,61] 62 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 62 5 [0,62] 63 (.stop (.pair 0 1 31 31)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 63 5 [0,63] 64 (.stop (.pair 0 1 61 61)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 64 5 [0,64] 65 (.stop (.pair 0 1 17 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 65 5 [0,65] 66 (.stop (.pair 0 1 13 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 66 5 [0,66] 67 (.stop (.pair 0 1 11 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 67 5 [0,67] 68 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 68 5 [0,68] 69 (.stop (.pair 0 1 23 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 69 5 [0,69] 70 (.stop (.pair 0 1 7 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 70 5 [0,70] 71 (.stop (.pair 0 1 7 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 71 5 [0,71] 72 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 72 5 [0,72] 73 (.stop (.pair 0 1 7 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 73 5 [0,73] 74 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 74 5 [0,74] 75 (.stop (.pair 0 1 13 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 75 5 [0,75] 76 (.stop (.pair 0 1 13 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 76 5 [0,76] 77 (.stop (.pair 0 1 19 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 77 5 [0,77] 78 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 78 5 [0,78] 79 (.stop (.pair 0 1 17 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 79 5 [0,79] 80 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 80 5 [0,80] 81 (.stop (.pair 0 1 11 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 81 5 [0,81] 82 (.stop (.pair 0 1 43 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 82 5 [0,82] 83 (.stop (.pair 0 1 41 41)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 83 5 [0,83] 84 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 84 5 [0,84] 85 (.stop (.pair 0 1 13 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 85 5 [0,85] 86 (.stop (.pair 0 1 17 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 86 5 [0,86] 87 (.stop (.pair 0 1 7 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 87 5 [0,87] 88 (.stop (.pair 0 1 29 29)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 88 5 [0,88] 89 (.stop (.pair 0 1 11 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 89 5 [0,89] 90 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 90 5 [0,90] 91 (.stop (.pair 0 1 7 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 91 5 [0,91] 92 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 92 5 [0,92] 93 (.stop (.pair 0 1 17 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 93 5 [0,93] 94 (.stop (.pair 0 1 31 31)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 94 5 [0,94] 95 (.stop (.pair 0 1 23 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 95 5 [0,95] 96 (.stop (.pair 0 1 19 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 96 5 [0,96] 97 (.stop (.pair 0 1 19 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 97 5 [0,97] 98 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 98 5 [0,98] 99 (.stop (.pair 0 1 49 49)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 99 5 [0,99] 100 (.stop (.pair 0 1 17 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 100 5 [0,100] 101 (.stop (.pair 0 1 11 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 101 5 [0,101] 102 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 102 5 [0,102] 103 (.stop (.pair 0 1 13 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 103 5 [0,103] 104 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 104 5 [0,104] 105 (.stop (.pair 0 1 7 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 105 5 [0,105] 106 (.stop (.pair 0 1 7 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 106 5 [0,106] 107 (.stop (.pair 0 1 17 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 107 5 [0,107] 108 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 108 5 [0,108] 109 (.stop (.pair 0 1 19 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 109 5 [0,109] 110 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 110 5 [0,110] 111 (.stop (.pair 0 1 11 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 111 5 [0,111] 112 (.stop (.pair 0 1 13 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 112 5 [0,112] 113 (.stop (.pair 0 1 29 29)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 113 5 [0,113] 114 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 114 5 [0,114] 115 (.stop (.pair 0 1 19 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 115 5 [0,115] 116 (.stop (.pair 0 1 23 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 116 5 [0,116] 117 (.stop (.pair 0 1 29 29)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 117 5 [0,117] 118 (.stop (.pair 0 1 79 79)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 118 5 [0,118] 119 (.stop (.pair 0 1 59 59)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 120 119 5 [0,119] 120 (.stop (.unitPair 0 1)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

namespace MinModulus

theorem not_validTuple_seven_mod_one_twenty (g : Fin 7 → ZMod 120) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 120) := ⟨⟨0, 1, by decide⟩⟩
  exact PrefixCertificate.not_validTuple_of_minimal_prefixes (by decide)
    PrefixCertificate.Seven120.unit_closed PrefixCertificate.Seven120.nonunit_closed g

end MinModulus

import MinModulus.G2Seven117.Assembly
import MinModulus.G2Seven117.BlockNonunit33
import MinModulus.G2Seven117.BlockUnit30
import MinModulus.G2Seven117.BlockUnit31

namespace MinModulus.PrefixCertificate.G2Seven117

theorem unit_closed (a : ℕ) (hlo : 2 ≤ a) (hhi : a < 117) :
    ClosedMinimalPrefix true 117 a 4 [0,1,a] (a+1) := by
  interval_cases a
  · exact (closedMinimalPrefix_of_verify true 117 2 4 [0,1,2] 3 (.stop (.collision 24)) (by decide +kernel))
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
  · exact unit_17_closed
  · exact unit_18_closed
  · exact unit_19_closed
  · exact unit_20_closed
  · exact unit_21_closed
  · exact (closedMinimalPrefix_of_verify true 117 22 4 [0,1,22] 23 (.stop (.third 0 2 1 16)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 23 4 [0,1,23] 24 (.stop (.third 2 1 0 101)) (by decide +kernel))
  · exact unit_24_closed
  · exact (closedMinimalPrefix_of_verify true 117 25 4 [0,1,25] 26 (.stop (.third 2 0 1 14)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 26 4 [0,1,26] 27 (.stop (.third 1 2 0 103)) (by decide +kernel))
  · exact unit_27_closed
  · exact unit_28_closed
  · exact (closedMinimalPrefix_of_verify true 117 29 4 [0,1,29] 30 (.stop (.third 2 0 1 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 30 4 [0,1,30] 31 (.stop (.third 1 2 0 113)) (by decide +kernel))
  · exact unit_31_closed
  · exact (closedMinimalPrefix_of_verify true 117 32 4 [0,1,32] 33 (.stop (.third 0 2 1 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 33 4 [0,1,33] 34 (.stop (.third 2 1 0 106)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 34 4 [0,1,34] 35 (.stop (.third 0 2 1 31)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 35 4 [0,1,35] 36 (.stop (.third 2 0 1 10)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 36 4 [0,1,36] 37 (.stop (.third 1 2 0 107)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 37 4 [0,1,37] 38 (.stop (.third 0 2 1 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 38 4 [0,1,38] 39 (.stop (.third 2 1 0 98)) (by decide +kernel))
  · exact unit_39_closed
  · exact (closedMinimalPrefix_of_verify true 117 40 4 [0,1,40] 41 (.stop (.third 2 0 1 38)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 41 4 [0,1,41] 42 (.stop (.third 0 2 1 20)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 42 4 [0,1,42] 43 (.stop (.third 2 1 0 97)) (by decide +kernel))
  · exact unit_43_closed
  · exact (closedMinimalPrefix_of_verify true 117 44 4 [0,1,44] 45 (.stop (.third 0 2 1 8)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 45 4 [0,1,45] 46 (.stop (.third 2 1 0 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 46 4 [0,1,46] 47 (.stop (.third 0 2 1 28)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 47 4 [0,1,47] 48 (.stop (.third 0 2 1 5)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 48 4 [0,1,48] 49 (.stop (.third 2 1 0 112)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 49 4 [0,1,49] 50 (.stop (.third 0 2 1 43)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 50 4 [0,1,50] 51 (.stop (.third 2 0 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 51 4 [0,1,51] 52 (.stop (.third 1 2 0 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 52 4 [0,1,52] 53 (.branch [.stop (.collision 144),.stop (.third 1 3 2 53),.stop (.third 3 0 1 17),.stop (.third 0 3 1 23),.stop (.third 1 3 2 23),.stop (.third 0 3 2 115),.stop (.third 0 3 1 2),.stop (.third 3 1 0 115),.stop (.third 3 0 1 23),.stop (.third 0 3 1 17),.stop (.third 1 3 2 17),.stop (.collision 4),.stop (.third 3 1 2 53),.stop (.third 2 3 0 92),.stop (.third 0 3 1 7),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 0 3 2 68),.stop (.third 1 0 3 116),.stop (.third 0 3 2 97),.stop (.third 0 3 1 38),.stop (.third 1 0 3 116),.stop (.third 0 3 1 40),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 0 3 1 10),.stop (.third 0 3 2 86),.stop (.third 1 0 3 116),.stop (.third 0 3 2 106),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 0 3 1 4),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 0 3 1 14),.stop (.third 1 0 3 116),.stop (.third 0 3 2 61),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 0 3 2 95),.stop (.third 1 0 3 116),.stop (.third 0 3 1 25),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 0 3 1 35),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 0 3 1 50),.stop (.third 1 0 3 116),.stop (.third 0 3 2 70),.stop (.third 0 3 1 29),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 53 4 [0,1,53] 54 (.branch [.stop (.collision 144),.stop (.third 0 3 2 100),.stop (.third 0 2 3 53),.stop (.third 1 3 2 23),.stop (.third 0 2 3 53),.stop (.third 0 3 1 2),.stop (.third 0 2 3 53),.stop (.third 2 0 3 64),.stop (.third 0 2 3 53),.stop (.third 3 1 0 100),.stop (.third 2 0 3 64),.stop (.third 0 2 3 53),.stop (.third 1 0 3 116),.stop (.third 0 2 3 53),.stop (.third 1 0 3 116),.stop (.third 0 2 3 53),.stop (.third 1 0 3 116),.stop (.third 0 2 3 53),.stop (.third 1 0 3 116),.stop (.third 0 2 3 53),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 0 2 3 53),.stop (.third 0 3 1 38),.stop (.third 0 2 3 53),.stop (.third 0 3 1 40),.stop (.third 0 2 3 53),.stop (.third 1 0 3 116),.stop (.third 0 2 3 53),.stop (.third 1 0 3 116),.stop (.third 0 2 3 53),.stop (.third 0 3 2 106),.stop (.third 1 0 3 116),.stop (.third 0 2 3 53),.stop (.third 0 3 1 4),.stop (.third 0 2 3 53),.stop (.third 1 0 3 116),.stop (.third 0 2 3 53),.stop (.third 0 3 1 14),.stop (.third 0 2 3 53),.stop (.third 1 0 3 116),.stop (.third 0 2 3 53),.stop (.third 1 0 3 116),.stop (.third 0 3 2 76),.stop (.third 0 2 3 53),.stop (.third 1 0 3 116),.stop (.third 0 2 3 53),.stop (.third 0 3 2 95),.stop (.third 0 2 3 53),.stop (.third 0 3 1 25),.stop (.third 0 2 3 53),.stop (.third 1 0 3 116),.stop (.third 0 2 3 53),.stop (.third 0 3 1 35),.stop (.third 1 0 3 116),.stop (.third 0 2 3 53),.stop (.third 0 3 1 50),.stop (.third 0 2 3 53),.stop (.third 1 0 3 116),.stop (.third 0 2 3 53),.stop (.third 1 0 3 116),.stop (.third 0 2 3 53),.stop (.third 1 0 3 116)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 54 4 [0,1,54] 55 (.branch [.stop (.third 0 3 2 100),.stop (.third 0 3 1 23),.stop (.third 1 2 3 53),.stop (.third 0 3 2 115),.stop (.third 0 3 1 2),.stop (.third 2 1 3 64),.stop (.third 0 3 2 94),.stop (.third 0 3 1 17),.stop (.third 1 2 3 53),.stop (.third 2 3 0 82),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 0 3 1 7),.stop (.third 0 3 2 74),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 0 3 2 89),.stop (.third 1 0 3 116),.stop (.third 0 3 2 109),.stop (.third 0 3 2 68),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 0 3 1 38),.stop (.third 1 0 3 116),.stop (.third 0 3 1 40),.stop (.third 0 3 2 98),.stop (.third 1 0 3 116),.stop (.third 0 3 1 10),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 0 3 2 83),.stop (.third 1 0 3 116),.stop (.third 0 3 1 4),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 0 3 1 14),.stop (.third 1 0 3 116),.stop (.third 0 3 2 61),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 0 3 2 76),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 0 3 2 55),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 0 3 1 25),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 0 3 2 85),.stop (.third 0 3 1 35),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 0 3 1 50),.stop (.third 1 0 3 116),.stop (.third 0 3 2 70),.stop (.third 0 3 1 29),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116),.stop (.third 1 0 3 116)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 55 4 [0,1,55] 56 (.stop (.third 2 0 1 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 56 4 [0,1,56] 57 (.stop (.third 0 2 1 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 57 4 [0,1,57] 58 (.stop (.third 2 1 0 94)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 58 4 [0,1,58] 59 (.stop (.third 2 0 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 59 4 [0,1,59] 60 (.stop (.third 0 2 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 60 4 [0,1,60] 61 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 61 4 [0,1,61] 62 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 62 4 [0,1,62] 63 (.stop (.third 0 2 1 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 63 4 [0,1,63] 64 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 64 4 [0,1,64] 65 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 65 4 [0,1,65] 66 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 66 4 [0,1,66] 67 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 67 4 [0,1,67] 68 (.stop (.third 0 2 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 68 4 [0,1,68] 69 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 69 4 [0,1,69] 70 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 70 4 [0,1,70] 71 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 71 4 [0,1,71] 72 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 72 4 [0,1,72] 73 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 73 4 [0,1,73] 74 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 74 4 [0,1,74] 75 (.stop (.third 0 2 1 68)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 75 4 [0,1,75] 76 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 76 4 [0,1,76] 77 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 77 4 [0,1,77] 78 (.stop (.third 0 2 1 38)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 78 4 [0,1,78] 79 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 79 4 [0,1,79] 80 (.stop (.third 0 2 1 40)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 80 4 [0,1,80] 81 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 81 4 [0,1,81] 82 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 82 4 [0,1,82] 83 (.stop (.third 0 2 1 10)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 83 4 [0,1,83] 84 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 84 4 [0,1,84] 85 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 85 4 [0,1,85] 86 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 86 4 [0,1,86] 87 (.stop (.third 0 2 1 83)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 87 4 [0,1,87] 88 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 88 4 [0,1,88] 89 (.stop (.third 0 2 1 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 89 4 [0,1,89] 90 (.stop (.third 0 2 1 71)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 90 4 [0,1,90] 91 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 91 4 [0,1,91] 92 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 92 4 [0,1,92] 93 (.stop (.third 0 2 1 14)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 93 4 [0,1,93] 94 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 94 4 [0,1,94] 95 (.stop (.third 0 2 1 61)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 95 4 [0,1,95] 96 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 96 4 [0,1,96] 97 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 97 4 [0,1,97] 98 (.stop (.third 0 2 1 76)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 98 4 [0,1,98] 99 (.stop (.third 0 2 1 80)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 99 4 [0,1,99] 100 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 100 4 [0,1,100] 101 (.stop (.third 0 2 1 55)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 101 4 [0,1,101] 102 (.stop (.third 0 2 1 95)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 102 4 [0,1,102] 103 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 103 4 [0,1,103] 104 (.stop (.third 0 2 1 25)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 104 4 [0,1,104] 105 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 105 4 [0,1,105] 106 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 106 4 [0,1,106] 107 (.stop (.third 0 2 1 85)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 107 4 [0,1,107] 108 (.stop (.third 0 2 1 35)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 108 4 [0,1,108] 109 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 109 4 [0,1,109] 110 (.stop (.third 0 2 1 73)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 110 4 [0,1,110] 111 (.stop (.third 0 2 1 50)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 111 4 [0,1,111] 112 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 112 4 [0,1,112] 113 (.stop (.third 0 2 1 70)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 113 4 [0,1,113] 114 (.stop (.third 0 2 1 29)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 114 4 [0,1,114] 115 (.stop (.third 1 0 2 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 115 4 [0,1,115] 116 (.stop (.third 0 2 1 58)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 117 116 4 [0,1,116] 117 (.stop (.third 1 0 2 116)) (by decide +kernel))

theorem nonunit_closed (a : ℕ) (hlo : 1 ≤ a) (hhi : a < 117) :
    ClosedMinimalPrefix false 117 a 5 [0,a] (a+1) := by
  interval_cases a
  · exact (closedMinimalPrefix_of_verify false 117 1 5 [0,1] 2 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 2 5 [0,2] 3 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact nonunit_3_closed
  · exact (closedMinimalPrefix_of_verify false 117 4 5 [0,4] 5 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 5 5 [0,5] 6 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 6 5 [0,6] 7 (.stop (.pair 0 1 20 41)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 7 5 [0,7] 8 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 8 5 [0,8] 9 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact nonunit_9_closed
  · exact (closedMinimalPrefix_of_verify false 117 10 5 [0,10] 11 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 11 5 [0,11] 12 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 12 5 [0,12] 13 (.stop (.pair 0 1 10 82)) (by decide +kernel))
  · exact nonunit_13_closed
  · exact (closedMinimalPrefix_of_verify false 117 14 5 [0,14] 15 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 15 5 [0,15] 16 (.stop (.pair 0 1 8 44)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 16 5 [0,16] 17 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 17 5 [0,17] 18 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 18 5 [0,18] 19 (.stop (.pair 0 1 7 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 19 5 [0,19] 20 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 20 5 [0,20] 21 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 21 5 [0,21] 22 (.stop (.pair 0 1 28 46)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 22 5 [0,22] 23 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 23 5 [0,23] 24 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 24 5 [0,24] 25 (.stop (.pair 0 1 5 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 25 5 [0,25] 26 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 26 5 [0,26] 27 (.stop (.pair 0 1 5 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 27 5 [0,27] 28 (.stop (.pair 0 1 22 16)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 28 5 [0,28] 29 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 29 5 [0,29] 30 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 30 5 [0,30] 31 (.stop (.pair 0 1 4 88)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 31 5 [0,31] 32 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 32 5 [0,32] 33 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 33 5 [0,33] 34 (.stop (.pair 0 1 32 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 34 5 [0,34] 35 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 35 5 [0,35] 36 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 36 5 [0,36] 37 (.stop (.pair 0 1 10 82)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 37 5 [0,37] 38 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 38 5 [0,38] 39 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact nonunit_39_closed
  · exact (closedMinimalPrefix_of_verify false 117 40 5 [0,40] 41 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 41 5 [0,41] 42 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 42 5 [0,42] 43 (.stop (.pair 0 1 14 92)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 43 5 [0,43] 44 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 44 5 [0,44] 45 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 45 5 [0,45] 46 (.stop (.pair 0 1 8 44)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 46 5 [0,46] 47 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 47 5 [0,47] 48 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 48 5 [0,48] 49 (.stop (.pair 0 1 22 16)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 49 5 [0,49] 50 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 50 5 [0,50] 51 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 51 5 [0,51] 52 (.stop (.pair 0 1 23 56)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 52 5 [0,52] 53 (.stop (.pair 0 1 7 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 53 5 [0,53] 54 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 54 5 [0,54] 55 (.stop (.pair 0 1 11 32)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 55 5 [0,55] 56 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 56 5 [0,56] 57 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 57 5 [0,57] 58 (.stop (.pair 0 1 37 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 58 5 [0,58] 59 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 59 5 [0,59] 60 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 60 5 [0,60] 61 (.stop (.pair 0 1 2 59)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 61 5 [0,61] 62 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 62 5 [0,62] 63 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 63 5 [0,63] 64 (.stop (.pair 0 1 2 59)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 64 5 [0,64] 65 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 65 5 [0,65] 66 (.stop (.pair 0 1 2 59)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 66 5 [0,66] 67 (.stop (.pair 0 1 16 22)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 67 5 [0,67] 68 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 68 5 [0,68] 69 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 69 5 [0,69] 70 (.stop (.pair 0 1 17 62)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 70 5 [0,70] 71 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 71 5 [0,71] 72 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 72 5 [0,72] 73 (.stop (.pair 0 1 5 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 73 5 [0,73] 74 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 74 5 [0,74] 75 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 75 5 [0,75] 76 (.stop (.pair 0 1 25 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 76 5 [0,76] 77 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 77 5 [0,77] 78 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 78 5 [0,78] 79 (.stop (.pair 0 1 2 59)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 79 5 [0,79] 80 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 80 5 [0,80] 81 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 81 5 [0,81] 82 (.stop (.pair 0 1 16 22)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 82 5 [0,82] 83 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 83 5 [0,83] 84 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 84 5 [0,84] 85 (.stop (.pair 0 1 7 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 85 5 [0,85] 86 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 86 5 [0,86] 87 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 87 5 [0,87] 88 (.stop (.pair 0 1 35 107)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 88 5 [0,88] 89 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 89 5 [0,89] 90 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 90 5 [0,90] 91 (.stop (.pair 0 1 4 88)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 91 5 [0,91] 92 (.stop (.pair 0 1 4 88)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 92 5 [0,92] 93 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 93 5 [0,93] 94 (.stop (.pair 0 1 34 31)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 94 5 [0,94] 95 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 95 5 [0,95] 96 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 96 5 [0,96] 97 (.stop (.pair 0 1 11 32)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 97 5 [0,97] 98 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 98 5 [0,98] 99 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 99 5 [0,99] 100 (.stop (.pair 0 1 19 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 100 5 [0,100] 101 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 101 5 [0,101] 102 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 102 5 [0,102] 103 (.stop (.pair 0 1 31 34)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 103 5 [0,103] 104 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 104 5 [0,104] 105 (.stop (.pair 0 1 8 44)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 105 5 [0,105] 106 (.stop (.pair 0 1 29 113)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 106 5 [0,106] 107 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 107 5 [0,107] 108 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 108 5 [0,108] 109 (.stop (.pair 0 1 25 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 109 5 [0,109] 110 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 110 5 [0,110] 111 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 111 5 [0,111] 112 (.stop (.pair 0 1 19 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 112 5 [0,112] 113 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 113 5 [0,113] 114 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 114 5 [0,114] 115 (.stop (.pair 0 1 38 77)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 115 5 [0,115] 116 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 117 116 5 [0,116] 117 (.stop (.unitPair 0 1)) (by decide +kernel))

end MinModulus.PrefixCertificate.G2Seven117

namespace MinModulus

theorem not_validTuple_seven_mod_117 (g : Fin 7 → ZMod 117) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 117) := ⟨⟨0, 1, by decide⟩⟩
  exact PrefixCertificate.not_validTuple_of_minimal_prefixes (by decide)
    PrefixCertificate.G2Seven117.unit_closed PrefixCertificate.G2Seven117.nonunit_closed g

end MinModulus

#print axioms MinModulus.not_validTuple_seven_mod_117

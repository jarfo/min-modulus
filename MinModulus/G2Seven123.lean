import MinModulus.G2Seven123.Assembly
import MinModulus.G2Seven123.BlockNonunit42
import MinModulus.G2Seven123.BlockUnit40

namespace MinModulus.PrefixCertificate.G2Seven123

theorem unit_closed (a : ℕ) (hlo : 2 ≤ a) (hhi : a < 123) :
    ClosedMinimalPrefix true 123 a 4 [0,1,a] (a+1) := by
  interval_cases a
  · exact (closedMinimalPrefix_of_verify true 123 2 4 [0,1,2] 3 (.stop (.collision 24)) (by decide +kernel))
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
  · exact (closedMinimalPrefix_of_verify true 123 19 4 [0,1,19] 20 (.stop (.third 0 2 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 20 4 [0,1,20] 21 (.stop (.third 2 1 0 110)) (by decide +kernel))
  · exact unit_21_closed
  · exact unit_22_closed
  · exact (closedMinimalPrefix_of_verify true 123 23 4 [0,1,23] 24 (.stop (.third 2 0 1 16)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 24 4 [0,1,24] 25 (.stop (.third 1 2 0 107)) (by decide +kernel))
  · exact unit_25_closed
  · exact unit_26_closed
  · exact unit_27_closed
  · exact (closedMinimalPrefix_of_verify true 123 28 4 [0,1,28] 29 (.stop (.third 0 2 1 22)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 29 4 [0,1,29] 30 (.stop (.third 0 2 1 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 30 4 [0,1,30] 31 (.stop (.third 2 1 0 106)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 31 4 [0,1,31] 32 (.stop (.third 0 2 1 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 32 4 [0,1,32] 33 (.stop (.third 2 1 0 119)) (by decide +kernel))
  · exact unit_33_closed
  · exact unit_34_closed
  · exact (closedMinimalPrefix_of_verify true 123 35 4 [0,1,35] 36 (.stop (.third 2 0 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 36 4 [0,1,36] 37 (.stop (.third 1 2 0 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 37 4 [0,1,37] 38 (.stop (.third 0 2 1 10)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 38 4 [0,1,38] 39 (.stop (.third 2 1 0 113)) (by decide +kernel))
  · exact unit_39_closed
  · exact unit_40_closed
  · exact unit_41_closed
  · exact unit_42_closed
  · exact (closedMinimalPrefix_of_verify true 123 43 4 [0,1,43] 44 (.stop (.third 2 0 1 20)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 44 4 [0,1,44] 45 (.stop (.third 0 2 1 14)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 45 4 [0,1,45] 46 (.stop (.third 2 1 0 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 46 4 [0,1,46] 47 (.stop (.third 2 0 1 8)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 47 4 [0,1,47] 48 (.stop (.third 1 2 0 115)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 48 4 [0,1,48] 49 (.stop (.third 1 2 0 89)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 49 4 [0,1,49] 50 (.stop (.third 2 0 1 5)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 50 4 [0,1,50] 51 (.stop (.third 0 2 1 32)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 51 4 [0,1,51] 52 (.stop (.third 2 1 0 91)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 52 4 [0,1,52] 53 (.stop (.third 2 0 1 26)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 53 4 [0,1,53] 54 (.stop (.third 1 2 0 97)) (by decide +kernel))
  · exact unit_54_closed
  · exact (closedMinimalPrefix_of_verify true 123 55 4 [0,1,55] 56 (.stop (.third 2 0 1 38)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 56 4 [0,1,56] 57 (.stop (.third 0 2 1 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 57 4 [0,1,57] 58 (.stop (.third 2 1 0 112)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 58 4 [0,1,58] 59 (.stop (.third 2 0 1 53)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 59 4 [0,1,59] 60 (.stop (.third 1 2 0 70)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 60 4 [0,1,60] 61 (.stop (.third 1 2 0 98)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 61 4 [0,1,61] 62 (.stop (.third 2 0 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 62 4 [0,1,62] 63 (.stop (.third 0 2 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 63 4 [0,1,63] 64 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 64 4 [0,1,64] 65 (.stop (.third 0 2 1 25)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 65 4 [0,1,65] 66 (.stop (.third 0 2 1 53)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 66 4 [0,1,66] 67 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 67 4 [0,1,67] 68 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 68 4 [0,1,68] 69 (.stop (.third 0 2 1 38)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 69 4 [0,1,69] 70 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 70 4 [0,1,70] 71 (.stop (.third 0 2 1 58)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 71 4 [0,1,71] 72 (.stop (.third 0 2 1 26)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 72 4 [0,1,72] 73 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 73 4 [0,1,73] 74 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 74 4 [0,1,74] 75 (.stop (.third 0 2 1 5)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 75 4 [0,1,75] 76 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 76 4 [0,1,76] 77 (.stop (.third 0 2 1 34)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 77 4 [0,1,77] 78 (.stop (.third 0 2 1 8)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 78 4 [0,1,78] 79 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 79 4 [0,1,79] 80 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 80 4 [0,1,80] 81 (.stop (.third 0 2 1 20)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 81 4 [0,1,81] 82 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 82 4 [0,1,82] 83 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 83 4 [0,1,83] 84 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 84 4 [0,1,84] 85 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 85 4 [0,1,85] 86 (.stop (.third 0 2 1 55)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 86 4 [0,1,86] 87 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 87 4 [0,1,87] 88 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 88 4 [0,1,88] 89 (.stop (.third 0 2 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 89 4 [0,1,89] 90 (.stop (.third 0 2 1 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 90 4 [0,1,90] 91 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 91 4 [0,1,91] 92 (.stop (.third 0 2 1 73)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 92 4 [0,1,92] 93 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 93 4 [0,1,93] 94 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 94 4 [0,1,94] 95 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 95 4 [0,1,95] 96 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 96 4 [0,1,96] 97 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 97 4 [0,1,97] 98 (.stop (.third 0 2 1 52)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 98 4 [0,1,98] 99 (.stop (.third 0 2 1 59)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 99 4 [0,1,99] 100 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 100 4 [0,1,100] 101 (.stop (.third 0 2 1 16)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 101 4 [0,1,101] 102 (.stop (.third 0 2 1 95)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 102 4 [0,1,102] 103 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 103 4 [0,1,103] 104 (.stop (.third 0 2 1 43)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 104 4 [0,1,104] 105 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 105 4 [0,1,105] 106 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 106 4 [0,1,106] 107 (.stop (.third 0 2 1 94)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 107 4 [0,1,107] 108 (.stop (.third 0 2 1 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 108 4 [0,1,108] 109 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 109 4 [0,1,109] 110 (.stop (.third 0 2 1 79)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 110 4 [0,1,110] 111 (.stop (.third 0 2 1 104)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 111 4 [0,1,111] 112 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 112 4 [0,1,112] 113 (.stop (.third 0 2 1 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 113 4 [0,1,113] 114 (.stop (.third 0 2 1 86)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 114 4 [0,1,114] 115 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 115 4 [0,1,115] 116 (.stop (.third 0 2 1 46)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 116 4 [0,1,116] 117 (.stop (.third 0 2 1 35)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 117 4 [0,1,117] 118 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 118 4 [0,1,118] 119 (.stop (.third 0 2 1 49)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 119 4 [0,1,119] 120 (.stop (.third 0 2 1 92)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 120 4 [0,1,120] 121 (.stop (.third 1 0 2 122)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 121 4 [0,1,121] 122 (.stop (.third 0 2 1 61)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 123 122 4 [0,1,122] 123 (.stop (.third 1 0 2 122)) (by decide +kernel))

theorem nonunit_closed (a : ℕ) (hlo : 1 ≤ a) (hhi : a < 123) :
    ClosedMinimalPrefix false 123 a 5 [0,a] (a+1) := by
  interval_cases a
  · exact (closedMinimalPrefix_of_verify false 123 1 5 [0,1] 2 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 2 5 [0,2] 3 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact nonunit_3_closed
  · exact (closedMinimalPrefix_of_verify false 123 4 5 [0,4] 5 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 5 5 [0,5] 6 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 6 5 [0,6] 7 (.stop (.pair 0 1 62 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 7 5 [0,7] 8 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 8 5 [0,8] 9 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 9 5 [0,9] 10 (.stop (.pair 0 1 14 44)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 10 5 [0,10] 11 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 11 5 [0,11] 12 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 12 5 [0,12] 13 (.stop (.pair 0 1 31 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 13 5 [0,13] 14 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 14 5 [0,14] 15 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 15 5 [0,15] 16 (.stop (.pair 0 1 74 5)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 16 5 [0,16] 17 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 17 5 [0,17] 18 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 18 5 [0,18] 19 (.stop (.pair 0 1 7 88)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 19 5 [0,19] 20 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 20 5 [0,20] 21 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 21 5 [0,21] 22 (.stop (.pair 0 1 47 89)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 22 5 [0,22] 23 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 23 5 [0,23] 24 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 24 5 [0,24] 25 (.stop (.pair 0 1 77 8)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 25 5 [0,25] 26 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 26 5 [0,26] 27 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 27 5 [0,27] 28 (.stop (.pair 0 1 32 50)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 28 5 [0,28] 29 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 29 5 [0,29] 30 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 30 5 [0,30] 31 (.stop (.pair 0 1 37 10)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 31 5 [0,31] 32 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 32 5 [0,32] 33 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 33 5 [0,33] 34 (.stop (.pair 0 1 56 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 34 5 [0,34] 35 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 35 5 [0,35] 36 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 36 5 [0,36] 37 (.stop (.pair 0 1 65 53)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 37 5 [0,37] 38 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 38 5 [0,38] 39 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 39 5 [0,39] 40 (.stop (.pair 0 1 19 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 40 5 [0,40] 41 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact nonunit_41_closed
  · exact (closedMinimalPrefix_of_verify false 123 42 5 [0,42] 43 (.stop (.pair 0 1 44 14)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 43 5 [0,43] 44 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 44 5 [0,44] 45 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 45 5 [0,45] 46 (.stop (.pair 0 1 11 56)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 46 5 [0,46] 47 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 47 5 [0,47] 48 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 48 5 [0,48] 49 (.stop (.pair 0 1 59 98)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 49 5 [0,49] 50 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 50 5 [0,50] 51 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 51 5 [0,51] 52 (.stop (.pair 0 1 29 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 52 5 [0,52] 53 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 53 5 [0,53] 54 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 54 5 [0,54] 55 (.stop (.pair 0 1 16 100)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 55 5 [0,55] 56 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 56 5 [0,56] 57 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 57 5 [0,57] 58 (.stop (.pair 0 1 13 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 58 5 [0,58] 59 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 59 5 [0,59] 60 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 60 5 [0,60] 61 (.stop (.pair 0 1 80 20)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 61 5 [0,61] 62 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 62 5 [0,62] 63 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 63 5 [0,63] 64 (.stop (.pair 0 1 2 62)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 64 5 [0,64] 65 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 65 5 [0,65] 66 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 66 5 [0,66] 67 (.stop (.pair 0 1 28 22)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 67 5 [0,67] 68 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 68 5 [0,68] 69 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 69 5 [0,69] 70 (.stop (.pair 0 1 25 64)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 70 5 [0,70] 71 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 71 5 [0,71] 72 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 72 5 [0,72] 73 (.stop (.pair 0 1 53 65)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 73 5 [0,73] 74 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 74 5 [0,74] 75 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 75 5 [0,75] 76 (.stop (.pair 0 1 23 107)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 76 5 [0,76] 77 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 77 5 [0,77] 78 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 78 5 [0,78] 79 (.stop (.pair 0 1 71 26)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 79 5 [0,79] 80 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 80 5 [0,80] 81 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 81 5 [0,81] 82 (.stop (.pair 0 1 38 68)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 82 5 [0,82] 83 (.stop (.pair 0 1 2 62)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 83 5 [0,83] 84 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 84 5 [0,84] 85 (.stop (.pair 0 1 22 28)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 85 5 [0,85] 86 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 86 5 [0,86] 87 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 87 5 [0,87] 88 (.stop (.pair 0 1 17 29)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 88 5 [0,88] 89 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 89 5 [0,89] 90 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 90 5 [0,90] 91 (.stop (.pair 0 1 26 71)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 91 5 [0,91] 92 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 92 5 [0,92] 93 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 93 5 [0,93] 94 (.stop (.pair 0 1 4 31)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 94 5 [0,94] 95 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 95 5 [0,95] 96 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 96 5 [0,96] 97 (.stop (.pair 0 1 50 32)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 97 5 [0,97] 98 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 98 5 [0,98] 99 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 99 5 [0,99] 100 (.stop (.pair 0 1 5 74)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 100 5 [0,100] 101 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 101 5 [0,101] 102 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 102 5 [0,102] 103 (.stop (.pair 0 1 35 116)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 103 5 [0,103] 104 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 104 5 [0,104] 105 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 105 5 [0,105] 106 (.stop (.pair 0 1 34 76)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 106 5 [0,106] 107 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 107 5 [0,107] 108 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 108 5 [0,108] 109 (.stop (.pair 0 1 8 77)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 109 5 [0,109] 110 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 110 5 [0,110] 111 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 111 5 [0,111] 112 (.stop (.pair 0 1 10 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 112 5 [0,112] 113 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 113 5 [0,113] 114 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 114 5 [0,114] 115 (.stop (.pair 0 1 68 38)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 115 5 [0,115] 116 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 116 5 [0,116] 117 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 117 5 [0,117] 118 (.stop (.pair 0 1 20 80)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 118 5 [0,118] 119 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 119 5 [0,119] 120 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 120 5 [0,120] 121 (.stop (.pair 0 1 40 40)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 121 5 [0,121] 122 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 123 122 5 [0,122] 123 (.stop (.unitPair 0 1)) (by decide +kernel))

end MinModulus.PrefixCertificate.G2Seven123

namespace MinModulus

theorem not_validTuple_seven_mod_123 (g : Fin 7 → ZMod 123) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 123) := ⟨⟨0, 1, by decide⟩⟩
  exact PrefixCertificate.not_validTuple_of_minimal_prefixes (by decide)
    PrefixCertificate.G2Seven123.unit_closed PrefixCertificate.G2Seven123.nonunit_closed g

end MinModulus

#print axioms MinModulus.not_validTuple_seven_mod_123

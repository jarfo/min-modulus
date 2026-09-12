import MinModulus.G2Seven111.Assembly
import MinModulus.G2Seven111.BlockNonunit22
import MinModulus.G2Seven111.BlockUnit20
import MinModulus.G2Seven111.BlockUnit21

namespace MinModulus.PrefixCertificate.G2Seven111

theorem unit_closed (a : ℕ) (hlo : 2 ≤ a) (hhi : a < 111) :
    ClosedMinimalPrefix true 111 a 4 [0,1,a] (a+1) := by
  interval_cases a
  · exact (closedMinimalPrefix_of_verify true 111 2 4 [0,1,2] 3 (.stop (.collision 24)) (by decide +kernel))
  · exact unit_3_closed
  · exact unit_4_closed
  · exact unit_5_closed
  · exact unit_6_closed
  · exact unit_7_closed
  · exact unit_8_closed
  · exact unit_9_closed
  · exact unit_10_closed
  · exact unit_11_closed
  · exact (closedMinimalPrefix_of_verify true 111 12 4 [0,1,12] 13 (.stop (.third 1 2 0 101)) (by decide +kernel))
  · exact unit_13_closed
  · exact (closedMinimalPrefix_of_verify true 111 14 4 [0,1,14] 15 (.stop (.third 0 2 1 8)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 15 4 [0,1,15] 16 (.stop (.third 2 1 0 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 16 4 [0,1,16] 17 (.stop (.third 0 2 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 17 4 [0,1,17] 18 (.stop (.third 2 0 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 18 4 [0,1,18] 19 (.stop (.third 1 2 0 98)) (by decide +kernel))
  · exact unit_19_closed
  · exact unit_20_closed
  · exact unit_21_closed
  · exact (closedMinimalPrefix_of_verify true 111 22 4 [0,1,22] 23 (.stop (.third 2 0 1 5)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 23 4 [0,1,23] 24 (.stop (.third 1 2 0 106)) (by decide +kernel))
  · exact unit_24_closed
  · exact unit_25_closed
  · exact unit_26_closed
  · exact unit_27_closed
  · exact (closedMinimalPrefix_of_verify true 111 28 4 [0,1,28] 29 (.stop (.third 0 2 1 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 29 4 [0,1,29] 30 (.stop (.third 0 2 1 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 30 4 [0,1,30] 31 (.stop (.third 2 1 0 88)) (by decide +kernel))
  · exact unit_31_closed
  · exact unit_32_closed
  · exact unit_33_closed
  · exact unit_34_closed
  · exact (closedMinimalPrefix_of_verify true 111 35 4 [0,1,35] 36 (.stop (.third 2 0 1 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 36 4 [0,1,36] 37 (.stop (.third 1 2 0 92)) (by decide +kernel))
  · exact unit_37_closed
  · exact unit_38_closed
  · exact unit_39_closed
  · exact (closedMinimalPrefix_of_verify true 111 40 4 [0,1,40] 41 (.stop (.third 0 2 1 25)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 41 4 [0,1,41] 42 (.stop (.third 2 1 0 86)) (by decide +kernel))
  · exact unit_42_closed
  · exact (closedMinimalPrefix_of_verify true 111 43 4 [0,1,43] 44 (.stop (.third 0 2 1 31)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 44 4 [0,1,44] 45 (.stop (.third 2 1 0 80)) (by decide +kernel))
  · exact unit_45_closed
  · exact (closedMinimalPrefix_of_verify true 111 46 4 [0,1,46] 47 (.stop (.third 2 0 1 41)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 47 4 [0,1,47] 48 (.stop (.third 0 2 1 26)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 48 4 [0,1,48] 49 (.stop (.third 2 1 0 85)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 49 4 [0,1,49] 50 (.stop (.third 0 2 1 34)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 50 4 [0,1,50] 51 (.stop (.third 0 2 1 20)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 51 4 [0,1,51] 52 (.stop (.third 2 1 0 91)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 52 4 [0,1,52] 53 (.stop (.third 2 0 1 32)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 53 4 [0,1,53] 54 (.stop (.third 0 2 1 44)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 54 4 [0,1,54] 55 (.stop (.third 2 1 0 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 55 4 [0,1,55] 56 (.stop (.third 2 0 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 56 4 [0,1,56] 57 (.stop (.third 0 2 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 57 4 [0,1,57] 58 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 58 4 [0,1,58] 59 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 59 4 [0,1,59] 60 (.stop (.third 0 2 1 32)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 60 4 [0,1,60] 61 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 61 4 [0,1,61] 62 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 62 4 [0,1,62] 63 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 63 4 [0,1,63] 64 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 64 4 [0,1,64] 65 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 65 4 [0,1,65] 66 (.stop (.third 0 2 1 41)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 66 4 [0,1,66] 67 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 67 4 [0,1,67] 68 (.stop (.third 0 2 1 58)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 68 4 [0,1,68] 69 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 69 4 [0,1,69] 70 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 70 4 [0,1,70] 71 (.stop (.third 0 2 1 46)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 71 4 [0,1,71] 72 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 72 4 [0,1,72] 73 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 73 4 [0,1,73] 74 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 74 4 [0,1,74] 75 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 75 4 [0,1,75] 76 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 76 4 [0,1,76] 77 (.stop (.third 0 2 1 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 77 4 [0,1,77] 78 (.stop (.third 0 2 1 62)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 78 4 [0,1,78] 79 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 79 4 [0,1,79] 80 (.stop (.third 0 2 1 52)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 80 4 [0,1,80] 81 (.stop (.third 0 2 1 68)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 81 4 [0,1,81] 82 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 82 4 [0,1,82] 83 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 83 4 [0,1,83] 84 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 84 4 [0,1,84] 85 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 85 4 [0,1,85] 86 (.stop (.third 0 2 1 64)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 86 4 [0,1,86] 87 (.stop (.third 0 2 1 71)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 87 4 [0,1,87] 88 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 88 4 [0,1,88] 89 (.stop (.third 0 2 1 82)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 89 4 [0,1,89] 90 (.stop (.third 0 2 1 5)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 90 4 [0,1,90] 91 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 91 4 [0,1,91] 92 (.stop (.third 0 2 1 61)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 92 4 [0,1,92] 93 (.stop (.third 0 2 1 35)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 93 4 [0,1,93] 94 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 94 4 [0,1,94] 95 (.stop (.third 0 2 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 95 4 [0,1,95] 96 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 96 4 [0,1,96] 97 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 97 4 [0,1,97] 98 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 98 4 [0,1,98] 99 (.stop (.third 0 2 1 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 99 4 [0,1,99] 100 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 100 4 [0,1,100] 101 (.stop (.third 0 2 1 10)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 101 4 [0,1,101] 102 (.stop (.third 0 2 1 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 102 4 [0,1,102] 103 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 103 4 [0,1,103] 104 (.stop (.third 0 2 1 97)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 104 4 [0,1,104] 105 (.stop (.third 0 2 1 95)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 105 4 [0,1,105] 106 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 106 4 [0,1,106] 107 (.stop (.third 0 2 1 22)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 107 4 [0,1,107] 108 (.stop (.third 0 2 1 83)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 108 4 [0,1,108] 109 (.stop (.third 1 0 2 110)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 109 4 [0,1,109] 110 (.stop (.third 0 2 1 55)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 111 110 4 [0,1,110] 111 (.stop (.third 1 0 2 110)) (by decide +kernel))

theorem nonunit_closed (a : ℕ) (hlo : 1 ≤ a) (hhi : a < 111) :
    ClosedMinimalPrefix false 111 a 5 [0,a] (a+1) := by
  interval_cases a
  · exact (closedMinimalPrefix_of_verify false 111 1 5 [0,1] 2 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 2 5 [0,2] 3 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact nonunit_3_closed
  · exact (closedMinimalPrefix_of_verify false 111 4 5 [0,4] 5 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 5 5 [0,5] 6 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 6 5 [0,6] 7 (.stop (.pair 0 1 19 76)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 7 5 [0,7] 8 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 8 5 [0,8] 9 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 9 5 [0,9] 10 (.stop (.pair 0 1 25 40)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 10 5 [0,10] 11 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 11 5 [0,11] 12 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 12 5 [0,12] 13 (.stop (.pair 0 1 28 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 13 5 [0,13] 14 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 14 5 [0,14] 15 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 15 5 [0,15] 16 (.stop (.pair 0 1 52 79)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 16 5 [0,16] 17 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 17 5 [0,17] 18 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 18 5 [0,18] 19 (.stop (.pair 0 1 31 43)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 19 5 [0,19] 20 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 20 5 [0,20] 21 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 21 5 [0,21] 22 (.stop (.pair 0 1 16 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 22 5 [0,22] 23 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 23 5 [0,23] 24 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 24 5 [0,24] 25 (.stop (.pair 0 1 14 8)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 25 5 [0,25] 26 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 26 5 [0,26] 27 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 27 5 [0,27] 28 (.stop (.pair 0 1 70 46)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 28 5 [0,28] 29 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 29 5 [0,29] 30 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 30 5 [0,30] 31 (.stop (.pair 0 1 26 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 31 5 [0,31] 32 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 32 5 [0,32] 33 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 33 5 [0,33] 34 (.stop (.pair 0 1 64 85)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 34 5 [0,34] 35 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 35 5 [0,35] 36 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 36 5 [0,36] 37 (.stop (.pair 0 1 34 49)) (by decide +kernel))
  · exact nonunit_37_closed
  · exact (closedMinimalPrefix_of_verify false 111 38 5 [0,38] 39 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 39 5 [0,39] 40 (.stop (.pair 0 1 20 50)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 40 5 [0,40] 41 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 41 5 [0,41] 42 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 42 5 [0,42] 43 (.stop (.pair 0 1 8 14)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 43 5 [0,43] 44 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 44 5 [0,44] 45 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 45 5 [0,45] 46 (.stop (.pair 0 1 5 89)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 46 5 [0,46] 47 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 47 5 [0,47] 48 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 48 5 [0,48] 49 (.stop (.pair 0 1 7 16)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 49 5 [0,49] 50 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 50 5 [0,50] 51 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 51 5 [0,51] 52 (.stop (.pair 0 1 61 91)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 52 5 [0,52] 53 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 53 5 [0,53] 54 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 54 5 [0,54] 55 (.stop (.pair 0 1 35 92)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 55 5 [0,55] 56 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 56 5 [0,56] 57 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 57 5 [0,57] 58 (.stop (.pair 0 1 2 56)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 58 5 [0,58] 59 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 59 5 [0,59] 60 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 60 5 [0,60] 61 (.stop (.pair 0 1 13 94)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 61 5 [0,61] 62 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 62 5 [0,62] 63 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 63 5 [0,63] 64 (.stop (.pair 0 1 67 58)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 64 5 [0,64] 65 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 65 5 [0,65] 66 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 66 5 [0,66] 67 (.stop (.pair 0 1 32 59)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 67 5 [0,67] 68 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 68 5 [0,68] 69 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 69 5 [0,69] 70 (.stop (.pair 0 1 29 23)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 70 5 [0,70] 71 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 71 5 [0,71] 72 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 72 5 [0,72] 73 (.stop (.pair 0 1 17 98)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 73 5 [0,73] 74 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 74 5 [0,74] 75 (.stop (.pair 0 1 2 56)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 75 5 [0,75] 76 (.stop (.pair 0 1 40 25)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 76 5 [0,76] 77 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 77 5 [0,77] 78 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 78 5 [0,78] 79 (.stop (.pair 0 1 10 100)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 79 5 [0,79] 80 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 80 5 [0,80] 81 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 81 5 [0,81] 82 (.stop (.pair 0 1 11 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 82 5 [0,82] 83 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 83 5 [0,83] 84 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 84 5 [0,84] 85 (.stop (.pair 0 1 4 28)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 85 5 [0,85] 86 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 86 5 [0,86] 87 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 87 5 [0,87] 88 (.stop (.pair 0 1 23 29)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 88 5 [0,88] 89 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 89 5 [0,89] 90 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 90 5 [0,90] 91 (.stop (.pair 0 1 58 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 91 5 [0,91] 92 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 92 5 [0,92] 93 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 93 5 [0,93] 94 (.stop (.pair 0 1 43 31)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 94 5 [0,94] 95 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 95 5 [0,95] 96 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 96 5 [0,96] 97 (.stop (.pair 0 1 22 106)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 97 5 [0,97] 98 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 98 5 [0,98] 99 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 99 5 [0,99] 100 (.stop (.pair 0 1 46 70)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 100 5 [0,100] 101 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 101 5 [0,101] 102 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 102 5 [0,102] 103 (.stop (.pair 0 1 49 34)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 103 5 [0,103] 104 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 104 5 [0,104] 105 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 105 5 [0,105] 106 (.stop (.pair 0 1 55 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 106 5 [0,106] 107 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 107 5 [0,107] 108 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 108 5 [0,108] 109 (.stop (.pair 0 1 73 73)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 109 5 [0,109] 110 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 111 110 5 [0,110] 111 (.stop (.unitPair 0 1)) (by decide +kernel))

end MinModulus.PrefixCertificate.G2Seven111

namespace MinModulus

theorem not_validTuple_seven_mod_111 (g : Fin 7 → ZMod 111) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 111) := ⟨⟨0, 1, by decide⟩⟩
  exact PrefixCertificate.not_validTuple_of_minimal_prefixes (by decide)
    PrefixCertificate.G2Seven111.unit_closed PrefixCertificate.G2Seven111.nonunit_closed g

end MinModulus

#print axioms MinModulus.not_validTuple_seven_mod_111

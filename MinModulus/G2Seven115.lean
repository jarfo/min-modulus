import MinModulus.G2Seven115.Assembly
import MinModulus.G2Seven115.BlockNonunit22
import MinModulus.G2Seven115.BlockUnit21

namespace MinModulus.PrefixCertificate.G2Seven115

theorem unit_closed (a : ℕ) (hlo : 2 ≤ a) (hhi : a < 115) :
    ClosedMinimalPrefix true 115 a 4 [0,1,a] (a+1) := by
  interval_cases a
  · exact (closedMinimalPrefix_of_verify true 115 2 4 [0,1,2] 3 (.stop (.collision 24)) (by decide +kernel))
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
  · exact (closedMinimalPrefix_of_verify true 115 19 4 [0,1,19] 20 (.stop (.third 2 0 1 6)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 20 4 [0,1,20] 21 (.stop (.third 1 2 0 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 21 4 [0,1,21] 22 (.stop (.third 0 2 1 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 22 4 [0,1,22] 23 (.stop (.third 2 1 0 104)) (by decide +kernel))
  · exact unit_23_closed
  · exact unit_24_closed
  · exact unit_25_closed
  · exact unit_26_closed
  · exact (closedMinimalPrefix_of_verify true 115 27 4 [0,1,27] 28 (.stop (.third 2 0 1 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 28 4 [0,1,28] 29 (.stop (.third 1 2 0 98)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 29 4 [0,1,29] 30 (.stop (.third 0 2 1 4)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 30 4 [0,1,30] 31 (.stop (.third 2 1 0 111)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 31 4 [0,1,31] 32 (.stop (.third 0 2 1 26)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 32 4 [0,1,32] 33 (.stop (.third 0 2 1 18)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 33 4 [0,1,33] 34 (.stop (.third 0 2 1 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 34 4 [0,1,34] 35 (.stop (.third 2 1 0 108)) (by decide +kernel))
  · exact unit_35_closed
  · exact (closedMinimalPrefix_of_verify true 115 36 4 [0,1,36] 37 (.stop (.third 0 2 1 16)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 37 4 [0,1,37] 38 (.stop (.third 0 2 1 28)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 38 4 [0,1,38] 39 (.stop (.third 2 0 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 39 4 [0,1,39] 40 (.stop (.third 1 2 0 112)) (by decide +kernel))
  · exact unit_40_closed
  · exact (closedMinimalPrefix_of_verify true 115 41 4 [0,1,41] 42 (.stop (.third 2 0 1 14)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 42 4 [0,1,42] 43 (.stop (.third 1 2 0 101)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 43 4 [0,1,43] 44 (.stop (.third 2 0 1 8)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 44 4 [0,1,44] 45 (.stop (.third 0 2 1 34)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 45 4 [0,1,45] 46 (.stop (.third 2 1 0 81)) (by decide +kernel))
  · exact unit_46_closed
  · exact (closedMinimalPrefix_of_verify true 115 47 4 [0,1,47] 48 (.stop (.third 2 0 1 22)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 48 4 [0,1,48] 49 (.stop (.third 0 2 1 12)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 49 4 [0,1,49] 50 (.stop (.third 2 1 0 103)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 50 4 [0,1,50] 51 (.branch [.stop (.third 0 3 2 106),.stop (.third 1 3 0 106),.stop (.third 0 3 2 102),.stop (.third 0 3 1 49),.stop (.third 1 2 3 54),.stop (.third 0 3 2 76),.stop (.third 0 3 2 113),.stop (.third 0 3 1 2),.stop (.third 0 3 1 39),.stop (.third 2 1 3 61),.stop (.third 1 2 3 54),.stop (.third 0 3 1 13),.stop (.third 0 3 1 42),.stop (.third 0 3 1 9),.stop (.third 1 2 3 54),.stop (.third 2 3 0 36),.stop (.third 1 0 3 114),.stop (.third 0 3 1 22),.stop (.third 1 0 3 114),.stop (.third 1 0 3 114),.stop (.third 0 3 2 81),.stop (.third 0 3 1 8),.stop (.third 1 0 3 114),.stop (.third 0 3 1 14),.stop (.third 1 0 3 114),.stop (.third 0 3 2 56),.stop (.third 0 3 1 3),.stop (.third 1 0 3 114),.stop (.third 0 3 2 99),.stop (.third 1 0 3 114),.stop (.third 1 0 3 114),.stop (.third 1 0 3 114),.stop (.third 0 3 2 97),.stop (.third 1 0 3 114),.stop (.third 1 0 3 114),.stop (.third 0 3 2 111),.stop (.third 1 0 3 114),.stop (.third 0 3 1 17),.stop (.third 1 0 3 114),.stop (.third 1 0 3 114),.stop (.third 1 0 3 114),.stop (.third 1 0 3 114),.stop (.third 0 3 1 47),.stop (.third 0 3 2 104),.stop (.third 1 0 3 114),.stop (.third 0 3 1 6),.stop (.third 0 3 2 83),.stop (.third 0 3 1 27),.stop (.third 0 3 2 79),.stop (.third 1 0 3 114),.stop (.third 0 3 1 41),.stop (.third 0 3 2 53),.stop (.third 0 3 2 67),.stop (.third 1 0 3 114),.stop (.third 1 0 3 114),.stop (.third 0 3 2 51),.stop (.third 0 3 1 43),.stop (.third 1 0 3 114),.stop (.third 0 3 1 19),.stop (.third 1 0 3 114),.stop (.third 0 3 2 86),.stop (.third 0 3 1 38),.stop (.third 1 0 3 114),.stop (.third 1 0 3 114)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 51 4 [0,1,51] 52 (.stop (.third 2 0 1 9)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 52 4 [0,1,52] 53 (.stop (.third 1 2 0 106)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 53 4 [0,1,53] 54 (.stop (.third 1 2 0 73)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 54 4 [0,1,54] 55 (.stop (.third 0 2 1 49)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 55 4 [0,1,55] 56 (.stop (.third 2 1 0 66)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 56 4 [0,1,56] 57 (.stop (.third 2 0 1 39)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 57 4 [0,1,57] 58 (.stop (.third 1 2 0 76)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 58 4 [0,1,58] 59 (.stop (.third 0 2 1 2)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 59 4 [0,1,59] 60 (.stop (.third 0 2 1 39)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 60 4 [0,1,60] 61 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 61 4 [0,1,61] 62 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 62 4 [0,1,62] 63 (.stop (.third 0 2 1 13)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 63 4 [0,1,63] 64 (.stop (.third 0 2 1 42)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 64 4 [0,1,64] 65 (.stop (.third 0 2 1 9)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 65 4 [0,1,65] 66 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 66 4 [0,1,66] 67 (.stop (.third 0 2 1 61)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 67 4 [0,1,67] 68 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 68 4 [0,1,68] 69 (.stop (.third 0 2 1 22)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 69 4 [0,1,69] 70 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 70 4 [0,1,70] 71 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 71 4 [0,1,71] 72 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 72 4 [0,1,72] 73 (.stop (.third 0 2 1 8)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 73 4 [0,1,73] 74 (.stop (.third 0 2 1 52)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 74 4 [0,1,74] 75 (.stop (.third 0 2 1 14)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 75 4 [0,1,75] 76 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 76 4 [0,1,76] 77 (.stop (.third 0 2 1 56)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 77 4 [0,1,77] 78 (.stop (.third 0 2 1 3)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 78 4 [0,1,78] 79 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 79 4 [0,1,79] 80 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 80 4 [0,1,80] 81 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 81 4 [0,1,81] 82 (.stop (.third 0 2 1 71)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 82 4 [0,1,82] 83 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 83 4 [0,1,83] 84 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 84 4 [0,1,84] 85 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 85 4 [0,1,85] 86 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 86 4 [0,1,86] 87 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 87 4 [0,1,87] 88 (.stop (.third 0 2 1 78)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 88 4 [0,1,88] 89 (.stop (.third 0 2 1 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 89 4 [0,1,89] 90 (.stop (.third 0 2 1 84)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 90 4 [0,1,90] 91 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 91 4 [0,1,91] 92 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 92 4 [0,1,92] 93 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 93 4 [0,1,93] 94 (.stop (.third 0 2 1 47)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 94 4 [0,1,94] 95 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 95 4 [0,1,95] 96 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 96 4 [0,1,96] 97 (.stop (.third 0 2 1 6)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 97 4 [0,1,97] 98 (.stop (.third 0 2 1 83)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 98 4 [0,1,98] 99 (.stop (.third 0 2 1 27)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 99 4 [0,1,99] 100 (.stop (.third 0 2 1 79)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 100 4 [0,1,100] 101 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 101 4 [0,1,101] 102 (.stop (.third 0 2 1 41)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 102 4 [0,1,102] 103 (.stop (.third 0 2 1 53)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 103 4 [0,1,103] 104 (.stop (.third 0 2 1 67)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 104 4 [0,1,104] 105 (.stop (.third 0 2 1 94)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 105 4 [0,1,105] 106 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 106 4 [0,1,106] 107 (.stop (.third 0 2 1 51)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 107 4 [0,1,107] 108 (.stop (.third 0 2 1 43)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 108 4 [0,1,108] 109 (.stop (.third 0 2 1 82)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 109 4 [0,1,109] 110 (.stop (.third 0 2 1 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 110 4 [0,1,110] 111 (.stop (.third 1 0 2 114)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 111 4 [0,1,111] 112 (.stop (.third 0 2 1 86)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 112 4 [0,1,112] 113 (.stop (.third 0 2 1 38)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 113 4 [0,1,113] 114 (.stop (.third 0 2 1 57)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 115 114 4 [0,1,114] 115 (.stop (.third 1 0 2 114)) (by decide +kernel))

theorem nonunit_closed (a : ℕ) (hlo : 1 ≤ a) (hhi : a < 115) :
    ClosedMinimalPrefix false 115 a 5 [0,a] (a+1) := by
  interval_cases a
  · exact (closedMinimalPrefix_of_verify false 115 1 5 [0,1] 2 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 2 5 [0,2] 3 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 3 5 [0,3] 4 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 4 5 [0,4] 5 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact nonunit_5_closed
  · exact (closedMinimalPrefix_of_verify false 115 6 5 [0,6] 7 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 7 5 [0,7] 8 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 8 5 [0,8] 9 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 9 5 [0,9] 10 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 10 5 [0,10] 11 (.stop (.pair 0 1 12 48)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 11 5 [0,11] 12 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 12 5 [0,12] 13 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 13 5 [0,13] 14 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 14 5 [0,14] 15 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 15 5 [0,15] 16 (.stop (.pair 0 1 8 72)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 16 5 [0,16] 17 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 17 5 [0,17] 18 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 18 5 [0,18] 19 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 19 5 [0,19] 20 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 20 5 [0,20] 21 (.stop (.pair 0 1 6 96)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 21 5 [0,21] 22 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 22 5 [0,22] 23 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact nonunit_23_closed
  · exact (closedMinimalPrefix_of_verify false 115 24 5 [0,24] 25 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 25 5 [0,25] 26 (.stop (.pair 0 1 14 74)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 26 5 [0,26] 27 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 27 5 [0,27] 28 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 28 5 [0,28] 29 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 29 5 [0,29] 30 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 30 5 [0,30] 31 (.stop (.pair 0 1 4 29)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 31 5 [0,31] 32 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 32 5 [0,32] 33 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 33 5 [0,33] 34 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 34 5 [0,34] 35 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 35 5 [0,35] 36 (.stop (.pair 0 1 33 7)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 36 5 [0,36] 37 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 37 5 [0,37] 38 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 38 5 [0,38] 39 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 39 5 [0,39] 40 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 40 5 [0,40] 41 (.stop (.pair 0 1 3 77)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 41 5 [0,41] 42 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 42 5 [0,42] 43 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 43 5 [0,43] 44 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 44 5 [0,44] 45 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 45 5 [0,45] 46 (.stop (.pair 0 1 18 32)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 46 5 [0,46] 47 (.stop (.pair 0 1 3 77)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 47 5 [0,47] 48 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 48 5 [0,48] 49 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 49 5 [0,49] 50 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 50 5 [0,50] 51 (.stop (.pair 0 1 7 33)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 51 5 [0,51] 52 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 52 5 [0,52] 53 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 53 5 [0,53] 54 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 54 5 [0,54] 55 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 55 5 [0,55] 56 (.stop (.pair 0 1 21 11)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 56 5 [0,56] 57 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 57 5 [0,57] 58 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 58 5 [0,58] 59 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 59 5 [0,59] 60 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 60 5 [0,60] 61 (.stop (.pair 0 1 2 58)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 61 5 [0,61] 62 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 62 5 [0,62] 63 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 63 5 [0,63] 64 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 64 5 [0,64] 65 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 65 5 [0,65] 66 (.stop (.pair 0 1 16 36)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 66 5 [0,66] 67 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 67 5 [0,67] 68 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 68 5 [0,68] 69 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 69 5 [0,69] 70 (.stop (.pair 0 1 2 58)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 70 5 [0,70] 71 (.stop (.pair 0 1 28 37)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 71 5 [0,71] 72 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 72 5 [0,72] 73 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 73 5 [0,73] 74 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 74 5 [0,74] 75 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 75 5 [0,75] 76 (.stop (.pair 0 1 43 107)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 76 5 [0,76] 77 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 77 5 [0,77] 78 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 78 5 [0,78] 79 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 79 5 [0,79] 80 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 80 5 [0,80] 81 (.stop (.pair 0 1 13 62)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 81 5 [0,81] 82 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 82 5 [0,82] 83 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 83 5 [0,83] 84 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 84 5 [0,84] 85 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 85 5 [0,85] 86 (.stop (.pair 0 1 19 109)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 86 5 [0,86] 87 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 87 5 [0,87] 88 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 88 5 [0,88] 89 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 89 5 [0,89] 90 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 90 5 [0,90] 91 (.stop (.pair 0 1 9 64)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 91 5 [0,91] 92 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 92 5 [0,92] 93 (.stop (.pair 0 1 4 29)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 93 5 [0,93] 94 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 94 5 [0,94] 95 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 95 5 [0,95] 96 (.stop (.pair 0 1 17 88)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 96 5 [0,96] 97 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 97 5 [0,97] 98 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 98 5 [0,98] 99 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 99 5 [0,99] 100 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 100 5 [0,100] 101 (.stop (.pair 0 1 38 112)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 101 5 [0,101] 102 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 102 5 [0,102] 103 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 103 5 [0,103] 104 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 104 5 [0,104] 105 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 105 5 [0,105] 106 (.stop (.pair 0 1 11 21)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 106 5 [0,106] 107 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 107 5 [0,107] 108 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 108 5 [0,108] 109 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 109 5 [0,109] 110 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 110 5 [0,110] 111 (.stop (.pair 0 1 22 68)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 111 5 [0,111] 112 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 112 5 [0,112] 113 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 113 5 [0,113] 114 (.stop (.unitPair 0 1)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify false 115 114 5 [0,114] 115 (.stop (.unitPair 0 1)) (by decide +kernel))

end MinModulus.PrefixCertificate.G2Seven115

namespace MinModulus

theorem not_validTuple_seven_mod_115 (g : Fin 7 → ZMod 115) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 115) := ⟨⟨0, 1, by decide⟩⟩
  exact PrefixCertificate.not_validTuple_of_minimal_prefixes (by decide)
    PrefixCertificate.G2Seven115.unit_closed PrefixCertificate.G2Seven115.nonunit_closed g

end MinModulus

#print axioms MinModulus.not_validTuple_seven_mod_115

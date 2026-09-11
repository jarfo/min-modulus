import MinModulus.SevenModOneTwenty.BlockUnit116
import MinModulus.SevenModOneTwenty.BlockUnit117

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_6_16_closed : ClosedMinimalPrefix true 120 6 3 [0,1,6,16] 17 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,17] 18 (.stop (.collision 1104)) (by decide +kernel))
  · exact unit_6_16_18_closed
  · exact unit_6_16_19_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,20] 21 (.stop (.collision 8216)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,21] 22 (.stop (.collision 1153)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,22] 23 (.stop (.collision 1160)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,23] 24 (.stop (.collision 8195)) (by decide +kernel))
  · exact unit_6_16_24_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,25] 26 (.stop (.collision 1538)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,26] 27 (.stop (.collision 1545)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,27] 28 (.stop (.collision 1216)) (by decide +kernel))
  · exact unit_6_16_28_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,29] 30 (.stop (.third 2 4 1 47)) (by decide +kernel))
  · exact unit_6_16_30_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,31] 32 (.stop (.collision 1601)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,32] 33 (.stop (.collision 1608)) (by decide +kernel))
  · exact unit_6_16_33_closed
  · exact unit_6_16_34_closed
  · exact unit_6_16_35_closed
  · exact unit_6_16_36_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,37] 38 (.stop (.collision 1664)) (by decide +kernel))
  · exact unit_6_16_38_closed
  · exact unit_6_16_39_closed
  · exact unit_6_16_40_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,41] 42 (.stop (.collision 2049)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,42] 43 (.stop (.collision 2056)) (by decide +kernel))
  · exact unit_6_16_43_closed
  · exact unit_6_16_44_closed
  · exact unit_6_16_45_closed
  · exact unit_6_16_46_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,47] 48 (.stop (.collision 2112)) (by decide +kernel))
  · exact unit_6_16_48_closed
  · exact unit_6_16_49_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,50] 51 (.stop (.third 1 4 2 49)) (by decide +kernel))
  · exact unit_6_16_51_closed
  · exact unit_6_16_52_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,53] 54 (.stop (.third 2 4 1 23)) (by decide +kernel))
  · exact unit_6_16_54_closed
  · exact unit_6_16_55_closed
  · exact unit_6_16_56_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,57] 58 (.stop (.collision 2560)) (by decide +kernel))
  · exact unit_6_16_58_closed
  · exact unit_6_16_59_closed
  · exact unit_6_16_60_closed
  · exact unit_6_16_61_closed
  · exact unit_6_16_62_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,63] 64 (.stop (.collision 12808)) (by decide +kernel))
  · exact unit_6_16_64_closed
  · exact unit_6_16_65_closed
  · exact unit_6_16_66_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,67] 68 (.branch [.stop (.collision 102472),.stop (.third 2 4 5 61),.stop (.collision 73793),.stop (.third 2 4 5 61),.stop (.collision 8833),.stop (.collision 8840),.stop (.third 1 5 2 97),.stop (.collision 73737),.stop (.collision 65680),.stop (.third 2 5 1 71),.stop (.collision 8896),.stop (.collision 1546),.stop (.collision 16960),.stop (.third 0 4 5 43),.stop (.collision 9281),.stop (.collision 9288),.stop (.third 5 4 3 7),.stop (.collision 1609),.stop (.collision 99392),.stop (.collision 65561),.stop (.collision 9344),.stop (.collision 99329),.stop (.third 4 5 3 47),.stop (.collision 98944),.stop (.third 4 0 5 77),.stop (.collision 9736),.stop (.collision 98881),.stop (.third 0 4 5 43),.stop (.collision 98832),.stop (.collision 98818),.stop (.third 1 5 2 73),.stop (.collision 98433),.stop (.collision 2113),.stop (.collision 2120),.stop (.collision 98370),.stop (.collision 4164),.stop (.collision 4171),.stop (.collision 70720),.stop (.third 4 0 5 77),.stop (.collision 4192),.stop (.collision 131137),.stop (.collision 4227),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 4248),.stop (.third 3 5 4 73),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,68] 69 (.stop (.collision 12360)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,69] 70 (.branch [.stop (.collision 8784),.stop (.collision 102409),.stop (.collision 73744),.stop (.collision 73737),.stop (.third 1 5 2 97),.stop (.collision 8840),.stop (.collision 66051),.stop (.third 2 5 1 71),.stop (.third 1 5 4 53),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 16904),.stop (.third 4 5 1 37),.stop (.third 4 3 5 43),.stop (.collision 9281),.stop (.collision 9288),.stop (.third 4 5 0 113),.stop (.collision 99392),.stop (.third 4 5 2 19),.stop (.collision 107008),.stop (.collision 9344),.stop (.collision 65547),.stop (.third 5 4 0 73),.stop (.collision 2057),.stop (.collision 106560),.stop (.collision 98881),.stop (.collision 17408),.stop (.third 4 3 5 43),.stop (.third 1 5 2 73),.stop (.collision 2120),.stop (.collision 9792),.stop (.collision 4129),.stop (.collision 98384),.stop (.third 0 5 4 7),.stop (.third 5 1 4 113),.stop (.collision 70720),.stop (.collision 4185),.stop (.third 2 5 4 101),.stop (.third 1 5 4 83),.stop (.collision 78336),.stop (.collision 70664),.stop (.collision 70657),.stop (.third 4 5 1 67),.stop (.collision 4612),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact unit_6_16_70_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,71] 72 (.stop (.collision 12297)) (by decide +kernel))
  · exact unit_6_16_72_closed
  · exact unit_6_16_73_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,74] 75 (.stop (.third 1 4 2 97)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,75] 76 (.branch [.stop (.collision 8784),.stop (.third 2 5 1 71),.stop (.collision 1616),.stop (.third 4 3 5 61),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 1665),.stop (.collision 1672),.stop (.third 5 1 4 13),.stop (.collision 9225),.stop (.collision 107008),.stop (.collision 2057),.stop (.collision 16449),.stop (.collision 16456),.stop (.collision 9281),.stop (.collision 9288),.stop (.third 4 5 2 113),.stop (.collision 2120),.stop (.collision 106497),.stop (.collision 71168),.stop (.collision 9344),.stop (.collision 78336),.stop (.third 1 5 2 73),.stop (.collision 16904),.stop (.collision 98832),.stop (.collision 9736),.stop (.collision 132096),.stop (.third 5 2 4 47),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 77888),.stop (.collision 98321),.stop (.third 2 5 4 7),.stop (.collision 70664),.stop (.collision 70657),.stop (.third 5 4 1 107),.stop (.collision 77825),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact unit_6_16_76_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,77] 78 (.stop (.third 2 4 1 71)) (by decide +kernel))
  · exact unit_6_16_78_closed
  · exact unit_6_16_79_closed
  · exact unit_6_16_80_closed
  · exact unit_6_16_81_closed
  · exact unit_6_16_82_closed
  · exact unit_6_16_83_closed
  · exact unit_6_16_84_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,85] 86 (.branch [.stop (.collision 8784),.stop (.collision 77888),.stop (.third 4 2 5 41),.stop (.third 0 5 4 89),.stop (.collision 8833),.stop (.collision 8840),.stop (.third 4 5 0 103),.stop (.collision 77825),.stop (.collision 65680),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 4101),.stop (.third 1 5 2 73),.stop (.collision 65624),.stop (.collision 9281),.stop (.collision 9288),.stop (.third 4 5 3 113),.stop (.collision 98881),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 4192),.stop (.third 5 4 3 73),.stop (.collision 4227),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 4248),.stop (.third 0 5 4 17),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact unit_6_16_86_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,87] 88 (.branch [.stop (.collision 8784),.stop (.collision 77825),.stop (.collision 2561),.stop (.third 5 0 4 29),.stop (.third 4 3 5 49),.stop (.collision 8840),.stop (.collision 66051),.stop (.collision 71168),.stop (.collision 99392),.stop (.collision 9225),.stop (.third 1 5 2 73),.stop (.collision 99329),.stop (.third 4 5 2 37),.stop (.collision 98944),.stop (.collision 9281),.stop (.collision 9288),.stop (.third 1 5 4 7),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 4192),.stop (.collision 9344),.stop (.third 0 5 4 109),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 4248),.stop (.third 2 5 4 83),.stop (.third 4 3 5 49),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact unit_6_16_88_closed
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,89] 90 (.branch [.stop (.collision 8784),.branch [.stop (.third 6 5 4 119),.stop (.third 4 0 6 31),.stop (.collision 41601),.stop (.third 0 5 6 91),.stop (.collision 70273),.stop (.collision 70280),.stop (.third 1 6 2 73),.stop (.collision 41993),.stop (.collision 41664),.stop (.collision 70665),.stop (.collision 819840),.stop (.collision 590912),.stop (.collision 42049),.stop (.collision 562240),.stop (.collision 791105),.stop (.collision 70728),.stop (.collision 590856),.stop (.collision 99400),.stop (.third 4 3 6 23),.stop (.collision 562177),.stop (.collision 70784),.stop (.collision 590464),.stop (.collision 37387),.stop (.third 3 4 6 97),.stop (.third 0 4 6 89),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119)],.stop (.collision 99840),.stop (.third 4 0 5 31),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 66051),.stop (.collision 99392),.stop (.third 1 5 2 73),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 4129),.stop (.collision 98944),.stop (.collision 65624),.stop (.collision 9281),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 98832),.stop (.collision 98818),.stop (.collision 65561),.stop (.third 4 3 5 23),.stop (.collision 70657),.stop (.collision 98384),.stop (.collision 98370),.stop (.collision 4619),.stop (.third 3 4 5 97),.stop (.third 0 4 5 89),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,90] 91 (.branch [.stop (.collision 8784),.branch [.stop (.third 6 5 4 119),.stop (.third 4 1 6 31),.stop (.third 3 6 5 79),.stop (.third 1 5 6 91),.stop (.third 6 0 5 47),.stop (.third 1 6 2 73),.stop (.third 5 6 0 103),.stop (.collision 41993),.stop (.collision 41664),.stop (.collision 70665),.stop (.third 5 6 3 11),.stop (.collision 36939),.stop (.collision 562240),.stop (.collision 791112),.stop (.collision 70721),.stop (.collision 70728),.stop (.third 2 6 5 7),.stop (.collision 562184),.stop (.third 6 5 3 101),.stop (.collision 1081864),.stop (.third 0 6 5 17),.stop (.collision 790601),.stop (.third 6 5 0 73),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119)],.stop (.collision 2624),.stop (.third 4 1 5 31),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 66051),.stop (.third 1 5 2 73),.stop (.third 5 3 4 13),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 4136),.stop (.collision 4164),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 9288),.stop (.collision 4192),.stop (.collision 98825),.stop (.collision 4227),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 131592),.stop (.third 3 5 4 73),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,91] 92 (.branch [.stop (.collision 8784),.stop (.collision 99840),.branch [.stop (.third 0 4 6 91),.stop (.collision 41601),.stop (.collision 41608),.stop (.third 1 6 2 73),.stop (.collision 70273),.stop (.collision 70280),.stop (.collision 41993),.stop (.collision 590912),.stop (.collision 819840),.stop (.collision 70665),.stop (.collision 562240),.stop (.collision 819777),.stop (.third 0 6 5 83),.stop (.collision 533568),.stop (.collision 70721),.stop (.collision 562184),.stop (.collision 562177),.stop (.collision 590464),.stop (.collision 533512),.stop (.collision 37387),.stop (.collision 561792),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119)],.stop (.third 0 4 5 91),.stop (.collision 8833),.stop (.collision 8840),.stop (.third 1 5 2 73),.stop (.collision 4115),.stop (.collision 65680),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 98944),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 98881),.stop (.collision 9288),.stop (.collision 98832),.stop (.collision 98818),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 9344),.stop (.collision 98384),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,92] 93 (.branch [.stop (.collision 8784),.branch [.stop (.third 3 6 4 79),.stop (.third 1 4 6 91),.stop (.third 6 0 4 47),.stop (.third 1 6 2 73),.stop (.third 4 6 0 103),.stop (.collision 70280),.stop (.collision 820232),.stop (.collision 41993),.stop (.third 4 6 3 11),.stop (.collision 70665),.stop (.collision 562240),.stop (.collision 819784),.stop (.third 0 6 5 83),.stop (.collision 42056),.stop (.third 2 6 4 7),.stop (.collision 562184),.stop (.third 6 4 3 101),.stop (.collision 533512),.stop (.third 0 6 4 17),.stop (.collision 819273),.stop (.third 6 4 0 73),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119)],.stop (.third 3 5 4 79),.stop (.third 1 4 5 91),.stop (.third 5 0 4 47),.stop (.third 1 5 2 73),.stop (.third 4 5 0 103),.stop (.collision 4122),.stop (.collision 99336),.stop (.collision 9225),.stop (.third 4 5 3 11),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 98888),.stop (.collision 9281),.stop (.collision 9288),.stop (.third 2 5 4 7),.stop (.collision 70664),.stop (.third 5 4 3 101),.stop (.collision 4248),.stop (.third 0 5 4 17),.stop (.collision 98377),.stop (.third 5 4 0 73),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,93] 94 (.branch [.stop (.collision 8784),.stop (.collision 71168),.branch [.stop (.third 6 2 4 29),.stop (.third 1 6 2 73),.stop (.collision 41608),.stop (.third 4 6 1 103),.stop (.collision 70273),.stop (.third 4 3 6 67),.stop (.collision 41993),.stop (.third 4 6 2 11),.stop (.collision 562240),.stop (.collision 70665),.stop (.collision 819777),.stop (.collision 791112),.stop (.collision 42056),.stop (.collision 562184),.stop (.collision 562177),.stop (.collision 70728),.stop (.collision 1081864),.stop (.third 1 6 4 17),.stop (.third 2 6 4 109),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119)],.stop (.third 5 2 4 29),.stop (.third 1 5 2 73),.stop (.collision 8840),.stop (.third 4 5 1 103),.stop (.collision 4129),.stop (.third 4 3 5 67),.stop (.collision 9225),.stop (.third 4 5 2 11),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 98881),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 4248),.stop (.collision 131592),.stop (.third 1 5 4 17),.stop (.third 2 5 4 109),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,94] 95 (.branch [.stop (.collision 8784),.branch [.stop (.third 6 5 4 119),.stop (.third 1 6 2 73),.stop (.collision 41601),.stop (.collision 41608),.stop (.collision 70273),.stop (.collision 70280),.stop (.collision 590912),.stop (.collision 41993),.stop (.collision 562240),.stop (.collision 70665),.stop (.third 0 6 4 83),.stop (.collision 791112),.stop (.collision 42049),.stop (.collision 562184),.stop (.collision 562177),.stop (.collision 70728),.stop (.collision 590464),.stop (.collision 37387),.stop (.collision 561792),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119)],.stop (.collision 4101),.stop (.third 1 5 2 73),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 4129),.stop (.collision 99336),.stop (.collision 65680),.stop (.collision 9225),.stop (.collision 70720),.stop (.collision 4185),.stop (.third 0 5 4 83),.stop (.collision 65624),.stop (.collision 9281),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 98440),.stop (.collision 4612),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,95] 96 (.stop (.collision 9728)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,96] 97 (.branch [.stop (.collision 8784),.stop (.third 1 5 2 73),.stop (.collision 4115),.stop (.collision 65736),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 99336),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 98888),.stop (.collision 4227),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 9288),.stop (.collision 98440),.stop (.collision 4619),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,97] 98 (.stop (.collision 5)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,98] 99 (.stop (.third 1 4 2 73)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,99] 100 (.stop (.collision 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,100] 101 (.stop (.collision 26)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,101] 102 (.stop (.collision 33)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,102] 103 (.stop (.collision 40)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,103] 104 (.stop (.collision 68)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,104] 105 (.stop (.collision 75)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,105] 106 (.stop (.collision 9280)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,106] 107 (.stop (.collision 89)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,107] 108 (.stop (.collision 96)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,108] 109 (.branch [.stop (.collision 8784),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 65736),.stop (.third 5 3 4 47),.stop (.collision 98888),.stop (.third 4 5 3 103),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,109] 110 (.stop (.collision 131)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,110] 111 (.stop (.collision 9224)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,111] 112 (.stop (.collision 9217)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,112] 113 (.stop (.collision 152)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,113] 114 (.stop (.collision 516)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,114] 115 (.stop (.collision 523)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,115] 116 (.stop (.collision 8832)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,116] 117 (.stop (.third 1 0 4 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,117] 118 (.stop (.third 1 0 4 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,118] 119 (.stop (.third 1 0 4 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 6 2 [0,1,6,16,119] 120 (.stop (.third 1 0 4 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

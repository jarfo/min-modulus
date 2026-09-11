import MinModulus.SevenModOneTwenty.BlockUnit0
import MinModulus.SevenModOneTwenty.BlockUnit1
import MinModulus.SevenModOneTwenty.BlockUnit2

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_3_7_closed : ClosedMinimalPrefix true 120 3 3 [0,1,3,7] 8 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,8] 9 (.stop (.collision 1104)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,9] 10 (.stop (.collision 1153)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,10] 11 (.stop (.collision 1160)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,11] 12 (.stop (.collision 1545)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,12] 13 (.stop (.collision 1216)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,13] 14 (.stop (.collision 1601)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,14] 15 (.stop (.third 0 3 4 103)) (by decide +kernel))
  · exact unit_3_7_15_closed
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,16] 17 (.stop (.collision 1664)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,17] 18 (.stop (.collision 2049)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,18] 19 (.stop (.collision 2056)) (by decide +kernel))
  · exact unit_3_7_19_closed
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,20] 21 (.stop (.collision 2112)) (by decide +kernel))
  · exact unit_3_7_21_closed
  · exact unit_3_7_22_closed
  · exact unit_3_7_23_closed
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,24] 25 (.stop (.collision 2560)) (by decide +kernel))
  · exact unit_3_7_25_closed
  · exact unit_3_7_26_closed
  · exact unit_3_7_27_closed
  · exact unit_3_7_28_closed
  · exact unit_3_7_29_closed
  · exact unit_3_7_30_closed
  · exact unit_3_7_31_closed
  · exact unit_3_7_32_closed
  · exact unit_3_7_33_closed
  · exact unit_3_7_34_closed
  · exact unit_3_7_35_closed
  · exact unit_3_7_36_closed
  · exact unit_3_7_37_closed
  · exact unit_3_7_38_closed
  · exact unit_3_7_39_closed
  · exact unit_3_7_40_closed
  · exact unit_3_7_41_closed
  · exact unit_3_7_42_closed
  · exact unit_3_7_43_closed
  · exact unit_3_7_44_closed
  · exact unit_3_7_45_closed
  · exact unit_3_7_46_closed
  · exact unit_3_7_47_closed
  · exact unit_3_7_48_closed
  · exact unit_3_7_49_closed
  · exact unit_3_7_50_closed
  · exact unit_3_7_51_closed
  · exact unit_3_7_52_closed
  · exact unit_3_7_53_closed
  · exact unit_3_7_54_closed
  · exact unit_3_7_55_closed
  · exact unit_3_7_56_closed
  · exact unit_3_7_57_closed
  · exact unit_3_7_58_closed
  · exact unit_3_7_59_closed
  · exact unit_3_7_60_closed
  · exact unit_3_7_61_closed
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,62] 63 (.stop (.third 1 4 2 61)) (by decide +kernel))
  · exact unit_3_7_63_closed
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,64] 65 (.stop (.collision 12353)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,65] 66 (.stop (.collision 12297)) (by decide +kernel))
  · exact unit_3_7_66_closed
  · exact unit_3_7_67_closed
  · exact unit_3_7_68_closed
  · exact unit_3_7_69_closed
  · exact unit_3_7_70_closed
  · exact unit_3_7_71_closed
  · exact unit_3_7_72_closed
  · exact unit_3_7_73_closed
  · exact unit_3_7_74_closed
  · exact unit_3_7_75_closed
  · exact unit_3_7_76_closed
  · exact unit_3_7_77_closed
  · exact unit_3_7_78_closed
  · exact unit_3_7_79_closed
  · exact unit_3_7_80_closed
  · exact unit_3_7_81_closed
  · exact unit_3_7_82_closed
  · exact unit_3_7_83_closed
  · exact unit_3_7_84_closed
  · exact unit_3_7_85_closed
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,86] 87 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65561),.stop (.collision 9344),.stop (.collision 9729),.stop (.collision 9736),.stop (.collision 99840),.stop (.collision 9792),.stop (.collision 99392),.stop (.collision 99336),.stop (.collision 98944),.stop (.third 0 5 4 7),.stop (.collision 98832),.stop (.collision 98440),.stop (.collision 98384),.stop (.collision 98370),.stop (.collision 98314),.stop (.collision 131648),.stop (.collision 71168),.stop (.collision 131144),.stop (.collision 131081),.stop (.third 3 0 5 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact unit_3_7_87_closed
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,88] 89 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65561),.stop (.collision 9344),.stop (.collision 9729),.stop (.collision 9736),.branch [.stop (.collision 70224),.stop (.collision 70273),.stop (.collision 70280),.stop (.collision 819784),.stop (.collision 70336),.stop (.collision 70721),.stop (.collision 70728),.stop (.collision 590408),.stop (.collision 590401),.stop (.collision 791112),.stop (.collision 590345),.stop (.collision 98889),.stop (.third 3 0 6 17),.stop (.collision 562240),.stop (.collision 589897),.stop (.collision 562184),.stop (.collision 562177),.stop (.collision 561792),.stop (.third 1 0 6 119)],.stop (.collision 99392),.stop (.collision 99336),.stop (.collision 98944),.stop (.collision 98888),.stop (.collision 98832),.stop (.collision 98440),.stop (.collision 98384),.stop (.collision 98370),.stop (.collision 98314),.stop (.collision 71168),.stop (.collision 4115),.stop (.collision 131137),.stop (.third 3 0 5 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,89] 90 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65561),.stop (.collision 9344),.stop (.collision 9729),.stop (.collision 9736),.branch [.stop (.collision 70224),.stop (.collision 70273),.stop (.collision 70280),.stop (.collision 819777),.stop (.third 2 6 4 7),.stop (.collision 70721),.stop (.third 3 6 4 101),.stop (.collision 590401),.stop (.collision 562688),.stop (.collision 791105),.stop (.third 2 6 5 109),.stop (.third 3 0 6 17),.stop (.third 3 6 5 83),.stop (.collision 589897),.stop (.collision 562184),.stop (.collision 562177),.stop (.collision 561792),.stop (.third 1 0 6 119)],.stop (.collision 9792),.stop (.collision 99329),.stop (.collision 81920),.stop (.collision 98881),.stop (.third 2 5 4 7),.stop (.collision 98433),.stop (.third 3 5 4 101),.stop (.collision 98321),.stop (.collision 71168),.stop (.collision 131585),.stop (.collision 131144),.stop (.third 3 0 5 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,90] 91 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65561),.stop (.collision 9344),.stop (.collision 9729),.stop (.collision 9736),.stop (.collision 99392),.stop (.collision 9792),.stop (.collision 98944),.stop (.collision 98888),.stop (.collision 98832),.stop (.collision 98440),.stop (.collision 98384),.stop (.collision 98370),.stop (.collision 71168),.stop (.collision 131592),.stop (.collision 4122),.stop (.third 3 0 5 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,91] 92 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65561),.stop (.collision 9344),.stop (.collision 9729),.stop (.collision 9736),.branch [.stop (.collision 70224),.stop (.collision 70273),.stop (.collision 70280),.stop (.collision 819721),.stop (.collision 590408),.stop (.collision 590401),.stop (.collision 70728),.stop (.collision 590345),.stop (.collision 791105),.stop (.third 3 0 6 17),.stop (.collision 562240),.stop (.collision 589897),.stop (.collision 562184),.stop (.collision 562177),.stop (.collision 561792),.stop (.third 1 0 6 119)],.stop (.collision 9792),.branch [.stop (.collision 590408),.stop (.collision 590401),.stop (.collision 70280),.stop (.collision 590345),.stop (.collision 562688),.stop (.collision 70721),.stop (.collision 70728),.stop (.third 3 0 6 17),.stop (.collision 562240),.stop (.collision 36953),.stop (.third 3 6 5 109),.stop (.collision 562177),.stop (.collision 561792),.stop (.third 1 0 6 119)],.stop (.collision 98881),.stop (.collision 98825),.stop (.collision 98433),.stop (.collision 98377),.stop (.collision 71168),.stop (.collision 4115),.stop (.collision 4122),.stop (.third 3 0 5 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,92] 93 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65561),.stop (.collision 9344),.stop (.collision 9729),.stop (.collision 99392),.stop (.collision 99336),.stop (.collision 9792),.stop (.collision 98888),.stop (.collision 98832),.stop (.collision 98440),.stop (.collision 98384),.stop (.collision 71168),.stop (.collision 131648),.stop (.collision 131585),.stop (.third 3 0 5 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,93] 94 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65561),.stop (.collision 9344),.stop (.collision 9729),.stop (.collision 9736),.stop (.collision 99329),.stop (.collision 9792),.stop (.collision 98881),.stop (.collision 98825),.stop (.collision 98433),.stop (.third 3 5 4 7),.stop (.collision 98321),.stop (.collision 131592),.stop (.third 3 0 5 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,94] 95 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65561),.stop (.collision 9344),.stop (.collision 99392),.stop (.collision 99336),.stop (.collision 98944),.stop (.third 0 5 4 83),.stop (.collision 98832),.stop (.collision 98440),.stop (.collision 71168),.stop (.collision 98370),.stop (.collision 98314),.stop (.third 3 0 5 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,95] 96 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65561),.stop (.collision 9344),.stop (.collision 9729),.stop (.collision 9736),.branch [.stop (.third 1 6 4 83),.stop (.collision 590401),.stop (.collision 70280),.stop (.collision 590345),.stop (.collision 1081920),.stop (.third 3 0 6 17),.stop (.third 1 6 5 17),.stop (.collision 791049),.stop (.collision 562184),.stop (.collision 562177),.stop (.collision 561792),.stop (.third 1 0 6 119)],.stop (.third 1 5 4 83),.stop (.collision 98825),.stop (.collision 71168),.stop (.collision 98377),.stop (.collision 131648),.stop (.third 3 0 5 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,96] 97 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65561),.stop (.collision 99392),.stop (.collision 99336),.stop (.collision 98944),.stop (.collision 98888),.stop (.collision 9792),.stop (.collision 71168),.stop (.collision 98384),.stop (.collision 98370),.stop (.third 3 0 5 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,97] 98 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65561),.stop (.collision 9344),.stop (.collision 99329),.stop (.collision 9736),.stop (.collision 98881),.stop (.third 2 5 4 83),.stop (.collision 98433),.stop (.collision 98377),.stop (.third 3 0 5 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,98] 99 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 99392),.stop (.collision 9344),.stop (.collision 98944),.stop (.third 0 5 4 109),.stop (.collision 71168),.stop (.collision 9792),.stop (.collision 98384),.stop (.third 3 0 5 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,99] 100 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65561),.stop (.collision 9344),.stop (.collision 9729),.stop (.third 1 5 4 109),.stop (.collision 98825),.stop (.collision 9792),.stop (.third 3 0 5 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,100] 101 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 99336),.stop (.collision 98944),.stop (.collision 98888),.stop (.collision 9736),.stop (.collision 98440),.stop (.third 3 0 5 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,101] 102 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 99329),.stop (.collision 71168),.stop (.collision 98881),.stop (.third 2 5 4 109),.stop (.third 3 0 5 17),.stop (.third 3 5 4 83),.stop (.collision 4185),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,102] 103 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 71168),.stop (.collision 98888),.stop (.collision 98832),.stop (.third 3 0 5 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,103] 104 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65561),.stop (.collision 98881),.stop (.third 3 0 5 17),.stop (.collision 70720),.stop (.collision 98377),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,104] 105 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 99392),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 98888),.stop (.third 3 0 5 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,105] 106 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 71168),.stop (.collision 9281),.stop (.collision 9288),.stop (.third 3 0 5 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.third 3 5 4 109),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,106] 107 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 8896),.stop (.collision 9281),.stop (.third 0 5 4 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,107] 108 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 8896),.stop (.third 3 0 5 17),.stop (.third 1 5 4 17),.stop (.collision 98825),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,108] 109 (.branch [.stop (.collision 8784),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.third 3 0 5 17),.stop (.collision 70720),.stop (.collision 9288),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,109] 110 (.stop (.collision 5)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,110] 111 (.stop (.collision 9728)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,111] 112 (.stop (.collision 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,112] 113 (.stop (.collision 26)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,113] 114 (.stop (.third 3 0 4 17)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,114] 115 (.stop (.collision 9280)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,115] 116 (.stop (.collision 89)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,116] 117 (.stop (.collision 9224)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,117] 118 (.stop (.collision 9217)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,118] 119 (.stop (.collision 8832)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 3 2 [0,1,3,7,119] 120 (.stop (.third 1 0 4 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

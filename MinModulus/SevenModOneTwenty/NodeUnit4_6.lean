import MinModulus.SevenModOneTwenty.BlockUnit48
import MinModulus.SevenModOneTwenty.BlockUnit49
import MinModulus.SevenModOneTwenty.BlockUnit50
import MinModulus.SevenModOneTwenty.BlockUnit51

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_4_6_closed : ClosedMinimalPrefix true 120 4 3 [0,1,4,6] 7 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,7] 8 (.stop (.third 4 3 2 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,8] 9 (.stop (.collision 712)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,9] 10 (.stop (.collision 1153)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,10] 11 (.stop (.collision 1160)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,11] 12 (.stop (.collision 1601)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,12] 13 (.stop (.collision 1608)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,13] 14 (.stop (.collision 1216)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,14] 15 (.stop (.collision 2056)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,15] 16 (.stop (.collision 1664)) (by decide +kernel))
  · exact unit_4_6_16_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,17] 18 (.stop (.collision 2112)) (by decide +kernel))
  · exact unit_4_6_18_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,19] 20 (.stop (.collision 2560)) (by decide +kernel))
  · exact unit_4_6_20_closed
  · exact unit_4_6_21_closed
  · exact unit_4_6_22_closed
  · exact unit_4_6_23_closed
  · exact unit_4_6_24_closed
  · exact unit_4_6_25_closed
  · exact unit_4_6_26_closed
  · exact unit_4_6_27_closed
  · exact unit_4_6_28_closed
  · exact unit_4_6_29_closed
  · exact unit_4_6_30_closed
  · exact unit_4_6_31_closed
  · exact unit_4_6_32_closed
  · exact unit_4_6_33_closed
  · exact unit_4_6_34_closed
  · exact unit_4_6_35_closed
  · exact unit_4_6_36_closed
  · exact unit_4_6_37_closed
  · exact unit_4_6_38_closed
  · exact unit_4_6_39_closed
  · exact unit_4_6_40_closed
  · exact unit_4_6_41_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,42] 43 (.stop (.third 1 4 2 41)) (by decide +kernel))
  · exact unit_4_6_43_closed
  · exact unit_4_6_44_closed
  · exact unit_4_6_45_closed
  · exact unit_4_6_46_closed
  · exact unit_4_6_47_closed
  · exact unit_4_6_48_closed
  · exact unit_4_6_49_closed
  · exact unit_4_6_50_closed
  · exact unit_4_6_51_closed
  · exact unit_4_6_52_closed
  · exact unit_4_6_53_closed
  · exact unit_4_6_54_closed
  · exact unit_4_6_55_closed
  · exact unit_4_6_56_closed
  · exact unit_4_6_57_closed
  · exact unit_4_6_58_closed
  · exact unit_4_6_59_closed
  · exact unit_4_6_60_closed
  · exact unit_4_6_61_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,62] 63 (.stop (.collision 12808)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,63] 64 (.stop (.third 4 2 3 61)) (by decide +kernel))
  · exact unit_4_6_64_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,65] 66 (.stop (.third 2 4 3 61)) (by decide +kernel))
  · exact unit_4_6_66_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,67] 68 (.stop (.third 4 3 2 59)) (by decide +kernel))
  · exact unit_4_6_68_closed
  · exact unit_4_6_69_closed
  · exact unit_4_6_70_closed
  · exact unit_4_6_71_closed
  · exact unit_4_6_72_closed
  · exact unit_4_6_73_closed
  · exact unit_4_6_74_closed
  · exact unit_4_6_75_closed
  · exact unit_4_6_76_closed
  · exact unit_4_6_77_closed
  · exact unit_4_6_78_closed
  · exact unit_4_6_79_closed
  · exact unit_4_6_80_closed
  · exact unit_4_6_81_closed
  · exact unit_4_6_82_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,83] 84 (.stop (.third 2 4 1 79)) (by decide +kernel))
  · exact unit_4_6_84_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,85] 86 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.third 4 3 5 41),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 8896),.stop (.collision 9736),.stop (.collision 9344),.stop (.collision 65547),.stop (.collision 9792),.branch [.stop (.third 4 6 2 37),.stop (.collision 70665),.stop (.collision 70273),.stop (.collision 70280),.stop (.collision 70721),.stop (.collision 70728),.stop (.collision 70336),.stop (.collision 590464),.stop (.collision 791616),.stop (.collision 791168),.stop (.collision 590408),.stop (.collision 590401),.stop (.collision 589960),.stop (.third 2 6 4 83),.stop (.collision 590345),.stop (.collision 562688),.stop (.collision 589897),.stop (.collision 562240),.stop (.collision 36953),.stop (.collision 561792),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119)],.stop (.third 4 5 2 37),.stop (.collision 99840),.stop (.collision 99392),.stop (.collision 98944),.stop (.collision 99329),.stop (.collision 98881),.stop (.collision 98832),.stop (.collision 98384),.stop (.collision 98370),.stop (.collision 98321),.stop (.collision 132096),.stop (.collision 4101),.stop (.collision 131585),.stop (.third 2 5 4 83),.stop (.collision 4122),.stop (.collision 71168),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact unit_4_6_86_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,87] 88 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 8896),.stop (.collision 9736),.stop (.collision 9344),.stop (.collision 65547),.stop (.third 4 5 0 11),.branch [.stop (.third 4 6 3 37),.stop (.collision 70665),.stop (.collision 70273),.stop (.collision 70280),.stop (.third 1 6 4 7),.stop (.collision 70728),.stop (.third 5 6 0 103),.stop (.collision 791616),.stop (.collision 590408),.stop (.third 0 6 4 109),.stop (.third 1 6 5 109),.stop (.collision 98889),.stop (.collision 590345),.stop (.third 0 6 5 17),.stop (.collision 589897),.stop (.collision 562240),.stop (.collision 36953),.stop (.collision 561792),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119)],.stop (.third 4 5 3 37),.stop (.collision 99392),.stop (.collision 98944),.stop (.collision 99329),.stop (.third 1 5 4 7),.stop (.collision 98832),.stop (.collision 98384),.stop (.collision 98370),.stop (.collision 98321),.stop (.third 0 5 4 109),.stop (.collision 4108),.stop (.collision 131144),.stop (.collision 4122),.stop (.third 3 5 4 83),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,88] 89 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 8896),.stop (.collision 9736),.stop (.collision 9344),.stop (.collision 65547),.stop (.third 4 5 1 11),.branch [.stop (.collision 70224),.stop (.collision 70665),.stop (.collision 70273),.stop (.collision 819784),.stop (.collision 70721),.stop (.collision 70728),.stop (.third 3 6 4 101),.stop (.collision 590408),.stop (.collision 590401),.stop (.third 1 6 4 109),.stop (.collision 71232),.stop (.collision 590345),.stop (.third 3 6 5 83),.stop (.third 1 6 5 17),.stop (.collision 562240),.stop (.collision 36953),.stop (.collision 561792),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119)],.stop (.collision 10240),.stop (.collision 20488),.stop (.collision 99336),.stop (.collision 98888),.stop (.collision 98440),.stop (.collision 98825),.stop (.third 3 5 4 101),.stop (.collision 98328),.stop (.collision 98314),.stop (.third 1 5 4 109),.stop (.collision 131585),.stop (.collision 4122),.stop (.collision 71168),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,89] 90 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 8896),.stop (.collision 9736),.stop (.collision 9344),.stop (.collision 65547),.stop (.collision 9792),.stop (.collision 99840),.stop (.collision 99392),.stop (.collision 98944),.stop (.collision 99329),.stop (.collision 98881),.stop (.collision 98832),.stop (.collision 98384),.stop (.collision 98370),.stop (.collision 98321),.stop (.collision 131648),.stop (.collision 131592),.stop (.collision 131137),.stop (.collision 71168),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,90] 91 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 8896),.stop (.collision 9736),.stop (.collision 9344),.stop (.collision 65547),.stop (.collision 9792),.branch [.stop (.collision 70224),.stop (.collision 70665),.stop (.collision 819784),.stop (.collision 70280),.stop (.third 2 6 4 7),.stop (.collision 590408),.stop (.collision 590401),.stop (.collision 791560),.stop (.collision 791112),.stop (.collision 590345),.stop (.third 2 6 5 109),.stop (.collision 589897),.stop (.collision 562240),.stop (.collision 36953),.stop (.collision 561792),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119)],.stop (.collision 10240),.stop (.collision 99336),.stop (.collision 98888),.stop (.collision 98440),.stop (.third 2 5 4 7),.stop (.collision 98377),.stop (.collision 98328),.stop (.collision 98314),.stop (.collision 4115),.stop (.collision 131144),.stop (.collision 71168),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,91] 92 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 8896),.stop (.collision 9736),.stop (.collision 9344),.stop (.collision 65547),.stop (.third 4 5 2 11),.stop (.collision 99392),.stop (.collision 98944),.stop (.collision 99329),.stop (.collision 98881),.stop (.collision 98832),.stop (.collision 98384),.stop (.collision 98370),.stop (.collision 98321),.stop (.collision 4115),.stop (.collision 131585),.stop (.third 2 5 4 109),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,92] 93 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 8896),.stop (.collision 9736),.stop (.collision 9344),.stop (.collision 65547),.stop (.collision 9792),.branch [.stop (.collision 70224),.stop (.collision 819784),.stop (.collision 70273),.stop (.collision 590408),.stop (.third 3 6 4 7),.stop (.collision 70728),.stop (.collision 1081920),.stop (.collision 791112),.stop (.collision 562688),.stop (.collision 791049),.stop (.third 3 6 5 109),.stop (.collision 98889),.stop (.collision 561792),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119)],.stop (.collision 99336),.stop (.collision 98888),.stop (.collision 98440),.stop (.collision 98825),.stop (.third 3 5 4 7),.stop (.collision 4108),.stop (.collision 131648),.stop (.collision 131592),.stop (.collision 71168),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,93] 94 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 8896),.stop (.collision 9736),.stop (.collision 9344),.stop (.collision 65547),.stop (.third 4 5 3 11),.stop (.collision 98944),.stop (.collision 99329),.stop (.collision 98881),.stop (.collision 98832),.stop (.collision 98384),.stop (.collision 98370),.stop (.collision 98321),.stop (.collision 4122),.stop (.collision 71168),.stop (.collision 4171),.stop (.third 3 5 4 109),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,94] 95 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 8896),.stop (.collision 9736),.stop (.collision 9344),.stop (.collision 65547),.stop (.collision 9792),.stop (.collision 99336),.stop (.third 0 5 4 83),.stop (.collision 98440),.stop (.collision 98825),.stop (.collision 98377),.stop (.collision 4115),.stop (.collision 98314),.stop (.collision 71168),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,95] 96 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 8896),.stop (.collision 9736),.stop (.collision 9344),.stop (.collision 99392),.stop (.collision 9792),.stop (.collision 99329),.stop (.third 1 5 4 83),.stop (.collision 98832),.stop (.collision 98384),.stop (.collision 98370),.stop (.collision 131648),.stop (.collision 71168),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,96] 97 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 8896),.stop (.collision 9736),.stop (.collision 9344),.stop (.collision 65547),.stop (.collision 9792),.stop (.collision 98888),.stop (.collision 98440),.stop (.collision 98825),.stop (.collision 98377),.stop (.collision 4122),.stop (.collision 71168),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,97] 98 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 8896),.stop (.collision 9736),.stop (.collision 99392),.stop (.collision 98944),.stop (.collision 9792),.stop (.collision 98881),.stop (.collision 98832),.stop (.collision 98384),.stop (.collision 98370),.stop (.collision 71168),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,98] 99 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 8896),.stop (.collision 9736),.stop (.collision 9344),.stop (.collision 99336),.stop (.third 0 5 4 109),.stop (.collision 98440),.stop (.third 2 5 4 83),.stop (.collision 98377),.stop (.collision 71168),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,99] 100 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.third 4 5 0 103),.stop (.collision 99392),.stop (.collision 98944),.stop (.collision 99329),.stop (.third 1 5 4 109),.stop (.collision 98832),.stop (.collision 98384),.stop (.third 0 5 4 17),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,100] 101 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.third 4 5 1 103),.stop (.collision 9736),.stop (.collision 9344),.stop (.collision 98888),.stop (.collision 9792),.stop (.collision 98825),.stop (.third 3 5 4 83),.stop (.third 1 5 4 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,101] 102 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 99392),.stop (.collision 98944),.stop (.collision 9344),.stop (.collision 98881),.stop (.collision 9792),.stop (.collision 71168),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,102] 103 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 8896),.stop (.collision 99336),.stop (.collision 98888),.stop (.collision 98440),.stop (.third 2 5 4 109),.stop (.collision 98377),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,103] 104 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.third 4 5 2 103),.stop (.collision 9736),.stop (.collision 98881),.stop (.collision 71168),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.third 2 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,104] 105 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 8896),.stop (.collision 98888),.stop (.collision 71168),.stop (.collision 98825),.stop (.third 3 5 4 109),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,105] 106 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.third 4 5 3 103),.stop (.collision 98881),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,106] 107 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.third 0 5 4 17),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 98377),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,107] 108 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 9288),.stop (.third 1 5 4 17),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,108] 109 (.branch [.stop (.collision 8784),.stop (.collision 9225),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9281),.stop (.collision 98888),.stop (.collision 70720),.stop (.collision 98825),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,109] 110 (.stop (.collision 5)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,110] 111 (.stop (.collision 12)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,111] 112 (.stop (.collision 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,112] 113 (.stop (.collision 26)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,113] 114 (.stop (.collision 9728)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,114] 115 (.stop (.collision 75)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,115] 116 (.stop (.collision 9280)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,116] 117 (.stop (.collision 89)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,117] 118 (.stop (.collision 8832)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,118] 119 (.stop (.third 1 0 4 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,6,119] 120 (.stop (.third 1 0 4 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

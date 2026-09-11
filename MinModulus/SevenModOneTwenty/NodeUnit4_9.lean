import MinModulus.SevenModOneTwenty.BlockUnit51
import MinModulus.SevenModOneTwenty.BlockUnit52

namespace MinModulus.PrefixCertificate.Seven120

theorem unit_4_9_closed : ClosedMinimalPrefix true 120 4 3 [0,1,4,9] 10 := by
  apply closedMinimalPrefix_of_children
  intro x hlo hhi
  interval_cases x
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,10] 11 (.stop (.collision 1104)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,11] 12 (.stop (.collision 768)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,12] 13 (.stop (.collision 1153)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,13] 14 (.stop (.collision 1160)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,14] 15 (.stop (.collision 1545)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,15] 16 (.stop (.collision 1552)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,16] 17 (.stop (.collision 1216)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,17] 18 (.stop (.collision 1601)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,18] 19 (.stop (.collision 1608)) (by decide +kernel))
  · exact unit_4_9_19_closed
  · exact unit_4_9_20_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,21] 22 (.stop (.collision 1664)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,22] 23 (.stop (.collision 2049)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,23] 24 (.stop (.collision 2056)) (by decide +kernel))
  · exact unit_4_9_24_closed
  · exact unit_4_9_25_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,26] 27 (.stop (.collision 2112)) (by decide +kernel))
  · exact unit_4_9_27_closed
  · exact unit_4_9_28_closed
  · exact unit_4_9_29_closed
  · exact unit_4_9_30_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,31] 32 (.stop (.collision 2560)) (by decide +kernel))
  · exact unit_4_9_32_closed
  · exact unit_4_9_33_closed
  · exact unit_4_9_34_closed
  · exact unit_4_9_35_closed
  · exact unit_4_9_36_closed
  · exact unit_4_9_37_closed
  · exact unit_4_9_38_closed
  · exact unit_4_9_39_closed
  · exact unit_4_9_40_closed
  · exact unit_4_9_41_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,42] 43 (.stop (.third 1 4 2 41)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,43] 44 (.stop (.third 0 4 3 67)) (by decide +kernel))
  · exact unit_4_9_44_closed
  · exact unit_4_9_45_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,46] 47 (.stop (.third 3 4 0 13)) (by decide +kernel))
  · exact unit_4_9_47_closed
  · exact unit_4_9_48_closed
  · exact unit_4_9_49_closed
  · exact unit_4_9_50_closed
  · exact unit_4_9_51_closed
  · exact unit_4_9_52_closed
  · exact unit_4_9_53_closed
  · exact unit_4_9_54_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,55] 56 (.branch [.stop (.collision 8784),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 74752),.stop (.collision 102920),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 102465),.stop (.collision 74304),.stop (.collision 601),.stop (.collision 608),.stop (.collision 74248),.stop (.collision 74241),.stop (.collision 73856),.stop (.collision 9792),.stop (.collision 713),.stop (.collision 73800),.stop (.collision 73793),.stop (.collision 1112),.stop (.collision 776),.stop (.third 4 5 2 47),.stop (.collision 1168),.stop (.collision 1553),.stop (.collision 1217),.stop (.collision 1224),.stop (.third 0 5 3 107),.stop (.collision 1616),.stop (.collision 99336),.stop (.third 3 5 0 53),.stop (.collision 1672),.stop (.collision 98881),.stop (.collision 98832),.stop (.collision 98440),.stop (.collision 2113),.stop (.third 3 5 4 107),.stop (.collision 98328),.stop (.collision 98314),.stop (.collision 107008),.stop (.collision 2561),.stop (.collision 12298),.stop (.collision 12305),.stop (.collision 106504),.stop (.collision 131585),.stop (.third 2 5 4 73),.stop (.collision 12368),.stop (.collision 131074),.stop (.collision 12417),.stop (.collision 12424),.stop (.third 5 3 4 47),.stop (.collision 71168),.stop (.collision 4115),.stop (.collision 12865),.stop (.collision 12872),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 4192),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact unit_4_9_56_closed
  · exact unit_4_9_57_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,58] 59 (.stop (.collision 13312)) (by decide +kernel))
  · exact unit_4_9_59_closed
  · exact unit_4_9_60_closed
  · exact unit_4_9_61_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,62] 63 (.stop (.collision 12808)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,63] 64 (.stop (.collision 12416)) (by decide +kernel))
  · exact unit_4_9_64_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,65] 66 (.stop (.collision 12353)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,66] 67 (.stop (.collision 12304)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,67] 68 (.stop (.collision 12290)) (by decide +kernel))
  · exact unit_4_9_68_closed
  · exact unit_4_9_69_closed
  · exact unit_4_9_70_closed
  · exact unit_4_9_71_closed
  · exact unit_4_9_72_closed
  · exact unit_4_9_73_closed
  · exact unit_4_9_74_closed
  · exact unit_4_9_75_closed
  · exact unit_4_9_76_closed
  · exact unit_4_9_77_closed
  · exact unit_4_9_78_closed
  · exact unit_4_9_79_closed
  · exact unit_4_9_80_closed
  · exact unit_4_9_81_closed
  · exact unit_4_9_82_closed
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,83] 84 (.stop (.third 0 4 3 107)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,84] 85 (.branch [.stop (.collision 8784),.stop (.third 3 5 0 53),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 9232),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65603),.stop (.collision 65561),.stop (.collision 9344),.stop (.collision 9729),.stop (.collision 99392),.branch [.stop (.collision 70224),.stop (.collision 42560),.stop (.collision 819784),.stop (.collision 70280),.stop (.collision 819721),.stop (.collision 590408),.stop (.third 5 6 0 103),.stop (.collision 70721),.stop (.collision 70728),.stop (.collision 590345),.stop (.third 1 6 5 109),.stop (.collision 36939),.stop (.collision 562240),.stop (.third 0 6 5 17),.stop (.collision 589897),.stop (.collision 562184),.stop (.collision 562177),.stop (.collision 561792),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119)],.stop (.collision 99329),.stop (.collision 9792),.stop (.collision 98888),.stop (.collision 110592),.stop (.collision 98825),.stop (.collision 98433),.stop (.collision 98384),.stop (.collision 71168),.stop (.collision 98321),.stop (.collision 4122),.stop (.collision 4129),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 4192),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,85] 86 (.branch [.stop (.third 3 5 0 53),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 9232),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65603),.stop (.collision 65561),.stop (.collision 9344),.stop (.third 4 5 2 37),.stop (.collision 9736),.stop (.collision 99336),.stop (.collision 98944),.stop (.collision 9792),.stop (.collision 98881),.stop (.collision 98832),.stop (.collision 98440),.stop (.collision 4101),.stop (.collision 98377),.stop (.collision 4115),.stop (.collision 98314),.stop (.collision 131585),.stop (.third 2 5 4 83),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 4192),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,86] 87 (.stop (.third 3 4 0 53)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,87] 88 (.branch [.stop (.collision 8784),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 9232),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65603),.stop (.third 4 5 0 11),.stop (.collision 9344),.stop (.collision 9729),.stop (.collision 99336),.stop (.collision 98944),.stop (.collision 20992),.stop (.third 1 5 4 7),.stop (.collision 98832),.stop (.collision 98440),.stop (.collision 71168),.stop (.collision 98377),.stop (.third 0 5 4 109),.stop (.collision 4129),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 4192),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,88] 89 (.branch [.stop (.collision 8784),.stop (.collision 66072),.stop (.third 4 3 5 41),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 9232),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65603),.stop (.third 4 5 1 11),.stop (.collision 99392),.stop (.collision 9729),.stop (.collision 9736),.branch [.stop (.collision 819784),.stop (.collision 590408),.stop (.collision 590401),.stop (.collision 70280),.stop (.collision 70665),.stop (.collision 590345),.stop (.third 1 6 4 109),.stop (.collision 70721),.stop (.collision 562240),.stop (.collision 36953),.stop (.collision 589897),.stop (.collision 562184),.stop (.third 3 6 5 83),.stop (.third 2 6 5 17),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119)],.stop (.collision 98888),.stop (.collision 9792),.stop (.collision 98825),.stop (.collision 71168),.stop (.collision 98384),.stop (.collision 98370),.stop (.third 1 5 4 109),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 4192),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,89] 90 (.branch [.stop (.collision 8784),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 9232),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65603),.stop (.collision 65561),.stop (.collision 9344),.stop (.collision 99336),.stop (.collision 98944),.branch [.stop (.collision 590408),.stop (.collision 590401),.stop (.collision 70273),.stop (.collision 70280),.stop (.collision 590345),.stop (.collision 1081920),.stop (.collision 36939),.stop (.collision 562240),.stop (.collision 70728),.stop (.collision 791049),.stop (.collision 562184),.stop (.collision 562177),.stop (.collision 561792),.stop (.third 1 0 6 119),.stop (.third 1 0 6 119)],.stop (.collision 98881),.stop (.collision 9792),.stop (.collision 71168),.stop (.collision 4115),.stop (.collision 98377),.stop (.collision 131648),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 4192),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,90] 91 (.branch [.stop (.collision 8784),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 9232),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65603),.stop (.collision 99392),.stop (.collision 9344),.stop (.third 4 5 3 37),.stop (.collision 9736),.stop (.collision 98888),.stop (.collision 98496),.stop (.third 2 5 4 7),.stop (.collision 98433),.stop (.collision 98384),.stop (.collision 4129),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 4192),.stop (.collision 70664),.stop (.third 3 5 4 83),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,91] 92 (.branch [.stop (.collision 8784),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 9232),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65603),.stop (.third 4 5 2 11),.stop (.collision 9344),.stop (.collision 98944),.stop (.collision 9736),.stop (.collision 98881),.stop (.collision 71168),.stop (.collision 9792),.stop (.collision 4122),.stop (.third 3 5 4 101),.stop (.collision 4171),.stop (.collision 70720),.stop (.third 2 5 4 109),.stop (.collision 4192),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,92] 93 (.branch [.stop (.collision 8784),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 9232),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 99392),.stop (.collision 65561),.stop (.collision 9344),.stop (.collision 9729),.stop (.collision 98888),.stop (.collision 71168),.stop (.collision 98825),.stop (.collision 9792),.stop (.collision 98384),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 4192),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,93] 94 (.branch [.stop (.collision 8784),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 9232),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65603),.stop (.collision 99336),.stop (.collision 98944),.stop (.collision 9729),.stop (.collision 98881),.stop (.collision 98832),.stop (.collision 98440),.stop (.collision 9792),.stop (.collision 98377),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 131144),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,94] 95 (.branch [.stop (.collision 8784),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 9232),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65603),.stop (.collision 99329),.stop (.collision 9344),.stop (.third 0 5 4 83),.stop (.collision 9736),.stop (.collision 98825),.stop (.collision 98433),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 4192),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,95] 96 (.branch [.stop (.collision 8784),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 9232),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 99336),.stop (.collision 98944),.stop (.collision 71168),.stop (.third 1 5 4 83),.stop (.collision 9736),.stop (.collision 98440),.stop (.collision 4171),.stop (.third 3 5 4 7),.stop (.collision 4185),.stop (.collision 4192),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,96] 97 (.branch [.stop (.collision 8784),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 9232),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 99329),.stop (.third 4 5 3 11),.stop (.collision 98888),.stop (.collision 9729),.stop (.collision 98825),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 4192),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,97] 98 (.branch [.stop (.collision 8784),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 9232),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 71168),.stop (.collision 65561),.stop (.collision 98881),.stop (.collision 98832),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 98377),.stop (.collision 9792),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,98] 99 (.branch [.stop (.collision 8784),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 9232),.stop (.collision 99392),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 65603),.stop (.third 0 5 4 109),.stop (.collision 9344),.stop (.third 2 5 4 83),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 131592),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,99] 100 (.branch [.stop (.collision 8784),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 9232),.stop (.third 4 5 0 103),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 4122),.stop (.third 1 5 4 109),.stop (.collision 4171),.stop (.collision 70720),.stop (.third 0 5 4 17),.stop (.collision 98377),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,100] 101 (.branch [.stop (.collision 8784),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 99392),.stop (.third 4 5 1 103),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 98888),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 4185),.stop (.third 1 5 4 17),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,101] 102 (.branch [.stop (.collision 8784),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 71168),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 9288),.stop (.collision 98881),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 131648),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,102] 103 (.branch [.stop (.collision 8784),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 9232),.stop (.collision 8896),.stop (.collision 9281),.stop (.collision 98888),.stop (.collision 70720),.stop (.third 2 5 4 109),.stop (.collision 9344),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,103] 104 (.branch [.stop (.collision 8784),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 99336),.stop (.third 4 5 2 103),.stop (.collision 9281),.stop (.collision 70720),.stop (.collision 4185),.stop (.collision 98440),.stop (.collision 70664),.stop (.third 3 5 4 83),.stop (.third 2 5 4 17),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,104] 105 (.branch [.stop (.collision 8784),.stop (.collision 66072),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 9232),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 9288),.stop (.collision 98825),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,105] 106 (.branch [.stop (.collision 8784),.stop (.collision 71168),.stop (.collision 8833),.stop (.collision 8840),.stop (.collision 9225),.stop (.collision 4171),.stop (.collision 70720),.stop (.collision 98881),.stop (.collision 9288),.stop (.collision 70664),.stop (.collision 70657),.stop (.collision 70272),.stop (.third 1 0 5 119),.stop (.third 1 0 5 119)]) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,106] 107 (.stop (.collision 5)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,107] 108 (.stop (.collision 9728)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,108] 109 (.stop (.collision 19)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,109] 110 (.stop (.collision 26)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,110] 111 (.stop (.collision 33)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,111] 112 (.stop (.collision 75)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,112] 113 (.stop (.collision 9280)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,113] 114 (.stop (.collision 89)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,114] 115 (.stop (.collision 96)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,115] 116 (.stop (.collision 9224)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,116] 117 (.stop (.collision 9217)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,117] 118 (.stop (.collision 8832)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,118] 119 (.stop (.third 1 0 4 119)) (by decide +kernel))
  · exact (closedMinimalPrefix_of_verify true 120 4 2 [0,1,4,9,119] 120 (.stop (.third 1 0 4 119)) (by decide +kernel))

end MinModulus.PrefixCertificate.Seven120

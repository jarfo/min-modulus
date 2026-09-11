import MinModulus.SevenModSixtySix.UnitSmall
import MinModulus.SevenModSixtySix.Unit3
import MinModulus.SevenModSixtySix.Unit4
import MinModulus.SevenModSixtySix.Unit5
import MinModulus.SevenModSixtySix.Unit6
import MinModulus.SevenModSixtySix.Unit7
import MinModulus.SevenModSixtySix.Unit8
import MinModulus.SevenModSixtySix.Unit9
import MinModulus.SevenModSixtySix.Unit10
import MinModulus.SevenModSixtySix.Unit11
import MinModulus.SevenModSixtySix.Unit12
import MinModulus.SevenModSixtySix.Unit13
import MinModulus.SevenModSixtySix.Unit14
import MinModulus.SevenModSixtySix.Unit15
import MinModulus.SevenModSixtySix.Unit16
import MinModulus.SevenModSixtySix.Unit17
import MinModulus.SevenModSixtySix.Unit18
import MinModulus.SevenModSixtySix.Unit19
import MinModulus.SevenModSixtySix.Unit20
import MinModulus.SevenModSixtySix.Unit21
import MinModulus.SevenModSixtySix.Unit22
import MinModulus.SevenModSixtySix.Unit23
import MinModulus.SevenModSixtySix.Unit24
import MinModulus.SevenModSixtySix.Unit25
import MinModulus.SevenModSixtySix.Unit26
import MinModulus.SevenModSixtySix.Unit27
import MinModulus.SevenModSixtySix.Unit28
import MinModulus.SevenModSixtySix.Unit29
import MinModulus.SevenModSixtySix.Unit30
import MinModulus.SevenModSixtySix.Unit31
import MinModulus.SevenModSixtySix.Unit32
import MinModulus.SevenModSixtySix.Unit33
import MinModulus.SevenModSixtySix.Unit34
import MinModulus.SevenModSixtySix.Unit35
import MinModulus.SevenModSixtySix.Unit36
import MinModulus.SevenModSixtySix.NonunitSmall
import MinModulus.SevenModSixtySix.Nonunit2
import MinModulus.SevenModSixtySix.Nonunit3
import MinModulus.SevenModSixtySix.Nonunit4
import MinModulus.SevenModSixtySix.Nonunit6
import MinModulus.SevenModSixtySix.Nonunit8
import MinModulus.SevenModSixtySix.Nonunit9
import MinModulus.SevenModSixtySix.Nonunit10
import MinModulus.SevenModSixtySix.Nonunit11
import MinModulus.SevenModSixtySix.Nonunit12
import MinModulus.SevenModSixtySix.Nonunit14
import MinModulus.SevenModSixtySix.Nonunit15
import MinModulus.SevenModSixtySix.Nonunit16
import MinModulus.SevenModSixtySix.Nonunit18
import MinModulus.SevenModSixtySix.Nonunit20
import MinModulus.SevenModSixtySix.Nonunit21
import MinModulus.SevenModSixtySix.Nonunit22
import MinModulus.SevenModSixtySix.Nonunit24
import MinModulus.SevenModSixtySix.Nonunit26
import MinModulus.SevenModSixtySix.Nonunit28
import MinModulus.SevenModSixtySix.Nonunit30

namespace MinModulus.PrefixCertificate.Seven66

theorem unit_closed : ClosedPrefix 66 5 [0,1] 2 := by
  apply closedPrefix_of_children
  intro a hlo hhi
  interval_cases a
  · exact unit_2_closed
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
  · exact unit_37_closed
  · exact unit_38_closed
  · exact unit_39_closed
  · exact unit_40_closed
  · exact unit_41_closed
  · exact unit_42_closed
  · exact unit_43_closed
  · exact unit_44_closed
  · exact unit_45_closed
  · exact unit_46_closed
  · exact unit_47_closed
  · exact unit_48_closed
  · exact unit_49_closed
  · exact unit_50_closed
  · exact unit_51_closed
  · exact unit_52_closed
  · exact unit_53_closed
  · exact unit_54_closed
  · exact unit_55_closed
  · exact unit_56_closed
  · exact unit_57_closed
  · exact unit_58_closed
  · exact unit_59_closed
  · exact unit_60_closed
  · exact unit_61_closed
  · exact unit_62_closed
  · exact unit_63_closed
  · exact unit_64_closed
  · exact unit_65_closed

theorem nonunit_closed : ClosedNoUnitPrefix 66 6 [0] 1 := by
  apply closedNoUnitPrefix_of_children
  intro a hlo hhi
  interval_cases a
  · exact nonunit_1_closed
  · exact nonunit_2_closed
  · exact nonunit_3_closed
  · exact nonunit_4_closed
  · exact nonunit_5_closed
  · exact nonunit_6_closed
  · exact nonunit_7_closed
  · exact nonunit_8_closed
  · exact nonunit_9_closed
  · exact nonunit_10_closed
  · exact nonunit_11_closed
  · exact nonunit_12_closed
  · exact nonunit_13_closed
  · exact nonunit_14_closed
  · exact nonunit_15_closed
  · exact nonunit_16_closed
  · exact nonunit_17_closed
  · exact nonunit_18_closed
  · exact nonunit_19_closed
  · exact nonunit_20_closed
  · exact nonunit_21_closed
  · exact nonunit_22_closed
  · exact nonunit_23_closed
  · exact nonunit_24_closed
  · exact nonunit_25_closed
  · exact nonunit_26_closed
  · exact nonunit_27_closed
  · exact nonunit_28_closed
  · exact nonunit_29_closed
  · exact nonunit_30_closed
  · exact nonunit_31_closed
  · exact nonunit_32_closed
  · exact nonunit_33_closed
  · exact nonunit_34_closed
  · exact nonunit_35_closed
  · exact nonunit_36_closed
  · exact nonunit_37_closed
  · exact nonunit_38_closed
  · exact nonunit_39_closed
  · exact nonunit_40_closed
  · exact nonunit_41_closed
  · exact nonunit_42_closed
  · exact nonunit_43_closed
  · exact nonunit_44_closed
  · exact nonunit_45_closed
  · exact nonunit_46_closed
  · exact nonunit_47_closed
  · exact nonunit_48_closed
  · exact nonunit_49_closed
  · exact nonunit_50_closed
  · exact nonunit_51_closed
  · exact nonunit_52_closed
  · exact nonunit_53_closed
  · exact nonunit_54_closed
  · exact nonunit_55_closed
  · exact nonunit_56_closed
  · exact nonunit_57_closed
  · exact nonunit_58_closed
  · exact nonunit_59_closed
  · exact nonunit_60_closed
  · exact nonunit_61_closed
  · exact nonunit_62_closed
  · exact nonunit_63_closed
  · exact nonunit_64_closed
  · exact nonunit_65_closed

end MinModulus.PrefixCertificate.Seven66

namespace MinModulus

theorem not_validTuple_seven_mod_sixty_six (g : Fin 7 → ZMod 66) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 66) := ⟨⟨0, 1, by decide⟩⟩
  exact PrefixCertificate.not_validTuple_of_unit_and_noUnit_prefixes (by decide)
    PrefixCertificate.Seven66.unit_closed PrefixCertificate.Seven66.nonunit_closed g

end MinModulus

import MinModulus.SevenModOneTwenty

/-! Bounded groups of independently checked modulo-120 prefix certificates. -/

namespace MinModulus.PrefixCertificate.Seven120
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- All prefix exclusions in bounded certificate BlockUnit0. -/
theorem certificate_BlockUnit0 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 15 List.nil.{0}))))) 16) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 19 List.nil.{0}))))) 20) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 21 List.nil.{0}))))) 22) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 22 List.nil.{0}))))) 23) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 23 List.nil.{0}))))) 24) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 25 List.nil.{0}))))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 26 List.nil.{0}))))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 27 List.nil.{0}))))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 28 List.nil.{0}))))) 29) := by
  exact ⟨unit_3_7_15_closed, unit_3_7_19_closed, unit_3_7_21_closed, unit_3_7_22_closed, unit_3_7_23_closed, unit_3_7_25_closed, unit_3_7_26_closed, unit_3_7_27_closed, unit_3_7_28_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit1. -/
theorem certificate_BlockUnit1 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 29 List.nil.{0}))))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 30 List.nil.{0}))))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 31 List.nil.{0}))))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 32 List.nil.{0}))))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 33 List.nil.{0}))))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 34 List.nil.{0}))))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 35 List.nil.{0}))))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 36 List.nil.{0}))))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 37 List.nil.{0}))))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 38 List.nil.{0}))))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 40 List.nil.{0}))))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 41 List.nil.{0}))))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 42 List.nil.{0}))))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 43 List.nil.{0}))))) 44) := by
  exact ⟨unit_3_7_29_closed, unit_3_7_30_closed, unit_3_7_31_closed, unit_3_7_32_closed, unit_3_7_33_closed, unit_3_7_34_closed, unit_3_7_35_closed, unit_3_7_36_closed, unit_3_7_37_closed, unit_3_7_38_closed, unit_3_7_39_closed, unit_3_7_40_closed, unit_3_7_41_closed, unit_3_7_42_closed, unit_3_7_43_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit2. -/
theorem certificate_BlockUnit2 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 44 List.nil.{0}))))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 45 List.nil.{0}))))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 46 List.nil.{0}))))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 47 List.nil.{0}))))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 48 List.nil.{0}))))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 49 List.nil.{0}))))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 50 List.nil.{0}))))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 52 List.nil.{0}))))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 53 List.nil.{0}))))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 54 List.nil.{0}))))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 55 List.nil.{0}))))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 56 List.nil.{0}))))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 57 List.nil.{0}))))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 58 List.nil.{0}))))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 59 List.nil.{0}))))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 63 List.nil.{0}))))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 66 List.nil.{0}))))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 67 List.nil.{0}))))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 68 List.nil.{0}))))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 69 List.nil.{0}))))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 70 List.nil.{0}))))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 71 List.nil.{0}))))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 72 List.nil.{0}))))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 73 List.nil.{0}))))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 74 List.nil.{0}))))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 75 List.nil.{0}))))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 76 List.nil.{0}))))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 77 List.nil.{0}))))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 78 List.nil.{0}))))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 79 List.nil.{0}))))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 80 List.nil.{0}))))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 81 List.nil.{0}))))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 82 List.nil.{0}))))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 83 List.nil.{0}))))) 84) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 84 List.nil.{0}))))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 85 List.nil.{0}))))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 7 (List.cons.{0} 87 List.nil.{0}))))) 88) := by
  exact ⟨unit_3_7_44_closed, unit_3_7_45_closed, unit_3_7_46_closed, unit_3_7_47_closed, unit_3_7_48_closed, unit_3_7_49_closed, unit_3_7_50_closed, unit_3_7_51_closed, unit_3_7_52_closed, unit_3_7_53_closed, unit_3_7_54_closed, unit_3_7_55_closed, unit_3_7_56_closed, unit_3_7_57_closed, unit_3_7_58_closed, unit_3_7_59_closed, unit_3_7_60_closed, unit_3_7_61_closed, unit_3_7_63_closed, unit_3_7_66_closed, unit_3_7_67_closed, unit_3_7_68_closed, unit_3_7_69_closed, unit_3_7_70_closed, unit_3_7_71_closed, unit_3_7_72_closed, unit_3_7_73_closed, unit_3_7_74_closed, unit_3_7_75_closed, unit_3_7_76_closed, unit_3_7_77_closed, unit_3_7_78_closed, unit_3_7_79_closed, unit_3_7_80_closed, unit_3_7_81_closed, unit_3_7_82_closed, unit_3_7_83_closed, unit_3_7_84_closed, unit_3_7_85_closed, unit_3_7_87_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit3. -/
theorem certificate_BlockUnit3 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 19 List.nil.{0}))))) 20) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 21 List.nil.{0}))))) 22) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 22 List.nil.{0}))))) 23) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 25 List.nil.{0}))))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 27 List.nil.{0}))))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 28 List.nil.{0}))))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 29 List.nil.{0}))))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 30 List.nil.{0}))))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 31 List.nil.{0}))))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 33 List.nil.{0}))))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 34 List.nil.{0}))))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 35 List.nil.{0}))))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 36 List.nil.{0}))))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 37 List.nil.{0}))))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 38 List.nil.{0}))))) 39) := by
  exact ⟨unit_3_9_19_closed, unit_3_9_21_closed, unit_3_9_22_closed, unit_3_9_25_closed, unit_3_9_27_closed, unit_3_9_28_closed, unit_3_9_29_closed, unit_3_9_30_closed, unit_3_9_31_closed, unit_3_9_33_closed, unit_3_9_34_closed, unit_3_9_35_closed, unit_3_9_36_closed, unit_3_9_37_closed, unit_3_9_38_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit4. -/
theorem certificate_BlockUnit4 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 40 List.nil.{0}))))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 41 List.nil.{0}))))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 42 List.nil.{0}))))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 43 List.nil.{0}))))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 45 List.nil.{0}))))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 46 List.nil.{0}))))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 47 List.nil.{0}))))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 48 List.nil.{0}))))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 49 List.nil.{0}))))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 50 List.nil.{0}))))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 52 List.nil.{0}))))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 53 List.nil.{0}))))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 54 List.nil.{0}))))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 55 List.nil.{0}))))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 56 List.nil.{0}))))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 57 List.nil.{0}))))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 58 List.nil.{0}))))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 59 List.nil.{0}))))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 63 List.nil.{0}))))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 64 List.nil.{0}))))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 67 List.nil.{0}))))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 68 List.nil.{0}))))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 69 List.nil.{0}))))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 70 List.nil.{0}))))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 71 List.nil.{0}))))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 72 List.nil.{0}))))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 73 List.nil.{0}))))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 75 List.nil.{0}))))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 77 List.nil.{0}))))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 81 List.nil.{0}))))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 9 (List.cons.{0} 83 List.nil.{0}))))) 84) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 21 List.nil.{0}))))) 22) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 23 List.nil.{0}))))) 24) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 24 List.nil.{0}))))) 25) := by
  exact ⟨unit_3_9_39_closed, unit_3_9_40_closed, unit_3_9_41_closed, unit_3_9_42_closed, unit_3_9_43_closed, unit_3_9_45_closed, unit_3_9_46_closed, unit_3_9_47_closed, unit_3_9_48_closed, unit_3_9_49_closed, unit_3_9_50_closed, unit_3_9_51_closed, unit_3_9_52_closed, unit_3_9_53_closed, unit_3_9_54_closed, unit_3_9_55_closed, unit_3_9_56_closed, unit_3_9_57_closed, unit_3_9_58_closed, unit_3_9_59_closed, unit_3_9_60_closed, unit_3_9_61_closed, unit_3_9_63_closed, unit_3_9_64_closed, unit_3_9_67_closed, unit_3_9_68_closed, unit_3_9_69_closed, unit_3_9_70_closed, unit_3_9_71_closed, unit_3_9_72_closed, unit_3_9_73_closed, unit_3_9_75_closed, unit_3_9_77_closed, unit_3_9_81_closed, unit_3_9_83_closed, unit_3_10_21_closed, unit_3_10_23_closed, unit_3_10_24_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit5. -/
theorem certificate_BlockUnit5 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 25 List.nil.{0}))))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 28 List.nil.{0}))))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 30 List.nil.{0}))))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 31 List.nil.{0}))))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 32 List.nil.{0}))))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 33 List.nil.{0}))))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 34 List.nil.{0}))))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 35 List.nil.{0}))))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 37 List.nil.{0}))))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 38 List.nil.{0}))))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 40 List.nil.{0}))))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 41 List.nil.{0}))))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 42 List.nil.{0}))))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 43 List.nil.{0}))))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 44 List.nil.{0}))))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 45 List.nil.{0}))))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 46 List.nil.{0}))))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 47 List.nil.{0}))))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 48 List.nil.{0}))))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 49 List.nil.{0}))))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 50 List.nil.{0}))))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 52 List.nil.{0}))))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 53 List.nil.{0}))))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 54 List.nil.{0}))))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 56 List.nil.{0}))))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 58 List.nil.{0}))))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 59 List.nil.{0}))))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 63 List.nil.{0}))))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 68 List.nil.{0}))))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 69 List.nil.{0}))))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 70 List.nil.{0}))))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 71 List.nil.{0}))))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 72 List.nil.{0}))))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 73 List.nil.{0}))))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 74 List.nil.{0}))))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 75 List.nil.{0}))))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 76 List.nil.{0}))))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 77 List.nil.{0}))))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 78 List.nil.{0}))))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 79 List.nil.{0}))))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 10 (List.cons.{0} 80 List.nil.{0}))))) 81) := by
  exact ⟨unit_3_10_25_closed, unit_3_10_28_closed, unit_3_10_30_closed, unit_3_10_31_closed, unit_3_10_32_closed, unit_3_10_33_closed, unit_3_10_34_closed, unit_3_10_35_closed, unit_3_10_37_closed, unit_3_10_38_closed, unit_3_10_39_closed, unit_3_10_40_closed, unit_3_10_41_closed, unit_3_10_42_closed, unit_3_10_43_closed, unit_3_10_44_closed, unit_3_10_45_closed, unit_3_10_46_closed, unit_3_10_47_closed, unit_3_10_48_closed, unit_3_10_49_closed, unit_3_10_50_closed, unit_3_10_51_closed, unit_3_10_52_closed, unit_3_10_53_closed, unit_3_10_54_closed, unit_3_10_56_closed, unit_3_10_58_closed, unit_3_10_59_closed, unit_3_10_60_closed, unit_3_10_61_closed, unit_3_10_63_closed, unit_3_10_68_closed, unit_3_10_69_closed, unit_3_10_70_closed, unit_3_10_71_closed, unit_3_10_72_closed, unit_3_10_73_closed, unit_3_10_74_closed, unit_3_10_75_closed, unit_3_10_76_closed, unit_3_10_77_closed, unit_3_10_78_closed, unit_3_10_79_closed, unit_3_10_80_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit6. -/
theorem certificate_BlockUnit6 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 17 List.nil.{0}))))) 18) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 23 List.nil.{0}))))) 24) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 25 List.nil.{0}))))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 26 List.nil.{0}))))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 27 List.nil.{0}))))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 28 List.nil.{0}))))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 31 List.nil.{0}))))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 33 List.nil.{0}))))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 34 List.nil.{0}))))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 35 List.nil.{0}))))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 36 List.nil.{0}))))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 37 List.nil.{0}))))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 38 List.nil.{0}))))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 41 List.nil.{0}))))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 42 List.nil.{0}))))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 43 List.nil.{0}))))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 46 List.nil.{0}))))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 47 List.nil.{0}))))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 48 List.nil.{0}))))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 49 List.nil.{0}))))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 50 List.nil.{0}))))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 52 List.nil.{0}))))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 53 List.nil.{0}))))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 54 List.nil.{0}))))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 55 List.nil.{0}))))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 57 List.nil.{0}))))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 58 List.nil.{0}))))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 59 List.nil.{0}))))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 63 List.nil.{0}))))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 64 List.nil.{0}))))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 65 List.nil.{0}))))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 69 List.nil.{0}))))) 70) := by
  exact ⟨unit_3_11_17_closed, unit_3_11_23_closed, unit_3_11_25_closed, unit_3_11_26_closed, unit_3_11_27_closed, unit_3_11_28_closed, unit_3_11_31_closed, unit_3_11_33_closed, unit_3_11_34_closed, unit_3_11_35_closed, unit_3_11_36_closed, unit_3_11_37_closed, unit_3_11_38_closed, unit_3_11_39_closed, unit_3_11_41_closed, unit_3_11_42_closed, unit_3_11_43_closed, unit_3_11_46_closed, unit_3_11_47_closed, unit_3_11_48_closed, unit_3_11_49_closed, unit_3_11_50_closed, unit_3_11_51_closed, unit_3_11_52_closed, unit_3_11_53_closed, unit_3_11_54_closed, unit_3_11_55_closed, unit_3_11_57_closed, unit_3_11_58_closed, unit_3_11_59_closed, unit_3_11_60_closed, unit_3_11_61_closed, unit_3_11_63_closed, unit_3_11_64_closed, unit_3_11_65_closed, unit_3_11_69_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit7. -/
theorem certificate_BlockUnit7 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 71 List.nil.{0}))))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 72 List.nil.{0}))))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 73 List.nil.{0}))))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 74 List.nil.{0}))))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 75 List.nil.{0}))))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 77 List.nil.{0}))))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 79 List.nil.{0}))))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 81 List.nil.{0}))))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 82 List.nil.{0}))))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 11 (List.cons.{0} 83 List.nil.{0}))))) 84) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 18 List.nil.{0}))))) 19) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 19 List.nil.{0}))))) 20) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 25 List.nil.{0}))))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 27 List.nil.{0}))))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 28 List.nil.{0}))))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 29 List.nil.{0}))))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 30 List.nil.{0}))))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 31 List.nil.{0}))))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 36 List.nil.{0}))))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 37 List.nil.{0}))))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 38 List.nil.{0}))))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 40 List.nil.{0}))))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 41 List.nil.{0}))))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 42 List.nil.{0}))))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 43 List.nil.{0}))))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 46 List.nil.{0}))))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 47 List.nil.{0}))))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 48 List.nil.{0}))))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 49 List.nil.{0}))))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 50 List.nil.{0}))))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 52 List.nil.{0}))))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 53 List.nil.{0}))))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 54 List.nil.{0}))))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 55 List.nil.{0}))))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 57 List.nil.{0}))))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 58 List.nil.{0}))))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 59 List.nil.{0}))))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 61 List.nil.{0}))))) 62) := by
  exact ⟨unit_3_11_71_closed, unit_3_11_72_closed, unit_3_11_73_closed, unit_3_11_74_closed, unit_3_11_75_closed, unit_3_11_77_closed, unit_3_11_79_closed, unit_3_11_81_closed, unit_3_11_82_closed, unit_3_11_83_closed, unit_3_12_18_closed, unit_3_12_19_closed, unit_3_12_25_closed, unit_3_12_27_closed, unit_3_12_28_closed, unit_3_12_29_closed, unit_3_12_30_closed, unit_3_12_31_closed, unit_3_12_36_closed, unit_3_12_37_closed, unit_3_12_38_closed, unit_3_12_39_closed, unit_3_12_40_closed, unit_3_12_41_closed, unit_3_12_42_closed, unit_3_12_43_closed, unit_3_12_46_closed, unit_3_12_47_closed, unit_3_12_48_closed, unit_3_12_49_closed, unit_3_12_50_closed, unit_3_12_51_closed, unit_3_12_52_closed, unit_3_12_53_closed, unit_3_12_54_closed, unit_3_12_55_closed, unit_3_12_57_closed, unit_3_12_58_closed, unit_3_12_59_closed, unit_3_12_60_closed, unit_3_12_61_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit8. -/
theorem certificate_BlockUnit8 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 63 List.nil.{0}))))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 69 List.nil.{0}))))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 70 List.nil.{0}))))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 71 List.nil.{0}))))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 72 List.nil.{0}))))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 73 List.nil.{0}))))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 75 List.nil.{0}))))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 78 List.nil.{0}))))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 80 List.nil.{0}))))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 12 (List.cons.{0} 81 List.nil.{0}))))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 19 List.nil.{0}))))) 20) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 20 List.nil.{0}))))) 21) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 21 List.nil.{0}))))) 22) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 27 List.nil.{0}))))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 29 List.nil.{0}))))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 30 List.nil.{0}))))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 31 List.nil.{0}))))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 32 List.nil.{0}))))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 33 List.nil.{0}))))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 34 List.nil.{0}))))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 37 List.nil.{0}))))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 40 List.nil.{0}))))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 41 List.nil.{0}))))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 42 List.nil.{0}))))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 43 List.nil.{0}))))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 44 List.nil.{0}))))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 45 List.nil.{0}))))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 46 List.nil.{0}))))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 47 List.nil.{0}))))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 49 List.nil.{0}))))) 50) := by
  exact ⟨unit_3_12_63_closed, unit_3_12_69_closed, unit_3_12_70_closed, unit_3_12_71_closed, unit_3_12_72_closed, unit_3_12_73_closed, unit_3_12_75_closed, unit_3_12_78_closed, unit_3_12_80_closed, unit_3_12_81_closed, unit_3_13_19_closed, unit_3_13_20_closed, unit_3_13_21_closed, unit_3_13_27_closed, unit_3_13_29_closed, unit_3_13_30_closed, unit_3_13_31_closed, unit_3_13_32_closed, unit_3_13_33_closed, unit_3_13_34_closed, unit_3_13_37_closed, unit_3_13_39_closed, unit_3_13_40_closed, unit_3_13_41_closed, unit_3_13_42_closed, unit_3_13_43_closed, unit_3_13_44_closed, unit_3_13_45_closed, unit_3_13_46_closed, unit_3_13_47_closed, unit_3_13_49_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit9. -/
theorem certificate_BlockUnit9 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 50 List.nil.{0}))))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 52 List.nil.{0}))))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 53 List.nil.{0}))))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 54 List.nil.{0}))))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 55 List.nil.{0}))))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 56 List.nil.{0}))))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 57 List.nil.{0}))))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 58 List.nil.{0}))))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 59 List.nil.{0}))))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 63 List.nil.{0}))))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 64 List.nil.{0}))))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 65 List.nil.{0}))))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 66 List.nil.{0}))))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 69 List.nil.{0}))))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 71 List.nil.{0}))))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 72 List.nil.{0}))))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 73 List.nil.{0}))))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 74 List.nil.{0}))))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 75 List.nil.{0}))))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 76 List.nil.{0}))))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 77 List.nil.{0}))))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 78 List.nil.{0}))))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 79 List.nil.{0}))))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 80 List.nil.{0}))))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 82 List.nil.{0}))))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 13 (List.cons.{0} 83 List.nil.{0}))))) 84) := by
  exact ⟨unit_3_13_50_closed, unit_3_13_51_closed, unit_3_13_52_closed, unit_3_13_53_closed, unit_3_13_54_closed, unit_3_13_55_closed, unit_3_13_56_closed, unit_3_13_57_closed, unit_3_13_58_closed, unit_3_13_59_closed, unit_3_13_60_closed, unit_3_13_61_closed, unit_3_13_63_closed, unit_3_13_64_closed, unit_3_13_65_closed, unit_3_13_66_closed, unit_3_13_69_closed, unit_3_13_71_closed, unit_3_13_72_closed, unit_3_13_73_closed, unit_3_13_74_closed, unit_3_13_75_closed, unit_3_13_76_closed, unit_3_13_77_closed, unit_3_13_78_closed, unit_3_13_79_closed, unit_3_13_80_closed, unit_3_13_82_closed, unit_3_13_83_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit11. -/
theorem certificate_BlockUnit11 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 21 List.nil.{0}))))) 22) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 22 List.nil.{0}))))) 23) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 23 List.nil.{0}))))) 24) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 24 List.nil.{0}))))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 25 List.nil.{0}))))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 31 List.nil.{0}))))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 33 List.nil.{0}))))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 34 List.nil.{0}))))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 35 List.nil.{0}))))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 36 List.nil.{0}))))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 37 List.nil.{0}))))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 38 List.nil.{0}))))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 40 List.nil.{0}))))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 43 List.nil.{0}))))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 45 List.nil.{0}))))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 47 List.nil.{0}))))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 48 List.nil.{0}))))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 49 List.nil.{0}))))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 50 List.nil.{0}))))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 52 List.nil.{0}))))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 53 List.nil.{0}))))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 54 List.nil.{0}))))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 55 List.nil.{0}))))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 57 List.nil.{0}))))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 59 List.nil.{0}))))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 63 List.nil.{0}))))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 64 List.nil.{0}))))) 65) := by
  exact ⟨unit_3_15_21_closed, unit_3_15_22_closed, unit_3_15_23_closed, unit_3_15_24_closed, unit_3_15_25_closed, unit_3_15_31_closed, unit_3_15_33_closed, unit_3_15_34_closed, unit_3_15_35_closed, unit_3_15_36_closed, unit_3_15_37_closed, unit_3_15_38_closed, unit_3_15_39_closed, unit_3_15_40_closed, unit_3_15_43_closed, unit_3_15_45_closed, unit_3_15_47_closed, unit_3_15_48_closed, unit_3_15_49_closed, unit_3_15_50_closed, unit_3_15_51_closed, unit_3_15_52_closed, unit_3_15_53_closed, unit_3_15_54_closed, unit_3_15_55_closed, unit_3_15_57_closed, unit_3_15_59_closed, unit_3_15_60_closed, unit_3_15_61_closed, unit_3_15_63_closed, unit_3_15_64_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit12. -/
theorem certificate_BlockUnit12 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 65 List.nil.{0}))))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 66 List.nil.{0}))))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 67 List.nil.{0}))))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 70 List.nil.{0}))))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 71 List.nil.{0}))))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 74 List.nil.{0}))))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 75 List.nil.{0}))))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 76 List.nil.{0}))))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 77 List.nil.{0}))))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 79 List.nil.{0}))))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 81 List.nil.{0}))))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 82 List.nil.{0}))))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 83 List.nil.{0}))))) 84) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 87 List.nil.{0}))))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 15 (List.cons.{0} 91 List.nil.{0}))))) 92) := by
  exact ⟨unit_3_15_65_closed, unit_3_15_66_closed, unit_3_15_67_closed, unit_3_15_70_closed, unit_3_15_71_closed, unit_3_15_74_closed, unit_3_15_75_closed, unit_3_15_76_closed, unit_3_15_77_closed, unit_3_15_79_closed, unit_3_15_81_closed, unit_3_15_82_closed, unit_3_15_83_closed, unit_3_15_87_closed, unit_3_15_91_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit13. -/
theorem certificate_BlockUnit13 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 16 List.nil.{0})))) 17) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 23 List.nil.{0}))))) 24) := by
  exact ⟨unit_3_16_closed, unit_3_17_23_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit14. -/
theorem certificate_BlockUnit14 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 24 List.nil.{0}))))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 25 List.nil.{0}))))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 26 List.nil.{0}))))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 27 List.nil.{0}))))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 28 List.nil.{0}))))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 29 List.nil.{0}))))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 35 List.nil.{0}))))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 37 List.nil.{0}))))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 38 List.nil.{0}))))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 40 List.nil.{0}))))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 41 List.nil.{0}))))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 42 List.nil.{0}))))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 43 List.nil.{0}))))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 44 List.nil.{0}))))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 45 List.nil.{0}))))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 49 List.nil.{0}))))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 52 List.nil.{0}))))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 53 List.nil.{0}))))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 54 List.nil.{0}))))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 55 List.nil.{0}))))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 57 List.nil.{0}))))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 59 List.nil.{0}))))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 63 List.nil.{0}))))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 65 List.nil.{0}))))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 66 List.nil.{0}))))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 67 List.nil.{0}))))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 68 List.nil.{0}))))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 71 List.nil.{0}))))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 75 List.nil.{0}))))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 76 List.nil.{0}))))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 77 List.nil.{0}))))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 78 List.nil.{0}))))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 81 List.nil.{0}))))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 83 List.nil.{0}))))) 84) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 85 List.nil.{0}))))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 88 List.nil.{0}))))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 17 (List.cons.{0} 91 List.nil.{0}))))) 92) := by
  exact ⟨unit_3_17_24_closed, unit_3_17_25_closed, unit_3_17_26_closed, unit_3_17_27_closed, unit_3_17_28_closed, unit_3_17_29_closed, unit_3_17_35_closed, unit_3_17_37_closed, unit_3_17_38_closed, unit_3_17_39_closed, unit_3_17_40_closed, unit_3_17_41_closed, unit_3_17_42_closed, unit_3_17_43_closed, unit_3_17_44_closed, unit_3_17_45_closed, unit_3_17_49_closed, unit_3_17_51_closed, unit_3_17_52_closed, unit_3_17_53_closed, unit_3_17_54_closed, unit_3_17_55_closed, unit_3_17_57_closed, unit_3_17_59_closed, unit_3_17_60_closed, unit_3_17_61_closed, unit_3_17_63_closed, unit_3_17_65_closed, unit_3_17_66_closed, unit_3_17_67_closed, unit_3_17_68_closed, unit_3_17_71_closed, unit_3_17_75_closed, unit_3_17_76_closed, unit_3_17_77_closed, unit_3_17_78_closed, unit_3_17_81_closed, unit_3_17_83_closed, unit_3_17_85_closed, unit_3_17_88_closed, unit_3_17_91_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit15. -/
theorem certificate_BlockUnit15 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 18 List.nil.{0})))) 19) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 25 List.nil.{0}))))) 26) := by
  exact ⟨unit_3_18_closed, unit_3_19_25_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit16. -/
theorem certificate_BlockUnit16 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 26 List.nil.{0}))))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 27 List.nil.{0}))))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 28 List.nil.{0}))))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 29 List.nil.{0}))))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 30 List.nil.{0}))))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 31 List.nil.{0}))))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 32 List.nil.{0}))))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 33 List.nil.{0}))))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 41 List.nil.{0}))))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 42 List.nil.{0}))))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 43 List.nil.{0}))))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 44 List.nil.{0}))))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 45 List.nil.{0}))))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 46 List.nil.{0}))))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 47 List.nil.{0}))))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 48 List.nil.{0}))))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 49 List.nil.{0}))))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 50 List.nil.{0}))))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 52 List.nil.{0}))))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 55 List.nil.{0}))))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 57 List.nil.{0}))))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 59 List.nil.{0}))))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 63 List.nil.{0}))))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 64 List.nil.{0}))))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 66 List.nil.{0}))))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 67 List.nil.{0}))))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 69 List.nil.{0}))))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 75 List.nil.{0}))))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 77 List.nil.{0}))))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 78 List.nil.{0}))))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 79 List.nil.{0}))))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 80 List.nil.{0}))))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 81 List.nil.{0}))))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 82 List.nil.{0}))))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 83 List.nil.{0}))))) 84) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 19 (List.cons.{0} 87 List.nil.{0}))))) 88) := by
  exact ⟨unit_3_19_26_closed, unit_3_19_27_closed, unit_3_19_28_closed, unit_3_19_29_closed, unit_3_19_30_closed, unit_3_19_31_closed, unit_3_19_32_closed, unit_3_19_33_closed, unit_3_19_39_closed, unit_3_19_41_closed, unit_3_19_42_closed, unit_3_19_43_closed, unit_3_19_44_closed, unit_3_19_45_closed, unit_3_19_46_closed, unit_3_19_47_closed, unit_3_19_48_closed, unit_3_19_49_closed, unit_3_19_50_closed, unit_3_19_51_closed, unit_3_19_52_closed, unit_3_19_55_closed, unit_3_19_57_closed, unit_3_19_59_closed, unit_3_19_60_closed, unit_3_19_61_closed, unit_3_19_63_closed, unit_3_19_64_closed, unit_3_19_66_closed, unit_3_19_67_closed, unit_3_19_69_closed, unit_3_19_75_closed, unit_3_19_77_closed, unit_3_19_78_closed, unit_3_19_79_closed, unit_3_19_80_closed, unit_3_19_81_closed, unit_3_19_82_closed, unit_3_19_83_closed, unit_3_19_87_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit35. -/
theorem certificate_BlockUnit35 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 38 List.nil.{0})))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 39 List.nil.{0})))) 40) := by
  exact ⟨unit_3_38_closed, unit_3_39_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit39. -/
theorem certificate_BlockUnit39 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 43 List.nil.{0})))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 44 List.nil.{0})))) 45) := by
  exact ⟨unit_3_43_closed, unit_3_44_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit40. -/
theorem certificate_BlockUnit40 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 45 List.nil.{0})))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 47 List.nil.{0})))) 48) := by
  exact ⟨unit_3_45_closed, unit_3_46_closed, unit_3_47_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit41. -/
theorem certificate_BlockUnit41 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 49 List.nil.{0})))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 50 List.nil.{0})))) 51) := by
  exact ⟨unit_3_48_closed, unit_3_49_closed, unit_3_50_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit42. -/
theorem certificate_BlockUnit42 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 51 List.nil.{0})))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 53 List.nil.{0})))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 54 List.nil.{0})))) 55) := by
  exact ⟨unit_3_51_closed, unit_3_52_closed, unit_3_53_closed, unit_3_54_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit43. -/
theorem certificate_BlockUnit43 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 55 List.nil.{0})))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 59 List.nil.{0})))) 60) := by
  exact ⟨unit_3_55_closed, unit_3_56_closed, unit_3_57_closed, unit_3_58_closed, unit_3_59_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit44. -/
theorem certificate_BlockUnit44 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 61 List.nil.{0})))) 62) := by
  exact ⟨unit_3_60_closed, unit_3_61_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit45. -/
theorem certificate_BlockUnit45 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 63 List.nil.{0})))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 65 List.nil.{0})))) 66) := by
  exact ⟨unit_3_63_closed, unit_3_64_closed, unit_3_65_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit46. -/
theorem certificate_BlockUnit46 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 67 List.nil.{0})))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 69 List.nil.{0})))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 71 List.nil.{0})))) 72) := by
  exact ⟨unit_3_66_closed, unit_3_67_closed, unit_3_68_closed, unit_3_69_closed, unit_3_70_closed, unit_3_71_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit47. -/
theorem certificate_BlockUnit47 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 73 List.nil.{0})))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 75 List.nil.{0})))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 77 List.nil.{0})))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 79 List.nil.{0})))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 80 List.nil.{0})))) 81) := by
  exact ⟨unit_3_72_closed, unit_3_73_closed, unit_3_74_closed, unit_3_75_closed, unit_3_76_closed, unit_3_77_closed, unit_3_78_closed, unit_3_79_closed, unit_3_80_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit48. -/
theorem certificate_BlockUnit48 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 83 List.nil.{0})))) 84) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 84 List.nil.{0})))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 85 List.nil.{0})))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 89 List.nil.{0})))) 90) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 91 List.nil.{0})))) 92) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 92 List.nil.{0})))) 93) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 93 List.nil.{0})))) 94) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 94 List.nil.{0})))) 95) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 95 List.nil.{0})))) 96) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 96 List.nil.{0})))) 97) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 97 List.nil.{0})))) 98) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 98 List.nil.{0})))) 99) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 3 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 3 (List.cons.{0} 99 List.nil.{0})))) 100) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 16 List.nil.{0}))))) 17) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 18 List.nil.{0}))))) 19) := by
  exact ⟨unit_3_81_closed, unit_3_82_closed, unit_3_83_closed, unit_3_84_closed, unit_3_85_closed, unit_3_86_closed, unit_3_87_closed, unit_3_88_closed, unit_3_89_closed, unit_3_90_closed, unit_3_91_closed, unit_3_92_closed, unit_3_93_closed, unit_3_94_closed, unit_3_95_closed, unit_3_96_closed, unit_3_97_closed, unit_3_98_closed, unit_3_99_closed, unit_4_6_16_closed, unit_4_6_18_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit49. -/
theorem certificate_BlockUnit49 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 20 List.nil.{0}))))) 21) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 21 List.nil.{0}))))) 22) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 22 List.nil.{0}))))) 23) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 23 List.nil.{0}))))) 24) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 24 List.nil.{0}))))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 25 List.nil.{0}))))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 26 List.nil.{0}))))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 27 List.nil.{0}))))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 28 List.nil.{0}))))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 29 List.nil.{0}))))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 30 List.nil.{0}))))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 31 List.nil.{0}))))) 32) := by
  exact ⟨unit_4_6_20_closed, unit_4_6_21_closed, unit_4_6_22_closed, unit_4_6_23_closed, unit_4_6_24_closed, unit_4_6_25_closed, unit_4_6_26_closed, unit_4_6_27_closed, unit_4_6_28_closed, unit_4_6_29_closed, unit_4_6_30_closed, unit_4_6_31_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit50. -/
theorem certificate_BlockUnit50 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 32 List.nil.{0}))))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 33 List.nil.{0}))))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 34 List.nil.{0}))))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 35 List.nil.{0}))))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 36 List.nil.{0}))))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 37 List.nil.{0}))))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 38 List.nil.{0}))))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 40 List.nil.{0}))))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 41 List.nil.{0}))))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 43 List.nil.{0}))))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 44 List.nil.{0}))))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 45 List.nil.{0}))))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 46 List.nil.{0}))))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 47 List.nil.{0}))))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 48 List.nil.{0}))))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 49 List.nil.{0}))))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 50 List.nil.{0}))))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 52 List.nil.{0}))))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 53 List.nil.{0}))))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 54 List.nil.{0}))))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 55 List.nil.{0}))))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 56 List.nil.{0}))))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 57 List.nil.{0}))))) 58) := by
  exact ⟨unit_4_6_32_closed, unit_4_6_33_closed, unit_4_6_34_closed, unit_4_6_35_closed, unit_4_6_36_closed, unit_4_6_37_closed, unit_4_6_38_closed, unit_4_6_39_closed, unit_4_6_40_closed, unit_4_6_41_closed, unit_4_6_43_closed, unit_4_6_44_closed, unit_4_6_45_closed, unit_4_6_46_closed, unit_4_6_47_closed, unit_4_6_48_closed, unit_4_6_49_closed, unit_4_6_50_closed, unit_4_6_51_closed, unit_4_6_52_closed, unit_4_6_53_closed, unit_4_6_54_closed, unit_4_6_55_closed, unit_4_6_56_closed, unit_4_6_57_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit51. -/
theorem certificate_BlockUnit51 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 58 List.nil.{0}))))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 59 List.nil.{0}))))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 64 List.nil.{0}))))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 66 List.nil.{0}))))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 68 List.nil.{0}))))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 69 List.nil.{0}))))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 70 List.nil.{0}))))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 71 List.nil.{0}))))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 72 List.nil.{0}))))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 73 List.nil.{0}))))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 74 List.nil.{0}))))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 75 List.nil.{0}))))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 76 List.nil.{0}))))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 77 List.nil.{0}))))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 78 List.nil.{0}))))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 79 List.nil.{0}))))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 80 List.nil.{0}))))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 81 List.nil.{0}))))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 82 List.nil.{0}))))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 84 List.nil.{0}))))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 6 (List.cons.{0} 86 List.nil.{0}))))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 19 List.nil.{0}))))) 20) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 20 List.nil.{0}))))) 21) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 24 List.nil.{0}))))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 25 List.nil.{0}))))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 27 List.nil.{0}))))) 28) := by
  exact ⟨unit_4_6_58_closed, unit_4_6_59_closed, unit_4_6_60_closed, unit_4_6_61_closed, unit_4_6_64_closed, unit_4_6_66_closed, unit_4_6_68_closed, unit_4_6_69_closed, unit_4_6_70_closed, unit_4_6_71_closed, unit_4_6_72_closed, unit_4_6_73_closed, unit_4_6_74_closed, unit_4_6_75_closed, unit_4_6_76_closed, unit_4_6_77_closed, unit_4_6_78_closed, unit_4_6_79_closed, unit_4_6_80_closed, unit_4_6_81_closed, unit_4_6_82_closed, unit_4_6_84_closed, unit_4_6_86_closed, unit_4_9_19_closed, unit_4_9_20_closed, unit_4_9_24_closed, unit_4_9_25_closed, unit_4_9_27_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit52. -/
theorem certificate_BlockUnit52 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 28 List.nil.{0}))))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 29 List.nil.{0}))))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 30 List.nil.{0}))))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 32 List.nil.{0}))))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 33 List.nil.{0}))))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 34 List.nil.{0}))))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 35 List.nil.{0}))))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 36 List.nil.{0}))))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 37 List.nil.{0}))))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 38 List.nil.{0}))))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 40 List.nil.{0}))))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 41 List.nil.{0}))))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 44 List.nil.{0}))))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 45 List.nil.{0}))))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 47 List.nil.{0}))))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 48 List.nil.{0}))))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 49 List.nil.{0}))))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 50 List.nil.{0}))))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 52 List.nil.{0}))))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 53 List.nil.{0}))))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 54 List.nil.{0}))))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 56 List.nil.{0}))))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 57 List.nil.{0}))))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 59 List.nil.{0}))))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 64 List.nil.{0}))))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 68 List.nil.{0}))))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 69 List.nil.{0}))))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 70 List.nil.{0}))))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 71 List.nil.{0}))))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 72 List.nil.{0}))))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 73 List.nil.{0}))))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 74 List.nil.{0}))))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 75 List.nil.{0}))))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 76 List.nil.{0}))))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 77 List.nil.{0}))))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 78 List.nil.{0}))))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 79 List.nil.{0}))))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 80 List.nil.{0}))))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 81 List.nil.{0}))))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 9 (List.cons.{0} 82 List.nil.{0}))))) 83) := by
  exact ⟨unit_4_9_28_closed, unit_4_9_29_closed, unit_4_9_30_closed, unit_4_9_32_closed, unit_4_9_33_closed, unit_4_9_34_closed, unit_4_9_35_closed, unit_4_9_36_closed, unit_4_9_37_closed, unit_4_9_38_closed, unit_4_9_39_closed, unit_4_9_40_closed, unit_4_9_41_closed, unit_4_9_44_closed, unit_4_9_45_closed, unit_4_9_47_closed, unit_4_9_48_closed, unit_4_9_49_closed, unit_4_9_50_closed, unit_4_9_51_closed, unit_4_9_52_closed, unit_4_9_53_closed, unit_4_9_54_closed, unit_4_9_56_closed, unit_4_9_57_closed, unit_4_9_59_closed, unit_4_9_60_closed, unit_4_9_61_closed, unit_4_9_64_closed, unit_4_9_68_closed, unit_4_9_69_closed, unit_4_9_70_closed, unit_4_9_71_closed, unit_4_9_72_closed, unit_4_9_73_closed, unit_4_9_74_closed, unit_4_9_75_closed, unit_4_9_76_closed, unit_4_9_77_closed, unit_4_9_78_closed, unit_4_9_79_closed, unit_4_9_80_closed, unit_4_9_81_closed, unit_4_9_82_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit53. -/
theorem certificate_BlockUnit53 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 18 List.nil.{0}))))) 19) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 21 List.nil.{0}))))) 22) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 22 List.nil.{0}))))) 23) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 24 List.nil.{0}))))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 27 List.nil.{0}))))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 28 List.nil.{0}))))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 30 List.nil.{0}))))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 31 List.nil.{0}))))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 32 List.nil.{0}))))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 33 List.nil.{0}))))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 34 List.nil.{0}))))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 36 List.nil.{0}))))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 37 List.nil.{0}))))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 38 List.nil.{0}))))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 40 List.nil.{0}))))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 41 List.nil.{0}))))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 43 List.nil.{0}))))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 46 List.nil.{0}))))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 48 List.nil.{0}))))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 49 List.nil.{0}))))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 50 List.nil.{0}))))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 52 List.nil.{0}))))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 53 List.nil.{0}))))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 54 List.nil.{0}))))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 56 List.nil.{0}))))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 58 List.nil.{0}))))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 59 List.nil.{0}))))) 60) := by
  exact ⟨unit_4_10_18_closed, unit_4_10_21_closed, unit_4_10_22_closed, unit_4_10_24_closed, unit_4_10_27_closed, unit_4_10_28_closed, unit_4_10_30_closed, unit_4_10_31_closed, unit_4_10_32_closed, unit_4_10_33_closed, unit_4_10_34_closed, unit_4_10_36_closed, unit_4_10_37_closed, unit_4_10_38_closed, unit_4_10_39_closed, unit_4_10_40_closed, unit_4_10_41_closed, unit_4_10_43_closed, unit_4_10_46_closed, unit_4_10_48_closed, unit_4_10_49_closed, unit_4_10_50_closed, unit_4_10_51_closed, unit_4_10_52_closed, unit_4_10_53_closed, unit_4_10_54_closed, unit_4_10_56_closed, unit_4_10_58_closed, unit_4_10_59_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit54. -/
theorem certificate_BlockUnit54 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 63 List.nil.{0}))))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 64 List.nil.{0}))))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 66 List.nil.{0}))))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 68 List.nil.{0}))))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 69 List.nil.{0}))))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 70 List.nil.{0}))))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 71 List.nil.{0}))))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 72 List.nil.{0}))))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 73 List.nil.{0}))))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 74 List.nil.{0}))))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 76 List.nil.{0}))))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 77 List.nil.{0}))))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 80 List.nil.{0}))))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 10 (List.cons.{0} 82 List.nil.{0}))))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 18 List.nil.{0}))))) 19) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 22 List.nil.{0}))))) 23) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 25 List.nil.{0}))))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 26 List.nil.{0}))))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 28 List.nil.{0}))))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 29 List.nil.{0}))))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 30 List.nil.{0}))))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 33 List.nil.{0}))))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 36 List.nil.{0}))))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 37 List.nil.{0}))))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 38 List.nil.{0}))))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 40 List.nil.{0}))))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 41 List.nil.{0}))))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 44 List.nil.{0}))))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 45 List.nil.{0}))))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 46 List.nil.{0}))))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 47 List.nil.{0}))))) 48) := by
  exact ⟨unit_4_10_60_closed, unit_4_10_61_closed, unit_4_10_63_closed, unit_4_10_64_closed, unit_4_10_66_closed, unit_4_10_68_closed, unit_4_10_69_closed, unit_4_10_70_closed, unit_4_10_71_closed, unit_4_10_72_closed, unit_4_10_73_closed, unit_4_10_74_closed, unit_4_10_76_closed, unit_4_10_77_closed, unit_4_10_80_closed, unit_4_10_82_closed, unit_4_12_18_closed, unit_4_12_22_closed, unit_4_12_25_closed, unit_4_12_26_closed, unit_4_12_28_closed, unit_4_12_29_closed, unit_4_12_30_closed, unit_4_12_33_closed, unit_4_12_36_closed, unit_4_12_37_closed, unit_4_12_38_closed, unit_4_12_39_closed, unit_4_12_40_closed, unit_4_12_41_closed, unit_4_12_44_closed, unit_4_12_45_closed, unit_4_12_46_closed, unit_4_12_47_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit55. -/
theorem certificate_BlockUnit55 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 48 List.nil.{0}))))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 49 List.nil.{0}))))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 50 List.nil.{0}))))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 52 List.nil.{0}))))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 53 List.nil.{0}))))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 54 List.nil.{0}))))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 55 List.nil.{0}))))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 56 List.nil.{0}))))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 57 List.nil.{0}))))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 58 List.nil.{0}))))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 59 List.nil.{0}))))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 63 List.nil.{0}))))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 64 List.nil.{0}))))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 65 List.nil.{0}))))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 67 List.nil.{0}))))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 70 List.nil.{0}))))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 71 List.nil.{0}))))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 72 List.nil.{0}))))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 74 List.nil.{0}))))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 76 List.nil.{0}))))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 78 List.nil.{0}))))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 80 List.nil.{0}))))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 81 List.nil.{0}))))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 12 (List.cons.{0} 82 List.nil.{0}))))) 83) := by
  exact ⟨unit_4_12_48_closed, unit_4_12_49_closed, unit_4_12_50_closed, unit_4_12_51_closed, unit_4_12_52_closed, unit_4_12_53_closed, unit_4_12_54_closed, unit_4_12_55_closed, unit_4_12_56_closed, unit_4_12_57_closed, unit_4_12_58_closed, unit_4_12_59_closed, unit_4_12_60_closed, unit_4_12_61_closed, unit_4_12_63_closed, unit_4_12_64_closed, unit_4_12_65_closed, unit_4_12_67_closed, unit_4_12_70_closed, unit_4_12_71_closed, unit_4_12_72_closed, unit_4_12_74_closed, unit_4_12_76_closed, unit_4_12_78_closed, unit_4_12_80_closed, unit_4_12_81_closed, unit_4_12_82_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit58. -/
theorem certificate_BlockUnit58 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 15 List.nil.{0})))) 16) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 22 List.nil.{0}))))) 23) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 24 List.nil.{0}))))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 25 List.nil.{0}))))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 26 List.nil.{0}))))) 27) := by
  exact ⟨unit_4_15_closed, unit_4_16_22_closed, unit_4_16_24_closed, unit_4_16_25_closed, unit_4_16_26_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit59. -/
theorem certificate_BlockUnit59 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 30 List.nil.{0}))))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 33 List.nil.{0}))))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 34 List.nil.{0}))))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 36 List.nil.{0}))))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 37 List.nil.{0}))))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 38 List.nil.{0}))))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 40 List.nil.{0}))))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 41 List.nil.{0}))))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 45 List.nil.{0}))))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 46 List.nil.{0}))))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 48 List.nil.{0}))))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 49 List.nil.{0}))))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 50 List.nil.{0}))))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 52 List.nil.{0}))))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 53 List.nil.{0}))))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 54 List.nil.{0}))))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 55 List.nil.{0}))))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 56 List.nil.{0}))))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 58 List.nil.{0}))))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 63 List.nil.{0}))))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 64 List.nil.{0}))))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 65 List.nil.{0}))))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 66 List.nil.{0}))))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 67 List.nil.{0}))))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 69 List.nil.{0}))))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 72 List.nil.{0}))))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 73 List.nil.{0}))))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 74 List.nil.{0}))))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 76 List.nil.{0}))))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 78 List.nil.{0}))))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 80 List.nil.{0}))))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 81 List.nil.{0}))))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 82 List.nil.{0}))))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 84 List.nil.{0}))))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 16 (List.cons.{0} 86 List.nil.{0}))))) 87) := by
  exact ⟨unit_4_16_30_closed, unit_4_16_33_closed, unit_4_16_34_closed, unit_4_16_36_closed, unit_4_16_37_closed, unit_4_16_38_closed, unit_4_16_39_closed, unit_4_16_40_closed, unit_4_16_41_closed, unit_4_16_45_closed, unit_4_16_46_closed, unit_4_16_48_closed, unit_4_16_49_closed, unit_4_16_50_closed, unit_4_16_51_closed, unit_4_16_52_closed, unit_4_16_53_closed, unit_4_16_54_closed, unit_4_16_55_closed, unit_4_16_56_closed, unit_4_16_58_closed, unit_4_16_60_closed, unit_4_16_61_closed, unit_4_16_63_closed, unit_4_16_64_closed, unit_4_16_65_closed, unit_4_16_66_closed, unit_4_16_67_closed, unit_4_16_69_closed, unit_4_16_72_closed, unit_4_16_73_closed, unit_4_16_74_closed, unit_4_16_76_closed, unit_4_16_78_closed, unit_4_16_80_closed, unit_4_16_81_closed, unit_4_16_82_closed, unit_4_16_84_closed, unit_4_16_86_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit65. -/
theorem certificate_BlockUnit65 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 22 List.nil.{0})))) 23) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 23 List.nil.{0})))) 24) := by
  exact ⟨unit_4_22_closed, unit_4_23_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit68. -/
theorem certificate_BlockUnit68 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 26 List.nil.{0})))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 27 List.nil.{0})))) 28) := by
  exact ⟨unit_4_26_closed, unit_4_27_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit70. -/
theorem certificate_BlockUnit70 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 29 List.nil.{0})))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 30 List.nil.{0})))) 31) := by
  exact ⟨unit_4_29_closed, unit_4_30_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit71. -/
theorem certificate_BlockUnit71 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 31 List.nil.{0})))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 32 List.nil.{0})))) 33) := by
  exact ⟨unit_4_31_closed, unit_4_32_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit72. -/
theorem certificate_BlockUnit72 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 33 List.nil.{0})))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 34 List.nil.{0})))) 35) := by
  exact ⟨unit_4_33_closed, unit_4_34_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit73. -/
theorem certificate_BlockUnit73 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 36 List.nil.{0})))) 37) := by
  exact ⟨unit_4_35_closed, unit_4_36_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit74. -/
theorem certificate_BlockUnit74 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 37 List.nil.{0})))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 38 List.nil.{0})))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 39 List.nil.{0})))) 40) := by
  exact ⟨unit_4_37_closed, unit_4_38_closed, unit_4_39_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit75. -/
theorem certificate_BlockUnit75 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 41 List.nil.{0})))) 42) := by
  exact ⟨unit_4_40_closed, unit_4_41_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit76. -/
theorem certificate_BlockUnit76 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 43 List.nil.{0})))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 45 List.nil.{0})))) 46) := by
  exact ⟨unit_4_43_closed, unit_4_44_closed, unit_4_45_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit77. -/
theorem certificate_BlockUnit77 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 47 List.nil.{0})))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 49 List.nil.{0})))) 50) := by
  exact ⟨unit_4_46_closed, unit_4_47_closed, unit_4_48_closed, unit_4_49_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit78. -/
theorem certificate_BlockUnit78 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 51 List.nil.{0})))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 53 List.nil.{0})))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 55 List.nil.{0})))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 56 List.nil.{0})))) 57) := by
  exact ⟨unit_4_50_closed, unit_4_51_closed, unit_4_52_closed, unit_4_53_closed, unit_4_54_closed, unit_4_55_closed, unit_4_56_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit79. -/
theorem certificate_BlockUnit79 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 59 List.nil.{0})))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 60 List.nil.{0})))) 61) := by
  exact ⟨unit_4_57_closed, unit_4_58_closed, unit_4_59_closed, unit_4_60_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit80. -/
theorem certificate_BlockUnit80 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 63 List.nil.{0})))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 65 List.nil.{0})))) 66) := by
  exact ⟨unit_4_61_closed, unit_4_63_closed, unit_4_64_closed, unit_4_65_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit81. -/
theorem certificate_BlockUnit81 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 67 List.nil.{0})))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 69 List.nil.{0})))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 71 List.nil.{0})))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 73 List.nil.{0})))) 74) := by
  exact ⟨unit_4_66_closed, unit_4_67_closed, unit_4_68_closed, unit_4_69_closed, unit_4_70_closed, unit_4_71_closed, unit_4_72_closed, unit_4_73_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit82. -/
theorem certificate_BlockUnit82 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 75 List.nil.{0})))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 77 List.nil.{0})))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 79 List.nil.{0})))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 84 List.nil.{0})))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 85 List.nil.{0})))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 89 List.nil.{0})))) 90) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 91 List.nil.{0})))) 92) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 92 List.nil.{0})))) 93) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 93 List.nil.{0})))) 94) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 94 List.nil.{0})))) 95) := by
  exact ⟨unit_4_74_closed, unit_4_75_closed, unit_4_76_closed, unit_4_77_closed, unit_4_78_closed, unit_4_79_closed, unit_4_80_closed, unit_4_81_closed, unit_4_82_closed, unit_4_84_closed, unit_4_85_closed, unit_4_86_closed, unit_4_87_closed, unit_4_88_closed, unit_4_89_closed, unit_4_90_closed, unit_4_91_closed, unit_4_92_closed, unit_4_93_closed, unit_4_94_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit83. -/
theorem certificate_BlockUnit83 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 95 List.nil.{0})))) 96) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 96 List.nil.{0})))) 97) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 97 List.nil.{0})))) 98) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 4 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 4 (List.cons.{0} 98 List.nil.{0})))) 99) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 17 List.nil.{0}))))) 18) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 19 List.nil.{0}))))) 20) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 23 List.nil.{0}))))) 24) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 24 List.nil.{0}))))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 25 List.nil.{0}))))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 26 List.nil.{0}))))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 27 List.nil.{0}))))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 29 List.nil.{0}))))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 30 List.nil.{0}))))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 31 List.nil.{0}))))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 33 List.nil.{0}))))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 35 List.nil.{0}))))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 36 List.nil.{0}))))) 37) := by
  exact ⟨unit_4_95_closed, unit_4_96_closed, unit_4_97_closed, unit_4_98_closed, unit_5_7_17_closed, unit_5_7_19_closed, unit_5_7_23_closed, unit_5_7_24_closed, unit_5_7_25_closed, unit_5_7_26_closed, unit_5_7_27_closed, unit_5_7_29_closed, unit_5_7_30_closed, unit_5_7_31_closed, unit_5_7_33_closed, unit_5_7_35_closed, unit_5_7_36_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit84. -/
theorem certificate_BlockUnit84 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 37 List.nil.{0}))))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 38 List.nil.{0}))))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 40 List.nil.{0}))))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 41 List.nil.{0}))))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 43 List.nil.{0}))))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 45 List.nil.{0}))))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 46 List.nil.{0}))))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 47 List.nil.{0}))))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 48 List.nil.{0}))))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 49 List.nil.{0}))))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 50 List.nil.{0}))))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 52 List.nil.{0}))))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 53 List.nil.{0}))))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 54 List.nil.{0}))))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 55 List.nil.{0}))))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 56 List.nil.{0}))))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 57 List.nil.{0}))))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 58 List.nil.{0}))))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 59 List.nil.{0}))))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 65 List.nil.{0}))))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 67 List.nil.{0}))))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 69 List.nil.{0}))))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 70 List.nil.{0}))))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 71 List.nil.{0}))))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 73 List.nil.{0}))))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 75 List.nil.{0}))))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 76 List.nil.{0}))))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 77 List.nil.{0}))))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 79 List.nil.{0}))))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 81 List.nil.{0}))))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 7 (List.cons.{0} 83 List.nil.{0}))))) 84) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 21 List.nil.{0}))))) 22) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 24 List.nil.{0}))))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 25 List.nil.{0}))))) 26) := by
  exact ⟨unit_5_7_37_closed, unit_5_7_38_closed, unit_5_7_39_closed, unit_5_7_40_closed, unit_5_7_41_closed, unit_5_7_43_closed, unit_5_7_45_closed, unit_5_7_46_closed, unit_5_7_47_closed, unit_5_7_48_closed, unit_5_7_49_closed, unit_5_7_50_closed, unit_5_7_51_closed, unit_5_7_52_closed, unit_5_7_53_closed, unit_5_7_54_closed, unit_5_7_55_closed, unit_5_7_56_closed, unit_5_7_57_closed, unit_5_7_58_closed, unit_5_7_59_closed, unit_5_7_60_closed, unit_5_7_61_closed, unit_5_7_65_closed, unit_5_7_67_closed, unit_5_7_69_closed, unit_5_7_70_closed, unit_5_7_71_closed, unit_5_7_73_closed, unit_5_7_75_closed, unit_5_7_76_closed, unit_5_7_77_closed, unit_5_7_79_closed, unit_5_7_81_closed, unit_5_7_83_closed, unit_5_8_21_closed, unit_5_8_24_closed, unit_5_8_25_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit85. -/
theorem certificate_BlockUnit85 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 27 List.nil.{0}))))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 28 List.nil.{0}))))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 30 List.nil.{0}))))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 31 List.nil.{0}))))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 33 List.nil.{0}))))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 35 List.nil.{0}))))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 36 List.nil.{0}))))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 37 List.nil.{0}))))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 38 List.nil.{0}))))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 40 List.nil.{0}))))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 41 List.nil.{0}))))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 44 List.nil.{0}))))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 45 List.nil.{0}))))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 47 List.nil.{0}))))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 48 List.nil.{0}))))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 50 List.nil.{0}))))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 52 List.nil.{0}))))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 53 List.nil.{0}))))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 54 List.nil.{0}))))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 55 List.nil.{0}))))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 56 List.nil.{0}))))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 65 List.nil.{0}))))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 68 List.nil.{0}))))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 69 List.nil.{0}))))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 70 List.nil.{0}))))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 72 List.nil.{0}))))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 73 List.nil.{0}))))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 75 List.nil.{0}))))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 77 List.nil.{0}))))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 8 (List.cons.{0} 80 List.nil.{0}))))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 13 List.nil.{0}))))) 14) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 19 List.nil.{0}))))) 20) := by
  exact ⟨unit_5_8_27_closed, unit_5_8_28_closed, unit_5_8_30_closed, unit_5_8_31_closed, unit_5_8_33_closed, unit_5_8_35_closed, unit_5_8_36_closed, unit_5_8_37_closed, unit_5_8_38_closed, unit_5_8_39_closed, unit_5_8_40_closed, unit_5_8_41_closed, unit_5_8_44_closed, unit_5_8_45_closed, unit_5_8_47_closed, unit_5_8_48_closed, unit_5_8_50_closed, unit_5_8_51_closed, unit_5_8_52_closed, unit_5_8_53_closed, unit_5_8_54_closed, unit_5_8_55_closed, unit_5_8_56_closed, unit_5_8_60_closed, unit_5_8_61_closed, unit_5_8_65_closed, unit_5_8_68_closed, unit_5_8_69_closed, unit_5_8_70_closed, unit_5_8_72_closed, unit_5_8_73_closed, unit_5_8_75_closed, unit_5_8_77_closed, unit_5_8_80_closed, unit_5_11_13_closed, unit_5_11_19_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit86. -/
theorem certificate_BlockUnit86 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 23 List.nil.{0}))))) 24) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 24 List.nil.{0}))))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 25 List.nil.{0}))))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 29 List.nil.{0}))))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 30 List.nil.{0}))))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 31 List.nil.{0}))))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 35 List.nil.{0}))))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 36 List.nil.{0}))))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 37 List.nil.{0}))))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 40 List.nil.{0}))))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 41 List.nil.{0}))))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 43 List.nil.{0}))))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 45 List.nil.{0}))))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 46 List.nil.{0}))))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 47 List.nil.{0}))))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 48 List.nil.{0}))))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 49 List.nil.{0}))))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 50 List.nil.{0}))))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 52 List.nil.{0}))))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 53 List.nil.{0}))))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 54 List.nil.{0}))))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 55 List.nil.{0}))))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 57 List.nil.{0}))))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 59 List.nil.{0}))))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 65 List.nil.{0}))))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 67 List.nil.{0}))))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 69 List.nil.{0}))))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 71 List.nil.{0}))))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 72 List.nil.{0}))))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 73 List.nil.{0}))))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 75 List.nil.{0}))))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 77 List.nil.{0}))))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 78 List.nil.{0}))))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 11 (List.cons.{0} 81 List.nil.{0}))))) 82) := by
  exact ⟨unit_5_11_23_closed, unit_5_11_24_closed, unit_5_11_25_closed, unit_5_11_29_closed, unit_5_11_30_closed, unit_5_11_31_closed, unit_5_11_35_closed, unit_5_11_36_closed, unit_5_11_37_closed, unit_5_11_39_closed, unit_5_11_40_closed, unit_5_11_41_closed, unit_5_11_43_closed, unit_5_11_45_closed, unit_5_11_46_closed, unit_5_11_47_closed, unit_5_11_48_closed, unit_5_11_49_closed, unit_5_11_50_closed, unit_5_11_51_closed, unit_5_11_52_closed, unit_5_11_53_closed, unit_5_11_54_closed, unit_5_11_55_closed, unit_5_11_57_closed, unit_5_11_59_closed, unit_5_11_60_closed, unit_5_11_61_closed, unit_5_11_65_closed, unit_5_11_67_closed, unit_5_11_69_closed, unit_5_11_71_closed, unit_5_11_72_closed, unit_5_11_73_closed, unit_5_11_75_closed, unit_5_11_77_closed, unit_5_11_78_closed, unit_5_11_81_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit87. -/
theorem certificate_BlockUnit87 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 12 List.nil.{0})))) 13) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 15 List.nil.{0}))))) 16) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 23 List.nil.{0}))))) 24) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 24 List.nil.{0}))))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 27 List.nil.{0}))))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 28 List.nil.{0}))))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 29 List.nil.{0}))))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 31 List.nil.{0}))))) 32) := by
  exact ⟨unit_5_12_closed, unit_5_13_15_closed, unit_5_13_23_closed, unit_5_13_24_closed, unit_5_13_27_closed, unit_5_13_28_closed, unit_5_13_29_closed, unit_5_13_31_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit88. -/
theorem certificate_BlockUnit88 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 35 List.nil.{0}))))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 36 List.nil.{0}))))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 37 List.nil.{0}))))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 40 List.nil.{0}))))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 41 List.nil.{0}))))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 43 List.nil.{0}))))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 44 List.nil.{0}))))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 45 List.nil.{0}))))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 47 List.nil.{0}))))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 48 List.nil.{0}))))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 49 List.nil.{0}))))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 50 List.nil.{0}))))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 53 List.nil.{0}))))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 54 List.nil.{0}))))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 55 List.nil.{0}))))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 56 List.nil.{0}))))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 57 List.nil.{0}))))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 58 List.nil.{0}))))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 59 List.nil.{0}))))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 65 List.nil.{0}))))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 66 List.nil.{0}))))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 71 List.nil.{0}))))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 73 List.nil.{0}))))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 75 List.nil.{0}))))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 77 List.nil.{0}))))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 79 List.nil.{0}))))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 83 List.nil.{0}))))) 84) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 13 (List.cons.{0} 89 List.nil.{0}))))) 90) := by
  exact ⟨unit_5_13_35_closed, unit_5_13_36_closed, unit_5_13_37_closed, unit_5_13_40_closed, unit_5_13_41_closed, unit_5_13_43_closed, unit_5_13_44_closed, unit_5_13_45_closed, unit_5_13_47_closed, unit_5_13_48_closed, unit_5_13_49_closed, unit_5_13_50_closed, unit_5_13_51_closed, unit_5_13_53_closed, unit_5_13_54_closed, unit_5_13_55_closed, unit_5_13_56_closed, unit_5_13_57_closed, unit_5_13_58_closed, unit_5_13_59_closed, unit_5_13_60_closed, unit_5_13_61_closed, unit_5_13_65_closed, unit_5_13_66_closed, unit_5_13_71_closed, unit_5_13_73_closed, unit_5_13_75_closed, unit_5_13_77_closed, unit_5_13_79_closed, unit_5_13_83_closed, unit_5_13_89_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit95. -/
theorem certificate_BlockUnit95 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 21 List.nil.{0})))) 22) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 22 List.nil.{0})))) 23) := by
  exact ⟨unit_5_21_closed, unit_5_22_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit99. -/
theorem certificate_BlockUnit99 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 26 List.nil.{0})))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 27 List.nil.{0})))) 28) := by
  exact ⟨unit_5_26_closed, unit_5_27_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit100. -/
theorem certificate_BlockUnit100 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 29 List.nil.{0})))) 30) := by
  exact ⟨unit_5_28_closed, unit_5_29_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit101. -/
theorem certificate_BlockUnit101 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 31 List.nil.{0})))) 32) := by
  exact ⟨unit_5_30_closed, unit_5_31_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit102. -/
theorem certificate_BlockUnit102 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 33 List.nil.{0})))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 35 List.nil.{0})))) 36) := by
  exact ⟨unit_5_33_closed, unit_5_35_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit103. -/
theorem certificate_BlockUnit103 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 37 List.nil.{0})))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 38 List.nil.{0})))) 39) := by
  exact ⟨unit_5_36_closed, unit_5_37_closed, unit_5_38_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit104. -/
theorem certificate_BlockUnit104 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 39 List.nil.{0})))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 41 List.nil.{0})))) 42) := by
  exact ⟨unit_5_39_closed, unit_5_40_closed, unit_5_41_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit105. -/
theorem certificate_BlockUnit105 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 43 List.nil.{0})))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 45 List.nil.{0})))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 46 List.nil.{0})))) 47) := by
  exact ⟨unit_5_43_closed, unit_5_44_closed, unit_5_45_closed, unit_5_46_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit106. -/
theorem certificate_BlockUnit106 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 47 List.nil.{0})))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 49 List.nil.{0})))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 51 List.nil.{0})))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 52 List.nil.{0})))) 53) := by
  exact ⟨unit_5_47_closed, unit_5_48_closed, unit_5_49_closed, unit_5_50_closed, unit_5_51_closed, unit_5_52_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit107. -/
theorem certificate_BlockUnit107 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 53 List.nil.{0})))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 55 List.nil.{0})))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 59 List.nil.{0})))) 60) := by
  exact ⟨unit_5_53_closed, unit_5_54_closed, unit_5_55_closed, unit_5_56_closed, unit_5_57_closed, unit_5_58_closed, unit_5_59_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit108. -/
theorem certificate_BlockUnit108 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 65 List.nil.{0})))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 66 List.nil.{0})))) 67) := by
  exact ⟨unit_5_60_closed, unit_5_61_closed, unit_5_65_closed, unit_5_66_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit109. -/
theorem certificate_BlockUnit109 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 67 List.nil.{0})))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 69 List.nil.{0})))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 71 List.nil.{0})))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 73 List.nil.{0})))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 75 List.nil.{0})))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 76 List.nil.{0})))) 77) := by
  exact ⟨unit_5_67_closed, unit_5_68_closed, unit_5_69_closed, unit_5_70_closed, unit_5_71_closed, unit_5_72_closed, unit_5_73_closed, unit_5_74_closed, unit_5_75_closed, unit_5_76_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit110. -/
theorem certificate_BlockUnit110 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 77 List.nil.{0})))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 79 List.nil.{0})))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 83 List.nil.{0})))) 84) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 84 List.nil.{0})))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 85 List.nil.{0})))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 89 List.nil.{0})))) 90) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 91 List.nil.{0})))) 92) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 93 List.nil.{0})))) 94) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 95 List.nil.{0})))) 96) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 96 List.nil.{0})))) 97) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 97 List.nil.{0})))) 98) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 98 List.nil.{0})))) 99) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 5 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 5 (List.cons.{0} 99 List.nil.{0})))) 100) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 20 List.nil.{0}))))) 21) := by
  exact ⟨unit_5_77_closed, unit_5_78_closed, unit_5_79_closed, unit_5_80_closed, unit_5_81_closed, unit_5_83_closed, unit_5_84_closed, unit_5_85_closed, unit_5_86_closed, unit_5_87_closed, unit_5_88_closed, unit_5_89_closed, unit_5_90_closed, unit_5_91_closed, unit_5_93_closed, unit_5_95_closed, unit_5_96_closed, unit_5_97_closed, unit_5_98_closed, unit_5_99_closed, unit_6_8_20_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit111. -/
theorem certificate_BlockUnit111 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 24 List.nil.{0}))))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 26 List.nil.{0}))))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 27 List.nil.{0}))))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 28 List.nil.{0}))))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 30 List.nil.{0}))))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 31 List.nil.{0}))))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 32 List.nil.{0}))))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 33 List.nil.{0}))))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 34 List.nil.{0}))))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 35 List.nil.{0}))))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 37 List.nil.{0}))))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 38 List.nil.{0}))))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 40 List.nil.{0}))))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 41 List.nil.{0}))))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 42 List.nil.{0}))))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 44 List.nil.{0}))))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 46 List.nil.{0}))))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 47 List.nil.{0}))))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 48 List.nil.{0}))))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 49 List.nil.{0}))))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 52 List.nil.{0}))))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 54 List.nil.{0}))))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 56 List.nil.{0}))))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 57 List.nil.{0}))))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 58 List.nil.{0}))))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 59 List.nil.{0}))))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 62 List.nil.{0}))))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 66 List.nil.{0}))))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 68 List.nil.{0}))))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 70 List.nil.{0}))))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 71 List.nil.{0}))))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 72 List.nil.{0}))))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 73 List.nil.{0}))))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 76 List.nil.{0}))))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 78 List.nil.{0}))))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 8 (List.cons.{0} 80 List.nil.{0}))))) 81) := by
  exact ⟨unit_6_8_24_closed, unit_6_8_26_closed, unit_6_8_27_closed, unit_6_8_28_closed, unit_6_8_30_closed, unit_6_8_31_closed, unit_6_8_32_closed, unit_6_8_33_closed, unit_6_8_34_closed, unit_6_8_35_closed, unit_6_8_37_closed, unit_6_8_38_closed, unit_6_8_39_closed, unit_6_8_40_closed, unit_6_8_41_closed, unit_6_8_42_closed, unit_6_8_44_closed, unit_6_8_46_closed, unit_6_8_47_closed, unit_6_8_48_closed, unit_6_8_49_closed, unit_6_8_51_closed, unit_6_8_52_closed, unit_6_8_54_closed, unit_6_8_56_closed, unit_6_8_57_closed, unit_6_8_58_closed, unit_6_8_59_closed, unit_6_8_60_closed, unit_6_8_61_closed, unit_6_8_62_closed, unit_6_8_66_closed, unit_6_8_68_closed, unit_6_8_70_closed, unit_6_8_71_closed, unit_6_8_72_closed, unit_6_8_73_closed, unit_6_8_76_closed, unit_6_8_78_closed, unit_6_8_80_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit116. -/
theorem certificate_BlockUnit116 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 15 List.nil.{0})))) 16) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 18 List.nil.{0}))))) 19) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 19 List.nil.{0}))))) 20) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 24 List.nil.{0}))))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 28 List.nil.{0}))))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 30 List.nil.{0}))))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 33 List.nil.{0}))))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 34 List.nil.{0}))))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 35 List.nil.{0}))))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 36 List.nil.{0}))))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 38 List.nil.{0}))))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 40 List.nil.{0}))))) 41) := by
  exact ⟨unit_6_15_closed, unit_6_16_18_closed, unit_6_16_19_closed, unit_6_16_24_closed, unit_6_16_28_closed, unit_6_16_30_closed, unit_6_16_33_closed, unit_6_16_34_closed, unit_6_16_35_closed, unit_6_16_36_closed, unit_6_16_38_closed, unit_6_16_39_closed, unit_6_16_40_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit117. -/
theorem certificate_BlockUnit117 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 43 List.nil.{0}))))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 44 List.nil.{0}))))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 45 List.nil.{0}))))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 46 List.nil.{0}))))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 48 List.nil.{0}))))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 49 List.nil.{0}))))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 52 List.nil.{0}))))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 54 List.nil.{0}))))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 55 List.nil.{0}))))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 56 List.nil.{0}))))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 58 List.nil.{0}))))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 59 List.nil.{0}))))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 62 List.nil.{0}))))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 64 List.nil.{0}))))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 65 List.nil.{0}))))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 66 List.nil.{0}))))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 70 List.nil.{0}))))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 72 List.nil.{0}))))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 73 List.nil.{0}))))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 76 List.nil.{0}))))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 78 List.nil.{0}))))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 79 List.nil.{0}))))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 80 List.nil.{0}))))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 81 List.nil.{0}))))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 82 List.nil.{0}))))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 83 List.nil.{0}))))) 84) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 84 List.nil.{0}))))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 86 List.nil.{0}))))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 16 (List.cons.{0} 88 List.nil.{0}))))) 89) := by
  exact ⟨unit_6_16_43_closed, unit_6_16_44_closed, unit_6_16_45_closed, unit_6_16_46_closed, unit_6_16_48_closed, unit_6_16_49_closed, unit_6_16_51_closed, unit_6_16_52_closed, unit_6_16_54_closed, unit_6_16_55_closed, unit_6_16_56_closed, unit_6_16_58_closed, unit_6_16_59_closed, unit_6_16_60_closed, unit_6_16_61_closed, unit_6_16_62_closed, unit_6_16_64_closed, unit_6_16_65_closed, unit_6_16_66_closed, unit_6_16_70_closed, unit_6_16_72_closed, unit_6_16_73_closed, unit_6_16_76_closed, unit_6_16_78_closed, unit_6_16_79_closed, unit_6_16_80_closed, unit_6_16_81_closed, unit_6_16_82_closed, unit_6_16_83_closed, unit_6_16_84_closed, unit_6_16_86_closed, unit_6_16_88_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit119. -/
theorem certificate_BlockUnit119 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 19 List.nil.{0})))) 20) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 20 List.nil.{0})))) 21) := by
  exact ⟨unit_6_19_closed, unit_6_20_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit124. -/
theorem certificate_BlockUnit124 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 25 List.nil.{0})))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 26 List.nil.{0})))) 27) := by
  exact ⟨unit_6_25_closed, unit_6_26_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit125. -/
theorem certificate_BlockUnit125 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 27 List.nil.{0})))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 28 List.nil.{0})))) 29) := by
  exact ⟨unit_6_27_closed, unit_6_28_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit127. -/
theorem certificate_BlockUnit127 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 31 List.nil.{0})))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 32 List.nil.{0})))) 33) := by
  exact ⟨unit_6_31_closed, unit_6_32_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit128. -/
theorem certificate_BlockUnit128 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 33 List.nil.{0})))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 35 List.nil.{0})))) 36) := by
  exact ⟨unit_6_33_closed, unit_6_34_closed, unit_6_35_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit129. -/
theorem certificate_BlockUnit129 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 37 List.nil.{0})))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 38 List.nil.{0})))) 39) := by
  exact ⟨unit_6_36_closed, unit_6_37_closed, unit_6_38_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit130. -/
theorem certificate_BlockUnit130 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 39 List.nil.{0})))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 41 List.nil.{0})))) 42) := by
  exact ⟨unit_6_39_closed, unit_6_40_closed, unit_6_41_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit131. -/
theorem certificate_BlockUnit131 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 43 List.nil.{0})))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 44 List.nil.{0})))) 45) := by
  exact ⟨unit_6_42_closed, unit_6_43_closed, unit_6_44_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit132. -/
theorem certificate_BlockUnit132 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 45 List.nil.{0})))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 47 List.nil.{0})))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 49 List.nil.{0})))) 50) := by
  exact ⟨unit_6_45_closed, unit_6_46_closed, unit_6_47_closed, unit_6_48_closed, unit_6_49_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit133. -/
theorem certificate_BlockUnit133 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 51 List.nil.{0})))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 55 List.nil.{0})))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 59 List.nil.{0})))) 60) := by
  exact ⟨unit_6_51_closed, unit_6_52_closed, unit_6_54_closed, unit_6_55_closed, unit_6_56_closed, unit_6_57_closed, unit_6_58_closed, unit_6_59_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit134. -/
theorem certificate_BlockUnit134 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 65 List.nil.{0})))) 66) := by
  exact ⟨unit_6_60_closed, unit_6_61_closed, unit_6_62_closed, unit_6_64_closed, unit_6_65_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit135. -/
theorem certificate_BlockUnit135 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 67 List.nil.{0})))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 69 List.nil.{0})))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 71 List.nil.{0})))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 73 List.nil.{0})))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 75 List.nil.{0})))) 76) := by
  exact ⟨unit_6_66_closed, unit_6_67_closed, unit_6_68_closed, unit_6_69_closed, unit_6_70_closed, unit_6_71_closed, unit_6_72_closed, unit_6_73_closed, unit_6_75_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit136. -/
theorem certificate_BlockUnit136 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 79 List.nil.{0})))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 83 List.nil.{0})))) 84) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 84 List.nil.{0})))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 85 List.nil.{0})))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 89 List.nil.{0})))) 90) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 91 List.nil.{0})))) 92) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 92 List.nil.{0})))) 93) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 93 List.nil.{0})))) 94) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 94 List.nil.{0})))) 95) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 95 List.nil.{0})))) 96) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 96 List.nil.{0})))) 97) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 97 List.nil.{0})))) 98) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 99 List.nil.{0})))) 100) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 6 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 6 (List.cons.{0} 100 List.nil.{0})))) 101) := by
  exact ⟨unit_6_76_closed, unit_6_78_closed, unit_6_79_closed, unit_6_80_closed, unit_6_81_closed, unit_6_82_closed, unit_6_83_closed, unit_6_84_closed, unit_6_85_closed, unit_6_86_closed, unit_6_87_closed, unit_6_88_closed, unit_6_89_closed, unit_6_90_closed, unit_6_91_closed, unit_6_92_closed, unit_6_93_closed, unit_6_94_closed, unit_6_95_closed, unit_6_96_closed, unit_6_97_closed, unit_6_99_closed, unit_6_100_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit140. -/
theorem certificate_BlockUnit140 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 12 List.nil.{0})))) 13) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 17 List.nil.{0}))))) 18) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 18 List.nil.{0}))))) 19) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 19 List.nil.{0}))))) 20) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 25 List.nil.{0}))))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 27 List.nil.{0}))))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 31 List.nil.{0}))))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 32 List.nil.{0}))))) 33) := by
  exact ⟨unit_7_12_closed, unit_7_15_17_closed, unit_7_15_18_closed, unit_7_15_19_closed, unit_7_15_25_closed, unit_7_15_27_closed, unit_7_15_31_closed, unit_7_15_32_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit141. -/
theorem certificate_BlockUnit141 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 33 List.nil.{0}))))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 34 List.nil.{0}))))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 39 List.nil.{0}))))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 40 List.nil.{0}))))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 41 List.nil.{0}))))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 43 List.nil.{0}))))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 45 List.nil.{0}))))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 46 List.nil.{0}))))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 47 List.nil.{0}))))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 48 List.nil.{0}))))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 49 List.nil.{0}))))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 50 List.nil.{0}))))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 51 List.nil.{0}))))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 53 List.nil.{0}))))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 57 List.nil.{0}))))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 58 List.nil.{0}))))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 59 List.nil.{0}))))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 60 List.nil.{0}))))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 61 List.nil.{0}))))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 63 List.nil.{0}))))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 65 List.nil.{0}))))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 67 List.nil.{0}))))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 69 List.nil.{0}))))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 73 List.nil.{0}))))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 75 List.nil.{0}))))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 78 List.nil.{0}))))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 79 List.nil.{0}))))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 80 List.nil.{0}))))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 81 List.nil.{0}))))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 2
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 15 (List.cons.{0} 83 List.nil.{0}))))) 84) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 16 List.nil.{0})))) 17) := by
  exact ⟨unit_7_15_33_closed, unit_7_15_34_closed, unit_7_15_39_closed, unit_7_15_40_closed, unit_7_15_41_closed, unit_7_15_43_closed, unit_7_15_45_closed, unit_7_15_46_closed, unit_7_15_47_closed, unit_7_15_48_closed, unit_7_15_49_closed, unit_7_15_50_closed, unit_7_15_51_closed, unit_7_15_53_closed, unit_7_15_57_closed, unit_7_15_58_closed, unit_7_15_59_closed, unit_7_15_60_closed, unit_7_15_61_closed, unit_7_15_63_closed, unit_7_15_65_closed, unit_7_15_67_closed, unit_7_15_69_closed, unit_7_15_73_closed, unit_7_15_75_closed, unit_7_15_78_closed, unit_7_15_79_closed, unit_7_15_80_closed, unit_7_15_81_closed, unit_7_15_83_closed, unit_7_16_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit142. -/
theorem certificate_BlockUnit142 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 17 List.nil.{0})))) 18) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 18 List.nil.{0})))) 19) := by
  exact ⟨unit_7_17_closed, unit_7_18_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit144. -/
theorem certificate_BlockUnit144 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 22 List.nil.{0})))) 23) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 23 List.nil.{0})))) 24) := by
  exact ⟨unit_7_22_closed, unit_7_23_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit145. -/
theorem certificate_BlockUnit145 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 24 List.nil.{0})))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 25 List.nil.{0})))) 26) := by
  exact ⟨unit_7_24_closed, unit_7_25_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit146. -/
theorem certificate_BlockUnit146 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 27 List.nil.{0})))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 29 List.nil.{0})))) 30) := by
  exact ⟨unit_7_27_closed, unit_7_29_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit147. -/
theorem certificate_BlockUnit147 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 31 List.nil.{0})))) 32) := by
  exact ⟨unit_7_30_closed, unit_7_31_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit148. -/
theorem certificate_BlockUnit148 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 33 List.nil.{0})))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 36 List.nil.{0})))) 37) := by
  exact ⟨unit_7_32_closed, unit_7_33_closed, unit_7_34_closed, unit_7_36_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit149. -/
theorem certificate_BlockUnit149 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 37 List.nil.{0})))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 38 List.nil.{0})))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 39 List.nil.{0})))) 40) := by
  exact ⟨unit_7_37_closed, unit_7_38_closed, unit_7_39_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit150. -/
theorem certificate_BlockUnit150 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 41 List.nil.{0})))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 43 List.nil.{0})))) 44) := by
  exact ⟨unit_7_40_closed, unit_7_41_closed, unit_7_43_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit151. -/
theorem certificate_BlockUnit151 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 45 List.nil.{0})))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 47 List.nil.{0})))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 48 List.nil.{0})))) 49) := by
  exact ⟨unit_7_44_closed, unit_7_45_closed, unit_7_46_closed, unit_7_47_closed, unit_7_48_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit152. -/
theorem certificate_BlockUnit152 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 49 List.nil.{0})))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 51 List.nil.{0})))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 53 List.nil.{0})))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 55 List.nil.{0})))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 57 List.nil.{0})))) 58) := by
  exact ⟨unit_7_49_closed, unit_7_50_closed, unit_7_51_closed, unit_7_52_closed, unit_7_53_closed, unit_7_54_closed, unit_7_55_closed, unit_7_56_closed, unit_7_57_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit153. -/
theorem certificate_BlockUnit153 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 59 List.nil.{0})))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 63 List.nil.{0})))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 65 List.nil.{0})))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 67 List.nil.{0})))) 68) := by
  exact ⟨unit_7_58_closed, unit_7_59_closed, unit_7_60_closed, unit_7_61_closed, unit_7_63_closed, unit_7_65_closed, unit_7_67_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit154. -/
theorem certificate_BlockUnit154 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 69 List.nil.{0})))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 71 List.nil.{0})))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 73 List.nil.{0})))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 75 List.nil.{0})))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 77 List.nil.{0})))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 79 List.nil.{0})))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 83 List.nil.{0})))) 84) := by
  exact ⟨unit_7_68_closed, unit_7_69_closed, unit_7_70_closed, unit_7_71_closed, unit_7_72_closed, unit_7_73_closed, unit_7_74_closed, unit_7_75_closed, unit_7_76_closed, unit_7_77_closed, unit_7_78_closed, unit_7_79_closed, unit_7_80_closed, unit_7_81_closed, unit_7_82_closed, unit_7_83_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit155. -/
theorem certificate_BlockUnit155 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 84 List.nil.{0})))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 89 List.nil.{0})))) 90) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 91 List.nil.{0})))) 92) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 93 List.nil.{0})))) 94) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 94 List.nil.{0})))) 95) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 95 List.nil.{0})))) 96) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 97 List.nil.{0})))) 98) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 98 List.nil.{0})))) 99) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 7 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 7 (List.cons.{0} 101 List.nil.{0})))) 102) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 10 List.nil.{0})))) 11) := by
  exact ⟨unit_7_84_closed, unit_7_87_closed, unit_7_88_closed, unit_7_89_closed, unit_7_90_closed, unit_7_91_closed, unit_7_93_closed, unit_7_94_closed, unit_7_95_closed, unit_7_97_closed, unit_7_98_closed, unit_7_101_closed, unit_8_10_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit158. -/
theorem certificate_BlockUnit158 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 13 List.nil.{0})))) 14) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 14 List.nil.{0})))) 15) := by
  exact ⟨unit_8_13_closed, unit_8_14_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit159. -/
theorem certificate_BlockUnit159 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 17 List.nil.{0})))) 18) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 19 List.nil.{0})))) 20) := by
  exact ⟨unit_8_17_closed, unit_8_19_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit160. -/
theorem certificate_BlockUnit160 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 20 List.nil.{0})))) 21) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 21 List.nil.{0})))) 22) := by
  exact ⟨unit_8_20_closed, unit_8_21_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit161. -/
theorem certificate_BlockUnit161 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 24 List.nil.{0})))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 25 List.nil.{0})))) 26) := by
  exact ⟨unit_8_24_closed, unit_8_25_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit162. -/
theorem certificate_BlockUnit162 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 26 List.nil.{0})))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 27 List.nil.{0})))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 28 List.nil.{0})))) 29) := by
  exact ⟨unit_8_26_closed, unit_8_27_closed, unit_8_28_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit163. -/
theorem certificate_BlockUnit163 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 31 List.nil.{0})))) 32) := by
  exact ⟨unit_8_30_closed, unit_8_31_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit164. -/
theorem certificate_BlockUnit164 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 33 List.nil.{0})))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 34 List.nil.{0})))) 35) := by
  exact ⟨unit_8_32_closed, unit_8_33_closed, unit_8_34_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit165. -/
theorem certificate_BlockUnit165 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 37 List.nil.{0})))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 38 List.nil.{0})))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 39 List.nil.{0})))) 40) := by
  exact ⟨unit_8_35_closed, unit_8_37_closed, unit_8_38_closed, unit_8_39_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit166. -/
theorem certificate_BlockUnit166 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 41 List.nil.{0})))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 44 List.nil.{0})))) 45) := by
  exact ⟨unit_8_40_closed, unit_8_41_closed, unit_8_42_closed, unit_8_44_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit167. -/
theorem certificate_BlockUnit167 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 45 List.nil.{0})))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 47 List.nil.{0})))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 49 List.nil.{0})))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 51 List.nil.{0})))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 52 List.nil.{0})))) 53) := by
  exact ⟨unit_8_45_closed, unit_8_46_closed, unit_8_47_closed, unit_8_48_closed, unit_8_49_closed, unit_8_51_closed, unit_8_52_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit168. -/
theorem certificate_BlockUnit168 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 53 List.nil.{0})))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 55 List.nil.{0})))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 59 List.nil.{0})))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 60 List.nil.{0})))) 61) := by
  exact ⟨unit_8_53_closed, unit_8_54_closed, unit_8_55_closed, unit_8_56_closed, unit_8_57_closed, unit_8_58_closed, unit_8_59_closed, unit_8_60_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit169. -/
theorem certificate_BlockUnit169 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 63 List.nil.{0})))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 65 List.nil.{0})))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 67 List.nil.{0})))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 69 List.nil.{0})))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 71 List.nil.{0})))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 73 List.nil.{0})))) 74) := by
  exact ⟨unit_8_61_closed, unit_8_62_closed, unit_8_63_closed, unit_8_65_closed, unit_8_66_closed, unit_8_67_closed, unit_8_68_closed, unit_8_69_closed, unit_8_70_closed, unit_8_71_closed, unit_8_72_closed, unit_8_73_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit170. -/
theorem certificate_BlockUnit170 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 75 List.nil.{0})))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 77 List.nil.{0})))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 84 List.nil.{0})))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 85 List.nil.{0})))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 89 List.nil.{0})))) 90) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 91 List.nil.{0})))) 92) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 92 List.nil.{0})))) 93) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 94 List.nil.{0})))) 95) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 95 List.nil.{0})))) 96) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 96 List.nil.{0})))) 97) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 98 List.nil.{0})))) 99) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 8 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 8 (List.cons.{0} 99 List.nil.{0})))) 100) := by
  exact ⟨unit_8_74_closed, unit_8_75_closed, unit_8_76_closed, unit_8_77_closed, unit_8_78_closed, unit_8_80_closed, unit_8_81_closed, unit_8_82_closed, unit_8_84_closed, unit_8_85_closed, unit_8_87_closed, unit_8_88_closed, unit_8_89_closed, unit_8_90_closed, unit_8_91_closed, unit_8_92_closed, unit_8_94_closed, unit_8_95_closed, unit_8_96_closed, unit_8_98_closed, unit_8_99_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit171. -/
theorem certificate_BlockUnit171 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 11 List.nil.{0})))) 12) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 12 List.nil.{0})))) 13) := by
  exact ⟨unit_9_11_closed, unit_9_12_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit173. -/
theorem certificate_BlockUnit173 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 14 List.nil.{0})))) 15) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 15 List.nil.{0})))) 16) := by
  exact ⟨unit_9_14_closed, unit_9_15_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit175. -/
theorem certificate_BlockUnit175 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 19 List.nil.{0})))) 20) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 20 List.nil.{0})))) 21) := by
  exact ⟨unit_9_19_closed, unit_9_20_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit176. -/
theorem certificate_BlockUnit176 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 21 List.nil.{0})))) 22) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 22 List.nil.{0})))) 23) := by
  exact ⟨unit_9_21_closed, unit_9_22_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit177. -/
theorem certificate_BlockUnit177 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 23 List.nil.{0})))) 24) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 24 List.nil.{0})))) 25) := by
  exact ⟨unit_9_23_closed, unit_9_24_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit178. -/
theorem certificate_BlockUnit178 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 25 List.nil.{0})))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 27 List.nil.{0})))) 28) := by
  exact ⟨unit_9_25_closed, unit_9_27_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit179. -/
theorem certificate_BlockUnit179 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 29 List.nil.{0})))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 30 List.nil.{0})))) 31) := by
  exact ⟨unit_9_28_closed, unit_9_29_closed, unit_9_30_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit180. -/
theorem certificate_BlockUnit180 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 31 List.nil.{0})))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 33 List.nil.{0})))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 34 List.nil.{0})))) 35) := by
  exact ⟨unit_9_31_closed, unit_9_33_closed, unit_9_34_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit181. -/
theorem certificate_BlockUnit181 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 39 List.nil.{0})))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 40 List.nil.{0})))) 41) := by
  exact ⟨unit_9_35_closed, unit_9_36_closed, unit_9_39_closed, unit_9_40_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit182. -/
theorem certificate_BlockUnit182 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 41 List.nil.{0})))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 45 List.nil.{0})))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 47 List.nil.{0})))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 48 List.nil.{0})))) 49) := by
  exact ⟨unit_9_41_closed, unit_9_42_closed, unit_9_44_closed, unit_9_45_closed, unit_9_47_closed, unit_9_48_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit183. -/
theorem certificate_BlockUnit183 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 49 List.nil.{0})))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 51 List.nil.{0})))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 53 List.nil.{0})))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 55 List.nil.{0})))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 59 List.nil.{0})))) 60) := by
  exact ⟨unit_9_49_closed, unit_9_50_closed, unit_9_51_closed, unit_9_53_closed, unit_9_54_closed, unit_9_55_closed, unit_9_56_closed, unit_9_57_closed, unit_9_58_closed, unit_9_59_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit184. -/
theorem certificate_BlockUnit184 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 63 List.nil.{0})))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 67 List.nil.{0})))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 69 List.nil.{0})))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 71 List.nil.{0})))) 72) := by
  exact ⟨unit_9_60_closed, unit_9_61_closed, unit_9_63_closed, unit_9_64_closed, unit_9_66_closed, unit_9_67_closed, unit_9_69_closed, unit_9_70_closed, unit_9_71_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit185. -/
theorem certificate_BlockUnit185 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 73 List.nil.{0})))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 75 List.nil.{0})))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 79 List.nil.{0})))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 84 List.nil.{0})))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 85 List.nil.{0})))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 89 List.nil.{0})))) 90) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 91 List.nil.{0})))) 92) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 93 List.nil.{0})))) 94) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 94 List.nil.{0})))) 95) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 95 List.nil.{0})))) 96) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 96 List.nil.{0})))) 97) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 97 List.nil.{0})))) 98) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 9 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 9 (List.cons.{0} 99 List.nil.{0})))) 100) := by
  exact ⟨unit_9_72_closed, unit_9_73_closed, unit_9_74_closed, unit_9_75_closed, unit_9_76_closed, unit_9_78_closed, unit_9_79_closed, unit_9_80_closed, unit_9_81_closed, unit_9_82_closed, unit_9_84_closed, unit_9_85_closed, unit_9_87_closed, unit_9_88_closed, unit_9_89_closed, unit_9_90_closed, unit_9_91_closed, unit_9_93_closed, unit_9_94_closed, unit_9_95_closed, unit_9_96_closed, unit_9_97_closed, unit_9_99_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit186. -/
theorem certificate_BlockUnit186 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 12 List.nil.{0})))) 13) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 13 List.nil.{0})))) 14) := by
  exact ⟨unit_10_12_closed, unit_10_13_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit187. -/
theorem certificate_BlockUnit187 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 14 List.nil.{0})))) 15) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 15 List.nil.{0})))) 16) := by
  exact ⟨unit_10_14_closed, unit_10_15_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit188. -/
theorem certificate_BlockUnit188 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 16 List.nil.{0})))) 17) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 21 List.nil.{0})))) 22) := by
  exact ⟨unit_10_16_closed, unit_10_21_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit189. -/
theorem certificate_BlockUnit189 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 22 List.nil.{0})))) 23) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 23 List.nil.{0})))) 24) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 24 List.nil.{0})))) 25) := by
  exact ⟨unit_10_22_closed, unit_10_23_closed, unit_10_24_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit190. -/
theorem certificate_BlockUnit190 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 25 List.nil.{0})))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 26 List.nil.{0})))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 27 List.nil.{0})))) 28) := by
  exact ⟨unit_10_25_closed, unit_10_26_closed, unit_10_27_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit191. -/
theorem certificate_BlockUnit191 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 30 List.nil.{0})))) 31) := by
  exact ⟨unit_10_28_closed, unit_10_30_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit192. -/
theorem certificate_BlockUnit192 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 31 List.nil.{0})))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 33 List.nil.{0})))) 34) := by
  exact ⟨unit_10_31_closed, unit_10_32_closed, unit_10_33_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit193. -/
theorem certificate_BlockUnit193 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 37 List.nil.{0})))) 38) := by
  exact ⟨unit_10_34_closed, unit_10_35_closed, unit_10_36_closed, unit_10_37_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit194. -/
theorem certificate_BlockUnit194 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 39 List.nil.{0})))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 41 List.nil.{0})))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 43 List.nil.{0})))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 45 List.nil.{0})))) 46) := by
  exact ⟨unit_10_39_closed, unit_10_40_closed, unit_10_41_closed, unit_10_43_closed, unit_10_45_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit195. -/
theorem certificate_BlockUnit195 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 49 List.nil.{0})))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 51 List.nil.{0})))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 55 List.nil.{0})))) 56) := by
  exact ⟨unit_10_46_closed, unit_10_48_closed, unit_10_49_closed, unit_10_50_closed, unit_10_51_closed, unit_10_52_closed, unit_10_54_closed, unit_10_55_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit196. -/
theorem certificate_BlockUnit196 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 59 List.nil.{0})))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 63 List.nil.{0})))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 67 List.nil.{0})))) 68) := by
  exact ⟨unit_10_56_closed, unit_10_57_closed, unit_10_58_closed, unit_10_59_closed, unit_10_60_closed, unit_10_61_closed, unit_10_62_closed, unit_10_63_closed, unit_10_64_closed, unit_10_66_closed, unit_10_67_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit197. -/
theorem certificate_BlockUnit197 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 69 List.nil.{0})))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 71 List.nil.{0})))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 73 List.nil.{0})))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 75 List.nil.{0})))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 77 List.nil.{0})))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 79 List.nil.{0})))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 83 List.nil.{0})))) 84) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 85 List.nil.{0})))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 91 List.nil.{0})))) 92) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 92 List.nil.{0})))) 93) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 94 List.nil.{0})))) 95) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 95 List.nil.{0})))) 96) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 96 List.nil.{0})))) 97) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 10 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 10 (List.cons.{0} 98 List.nil.{0})))) 99) := by
  exact ⟨unit_10_68_closed, unit_10_69_closed, unit_10_70_closed, unit_10_71_closed, unit_10_72_closed, unit_10_73_closed, unit_10_74_closed, unit_10_75_closed, unit_10_76_closed, unit_10_77_closed, unit_10_79_closed, unit_10_80_closed, unit_10_81_closed, unit_10_82_closed, unit_10_83_closed, unit_10_85_closed, unit_10_86_closed, unit_10_88_closed, unit_10_90_closed, unit_10_91_closed, unit_10_92_closed, unit_10_94_closed, unit_10_95_closed, unit_10_96_closed, unit_10_98_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit198. -/
theorem certificate_BlockUnit198 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 13 List.nil.{0})))) 14) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 15 List.nil.{0})))) 16) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 16 List.nil.{0})))) 17) := by
  exact ⟨unit_11_13_closed, unit_11_15_closed, unit_11_16_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit199. -/
theorem certificate_BlockUnit199 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 19 List.nil.{0})))) 20) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 20 List.nil.{0})))) 21) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 23 List.nil.{0})))) 24) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 24 List.nil.{0})))) 25) := by
  exact ⟨unit_11_19_closed, unit_11_20_closed, unit_11_23_closed, unit_11_24_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit200. -/
theorem certificate_BlockUnit200 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 25 List.nil.{0})))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 26 List.nil.{0})))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 27 List.nil.{0})))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 29 List.nil.{0})))) 30) := by
  exact ⟨unit_11_25_closed, unit_11_26_closed, unit_11_27_closed, unit_11_28_closed, unit_11_29_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit201. -/
theorem certificate_BlockUnit201 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 31 List.nil.{0})))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 37 List.nil.{0})))) 38) := by
  exact ⟨unit_11_30_closed, unit_11_31_closed, unit_11_35_closed, unit_11_36_closed, unit_11_37_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit202. -/
theorem certificate_BlockUnit202 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 39 List.nil.{0})))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 41 List.nil.{0})))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 45 List.nil.{0})))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 47 List.nil.{0})))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 49 List.nil.{0})))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 51 List.nil.{0})))) 52) := by
  exact ⟨unit_11_39_closed, unit_11_40_closed, unit_11_41_closed, unit_11_42_closed, unit_11_45_closed, unit_11_46_closed, unit_11_47_closed, unit_11_48_closed, unit_11_49_closed, unit_11_51_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit203. -/
theorem certificate_BlockUnit203 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 59 List.nil.{0})))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 63 List.nil.{0})))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 69 List.nil.{0})))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 71 List.nil.{0})))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 73 List.nil.{0})))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 75 List.nil.{0})))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 79 List.nil.{0})))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 83 List.nil.{0})))) 84) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 85 List.nil.{0})))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 89 List.nil.{0})))) 90) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 91 List.nil.{0})))) 92) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 93 List.nil.{0})))) 94) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 95 List.nil.{0})))) 96) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 11 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 11 (List.cons.{0} 97 List.nil.{0})))) 98) := by
  exact ⟨unit_11_52_closed, unit_11_56_closed, unit_11_57_closed, unit_11_59_closed, unit_11_60_closed, unit_11_61_closed, unit_11_63_closed, unit_11_68_closed, unit_11_69_closed, unit_11_71_closed, unit_11_72_closed, unit_11_73_closed, unit_11_75_closed, unit_11_79_closed, unit_11_80_closed, unit_11_81_closed, unit_11_83_closed, unit_11_85_closed, unit_11_86_closed, unit_11_89_closed, unit_11_90_closed, unit_11_91_closed, unit_11_93_closed, unit_11_95_closed, unit_11_97_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit204. -/
theorem certificate_BlockUnit204 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 14 List.nil.{0})))) 15) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 15 List.nil.{0})))) 16) := by
  exact ⟨unit_12_14_closed, unit_12_15_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit205. -/
theorem certificate_BlockUnit205 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 16 List.nil.{0})))) 17) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 19 List.nil.{0})))) 20) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 20 List.nil.{0})))) 21) := by
  exact ⟨unit_12_16_closed, unit_12_19_closed, unit_12_20_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit206. -/
theorem certificate_BlockUnit206 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 21 List.nil.{0})))) 22) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 25 List.nil.{0})))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 26 List.nil.{0})))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 27 List.nil.{0})))) 28) := by
  exact ⟨unit_12_21_closed, unit_12_25_closed, unit_12_26_closed, unit_12_27_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit207. -/
theorem certificate_BlockUnit207 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 29 List.nil.{0})))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 31 List.nil.{0})))) 32) := by
  exact ⟨unit_12_28_closed, unit_12_29_closed, unit_12_30_closed, unit_12_31_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit208. -/
theorem certificate_BlockUnit208 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 37 List.nil.{0})))) 38) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 38 List.nil.{0})))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 39 List.nil.{0})))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 40 List.nil.{0})))) 41) := by
  exact ⟨unit_12_32_closed, unit_12_36_closed, unit_12_37_closed, unit_12_38_closed, unit_12_39_closed, unit_12_40_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit209. -/
theorem certificate_BlockUnit209 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 41 List.nil.{0})))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 43 List.nil.{0})))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 47 List.nil.{0})))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 49 List.nil.{0})))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 51 List.nil.{0})))) 52) := by
  exact ⟨unit_12_41_closed, unit_12_42_closed, unit_12_43_closed, unit_12_46_closed, unit_12_47_closed, unit_12_48_closed, unit_12_49_closed, unit_12_50_closed, unit_12_51_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit210. -/
theorem certificate_BlockUnit210 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 53 List.nil.{0})))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 59 List.nil.{0})))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 63 List.nil.{0})))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 69 List.nil.{0})))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 71 List.nil.{0})))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 73 List.nil.{0})))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 75 List.nil.{0})))) 76) := by
  exact ⟨unit_12_52_closed, unit_12_53_closed, unit_12_57_closed, unit_12_58_closed, unit_12_59_closed, unit_12_60_closed, unit_12_61_closed, unit_12_62_closed, unit_12_63_closed, unit_12_64_closed, unit_12_69_closed, unit_12_70_closed, unit_12_71_closed, unit_12_72_closed, unit_12_73_closed, unit_12_74_closed, unit_12_75_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit211. -/
theorem certificate_BlockUnit211 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 83 List.nil.{0})))) 84) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 84 List.nil.{0})))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 85 List.nil.{0})))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 91 List.nil.{0})))) 92) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 92 List.nil.{0})))) 93) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 93 List.nil.{0})))) 94) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 94 List.nil.{0})))) 95) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 95 List.nil.{0})))) 96) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 96 List.nil.{0})))) 97) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 12 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 12 (List.cons.{0} 98 List.nil.{0})))) 99) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 15 List.nil.{0})))) 16) := by
  exact ⟨unit_12_76_closed, unit_12_80_closed, unit_12_81_closed, unit_12_82_closed, unit_12_83_closed, unit_12_84_closed, unit_12_85_closed, unit_12_86_closed, unit_12_87_closed, unit_12_90_closed, unit_12_91_closed, unit_12_92_closed, unit_12_93_closed, unit_12_94_closed, unit_12_95_closed, unit_12_96_closed, unit_12_98_closed, unit_13_15_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit212. -/
theorem certificate_BlockUnit212 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 20 List.nil.{0})))) 21) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 21 List.nil.{0})))) 22) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 22 List.nil.{0})))) 23) := by
  exact ⟨unit_13_20_closed, unit_13_21_closed, unit_13_22_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit213. -/
theorem certificate_BlockUnit213 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 24 List.nil.{0})))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 27 List.nil.{0})))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 30 List.nil.{0})))) 31) := by
  exact ⟨unit_13_24_closed, unit_13_27_closed, unit_13_28_closed, unit_13_30_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit214. -/
theorem certificate_BlockUnit214 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 31 List.nil.{0})))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 33 List.nil.{0})))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 37 List.nil.{0})))) 38) := by
  exact ⟨unit_13_31_closed, unit_13_33_closed, unit_13_34_closed, unit_13_35_closed, unit_13_37_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit215. -/
theorem certificate_BlockUnit215 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 41 List.nil.{0})))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 43 List.nil.{0})))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 45 List.nil.{0})))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 46 List.nil.{0})))) 47) := by
  exact ⟨unit_13_40_closed, unit_13_41_closed, unit_13_43_closed, unit_13_44_closed, unit_13_45_closed, unit_13_46_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit216. -/
theorem certificate_BlockUnit216 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 47 List.nil.{0})))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 49 List.nil.{0})))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 51 List.nil.{0})))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 53 List.nil.{0})))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 59 List.nil.{0})))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 60 List.nil.{0})))) 61) := by
  exact ⟨unit_13_47_closed, unit_13_48_closed, unit_13_49_closed, unit_13_50_closed, unit_13_51_closed, unit_13_53_closed, unit_13_54_closed, unit_13_56_closed, unit_13_57_closed, unit_13_58_closed, unit_13_59_closed, unit_13_60_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit217. -/
theorem certificate_BlockUnit217 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 63 List.nil.{0})))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 69 List.nil.{0})))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 71 List.nil.{0})))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 73 List.nil.{0})))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 75 List.nil.{0})))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 77 List.nil.{0})))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 79 List.nil.{0})))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 83 List.nil.{0})))) 84) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 84 List.nil.{0})))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 85 List.nil.{0})))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 89 List.nil.{0})))) 90) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 93 List.nil.{0})))) 94) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 95 List.nil.{0})))) 96) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 13 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 13 (List.cons.{0} 96 List.nil.{0})))) 97) := by
  exact ⟨unit_13_61_closed, unit_13_63_closed, unit_13_64_closed, unit_13_66_closed, unit_13_69_closed, unit_13_70_closed, unit_13_71_closed, unit_13_73_closed, unit_13_74_closed, unit_13_75_closed, unit_13_76_closed, unit_13_77_closed, unit_13_79_closed, unit_13_80_closed, unit_13_82_closed, unit_13_83_closed, unit_13_84_closed, unit_13_85_closed, unit_13_86_closed, unit_13_87_closed, unit_13_88_closed, unit_13_89_closed, unit_13_90_closed, unit_13_93_closed, unit_13_95_closed, unit_13_96_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit218. -/
theorem certificate_BlockUnit218 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 16 List.nil.{0})))) 17) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 19 List.nil.{0})))) 20) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 22 List.nil.{0})))) 23) := by
  exact ⟨unit_14_16_closed, unit_14_19_closed, unit_14_22_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit219. -/
theorem certificate_BlockUnit219 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 23 List.nil.{0})))) 24) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 25 List.nil.{0})))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 26 List.nil.{0})))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 29 List.nil.{0})))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 31 List.nil.{0})))) 32) := by
  exact ⟨unit_14_23_closed, unit_14_25_closed, unit_14_26_closed, unit_14_29_closed, unit_14_31_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit220. -/
theorem certificate_BlockUnit220 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 38 List.nil.{0})))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 39 List.nil.{0})))) 40) := by
  exact ⟨unit_14_32_closed, unit_14_34_closed, unit_14_35_closed, unit_14_36_closed, unit_14_38_closed, unit_14_39_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit221. -/
theorem certificate_BlockUnit221 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 47 List.nil.{0})))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 49 List.nil.{0})))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 51 List.nil.{0})))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 55 List.nil.{0})))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 57 List.nil.{0})))) 58) := by
  exact ⟨unit_14_42_closed, unit_14_44_closed, unit_14_46_closed, unit_14_47_closed, unit_14_48_closed, unit_14_49_closed, unit_14_51_closed, unit_14_52_closed, unit_14_54_closed, unit_14_55_closed, unit_14_57_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit222. -/
theorem certificate_BlockUnit222 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 59 List.nil.{0})))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 63 List.nil.{0})))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 65 List.nil.{0})))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 71 List.nil.{0})))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 73 List.nil.{0})))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 75 List.nil.{0})))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 77 List.nil.{0})))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 83 List.nil.{0})))) 84) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 89 List.nil.{0})))) 90) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 91 List.nil.{0})))) 92) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 94 List.nil.{0})))) 95) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 96 List.nil.{0})))) 97) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 14 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 14 (List.cons.{0} 97 List.nil.{0})))) 98) := by
  exact ⟨unit_14_58_closed, unit_14_59_closed, unit_14_60_closed, unit_14_61_closed, unit_14_62_closed, unit_14_63_closed, unit_14_64_closed, unit_14_65_closed, unit_14_68_closed, unit_14_70_closed, unit_14_71_closed, unit_14_72_closed, unit_14_73_closed, unit_14_74_closed, unit_14_75_closed, unit_14_76_closed, unit_14_77_closed, unit_14_78_closed, unit_14_80_closed, unit_14_83_closed, unit_14_86_closed, unit_14_87_closed, unit_14_88_closed, unit_14_89_closed, unit_14_90_closed, unit_14_91_closed, unit_14_94_closed, unit_14_96_closed, unit_14_97_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit223. -/
theorem certificate_BlockUnit223 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 19 List.nil.{0})))) 20) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 20 List.nil.{0})))) 21) := by
  exact ⟨unit_15_19_closed, unit_15_20_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit224. -/
theorem certificate_BlockUnit224 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 21 List.nil.{0})))) 22) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 23 List.nil.{0})))) 24) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 24 List.nil.{0})))) 25) := by
  exact ⟨unit_15_21_closed, unit_15_23_closed, unit_15_24_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit225. -/
theorem certificate_BlockUnit225 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 25 List.nil.{0})))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 26 List.nil.{0})))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 27 List.nil.{0})))) 28) := by
  exact ⟨unit_15_25_closed, unit_15_26_closed, unit_15_27_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit226. -/
theorem certificate_BlockUnit226 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 31 List.nil.{0})))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 33 List.nil.{0})))) 34) := by
  exact ⟨unit_15_28_closed, unit_15_31_closed, unit_15_32_closed, unit_15_33_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit227. -/
theorem certificate_BlockUnit227 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 39 List.nil.{0})))) 40) := by
  exact ⟨unit_15_34_closed, unit_15_35_closed, unit_15_36_closed, unit_15_39_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit228. -/
theorem certificate_BlockUnit228 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 41 List.nil.{0})))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 43 List.nil.{0})))) 44) := by
  exact ⟨unit_15_40_closed, unit_15_41_closed, unit_15_42_closed, unit_15_43_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit229. -/
theorem certificate_BlockUnit229 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 45 List.nil.{0})))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 47 List.nil.{0})))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 49 List.nil.{0})))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 51 List.nil.{0})))) 52) := by
  exact ⟨unit_15_45_closed, unit_15_46_closed, unit_15_47_closed, unit_15_48_closed, unit_15_49_closed, unit_15_50_closed, unit_15_51_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit230. -/
theorem certificate_BlockUnit230 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 53 List.nil.{0})))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 55 List.nil.{0})))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 59 List.nil.{0})))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 63 List.nil.{0})))) 64) := by
  exact ⟨unit_15_52_closed, unit_15_53_closed, unit_15_55_closed, unit_15_56_closed, unit_15_57_closed, unit_15_58_closed, unit_15_59_closed, unit_15_60_closed, unit_15_61_closed, unit_15_63_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit231. -/
theorem certificate_BlockUnit231 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 65 List.nil.{0})))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 67 List.nil.{0})))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 69 List.nil.{0})))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 71 List.nil.{0})))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 73 List.nil.{0})))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 75 List.nil.{0})))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 77 List.nil.{0})))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 79 List.nil.{0})))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 85 List.nil.{0})))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 89 List.nil.{0})))) 90) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 91 List.nil.{0})))) 92) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 92 List.nil.{0})))) 93) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 93 List.nil.{0})))) 94) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 94 List.nil.{0})))) 95) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 95 List.nil.{0})))) 96) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 96 List.nil.{0})))) 97) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 15 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 15 (List.cons.{0} 97 List.nil.{0})))) 98) := by
  exact ⟨unit_15_64_closed, unit_15_65_closed, unit_15_66_closed, unit_15_67_closed, unit_15_69_closed, unit_15_70_closed, unit_15_71_closed, unit_15_72_closed, unit_15_73_closed, unit_15_75_closed, unit_15_76_closed, unit_15_77_closed, unit_15_78_closed, unit_15_79_closed, unit_15_80_closed, unit_15_81_closed, unit_15_85_closed, unit_15_86_closed, unit_15_87_closed, unit_15_88_closed, unit_15_89_closed, unit_15_90_closed, unit_15_91_closed, unit_15_92_closed, unit_15_93_closed, unit_15_94_closed, unit_15_95_closed, unit_15_96_closed, unit_15_97_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit232. -/
theorem certificate_BlockUnit232 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 19 List.nil.{0})))) 20) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 20 List.nil.{0})))) 21) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 21 List.nil.{0})))) 22) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 22 List.nil.{0})))) 23) := by
  exact ⟨unit_16_19_closed, unit_16_20_closed, unit_16_21_closed, unit_16_22_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit233. -/
theorem certificate_BlockUnit233 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 24 List.nil.{0})))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 25 List.nil.{0})))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 26 List.nil.{0})))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 27 List.nil.{0})))) 28) := by
  exact ⟨unit_16_24_closed, unit_16_25_closed, unit_16_26_closed, unit_16_27_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit234. -/
theorem certificate_BlockUnit234 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 35 List.nil.{0})))) 36) := by
  exact ⟨unit_16_28_closed, unit_16_30_closed, unit_16_34_closed, unit_16_35_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit235. -/
theorem certificate_BlockUnit235 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 41 List.nil.{0})))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 45 List.nil.{0})))) 46) := by
  exact ⟨unit_16_36_closed, unit_16_40_closed, unit_16_41_closed, unit_16_44_closed, unit_16_45_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit236. -/
theorem certificate_BlockUnit236 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 49 List.nil.{0})))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 51 List.nil.{0})))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 53 List.nil.{0})))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 55 List.nil.{0})))) 56) := by
  exact ⟨unit_16_46_closed, unit_16_48_closed, unit_16_49_closed, unit_16_51_closed, unit_16_52_closed, unit_16_53_closed, unit_16_54_closed, unit_16_55_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit237. -/
theorem certificate_BlockUnit237 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 65 List.nil.{0})))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 67 List.nil.{0})))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 69 List.nil.{0})))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 71 List.nil.{0})))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 75 List.nil.{0})))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 79 List.nil.{0})))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 82 List.nil.{0})))) 83) := by
  exact ⟨unit_16_56_closed, unit_16_57_closed, unit_16_58_closed, unit_16_60_closed, unit_16_61_closed, unit_16_62_closed, unit_16_64_closed, unit_16_65_closed, unit_16_66_closed, unit_16_67_closed, unit_16_69_closed, unit_16_70_closed, unit_16_71_closed, unit_16_72_closed, unit_16_75_closed, unit_16_76_closed, unit_16_78_closed, unit_16_79_closed, unit_16_80_closed, unit_16_81_closed, unit_16_82_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit238. -/
theorem certificate_BlockUnit238 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 85 List.nil.{0})))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 91 List.nil.{0})))) 92) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 92 List.nil.{0})))) 93) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 94 List.nil.{0})))) 95) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 16 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 16 (List.cons.{0} 96 List.nil.{0})))) 97) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 21 List.nil.{0})))) 22) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 22 List.nil.{0})))) 23) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 23 List.nil.{0})))) 24) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 27 List.nil.{0})))) 28) := by
  exact ⟨unit_16_85_closed, unit_16_86_closed, unit_16_88_closed, unit_16_91_closed, unit_16_92_closed, unit_16_94_closed, unit_16_96_closed, unit_19_21_closed, unit_19_22_closed, unit_19_23_closed, unit_19_27_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit239. -/
theorem certificate_BlockUnit239 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 29 List.nil.{0})))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 33 List.nil.{0})))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 35 List.nil.{0})))) 36) := by
  exact ⟨unit_19_28_closed, unit_19_29_closed, unit_19_30_closed, unit_19_33_closed, unit_19_34_closed, unit_19_35_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit240. -/
theorem certificate_BlockUnit240 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 39 List.nil.{0})))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 41 List.nil.{0})))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 43 List.nil.{0})))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 47 List.nil.{0})))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 49 List.nil.{0})))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 53 List.nil.{0})))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 55 List.nil.{0})))) 56) := by
  exact ⟨unit_19_39_closed, unit_19_40_closed, unit_19_41_closed, unit_19_43_closed, unit_19_46_closed, unit_19_47_closed, unit_19_48_closed, unit_19_49_closed, unit_19_52_closed, unit_19_53_closed, unit_19_54_closed, unit_19_55_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit241. -/
theorem certificate_BlockUnit241 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 59 List.nil.{0})))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 65 List.nil.{0})))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 67 List.nil.{0})))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 71 List.nil.{0})))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 73 List.nil.{0})))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 77 List.nil.{0})))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 79 List.nil.{0})))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 85 List.nil.{0})))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 91 List.nil.{0})))) 92) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 19 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 19 (List.cons.{0} 93 List.nil.{0})))) 94) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 22 List.nil.{0})))) 23) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 23 List.nil.{0})))) 24) := by
  exact ⟨unit_19_58_closed, unit_19_59_closed, unit_19_60_closed, unit_19_61_closed, unit_19_65_closed, unit_19_66_closed, unit_19_67_closed, unit_19_68_closed, unit_19_71_closed, unit_19_72_closed, unit_19_73_closed, unit_19_74_closed, unit_19_77_closed, unit_19_79_closed, unit_19_80_closed, unit_19_81_closed, unit_19_85_closed, unit_19_86_closed, unit_19_87_closed, unit_19_90_closed, unit_19_91_closed, unit_19_93_closed, unit_20_22_closed, unit_20_23_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit242. -/
theorem certificate_BlockUnit242 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 24 List.nil.{0})))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 25 List.nil.{0})))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 29 List.nil.{0})))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 31 List.nil.{0})))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 35 List.nil.{0})))) 36) := by
  exact ⟨unit_20_24_closed, unit_20_25_closed, unit_20_28_closed, unit_20_29_closed, unit_20_30_closed, unit_20_31_closed, unit_20_34_closed, unit_20_35_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit243. -/
theorem certificate_BlockUnit243 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 41 List.nil.{0})))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 43 List.nil.{0})))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 49 List.nil.{0})))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 53 List.nil.{0})))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 55 List.nil.{0})))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 63 List.nil.{0})))) 64) := by
  exact ⟨unit_20_36_closed, unit_20_41_closed, unit_20_42_closed, unit_20_43_closed, unit_20_44_closed, unit_20_48_closed, unit_20_49_closed, unit_20_50_closed, unit_20_53_closed, unit_20_54_closed, unit_20_55_closed, unit_20_56_closed, unit_20_60_closed, unit_20_61_closed, unit_20_62_closed, unit_20_63_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit244. -/
theorem certificate_BlockUnit244 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 67 List.nil.{0})))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 69 List.nil.{0})))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 73 List.nil.{0})))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 75 List.nil.{0})))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 91 List.nil.{0})))) 92) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 92 List.nil.{0})))) 93) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 20 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 20 (List.cons.{0} 94 List.nil.{0})))) 95) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 23 List.nil.{0})))) 24) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 24 List.nil.{0})))) 25) := by
  exact ⟨unit_20_66_closed, unit_20_67_closed, unit_20_68_closed, unit_20_69_closed, unit_20_72_closed, unit_20_73_closed, unit_20_74_closed, unit_20_75_closed, unit_20_78_closed, unit_20_80_closed, unit_20_81_closed, unit_20_82_closed, unit_20_86_closed, unit_20_91_closed, unit_20_92_closed, unit_20_94_closed, unit_21_23_closed, unit_21_24_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit245. -/
theorem certificate_BlockUnit245 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 25 List.nil.{0})))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 26 List.nil.{0})))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 27 List.nil.{0})))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 30 List.nil.{0})))) 31) := by
  exact ⟨unit_21_25_closed, unit_21_26_closed, unit_21_27_closed, unit_21_30_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit246. -/
theorem certificate_BlockUnit246 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 31 List.nil.{0})))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 33 List.nil.{0})))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 36 List.nil.{0})))) 37) := by
  exact ⟨unit_21_31_closed, unit_21_33_closed, unit_21_34_closed, unit_21_35_closed, unit_21_36_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit247. -/
theorem certificate_BlockUnit247 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 39 List.nil.{0})))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 43 List.nil.{0})))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 45 List.nil.{0})))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 49 List.nil.{0})))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 51 List.nil.{0})))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 52 List.nil.{0})))) 53) := by
  exact ⟨unit_21_39_closed, unit_21_40_closed, unit_21_43_closed, unit_21_45_closed, unit_21_46_closed, unit_21_48_closed, unit_21_49_closed, unit_21_51_closed, unit_21_52_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit248. -/
theorem certificate_BlockUnit248 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 53 List.nil.{0})))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 55 List.nil.{0})))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 59 List.nil.{0})))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 63 List.nil.{0})))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 65 List.nil.{0})))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 67 List.nil.{0})))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 69 List.nil.{0})))) 70) := by
  exact ⟨unit_21_53_closed, unit_21_54_closed, unit_21_55_closed, unit_21_56_closed, unit_21_57_closed, unit_21_58_closed, unit_21_59_closed, unit_21_60_closed, unit_21_61_closed, unit_21_63_closed, unit_21_64_closed, unit_21_65_closed, unit_21_66_closed, unit_21_67_closed, unit_21_69_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit249. -/
theorem certificate_BlockUnit249 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 75 List.nil.{0})))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 77 List.nil.{0})))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 79 List.nil.{0})))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 85 List.nil.{0})))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 89 List.nil.{0})))) 90) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 21 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 21 (List.cons.{0} 93 List.nil.{0})))) 94) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 24 List.nil.{0})))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 25 List.nil.{0})))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 26 List.nil.{0})))) 27) := by
  exact ⟨unit_21_70_closed, unit_21_72_closed, unit_21_75_closed, unit_21_76_closed, unit_21_77_closed, unit_21_78_closed, unit_21_79_closed, unit_21_81_closed, unit_21_82_closed, unit_21_85_closed, unit_21_86_closed, unit_21_87_closed, unit_21_88_closed, unit_21_89_closed, unit_21_90_closed, unit_21_93_closed, unit_22_24_closed, unit_22_25_closed, unit_22_26_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit250. -/
theorem certificate_BlockUnit250 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 27 List.nil.{0})))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 31 List.nil.{0})))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 35 List.nil.{0})))) 36) := by
  exact ⟨unit_22_27_closed, unit_22_28_closed, unit_22_31_closed, unit_22_32_closed, unit_22_34_closed, unit_22_35_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit251. -/
theorem certificate_BlockUnit251 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 39 List.nil.{0})))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 41 List.nil.{0})))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 45 List.nil.{0})))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 47 List.nil.{0})))) 48) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 52 List.nil.{0})))) 53) := by
  exact ⟨unit_22_36_closed, unit_22_39_closed, unit_22_40_closed, unit_22_41_closed, unit_22_45_closed, unit_22_46_closed, unit_22_47_closed, unit_22_50_closed, unit_22_52_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit252. -/
theorem certificate_BlockUnit252 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 55 List.nil.{0})))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 59 List.nil.{0})))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 63 List.nil.{0})))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 73 List.nil.{0})))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 76 List.nil.{0})))) 77) := by
  exact ⟨unit_22_54_closed, unit_22_55_closed, unit_22_56_closed, unit_22_57_closed, unit_22_58_closed, unit_22_59_closed, unit_22_60_closed, unit_22_61_closed, unit_22_62_closed, unit_22_63_closed, unit_22_64_closed, unit_22_66_closed, unit_22_68_closed, unit_22_70_closed, unit_22_72_closed, unit_22_73_closed, unit_22_76_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit253. -/
theorem certificate_BlockUnit253 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 77 List.nil.{0})))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 79 List.nil.{0})))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 85 List.nil.{0})))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 22 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 22 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 25 List.nil.{0})))) 26) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 27 List.nil.{0})))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 29 List.nil.{0})))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 39 List.nil.{0})))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 47 List.nil.{0})))) 48) := by
  exact ⟨unit_22_77_closed, unit_22_78_closed, unit_22_79_closed, unit_22_80_closed, unit_22_81_closed, unit_22_82_closed, unit_22_85_closed, unit_22_86_closed, unit_22_87_closed, unit_22_88_closed, unit_23_25_closed, unit_23_27_closed, unit_23_29_closed, unit_23_32_closed, unit_23_35_closed, unit_23_39_closed, unit_23_40_closed, unit_23_42_closed, unit_23_44_closed, unit_23_47_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit254. -/
theorem certificate_BlockUnit254 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 49 List.nil.{0})))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 53 List.nil.{0})))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 55 List.nil.{0})))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 63 List.nil.{0})))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 65 List.nil.{0})))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 67 List.nil.{0})))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 71 List.nil.{0})))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 73 List.nil.{0})))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 75 List.nil.{0})))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 85 List.nil.{0})))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 23 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 23 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 26 List.nil.{0})))) 27) := by
  exact ⟨unit_23_49_closed, unit_23_52_closed, unit_23_53_closed, unit_23_55_closed, unit_23_57_closed, unit_23_58_closed, unit_23_60_closed, unit_23_63_closed, unit_23_65_closed, unit_23_67_closed, unit_23_70_closed, unit_23_71_closed, unit_23_73_closed, unit_23_75_closed, unit_23_78_closed, unit_23_80_closed, unit_23_81_closed, unit_23_85_closed, unit_23_86_closed, unit_24_26_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit255. -/
theorem certificate_BlockUnit255 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 31 List.nil.{0})))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 33 List.nil.{0})))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 41 List.nil.{0})))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 43 List.nil.{0})))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 45 List.nil.{0})))) 46) := by
  exact ⟨unit_24_28_closed, unit_24_30_closed, unit_24_31_closed, unit_24_33_closed, unit_24_36_closed, unit_24_40_closed, unit_24_41_closed, unit_24_43_closed, unit_24_45_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit256. -/
theorem certificate_BlockUnit256 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 49 List.nil.{0})))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 51 List.nil.{0})))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 53 List.nil.{0})))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 59 List.nil.{0})))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 63 List.nil.{0})))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 69 List.nil.{0})))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 73 List.nil.{0})))) 74) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 77 List.nil.{0})))) 78) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 79 List.nil.{0})))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 24 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 24 (List.cons.{0} 89 List.nil.{0})))) 90) := by
  exact ⟨unit_24_46_closed, unit_24_49_closed, unit_24_51_closed, unit_24_53_closed, unit_24_54_closed, unit_24_56_closed, unit_24_58_closed, unit_24_59_closed, unit_24_61_closed, unit_24_63_closed, unit_24_64_closed, unit_24_66_closed, unit_24_68_closed, unit_24_69_closed, unit_24_73_closed, unit_24_76_closed, unit_24_77_closed, unit_24_79_closed, unit_24_81_closed, unit_24_82_closed, unit_24_86_closed, unit_24_89_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit257. -/
theorem certificate_BlockUnit257 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 27 List.nil.{0})))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 31 List.nil.{0})))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 33 List.nil.{0})))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 35 List.nil.{0})))) 36) := by
  exact ⟨unit_25_27_closed, unit_25_28_closed, unit_25_30_closed, unit_25_31_closed, unit_25_33_closed, unit_25_34_closed, unit_25_35_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit258. -/
theorem certificate_BlockUnit258 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 39 List.nil.{0})))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 41 List.nil.{0})))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 45 List.nil.{0})))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 51 List.nil.{0})))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 55 List.nil.{0})))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 58 List.nil.{0})))) 59) := by
  exact ⟨unit_25_36_closed, unit_25_39_closed, unit_25_40_closed, unit_25_41_closed, unit_25_45_closed, unit_25_46_closed, unit_25_51_closed, unit_25_52_closed, unit_25_55_closed, unit_25_56_closed, unit_25_57_closed, unit_25_58_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit259. -/
theorem certificate_BlockUnit259 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 59 List.nil.{0})))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 63 List.nil.{0})))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 65 List.nil.{0})))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 69 List.nil.{0})))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 71 List.nil.{0})))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 75 List.nil.{0})))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 79 List.nil.{0})))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 85 List.nil.{0})))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 25 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 25 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 29 List.nil.{0})))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 31 List.nil.{0})))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 33 List.nil.{0})))) 34) := by
  exact ⟨unit_25_59_closed, unit_25_60_closed, unit_25_61_closed, unit_25_63_closed, unit_25_64_closed, unit_25_65_closed, unit_25_66_closed, unit_25_69_closed, unit_25_70_closed, unit_25_71_closed, unit_25_75_closed, unit_25_76_closed, unit_25_79_closed, unit_25_80_closed, unit_25_81_closed, unit_25_82_closed, unit_25_85_closed, unit_25_87_closed, unit_26_28_closed, unit_26_29_closed, unit_26_31_closed, unit_26_32_closed, unit_26_33_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit260. -/
theorem certificate_BlockUnit260 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 43 List.nil.{0})))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 53 List.nil.{0})))) 54) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 59 List.nil.{0})))) 60) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 65 List.nil.{0})))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 75 List.nil.{0})))) 76) := by
  exact ⟨unit_26_34_closed, unit_26_35_closed, unit_26_36_closed, unit_26_40_closed, unit_26_42_closed, unit_26_43_closed, unit_26_46_closed, unit_26_53_closed, unit_26_56_closed, unit_26_57_closed, unit_26_58_closed, unit_26_59_closed, unit_26_60_closed, unit_26_61_closed, unit_26_62_closed, unit_26_64_closed, unit_26_65_closed, unit_26_66_closed, unit_26_70_closed, unit_26_72_closed, unit_26_75_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit261. -/
theorem certificate_BlockUnit261 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 26 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 26 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 29 List.nil.{0})))) 30) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 33 List.nil.{0})))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 39 List.nil.{0})))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 41 List.nil.{0})))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 45 List.nil.{0})))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 51 List.nil.{0})))) 52) := by
  exact ⟨unit_26_76_closed, unit_26_80_closed, unit_26_81_closed, unit_26_82_closed, unit_26_86_closed, unit_27_29_closed, unit_27_30_closed, unit_27_32_closed, unit_27_33_closed, unit_27_35_closed, unit_27_36_closed, unit_27_39_closed, unit_27_41_closed, unit_27_44_closed, unit_27_45_closed, unit_27_51_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit262. -/
theorem certificate_BlockUnit262 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 55 List.nil.{0})))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 63 List.nil.{0})))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 65 List.nil.{0})))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 67 List.nil.{0})))) 68) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 69 List.nil.{0})))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 75 List.nil.{0})))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 79 List.nil.{0})))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 81 List.nil.{0})))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 27 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 27 (List.cons.{0} 85 List.nil.{0})))) 86) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 31 List.nil.{0})))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 33 List.nil.{0})))) 34) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 34 List.nil.{0})))) 35) := by
  exact ⟨unit_27_52_closed, unit_27_55_closed, unit_27_56_closed, unit_27_57_closed, unit_27_60_closed, unit_27_61_closed, unit_27_63_closed, unit_27_65_closed, unit_27_66_closed, unit_27_67_closed, unit_27_69_closed, unit_27_72_closed, unit_27_75_closed, unit_27_78_closed, unit_27_79_closed, unit_27_81_closed, unit_27_82_closed, unit_27_85_closed, unit_28_30_closed, unit_28_31_closed, unit_28_33_closed, unit_28_34_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit263. -/
theorem certificate_BlockUnit263 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 39 List.nil.{0})))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 41 List.nil.{0})))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 43 List.nil.{0})))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 45 List.nil.{0})))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 49 List.nil.{0})))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 61 List.nil.{0})))) 62) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 63 List.nil.{0})))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 69 List.nil.{0})))) 70) := by
  exact ⟨unit_28_36_closed, unit_28_39_closed, unit_28_40_closed, unit_28_41_closed, unit_28_43_closed, unit_28_45_closed, unit_28_46_closed, unit_28_49_closed, unit_28_52_closed, unit_28_54_closed, unit_28_57_closed, unit_28_58_closed, unit_28_60_closed, unit_28_61_closed, unit_28_63_closed, unit_28_64_closed, unit_28_66_closed, unit_28_68_closed, unit_28_69_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit264. -/
theorem certificate_BlockUnit264 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 28 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 28 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 29 4
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 29 List.nil.{0}))) 30) := by
  exact ⟨unit_28_70_closed, unit_28_76_closed, unit_28_80_closed, unit_28_82_closed, unit_29_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit266. -/
theorem certificate_BlockUnit266 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 31 4
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 31 List.nil.{0}))) 32) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 32 4
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 32 List.nil.{0}))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 36 List.nil.{0})))) 37) := by
  exact ⟨unit_31_closed, unit_32_closed, unit_33_35_closed, unit_33_36_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit267. -/
theorem certificate_BlockUnit267 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 39 List.nil.{0})))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 41 List.nil.{0})))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 43 List.nil.{0})))) 44) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 45 List.nil.{0})))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 49 List.nil.{0})))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 51 List.nil.{0})))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 55 List.nil.{0})))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 63 List.nil.{0})))) 64) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 69 List.nil.{0})))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 71 List.nil.{0})))) 72) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 75 List.nil.{0})))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 79 List.nil.{0})))) 80) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 33 3
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 33 (List.cons.{0} 81 List.nil.{0})))) 82) := by
  exact ⟨unit_33_39_closed, unit_33_40_closed, unit_33_41_closed, unit_33_43_closed, unit_33_45_closed, unit_33_49_closed, unit_33_51_closed, unit_33_54_closed, unit_33_55_closed, unit_33_57_closed, unit_33_58_closed, unit_33_60_closed, unit_33_63_closed, unit_33_64_closed, unit_33_69_closed, unit_33_70_closed, unit_33_71_closed, unit_33_75_closed, unit_33_79_closed, unit_33_81_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit272. -/
theorem certificate_BlockUnit272 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 40 4
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 40 List.nil.{0}))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 41 4
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 41 List.nil.{0}))) 42) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 42 4
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 42 List.nil.{0}))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 43 4
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 43 List.nil.{0}))) 44) := by
  exact ⟨unit_40_closed, unit_41_closed, unit_42_closed, unit_43_closed⟩

/-- All prefix exclusions in bounded certificate BlockUnit273. -/
theorem certificate_BlockUnit273 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 44 4
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 44 List.nil.{0}))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 45 4
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 45 List.nil.{0}))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 46 4
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 46 List.nil.{0}))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 49 4
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 49 List.nil.{0}))) 50) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 50 4
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 50 List.nil.{0}))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 51 4
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 51 List.nil.{0}))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 52 4
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 52 List.nil.{0}))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 55 4
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 55 List.nil.{0}))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 56 4
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 56 List.nil.{0}))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix true 120 57 4
  (List.cons.{0} 0 (List.cons.{0} 1 (List.cons.{0} 57 List.nil.{0}))) 58) := by
  exact ⟨unit_44_closed, unit_45_closed, unit_46_closed, unit_49_closed, unit_50_closed, unit_51_closed, unit_52_closed, unit_55_closed, unit_56_closed, unit_57_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit274. -/
theorem certificate_BlockNonunit274 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 14 List.nil.{0})))) 15) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 20 List.nil.{0})))) 21) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 26 List.nil.{0})))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 27 List.nil.{0})))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 30 List.nil.{0})))) 31) := by
  exact ⟨nonunit_2_5_14_closed, nonunit_2_5_20_closed, nonunit_2_5_26_closed, nonunit_2_5_27_closed, nonunit_2_5_30_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit275. -/
theorem certificate_BlockNonunit275 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 38 List.nil.{0})))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 65 List.nil.{0})))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 70 List.nil.{0})))) 71) := by
  exact ⟨nonunit_2_5_32_closed, nonunit_2_5_35_closed, nonunit_2_5_38_closed, nonunit_2_5_40_closed, nonunit_2_5_44_closed, nonunit_2_5_50_closed, nonunit_2_5_56_closed, nonunit_2_5_60_closed, nonunit_2_5_62_closed, nonunit_2_5_65_closed, nonunit_2_5_68_closed, nonunit_2_5_70_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit276. -/
theorem certificate_BlockNonunit276 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 5 (List.cons.{0} 92 List.nil.{0})))) 93) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 14 List.nil.{0})))) 15) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 18 List.nil.{0})))) 19) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 20 List.nil.{0})))) 21) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 22 List.nil.{0})))) 23) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 24 List.nil.{0})))) 25) := by
  exact ⟨nonunit_2_5_74_closed, nonunit_2_5_80_closed, nonunit_2_5_86_closed, nonunit_2_5_90_closed, nonunit_2_5_92_closed, nonunit_2_6_14_closed, nonunit_2_6_18_closed, nonunit_2_6_20_closed, nonunit_2_6_22_closed, nonunit_2_6_24_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit277. -/
theorem certificate_BlockNonunit277 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 26 List.nil.{0})))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 27 List.nil.{0})))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 38 List.nil.{0})))) 39) := by
  exact ⟨nonunit_2_6_26_closed, nonunit_2_6_27_closed, nonunit_2_6_28_closed, nonunit_2_6_30_closed, nonunit_2_6_32_closed, nonunit_2_6_34_closed, nonunit_2_6_36_closed, nonunit_2_6_38_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit278. -/
theorem certificate_BlockNonunit278 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 84 List.nil.{0})))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 87 List.nil.{0})))) 88) := by
  exact ⟨nonunit_2_6_40_closed, nonunit_2_6_42_closed, nonunit_2_6_44_closed, nonunit_2_6_46_closed, nonunit_2_6_48_closed, nonunit_2_6_50_closed, nonunit_2_6_52_closed, nonunit_2_6_54_closed, nonunit_2_6_56_closed, nonunit_2_6_57_closed, nonunit_2_6_58_closed, nonunit_2_6_60_closed, nonunit_2_6_62_closed, nonunit_2_6_66_closed, nonunit_2_6_68_closed, nonunit_2_6_70_closed, nonunit_2_6_72_closed, nonunit_2_6_74_closed, nonunit_2_6_76_closed, nonunit_2_6_78_closed, nonunit_2_6_80_closed, nonunit_2_6_82_closed, nonunit_2_6_84_closed, nonunit_2_6_86_closed, nonunit_2_6_87_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit279. -/
theorem certificate_BlockNonunit279 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 6 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 12 List.nil.{0})))) 13) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 18 List.nil.{0})))) 19) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 20 List.nil.{0})))) 21) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 24 List.nil.{0})))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 26 List.nil.{0})))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 32 List.nil.{0})))) 33) := by
  exact ⟨nonunit_2_6_90_closed, nonunit_2_8_12_closed, nonunit_2_8_18_closed, nonunit_2_8_20_closed, nonunit_2_8_24_closed, nonunit_2_8_26_closed, nonunit_2_8_28_closed, nonunit_2_8_30_closed, nonunit_2_8_32_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit280. -/
theorem certificate_BlockNonunit280 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 38 List.nil.{0})))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 84 List.nil.{0})))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 92 List.nil.{0})))) 93) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 8 (List.cons.{0} 95 List.nil.{0})))) 96) := by
  exact ⟨nonunit_2_8_34_closed, nonunit_2_8_35_closed, nonunit_2_8_36_closed, nonunit_2_8_38_closed, nonunit_2_8_40_closed, nonunit_2_8_42_closed, nonunit_2_8_44_closed, nonunit_2_8_46_closed, nonunit_2_8_48_closed, nonunit_2_8_50_closed, nonunit_2_8_52_closed, nonunit_2_8_54_closed, nonunit_2_8_56_closed, nonunit_2_8_58_closed, nonunit_2_8_60_closed, nonunit_2_8_62_closed, nonunit_2_8_66_closed, nonunit_2_8_68_closed, nonunit_2_8_70_closed, nonunit_2_8_72_closed, nonunit_2_8_74_closed, nonunit_2_8_76_closed, nonunit_2_8_78_closed, nonunit_2_8_80_closed, nonunit_2_8_82_closed, nonunit_2_8_84_closed, nonunit_2_8_86_closed, nonunit_2_8_92_closed, nonunit_2_8_95_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit281. -/
theorem certificate_BlockNonunit281 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 14 List.nil.{0})))) 15) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 16 List.nil.{0})))) 17) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 22 List.nil.{0})))) 23) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 24 List.nil.{0})))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 26 List.nil.{0})))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 36 List.nil.{0})))) 37) := by
  exact ⟨nonunit_2_10_14_closed, nonunit_2_10_16_closed, nonunit_2_10_22_closed, nonunit_2_10_24_closed, nonunit_2_10_26_closed, nonunit_2_10_30_closed, nonunit_2_10_32_closed, nonunit_2_10_34_closed, nonunit_2_10_35_closed, nonunit_2_10_36_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit282. -/
theorem certificate_BlockNonunit282 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 38 List.nil.{0})))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 92 List.nil.{0})))) 93) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 10 (List.cons.{0} 95 List.nil.{0})))) 96) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 16 List.nil.{0})))) 17) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 18 List.nil.{0})))) 19) := by
  exact ⟨nonunit_2_10_38_closed, nonunit_2_10_40_closed, nonunit_2_10_42_closed, nonunit_2_10_46_closed, nonunit_2_10_48_closed, nonunit_2_10_50_closed, nonunit_2_10_52_closed, nonunit_2_10_54_closed, nonunit_2_10_56_closed, nonunit_2_10_58_closed, nonunit_2_10_60_closed, nonunit_2_10_62_closed, nonunit_2_10_64_closed, nonunit_2_10_68_closed, nonunit_2_10_70_closed, nonunit_2_10_72_closed, nonunit_2_10_74_closed, nonunit_2_10_76_closed, nonunit_2_10_78_closed, nonunit_2_10_80_closed, nonunit_2_10_82_closed, nonunit_2_10_86_closed, nonunit_2_10_88_closed, nonunit_2_10_90_closed, nonunit_2_10_92_closed, nonunit_2_10_95_closed, nonunit_2_12_16_closed, nonunit_2_12_18_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit283. -/
theorem certificate_BlockNonunit283 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 20 List.nil.{0})))) 21) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 26 List.nil.{0})))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 27 List.nil.{0})))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 38 List.nil.{0})))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 46 List.nil.{0})))) 47) := by
  exact ⟨nonunit_2_12_20_closed, nonunit_2_12_26_closed, nonunit_2_12_27_closed, nonunit_2_12_28_closed, nonunit_2_12_30_closed, nonunit_2_12_32_closed, nonunit_2_12_36_closed, nonunit_2_12_38_closed, nonunit_2_12_40_closed, nonunit_2_12_42_closed, nonunit_2_12_44_closed, nonunit_2_12_46_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit284. -/
theorem certificate_BlockNonunit284 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 84 List.nil.{0})))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 12 (List.cons.{0} 92 List.nil.{0})))) 93) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 18 List.nil.{0})))) 19) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 20 List.nil.{0})))) 21) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 22 List.nil.{0})))) 23) := by
  exact ⟨nonunit_2_12_48_closed, nonunit_2_12_50_closed, nonunit_2_12_52_closed, nonunit_2_12_54_closed, nonunit_2_12_56_closed, nonunit_2_12_57_closed, nonunit_2_12_58_closed, nonunit_2_12_60_closed, nonunit_2_12_62_closed, nonunit_2_12_64_closed, nonunit_2_12_68_closed, nonunit_2_12_70_closed, nonunit_2_12_72_closed, nonunit_2_12_74_closed, nonunit_2_12_76_closed, nonunit_2_12_78_closed, nonunit_2_12_80_closed, nonunit_2_12_82_closed, nonunit_2_12_84_closed, nonunit_2_12_86_closed, nonunit_2_12_87_closed, nonunit_2_12_88_closed, nonunit_2_12_90_closed, nonunit_2_12_92_closed, nonunit_2_14_18_closed, nonunit_2_14_20_closed, nonunit_2_14_22_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit285. -/
theorem certificate_BlockNonunit285 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 24 List.nil.{0})))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 38 List.nil.{0})))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 56 List.nil.{0})))) 57) := by
  exact ⟨nonunit_2_14_24_closed, nonunit_2_14_30_closed, nonunit_2_14_32_closed, nonunit_2_14_34_closed, nonunit_2_14_35_closed, nonunit_2_14_36_closed, nonunit_2_14_38_closed, nonunit_2_14_42_closed, nonunit_2_14_44_closed, nonunit_2_14_46_closed, nonunit_2_14_48_closed, nonunit_2_14_50_closed, nonunit_2_14_52_closed, nonunit_2_14_54_closed, nonunit_2_14_56_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit286. -/
theorem certificate_BlockNonunit286 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 65 List.nil.{0})))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 84 List.nil.{0})))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 92 List.nil.{0})))) 93) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 14 (List.cons.{0} 94 List.nil.{0})))) 95) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 20 List.nil.{0})))) 21) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 22 List.nil.{0})))) 23) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 24 List.nil.{0})))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 26 List.nil.{0})))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 38 List.nil.{0})))) 39) := by
  exact ⟨nonunit_2_14_58_closed, nonunit_2_14_60_closed, nonunit_2_14_62_closed, nonunit_2_14_64_closed, nonunit_2_14_65_closed, nonunit_2_14_66_closed, nonunit_2_14_70_closed, nonunit_2_14_72_closed, nonunit_2_14_74_closed, nonunit_2_14_76_closed, nonunit_2_14_78_closed, nonunit_2_14_80_closed, nonunit_2_14_82_closed, nonunit_2_14_84_closed, nonunit_2_14_86_closed, nonunit_2_14_88_closed, nonunit_2_14_90_closed, nonunit_2_14_92_closed, nonunit_2_14_94_closed, nonunit_2_16_20_closed, nonunit_2_16_22_closed, nonunit_2_16_24_closed, nonunit_2_16_26_closed, nonunit_2_16_28_closed, nonunit_2_16_34_closed, nonunit_2_16_36_closed, nonunit_2_16_38_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit287. -/
theorem certificate_BlockNonunit287 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 84 List.nil.{0})))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 16 (List.cons.{0} 92 List.nil.{0})))) 93) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 22 List.nil.{0})))) 23) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 24 List.nil.{0})))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 26 List.nil.{0})))) 27) := by
  exact ⟨nonunit_2_16_40_closed, nonunit_2_16_42_closed, nonunit_2_16_44_closed, nonunit_2_16_48_closed, nonunit_2_16_50_closed, nonunit_2_16_52_closed, nonunit_2_16_54_closed, nonunit_2_16_56_closed, nonunit_2_16_58_closed, nonunit_2_16_60_closed, nonunit_2_16_62_closed, nonunit_2_16_64_closed, nonunit_2_16_66_closed, nonunit_2_16_70_closed, nonunit_2_16_72_closed, nonunit_2_16_74_closed, nonunit_2_16_76_closed, nonunit_2_16_78_closed, nonunit_2_16_80_closed, nonunit_2_16_82_closed, nonunit_2_16_84_closed, nonunit_2_16_88_closed, nonunit_2_16_90_closed, nonunit_2_16_92_closed, nonunit_2_18_22_closed, nonunit_2_18_24_closed, nonunit_2_18_26_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit288. -/
theorem certificate_BlockNonunit288 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 27 List.nil.{0})))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 38 List.nil.{0})))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 57 List.nil.{0})))) 58) := by
  exact ⟨nonunit_2_18_27_closed, nonunit_2_18_28_closed, nonunit_2_18_30_closed, nonunit_2_18_32_closed, nonunit_2_18_38_closed, nonunit_2_18_40_closed, nonunit_2_18_42_closed, nonunit_2_18_44_closed, nonunit_2_18_46_closed, nonunit_2_18_48_closed, nonunit_2_18_50_closed, nonunit_2_18_54_closed, nonunit_2_18_56_closed, nonunit_2_18_57_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit289. -/
theorem certificate_BlockNonunit289 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 84 List.nil.{0})))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 18 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 24 List.nil.{0})))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 26 List.nil.{0})))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 34 List.nil.{0})))) 35) := by
  exact ⟨nonunit_2_18_58_closed, nonunit_2_18_60_closed, nonunit_2_18_62_closed, nonunit_2_18_64_closed, nonunit_2_18_66_closed, nonunit_2_18_68_closed, nonunit_2_18_72_closed, nonunit_2_18_74_closed, nonunit_2_18_76_closed, nonunit_2_18_78_closed, nonunit_2_18_80_closed, nonunit_2_18_82_closed, nonunit_2_18_84_closed, nonunit_2_18_86_closed, nonunit_2_18_87_closed, nonunit_2_18_88_closed, nonunit_2_18_90_closed, nonunit_2_20_24_closed, nonunit_2_20_26_closed, nonunit_2_20_28_closed, nonunit_2_20_30_closed, nonunit_2_20_32_closed, nonunit_2_20_34_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit290. -/
theorem certificate_BlockNonunit290 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 65 List.nil.{0})))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 84 List.nil.{0})))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 90 List.nil.{0})))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 20 (List.cons.{0} 92 List.nil.{0})))) 93) := by
  exact ⟨nonunit_2_20_35_closed, nonunit_2_20_36_closed, nonunit_2_20_42_closed, nonunit_2_20_44_closed, nonunit_2_20_46_closed, nonunit_2_20_48_closed, nonunit_2_20_50_closed, nonunit_2_20_52_closed, nonunit_2_20_54_closed, nonunit_2_20_56_closed, nonunit_2_20_60_closed, nonunit_2_20_62_closed, nonunit_2_20_64_closed, nonunit_2_20_65_closed, nonunit_2_20_66_closed, nonunit_2_20_68_closed, nonunit_2_20_72_closed, nonunit_2_20_74_closed, nonunit_2_20_76_closed, nonunit_2_20_78_closed, nonunit_2_20_80_closed, nonunit_2_20_82_closed, nonunit_2_20_84_closed, nonunit_2_20_86_closed, nonunit_2_20_88_closed, nonunit_2_20_90_closed, nonunit_2_20_92_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit291. -/
theorem certificate_BlockNonunit291 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 26 List.nil.{0})))) 27) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 27 List.nil.{0})))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 38 List.nil.{0})))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 78 List.nil.{0})))) 79) := by
  exact ⟨nonunit_2_22_26_closed, nonunit_2_22_27_closed, nonunit_2_22_28_closed, nonunit_2_22_30_closed, nonunit_2_22_32_closed, nonunit_2_22_34_closed, nonunit_2_22_36_closed, nonunit_2_22_38_closed, nonunit_2_22_40_closed, nonunit_2_22_46_closed, nonunit_2_22_50_closed, nonunit_2_22_52_closed, nonunit_2_22_54_closed, nonunit_2_22_56_closed, nonunit_2_22_57_closed, nonunit_2_22_58_closed, nonunit_2_22_60_closed, nonunit_2_22_62_closed, nonunit_2_22_66_closed, nonunit_2_22_68_closed, nonunit_2_22_70_closed, nonunit_2_22_74_closed, nonunit_2_22_76_closed, nonunit_2_22_78_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit292. -/
theorem certificate_BlockNonunit292 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 22 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 27 List.nil.{0})))) 28) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 28 List.nil.{0})))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 38 List.nil.{0})))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 60 List.nil.{0})))) 61) := by
  exact ⟨nonunit_2_22_80_closed, nonunit_2_22_82_closed, nonunit_2_22_86_closed, nonunit_2_22_87_closed, nonunit_2_24_27_closed, nonunit_2_24_28_closed, nonunit_2_24_30_closed, nonunit_2_24_32_closed, nonunit_2_24_34_closed, nonunit_2_24_36_closed, nonunit_2_24_38_closed, nonunit_2_24_40_closed, nonunit_2_24_42_closed, nonunit_2_24_44_closed, nonunit_2_24_50_closed, nonunit_2_24_52_closed, nonunit_2_24_54_closed, nonunit_2_24_56_closed, nonunit_2_24_57_closed, nonunit_2_24_58_closed, nonunit_2_24_60_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit293. -/
theorem certificate_BlockNonunit293 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 76 List.nil.{0})))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 84 List.nil.{0})))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 24 (List.cons.{0} 88 List.nil.{0})))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 30 List.nil.{0})))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 32 List.nil.{0})))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 38 List.nil.{0})))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 46 List.nil.{0})))) 47) := by
  exact ⟨nonunit_2_24_62_closed, nonunit_2_24_64_closed, nonunit_2_24_66_closed, nonunit_2_24_68_closed, nonunit_2_24_74_closed, nonunit_2_24_76_closed, nonunit_2_24_78_closed, nonunit_2_24_80_closed, nonunit_2_24_84_closed, nonunit_2_24_87_closed, nonunit_2_24_88_closed, nonunit_2_26_30_closed, nonunit_2_26_32_closed, nonunit_2_26_34_closed, nonunit_2_26_35_closed, nonunit_2_26_36_closed, nonunit_2_26_38_closed, nonunit_2_26_40_closed, nonunit_2_26_42_closed, nonunit_2_26_44_closed, nonunit_2_26_46_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit294. -/
theorem certificate_BlockNonunit294 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 65 List.nil.{0})))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 26 (List.cons.{0} 90 List.nil.{0})))) 91) := by
  exact ⟨nonunit_2_26_48_closed, nonunit_2_26_54_closed, nonunit_2_26_56_closed, nonunit_2_26_58_closed, nonunit_2_26_60_closed, nonunit_2_26_62_closed, nonunit_2_26_64_closed, nonunit_2_26_65_closed, nonunit_2_26_66_closed, nonunit_2_26_68_closed, nonunit_2_26_70_closed, nonunit_2_26_72_closed, nonunit_2_26_78_closed, nonunit_2_26_80_closed, nonunit_2_26_82_closed, nonunit_2_26_86_closed, nonunit_2_26_90_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit296. -/
theorem certificate_BlockNonunit296 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 28 List.nil.{0}))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 34 List.nil.{0})))) 35) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 35 List.nil.{0})))) 36) := by
  exact ⟨nonunit_2_28_closed, nonunit_2_30_34_closed, nonunit_2_30_35_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit297. -/
theorem certificate_BlockNonunit297 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 38 List.nil.{0})))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 62 List.nil.{0})))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 64 List.nil.{0})))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 65 List.nil.{0})))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 66 List.nil.{0})))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 84 List.nil.{0})))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 86 List.nil.{0})))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 87 List.nil.{0})))) 88) := by
  exact ⟨nonunit_2_30_36_closed, nonunit_2_30_38_closed, nonunit_2_30_40_closed, nonunit_2_30_42_closed, nonunit_2_30_44_closed, nonunit_2_30_46_closed, nonunit_2_30_48_closed, nonunit_2_30_50_closed, nonunit_2_30_52_closed, nonunit_2_30_54_closed, nonunit_2_30_56_closed, nonunit_2_30_57_closed, nonunit_2_30_62_closed, nonunit_2_30_64_closed, nonunit_2_30_65_closed, nonunit_2_30_66_closed, nonunit_2_30_68_closed, nonunit_2_30_70_closed, nonunit_2_30_72_closed, nonunit_2_30_74_closed, nonunit_2_30_78_closed, nonunit_2_30_80_closed, nonunit_2_30_82_closed, nonunit_2_30_84_closed, nonunit_2_30_86_closed, nonunit_2_30_87_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit298. -/
theorem certificate_BlockNonunit298 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 30 (List.cons.{0} 95 List.nil.{0})))) 96) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 35 List.nil.{0})))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 36 List.nil.{0})))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 38 List.nil.{0})))) 39) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 40 List.nil.{0})))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 42 List.nil.{0})))) 43) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 44 List.nil.{0})))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 46 List.nil.{0})))) 47) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 48 List.nil.{0})))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 50 List.nil.{0})))) 51) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 52 List.nil.{0})))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 54 List.nil.{0})))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 56 List.nil.{0})))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 57 List.nil.{0})))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 58 List.nil.{0})))) 59) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 60 List.nil.{0})))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 65 List.nil.{0})))) 66) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 66 List.nil.{0})))) 67) := by
  exact ⟨nonunit_2_30_95_closed, nonunit_2_32_35_closed, nonunit_2_32_36_closed, nonunit_2_32_38_closed, nonunit_2_32_40_closed, nonunit_2_32_42_closed, nonunit_2_32_44_closed, nonunit_2_32_46_closed, nonunit_2_32_48_closed, nonunit_2_32_50_closed, nonunit_2_32_52_closed, nonunit_2_32_54_closed, nonunit_2_32_56_closed, nonunit_2_32_57_closed, nonunit_2_32_58_closed, nonunit_2_32_60_closed, nonunit_2_32_65_closed, nonunit_2_32_66_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit299. -/
theorem certificate_BlockNonunit299 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 68 List.nil.{0})))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 70 List.nil.{0})))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 72 List.nil.{0})))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 74 List.nil.{0})))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 78 List.nil.{0})))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 80 List.nil.{0})))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 82 List.nil.{0})))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 84 List.nil.{0})))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 87 List.nil.{0})))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 95 List.nil.{0})))) 96) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 3
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 32 (List.cons.{0} 96 List.nil.{0})))) 97) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 34 List.nil.{0}))) 35) := by
  exact ⟨nonunit_2_32_68_closed, nonunit_2_32_70_closed, nonunit_2_32_72_closed, nonunit_2_32_74_closed, nonunit_2_32_78_closed, nonunit_2_32_80_closed, nonunit_2_32_82_closed, nonunit_2_32_84_closed, nonunit_2_32_87_closed, nonunit_2_32_95_closed, nonunit_2_32_96_closed, nonunit_2_34_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit305. -/
theorem certificate_BlockNonunit305 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 44 List.nil.{0}))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 46 List.nil.{0}))) 47) := by
  exact ⟨nonunit_2_44_closed, nonunit_2_46_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit306. -/
theorem certificate_BlockNonunit306 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 48 List.nil.{0}))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 50 List.nil.{0}))) 51) := by
  exact ⟨nonunit_2_48_closed, nonunit_2_50_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit307. -/
theorem certificate_BlockNonunit307 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 52 List.nil.{0}))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 54 List.nil.{0}))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 56 List.nil.{0}))) 57) := by
  exact ⟨nonunit_2_52_closed, nonunit_2_54_closed, nonunit_2_56_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit308. -/
theorem certificate_BlockNonunit308 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 57 List.nil.{0}))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 58 List.nil.{0}))) 59) := by
  exact ⟨nonunit_2_57_closed, nonunit_2_58_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit310. -/
theorem certificate_BlockNonunit310 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 62 List.nil.{0}))) 63) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 64 List.nil.{0}))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 65 List.nil.{0}))) 66) := by
  exact ⟨nonunit_2_62_closed, nonunit_2_64_closed, nonunit_2_65_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit311. -/
theorem certificate_BlockNonunit311 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 66 List.nil.{0}))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 68 List.nil.{0}))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 70 List.nil.{0}))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 72 List.nil.{0}))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 74 List.nil.{0}))) 75) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 76 List.nil.{0}))) 77) := by
  exact ⟨nonunit_2_66_closed, nonunit_2_68_closed, nonunit_2_70_closed, nonunit_2_72_closed, nonunit_2_74_closed, nonunit_2_76_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit312. -/
theorem certificate_BlockNonunit312 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 78 List.nil.{0}))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 80 List.nil.{0}))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 82 List.nil.{0}))) 83) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 84 List.nil.{0}))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 86 List.nil.{0}))) 87) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 87 List.nil.{0}))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 88 List.nil.{0}))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 90 List.nil.{0}))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 92 List.nil.{0}))) 93) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 94 List.nil.{0}))) 95) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 95 List.nil.{0}))) 96) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 96 List.nil.{0}))) 97) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 2 4
  (List.cons.{0} 0 (List.cons.{0} 2 (List.cons.{0} 98 List.nil.{0}))) 99) := by
  exact ⟨nonunit_2_78_closed, nonunit_2_80_closed, nonunit_2_82_closed, nonunit_2_84_closed, nonunit_2_86_closed, nonunit_2_87_closed, nonunit_2_88_closed, nonunit_2_90_closed, nonunit_2_92_closed, nonunit_2_94_closed, nonunit_2_95_closed, nonunit_2_96_closed, nonunit_2_98_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit314. -/
theorem certificate_BlockNonunit314 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 9 List.nil.{0}))) 10) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 12 List.nil.{0}))) 13) := by
  exact ⟨nonunit_3_9_closed, nonunit_3_12_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit315. -/
theorem certificate_BlockNonunit315 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 15 List.nil.{0}))) 16) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 18 List.nil.{0}))) 19) := by
  exact ⟨nonunit_3_15_closed, nonunit_3_18_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit316. -/
theorem certificate_BlockNonunit316 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 21 List.nil.{0}))) 22) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 24 List.nil.{0}))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 27 List.nil.{0}))) 28) := by
  exact ⟨nonunit_3_21_closed, nonunit_3_24_closed, nonunit_3_27_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit317. -/
theorem certificate_BlockNonunit317 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 28 List.nil.{0}))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 30 List.nil.{0}))) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 33 List.nil.{0}))) 34) := by
  exact ⟨nonunit_3_28_closed, nonunit_3_30_closed, nonunit_3_33_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit318. -/
theorem certificate_BlockNonunit318 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 35 List.nil.{0}))) 36) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 36 List.nil.{0}))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 39 List.nil.{0}))) 40) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 42 List.nil.{0}))) 43) := by
  exact ⟨nonunit_3_35_closed, nonunit_3_36_closed, nonunit_3_39_closed, nonunit_3_42_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit319. -/
theorem certificate_BlockNonunit319 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 45 List.nil.{0}))) 46) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 48 List.nil.{0}))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 51 List.nil.{0}))) 52) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 54 List.nil.{0}))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 55 List.nil.{0}))) 56) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 57 List.nil.{0}))) 58) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 60 List.nil.{0}))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 63 List.nil.{0}))) 64) := by
  exact ⟨nonunit_3_45_closed, nonunit_3_48_closed, nonunit_3_51_closed, nonunit_3_54_closed, nonunit_3_55_closed, nonunit_3_57_closed, nonunit_3_60_closed, nonunit_3_63_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit320. -/
theorem certificate_BlockNonunit320 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 66 List.nil.{0}))) 67) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 68 List.nil.{0}))) 69) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 69 List.nil.{0}))) 70) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 72 List.nil.{0}))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 75 List.nil.{0}))) 76) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 78 List.nil.{0}))) 79) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 81 List.nil.{0}))) 82) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 84 List.nil.{0}))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 87 List.nil.{0}))) 88) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 88 List.nil.{0}))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 90 List.nil.{0}))) 91) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 93 List.nil.{0}))) 94) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 3 4
  (List.cons.{0} 0 (List.cons.{0} 3 (List.cons.{0} 95 List.nil.{0}))) 96) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 10 List.nil.{0}))) 11) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 12 List.nil.{0}))) 13) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 16 List.nil.{0}))) 17) := by
  exact ⟨nonunit_3_66_closed, nonunit_3_68_closed, nonunit_3_69_closed, nonunit_3_72_closed, nonunit_3_75_closed, nonunit_3_78_closed, nonunit_3_81_closed, nonunit_3_84_closed, nonunit_3_87_closed, nonunit_3_88_closed, nonunit_3_90_closed, nonunit_3_93_closed, nonunit_3_95_closed, nonunit_4_10_closed, nonunit_4_12_closed, nonunit_4_16_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit321. -/
theorem certificate_BlockNonunit321 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 20 List.nil.{0}))) 21) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 24 List.nil.{0}))) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 28 List.nil.{0}))) 29) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 32 List.nil.{0}))) 33) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 36 List.nil.{0}))) 37) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 40 List.nil.{0}))) 41) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 44 List.nil.{0}))) 45) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 48 List.nil.{0}))) 49) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 52 List.nil.{0}))) 53) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 54 List.nil.{0}))) 55) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 56 List.nil.{0}))) 57) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 60 List.nil.{0}))) 61) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 64 List.nil.{0}))) 65) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 68 List.nil.{0}))) 69) := by
  exact ⟨nonunit_4_20_closed, nonunit_4_24_closed, nonunit_4_28_closed, nonunit_4_32_closed, nonunit_4_36_closed, nonunit_4_40_closed, nonunit_4_44_closed, nonunit_4_48_closed, nonunit_4_52_closed, nonunit_4_54_closed, nonunit_4_56_closed, nonunit_4_60_closed, nonunit_4_64_closed, nonunit_4_68_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit322. -/
theorem certificate_BlockNonunit322 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 70 List.nil.{0}))) 71) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 72 List.nil.{0}))) 73) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 76 List.nil.{0}))) 77) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 80 List.nil.{0}))) 81) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 84 List.nil.{0}))) 85) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 4 4
  (List.cons.{0} 0 (List.cons.{0} 4 (List.cons.{0} 88 List.nil.{0}))) 89) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 5 5 (List.cons.{0} 0 (List.cons.{0} 5 List.nil.{0})) 6) := by
  exact ⟨nonunit_4_70_closed, nonunit_4_72_closed, nonunit_4_76_closed, nonunit_4_80_closed, nonunit_4_84_closed, nonunit_4_88_closed, nonunit_5_closed⟩

/-- All prefix exclusions in bounded certificate BlockNonunit323. -/
theorem certificate_BlockNonunit323 :
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 6 5 (List.cons.{0} 0 (List.cons.{0} 6 List.nil.{0})) 7) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 8 5 (List.cons.{0} 0 (List.cons.{0} 8 List.nil.{0})) 9) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 10 5 (List.cons.{0} 0 (List.cons.{0} 10 List.nil.{0})) 11) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 12 5 (List.cons.{0} 0 (List.cons.{0} 12 List.nil.{0})) 13) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 15 5 (List.cons.{0} 0 (List.cons.{0} 15 List.nil.{0})) 16) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 20 5 (List.cons.{0} 0 (List.cons.{0} 20 List.nil.{0})) 21) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 24 5 (List.cons.{0} 0 (List.cons.{0} 24 List.nil.{0})) 25) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 30 5 (List.cons.{0} 0 (List.cons.{0} 30 List.nil.{0})) 31) ∧
    (MinModulus.PrefixCertificate.ClosedMinimalPrefix false 120 40 5 (List.cons.{0} 0 (List.cons.{0} 40 List.nil.{0})) 41) := by
  exact ⟨nonunit_6_closed, nonunit_8_closed, nonunit_10_closed, nonunit_12_closed, nonunit_15_closed, nonunit_20_closed, nonunit_24_closed, nonunit_30_closed, nonunit_40_closed⟩

end MinModulus.PrefixCertificate.Seven120

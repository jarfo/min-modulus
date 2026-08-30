import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_27 : List ℕ := [17, 521, 261, 131, 3785, 2485, 4227, 642, 85, 643, 772, 2626, 402, 2308, 153, 2786, 403, 2631, 589, 773, 1347, 2468, 4232, 4234, 4387, 4884, 1548, 89, 3756, 3912, 770, 387, 1827, 386, 5045, 1667, 465, 771, 2954, 898, 526, 449, 705, 4885]

private theorem valid53_27 : ∀ code ∈ codes53_27, validRelationCode code := by
  decide

private theorem cover53_27 : ∀ q : IncreasingFourTail 51 (⟨27, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_27 (increasingFourValues (N := 53) ⟨⟨27, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a27
    (q : IncreasingFourTail 51 (⟨27, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨27, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_27 _ valid53_27 (cover53_27 q)

end MinModulus.SHCFiveCertificate.Generated

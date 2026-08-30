import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_31 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 589, 403, 4387, 4227, 4232, 2786, 2631, 2308, 85, 153, 773, 643, 386, 1347, 1667, 770, 3907, 387, 1827]

private theorem valid53_31 : ∀ code ∈ codes53_31, validRelationCode code := by
  decide

private theorem cover53_31 : ∀ q : IncreasingFourTail 51 (⟨31, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_31 (increasingFourValues (N := 53) ⟨⟨31, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a31
    (q : IncreasingFourTail 51 (⟨31, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨31, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_31 _ valid53_31 (cover53_31 q)

end MinModulus.SHCFiveCertificate.Generated

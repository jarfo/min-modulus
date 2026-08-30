import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_30 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 153, 4232, 773, 403, 643, 4387, 2786, 2631, 2468, 4884, 4234, 14, 1507, 387, 3906, 1827, 3765, 1907, 770, 771, 5505]

private theorem valid53_30 : ∀ code ∈ codes53_30, validRelationCode code := by
  decide

private theorem cover53_30 : ∀ q : IncreasingFourTail 51 (⟨30, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_30 (increasingFourValues (N := 53) ⟨⟨30, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a30
    (q : IncreasingFourTail 51 (⟨30, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨30, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_30 _ valid53_30 (cover53_30 q)

end MinModulus.SHCFiveCertificate.Generated

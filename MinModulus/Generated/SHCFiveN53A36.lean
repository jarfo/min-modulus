import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_36 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 77, 2631, 3911, 153, 773]

private theorem valid53_36 : ∀ code ∈ codes53_36, validRelationCode code := by
  decide

private theorem cover53_36 : ∀ q : IncreasingFourTail 51 (⟨36, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_36 (increasingFourValues (N := 53) ⟨⟨36, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a36
    (q : IncreasingFourTail 51 (⟨36, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨36, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_36 _ valid53_36 (cover53_36 q)

end MinModulus.SHCFiveCertificate.Generated

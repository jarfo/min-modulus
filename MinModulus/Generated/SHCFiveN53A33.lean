import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_33 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 403, 4387, 402, 589, 4227, 4232, 2786, 2631, 2308, 85, 153, 773, 643, 1347, 386, 1667]

private theorem valid53_33 : ∀ code ∈ codes53_33, validRelationCode code := by
  decide

private theorem cover53_33 : ∀ q : IncreasingFourTail 51 (⟨33, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_33 (increasingFourValues (N := 53) ⟨⟨33, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a33
    (q : IncreasingFourTail 51 (⟨33, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨33, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_33 _ valid53_33 (cover53_33 q)

end MinModulus.SHCFiveCertificate.Generated

import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_32 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 153, 4232, 773, 403, 643, 4387, 2786, 2631, 2468, 89, 2866, 5191, 898, 387]

private theorem valid53_32 : ∀ code ∈ codes53_32, validRelationCode code := by
  decide

private theorem cover53_32 : ∀ q : IncreasingFourTail 51 (⟨32, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_32 (increasingFourValues (N := 53) ⟨⟨32, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a32
    (q : IncreasingFourTail 51 (⟨32, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨32, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_32 _ valid53_32 (cover53_32 q)

end MinModulus.SHCFiveCertificate.Generated

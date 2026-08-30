import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_23 : List ℕ := [17, 521, 261, 131, 7, 6, 193, 1984, 3585, 3745, 1865, 2545, 4227, 465, 2476, 773, 2468, 4544, 643, 4885, 772, 85, 23, 705, 642, 22, 2308, 526, 4387, 4232, 3344, 403, 527, 1828, 3264, 2786, 402, 589, 1346, 1827, 2866, 4066, 3786, 2626, 89, 387, 771, 27]

private theorem valid53_23 : ∀ code ∈ codes53_23, validRelationCode code := by
  decide

private theorem cover53_23 : ∀ q : IncreasingFourTail 51 (⟨23, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_23 (increasingFourValues (N := 53) ⟨⟨23, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a23
    (q : IncreasingFourTail 51 (⟨23, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨23, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_23 _ valid53_23 (cover53_23 q)

end MinModulus.SHCFiveCertificate.Generated

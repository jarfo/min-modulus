import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_22 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 1984, 3585, 3745, 1865, 2545, 4227, 772, 2308, 773, 2468, 4387, 4232, 153, 4884, 402, 2626, 642, 85, 589, 2465, 1905, 2631, 833, 1868, 1828, 386, 770, 705, 465, 321, 2706, 713, 209, 2624, 4425, 2305, 643, 2648, 23, 1506, 2476, 4584, 14, 527, 5186, 449, 771]

private theorem valid53_22 : ∀ code ∈ codes53_22, validRelationCode code := by
  decide

private theorem cover53_22 : ∀ q : IncreasingFourTail 51 (⟨22, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_22 (increasingFourValues (N := 53) ⟨⟨22, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a22
    (q : IncreasingFourTail 51 (⟨22, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨22, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_22 _ valid53_22 (cover53_22 q)

end MinModulus.SHCFiveCertificate.Generated

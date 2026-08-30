import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_24 : List ℕ := [6, 193, 17, 521, 261, 1984, 1865, 2545, 3745, 772, 22, 2786, 1507, 526, 4227, 2308, 402, 642, 2626, 773, 4387, 465, 705, 2476, 153, 4232, 2468, 589, 4884, 2631, 386, 85, 2706, 3906, 26, 449, 4544, 14, 961, 89]

private theorem valid53_24 : ∀ code ∈ codes53_24, validRelationCode code := by
  decide

private theorem cover53_24 : ∀ q : IncreasingFourTail 51 (⟨24, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_24 (increasingFourValues (N := 53) ⟨⟨24, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a24
    (q : IncreasingFourTail 51 (⟨24, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨24, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_24 _ valid53_24 (cover53_24 q)

end MinModulus.SHCFiveCertificate.Generated

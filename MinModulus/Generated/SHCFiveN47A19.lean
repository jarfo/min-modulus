import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_19 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 1984, 3585, 3745, 4227, 1865, 2545, 772, 2308, 773, 2468, 4387, 4232, 153, 642, 402, 465, 4885, 2626, 85, 4544, 705, 2476, 10, 278, 2706, 209, 713, 3906, 321, 386, 526, 2624, 2305, 77, 4584, 22, 14, 3344]

private theorem valid47_19 : ∀ code ∈ codes47_19, validRelationCode code := by
  decide

private theorem cover47_19 : ∀ q : IncreasingFourTail 45 (⟨19, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_19 (increasingFourValues (N := 47) ⟨⟨19, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a19
    (q : IncreasingFourTail 45 (⟨19, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨19, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_19 _ valid47_19 (cover47_19 q)

end MinModulus.SHCFiveCertificate.Generated

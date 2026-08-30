import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_19 : List ℕ := [17, 521, 261, 131, 1186, 772, 4227, 2308, 153, 773, 402, 4387, 4232, 642, 2468, 2626, 2631, 2786, 589, 85, 643, 1347, 403, 4884, 4234, 7, 1905, 2465, 4425, 713, 4584, 321, 209, 2624, 2064, 518, 2305, 4265, 10, 278, 1984, 519, 193, 3273, 1187, 1346, 11, 3585, 279, 1827, 1828, 1868, 2808, 6, 526, 1825, 22, 705, 3757, 465, 201, 833, 385, 12, 898, 770, 30, 93, 897, 771, 2944]

private theorem valid53_19 : ∀ code ∈ codes53_19, validRelationCode code := by
  decide

private theorem cover53_19 : ∀ q : IncreasingFourTail 51 (⟨19, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_19 (increasingFourValues (N := 53) ⟨⟨19, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a19
    (q : IncreasingFourTail 51 (⟨19, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨19, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_19 _ valid53_19 (cover53_19 q)

end MinModulus.SHCFiveCertificate.Generated

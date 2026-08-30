import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_15 : List ℕ := [17, 521, 261, 131, 1186, 772, 4584, 4265, 402, 278, 713, 4425, 589, 403, 279, 153, 773, 4884, 1868, 4227, 2626, 4232, 2468, 4387, 2308, 642, 10, 518, 209, 321, 2786, 1905, 2305, 2465, 643, 519, 2631, 193, 85, 11, 1984, 2624, 1825, 2546, 1187, 201, 385, 1665, 2808, 12, 6, 526, 30]

private theorem valid45_15 : ∀ code ∈ codes45_15, validRelationCode code := by
  decide

private theorem cover45_15 : ∀ q : IncreasingFourTail 43 (⟨15, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_15 (increasingFourValues (N := 45) ⟨⟨15, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a15
    (q : IncreasingFourTail 43 (⟨15, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨15, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_15 _ valid45_15 (cover45_15 q)

end MinModulus.SHCFiveCertificate.Generated

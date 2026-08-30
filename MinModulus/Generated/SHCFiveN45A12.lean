import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_12 : List ℕ := [17, 521, 261, 131, 772, 402, 279, 278, 713, 4425, 4265, 4584, 589, 403, 153, 773, 4884, 1868, 1186, 642, 2626, 4227, 2308, 2468, 4232, 643, 2786, 2631, 4387, 85, 11, 4234, 2624, 10, 321, 18, 1905, 209, 2465, 2064, 518, 2305, 1187, 3586, 2148, 193, 3585, 775, 3118, 12, 519, 1825, 28, 1984, 1865, 3745, 5191, 770, 262, 837, 2227, 386, 6, 385, 641, 769, 26, 22, 961, 337, 401, 387, 3904]

private theorem valid45_12 : ∀ code ∈ codes45_12, validRelationCode code := by
  decide

private theorem cover45_12 : ∀ q : IncreasingFourTail 43 (⟨12, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_12 (increasingFourValues (N := 45) ⟨⟨12, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a12
    (q : IncreasingFourTail 43 (⟨12, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨12, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_12 _ valid45_12 (cover45_12 q)

end MinModulus.SHCFiveCertificate.Generated

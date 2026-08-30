import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_19 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 772, 4227, 2308, 153, 773, 402, 4387, 4232, 642, 2468, 2626, 2631, 589, 85, 3585, 2786, 643, 4884, 403, 1347, 4234, 713, 1865, 10, 518, 209, 1905, 4425, 321, 2465, 278, 2545, 3745, 4265, 2305, 4544, 2624, 4584, 22, 1827, 526, 519, 1828, 770, 385, 3344, 1837, 26, 5036, 12, 465, 77, 899]

private theorem valid51_19 : ∀ code ∈ codes51_19, validRelationCode code := by
  decide

private theorem cover51_19 : ∀ q : IncreasingFourTail 49 (⟨19, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_19 (increasingFourValues (N := 51) ⟨⟨19, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a19
    (q : IncreasingFourTail 49 (⟨19, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨19, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_19 _ valid51_19 (cover51_19 q)

end MinModulus.SHCFiveCertificate.Generated

import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_21 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 1984, 3585, 3745, 1865, 2545, 4227, 772, 2308, 773, 2468, 4387, 4232, 153, 642, 402, 2626, 465, 2631, 85, 3757, 705, 2476, 1668, 589, 1667, 1868, 1905, 321, 2465, 209, 2624, 4884, 2305, 2866, 3273, 22, 898, 526, 713, 4584, 449, 89, 387, 643, 3344]

private theorem valid51_21 : ∀ code ∈ codes51_21, validRelationCode code := by
  decide

private theorem cover51_21 : ∀ q : IncreasingFourTail 49 (⟨21, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_21 (increasingFourValues (N := 51) ⟨⟨21, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a21
    (q : IncreasingFourTail 49 (⟨21, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨21, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_21 _ valid51_21 (cover51_21 q)

end MinModulus.SHCFiveCertificate.Generated

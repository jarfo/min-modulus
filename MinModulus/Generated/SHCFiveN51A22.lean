import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_22 : List ℕ := [17, 521, 261, 131, 7, 6, 193, 1984, 3585, 3745, 1865, 2545, 4227, 772, 465, 2476, 2308, 705, 3344, 526, 773, 2468, 4544, 4885, 5045, 4387, 4232, 527, 153, 403, 2706, 643, 1667, 1668, 402, 771, 642, 22, 449, 589, 2786, 3786, 386, 26]

private theorem valid51_22 : ∀ code ∈ codes51_22, validRelationCode code := by
  decide

private theorem cover51_22 : ∀ q : IncreasingFourTail 49 (⟨22, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_22 (increasingFourValues (N := 51) ⟨⟨22, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a22
    (q : IncreasingFourTail 49 (⟨22, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨22, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_22 _ valid51_22 (cover51_22 q)

end MinModulus.SHCFiveCertificate.Generated

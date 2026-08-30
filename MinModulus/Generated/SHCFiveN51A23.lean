import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_23 : List ℕ := [6, 193, 17, 521, 261, 1984, 1865, 2545, 3745, 772, 526, 22, 2786, 4227, 2308, 402, 642, 153, 4232, 1347, 2476, 2626, 2468, 705, 773, 465, 4387, 14, 589, 2631, 85, 386, 2866, 4884, 5045, 3906, 770]

private theorem valid51_23 : ∀ code ∈ codes51_23, validRelationCode code := by
  decide

private theorem cover51_23 : ∀ q : IncreasingFourTail 49 (⟨23, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_23 (increasingFourValues (N := 51) ⟨⟨23, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a23
    (q : IncreasingFourTail 49 (⟨23, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨23, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_23 _ valid51_23 (cover51_23 q)

end MinModulus.SHCFiveCertificate.Generated

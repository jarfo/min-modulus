import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_27 : List ℕ := [17, 521, 261, 131, 3785, 2485, 4227, 772, 2308, 643, 403, 2786, 642, 402, 2626, 153, 85, 2631, 589, 4232, 4387, 773, 1347, 2468, 3765, 4234, 3907, 770, 93, 4884, 1868, 2648, 89, 386, 899, 387, 4544]

private theorem valid51_27 : ∀ code ∈ codes51_27, validRelationCode code := by
  decide

private theorem cover51_27 : ∀ q : IncreasingFourTail 49 (⟨27, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_27 (increasingFourValues (N := 51) ⟨⟨27, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a27
    (q : IncreasingFourTail 49 (⟨27, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨27, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_27 _ valid51_27 (cover51_27 q)

end MinModulus.SHCFiveCertificate.Generated

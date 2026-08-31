/-
Axiom audit for the main results.  Run with

    lake env lean scripts/check_axioms.lean

Every declaration below must depend only on the three standard Lean axioms
`propext`, `Classical.choice`, `Quot.sound`.  In particular `sorryAx` must
never appear.  CI (`.github/workflows/build.yml`) fails the build if it does.
-/
import MinModulus

-- Theorem A (validity / upper bound), Theorem B (optimality / lower bound),
-- and the main theorem `Nmin(n) = 2^n - 2^⌊log₂ n⌋`.
#print axioms MinModulus.theoremA
#print axioms MinModulus.valid_gap
#print axioms MinModulus.theoremB
#print axioms MinModulus.nmin_eq

-- Proposition 2: optimality among elementary abelian 2-groups.
#print axioms MinModulus.elementaryAbelianTwoGroups_optimal

-- Inal's theorem (open problem 4): the exact minimum order for unique multiset
-- sums in finite abelian groups is `2^(n-1)`.
#print axioms MinModulus.card_ge          -- lower bound: valid ⟹ 2^m ≤ |G|
#print axioms MinModulus.elem_valid       -- sharpness: standard tuple is valid
#print axioms MinModulus.elem_card        -- the extremal group has order 2^m
#print axioms MinModulus.mab_isLeast      -- headline: m_ab(n) = 2^(n-1) (IsLeast)
#print axioms MinModulus.equality_classification  -- classification at equality
#print axioms MinModulus.equality_addEquiv        -- explicit φ : G ≃+ (ZMod 2)^m

-- Descent lemmas toward the global optimality conjecture (open problem 1):
-- combination and deletion for witnesses at an order-two element.
#print axioms MinModulus.validTuple_iff_no_zero_witness
#print axioms MinModulus.witness_combination        -- Lemma A
#print axioms MinModulus.common_touched_of_unique_omission
#print axioms MinModulus.three_witnesses_sum_ne_zero
#print axioms MinModulus.exists_pair_difference_witness
#print axioms MinModulus.validTuple_injective
#print axioms MinModulus.common_touched_of_pair_difference
#print axioms MinModulus.common_touched_of_two_smul_eq
#print axioms MinModulus.witness_compl_sum_eq_card_exactOmissions
#print axioms MinModulus.witness_coeff_bounds_of_exactOmissions
#print axioms MinModulus.witness_coeff_eq_zero_or_one_or_two_of_exact_pair
#print axioms MinModulus.exists_companion_one_of_exact_pair_coeff_one
#print axioms MinModulus.exists_coeff_two_of_same_exact_pair_zero_two
#print axioms MinModulus.two_smul_eq_of_same_exact_pair_coeff_two
#print axioms MinModulus.two_smul_eq_of_adjacent_triangle_same_companion
#print axioms MinModulus.common_touched_of_same_exact_pair_zero_two
#print axioms MinModulus.zmod_eq_zero_or_half_of_add_self_eq_zero
#print axioms MinModulus.triangle_opposite_coefficients_zero_one_or_two
#print axioms MinModulus.not_triangle_all_opposites_two
#print axioms MinModulus.witness_three_sum
#print axioms MinModulus.witness_neg_of_le_one
#print axioms MinModulus.witness_neg_pair_sum_at_zero_of_le_one
#print axioms MinModulus.witness_triangle_sum_of_positive_opposites
#print axioms MinModulus.triangle_one_one_two_sum_witness_zero_opposite
#print axioms MinModulus.triangle_all_one_sum_witness_exact_triple
#print axioms MinModulus.common_touched_of_triangle_one_one_two
#print axioms MinModulus.common_touched_of_triangle_one_one_two_zmod
#print axioms MinModulus.common_touched_of_triangle_all_one
#print axioms MinModulus.common_touched_of_triangle_all_one_zmod
#print axioms MinModulus.common_touched_of_two_adjacent_light_opposites
#print axioms MinModulus.common_touched_of_two_adjacent_light_opposites_zmod
#print axioms MinModulus.exists_pure_companion_two_of_triangle_zero_opposite
#print axioms MinModulus.two_smul_eq_target_add_pair_of_exact_pair_coeff_two
#print axioms MinModulus.pure_companions_ne_of_adjacent_zero_opposites
#print axioms MinModulus.exists_six_distinct_pure_centers_of_triangle_all_zero
#print axioms MinModulus.common_touched_of_three_sum_unique_omission
#print axioms MinModulus.common_touched_of_triangle_one_light_opposite
#print axioms MinModulus.exists_double_difference_eq_target_of_triangle_zero_two_two
#print axioms MinModulus.not_two_adjacent_heavy_opposites_of_involution
#print axioms MinModulus.not_two_adjacent_heavy_opposites_at_half_zmod
#print axioms MinModulus.three_smul_eq_of_two_adjacent_heavy_opposites
#print axioms MinModulus.not_two_adjacent_heavy_opposites_of_three_smul_injective
#print axioms MinModulus.nonzero_three_torsion_of_two_adjacent_heavy_opposites
#print axioms MinModulus.zmod_three_zsmul_injective
#print axioms MinModulus.not_two_adjacent_heavy_opposites_zmod
#print axioms MinModulus.three_dvd_of_two_adjacent_heavy_opposites_zmod
#print axioms MinModulus.four_dvd_of_double_eq_half
#print axioms MinModulus.twelve_dvd_of_triangle_zero_two_two_zmod
#print axioms MinModulus.zsmul_eq_zero_or_self_or_neg_of_order_three
#print axioms MinModulus.pair_descent_order_three
#print axioms MinModulus.exists_validTuple_quotient_of_two_adjacent_heavy_opposites
#print axioms MinModulus.nat_card_quotient_three_smul
#print axioms MinModulus.zmod_eq_third_or_two_thirds_of_order_three
#print axioms MinModulus.zmultiples_order_three_eq_third
#print axioms MinModulus.quotOrderThreeEquivZMod
#print axioms MinModulus.exists_validTuple_third_of_two_adjacent_heavy_opposites
#print axioms MinModulus.common_touched_of_triangle_positive
#print axioms MinModulus.common_touched_of_triangle_positive_zmod
#print axioms MinModulus.quotient_valid_of_no_witness  -- halving branch
#print axioms MinModulus.deletion_descent           -- Lemma B
#print axioms MinModulus.pair_descent               -- the clean descent rung
#print axioms MinModulus.nat_card_quotient_two_smul -- |G/⟨h⟩| * 2 = |G|
#print axioms MinModulus.validTuple_comp            -- transport along injective maps
#print axioms MinModulus.quotZMultiplesEquivZMod    -- ZMod N / <M>  ≃+  ZMod M
#print axioms MinModulus.exists_validTuple_half_of_no_witness  -- halving, cyclic
#print axioms MinModulus.exists_validTuple_half_of_delete      -- deletion, cyclic
#print axioms MinModulus.exists_validTuple_half_of_pair        -- pair descent, cyclic
#print axioms MinModulus.card_ge_of_odd     -- odd order: |G| >= 2^m + 2m (m >= 3)
#print axioms MinModulus.validTuple_cons_zero_iff_no_diff_relation
#print axioms MinModulus.card_ge_of_odd'    -- odd order: |G| >= 2^m + m
#print axioms MinModulus.valid_odd_zmod_bound
#print axioms MinModulus.odd_min_three      -- least odd valid modulus = 7 for n = 3
#print axioms MinModulus.odd_min_four       -- least odd valid modulus = 15 for n = 4 (G2, n <= 4)
#print axioms MinModulus.chain_card_bound   -- the SI-shape chain pins |G| >= 2^(m+1) - 1
#print axioms MinModulus.chain_order_eq
#print axioms MinModulus.chain_quotient_card_bound
#print axioms MinModulus.chain_mem_zmultiples
#print axioms MinModulus.chain_quotient_card_bound_of_joint_dissociated
#print axioms MinModulus.codim_one_chain_odd_card_bound
#print axioms MinModulus.addOrderOf_eq_mersenne_of_le
#print axioms MinModulus.mersenne_certificate_order_eq
#print axioms MinModulus.mersenne_certificate_card_bound
#print axioms MinModulus.mersenne_certificate_card_bound_of_span
#print axioms MinModulus.det_zsmul_eq_zero_of_matrixRelations
#print axioms MinModulus.torsion15RelationMatrix_det
#print axioms MinModulus.mersenne_card_bound_of_relation_matrix
#print axioms MinModulus.torsion15_relation_card_bound
#print axioms MinModulus.SHC.comp_embedding
#print axioms MinModulus.SHC.delete
#print axioms MinModulus.SHC.subtype
#print axioms MinModulus.addSubgroup_eq_top_of_mersenne_window
#print axioms MinModulus.shc_deleted_span_eq_top
#print axioms MinModulus.SHC.map_addEquiv
#print axioms MinModulus.SHC.reindex_equiv
#print axioms MinModulus.SHC.normalize_generator
#print axioms MinModulus.not_exists_shc_of_normalized
#print axioms MinModulus.normalizedSHCFourExcluded_of_sorted
#print axioms MinModulus.normalized_shc_four_excluded_seventeen
#print axioms MinModulus.normalized_shc_four_excluded_nineteen
#print axioms MinModulus.normalized_shc_four_excluded_twenty_one
#print axioms MinModulus.normalized_shc_four_excluded_twenty_three
#print axioms MinModulus.normalized_shc_four_excluded_twenty_five
#print axioms MinModulus.normalized_shc_four_excluded_twenty_seven
#print axioms MinModulus.normalized_shc_four_excluded_twenty_nine
#print axioms MinModulus.normalized_shc_four_excluded_of_odd_window
#print axioms MinModulus.not_exists_shc_fin_three_zmod_nine
#print axioms MinModulus.not_exists_shc_fin_three_zmod_eleven
#print axioms MinModulus.not_exists_shc_fin_three_zmod_thirteen
#print axioms MinModulus.cyclicSHCOddLowerBound_three
#print axioms MinModulus.shc_four_deleted_span_eq_top
#print axioms MinModulus.zmod_generator_of_isUnit
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_prime
#print axioms MinModulus.exists_isUnit_of_span_eq_top
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_twenty_one
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_twenty_five
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_twenty_seven
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_of_odd_window
#print axioms MinModulus.not_exists_shc_fin_four_zmod_of_odd_window
#print axioms MinModulus.cyclicSHCOddLowerBound_four
#print axioms MinModulus.odd_min_five
#print axioms MinModulus.shc_five_deleted_span_eq_top
#print axioms MinModulus.shc_index_card_lt_of_cyclic_lower_bound
#print axioms MinModulus.shc_index_card_lt_of_dissociation
#print axioms MinModulus.hasGeneratorCoordinate_of_index_cover
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_thirty_three
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_thirty_five
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_thirty_nine
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_forty_nine
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_fifty_one
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_fifty_five
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_fifty_seven
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_prime_five
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_five_of_odd_window_ne_forty_five
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_forty_five
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_five_of_odd_window
#print axioms MinModulus.SHCFiveCertificate.relationZeroNat_not_shc
#print axioms MinModulus.normalized_shc_five_excluded_thirty_three
#print axioms MinModulus.normalized_shc_five_excluded_thirty_five
#print axioms MinModulus.normalized_shc_five_excluded_thirty_seven
#print axioms MinModulus.normalized_shc_five_excluded_thirty_nine
#print axioms MinModulus.normalized_shc_five_excluded_forty_one
#print axioms MinModulus.normalized_shc_five_excluded_of_odd_window_le_forty_one
#print axioms MinModulus.normalized_shc_five_excluded_forty_three
#print axioms MinModulus.normalized_shc_five_excluded_forty_five
#print axioms MinModulus.normalized_shc_five_excluded_forty_seven
#print axioms MinModulus.normalized_shc_five_excluded_of_odd_window_le_forty_seven
#print axioms MinModulus.normalized_shc_five_excluded_forty_nine
#print axioms MinModulus.normalized_shc_five_excluded_fifty_one
#print axioms MinModulus.normalized_shc_five_excluded_fifty_three
#print axioms MinModulus.normalized_shc_five_excluded_of_odd_window_le_fifty_three
#print axioms MinModulus.normalized_shc_five_excluded_fifty_five
#print axioms MinModulus.normalized_shc_five_excluded_fifty_seven
#print axioms MinModulus.normalized_shc_five_excluded_fifty_nine
#print axioms MinModulus.normalized_shc_five_excluded_of_odd_window_le_fifty_nine
#print axioms MinModulus.normalized_shc_five_excluded_sixty_one
#print axioms MinModulus.normalized_shc_five_excluded_of_odd_window
#print axioms MinModulus.not_exists_shc_fin_five_zmod_of_odd_window
#print axioms MinModulus.cyclicSHCOddLowerBound_five
#print axioms MinModulus.odd_min_six
#print axioms MinModulus.shc_six_deleted_span_eq_top
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_prime_six
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_six_of_odd_window_ne_exceptions
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_six_seventy_five
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_six_ninety_nine
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_six_one_hundred_seventeen
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_six_of_odd_window_ne_one_hundred_five
#print axioms MinModulus.SHCSixExceptionalCertificate.relationZeroNat_not_shc
#print axioms MinModulus.SHCSixExceptionalCertificate.Generated.certificate105
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_six_one_hundred_five
#print axioms MinModulus.shc_hasGeneratorCoordinate_zmod_six_of_odd_window
#print axioms MinModulus.SHCSixCertificate.relationZeroNat_not_shc
#print axioms MinModulus.SHCSixCertificate.Generated.certificate67
#print axioms MinModulus.shc_card_ge_cube_add_doubles
#print axioms MinModulus.shc_card_ge_cube_add_two_doubles
#print axioms MinModulus.normalized_shc_six_excluded_of_lt_seventy_six
#print axioms MinModulus.normalized_shc_six_excluded_sixty_five
#print axioms MinModulus.normalized_shc_six_excluded_sixty_seven
#print axioms MinModulus.normalized_shc_six_excluded_of_odd_window_le_sixty_seven
#print axioms MinModulus.SHCSixCertificate.Generated.certificate69
#print axioms MinModulus.normalized_shc_six_excluded_sixty_nine
#print axioms MinModulus.normalized_shc_six_excluded_of_odd_window_le_sixty_nine
#print axioms MinModulus.normalized_shc_six_excluded_of_odd_window_le_seventy_five
#print axioms MinModulus.bottom_wedge       -- the bottom wedge: 2^(m+1) + m <= 2|G| + 2
#print axioms MinModulus.survival22        -- two (2,2)-reps of one value: |M1∩P2| + |M2∩P1| >= 2
#print axioms MinModulus.cluster22         -- pairwise-surviving families have <= 13 members
#print axioms MinModulus.quadratic_wedge   -- C(m,2) <= 3(m + (|G| - 2^m) + 14)
#print axioms MinModulus.shc_diff_of_valid
#print axioms MinModulus.bottom_wedge_of_valid
#print axioms MinModulus.quadratic_wedge_of_valid
#print axioms MinModulus.valid_odd_zmod_bottom_wedge
#print axioms MinModulus.valid_odd_zmod_quadratic_wedge
#print axioms MinModulus.shc_shift_target_card_gt
#print axioms MinModulus.card_le_of_two_smul_add_sum_eq
#print axioms MinModulus.admits_half_or_delete_of_g1
#print axioms MinModulus.validTuple_fixed_of_valid
#print axioms MinModulus.admitsValidTuple_gap
#print axioms MinModulus.stratum_lower_bound_of_gaps
#print axioms MinModulus.global_lower_bound_of_gaps

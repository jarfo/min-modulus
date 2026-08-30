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
#print axioms MinModulus.not_exists_shc_fin_three_zmod_nine
#print axioms MinModulus.not_exists_shc_fin_three_zmod_eleven
#print axioms MinModulus.not_exists_shc_fin_three_zmod_thirteen
#print axioms MinModulus.cyclicSHCOddLowerBound_three
#print axioms MinModulus.shc_four_deleted_span_eq_top
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

/-
# Exact multiset representations on a pointed Mersenne leaf

The canonical pointed leaf cycle in the exact-Mersenne C1 residual is an
affine copy of the super-increasing digits.  The exact digit-sum theorem from
`UniqueSums` therefore represents every nonzero element of the cyclic leaf
direction by a rival size-`d` multiset on those leaves.

This module makes that passage explicit in three reusable layers: a natural
multiset equality, its signed `Witness` form, and zero-extension to the
ambient tuple along an injective pointed leaf map.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneFiveExternalRows
import MinModulus.G1PrivateHeavyJointFiberAlgebra

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- An affine Mersenne leaf cycle realizes every nonzero cyclic target as a
size-`d` multiset difference. -/
theorem exists_mersenneLeaf_exactMultisetRepresentation
    {d s : ℕ} (hd : 3 ≤ d) (hs0 : 0 < s) (hsq : s < 2 ^ d - 1)
    (root v : G) (hv : addOrderOf v = 2 ^ d - 1)
    (h : Fin d → G) (hnormal : ∀ i, h i = root + a i.val • v) :
    ∃ k : Fin d → ℕ,
      (∑ i, k i) = d ∧
      (∑ i, k i • h i) = (∑ i, h i) + s • v := by
  obtain ⟨k₀, hk₀, hkval⟩ :=
    exists_exact_dsum_rep_modEq_mersenne hd hs0 hsq
  let k : Fin d → ℕ := fun i ↦ k₀ i.val
  have hksum : (∑ i, k i) = d := by
    rw [Fin.sum_univ_eq_sum_range]
    exact hk₀
  let A : ℕ := ∑ i : Fin d, k i * a i.val
  let U : ℕ := ∑ i : Fin d, a i.val
  have hkA : A + d = val d k₀ := by
    have h := sum_a_add_dsum d k₀
    rw [hk₀] at h
    change (∑ i : Fin d, k₀ i.val * a i.val) + d = val d k₀
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ k₀ i * a i) d]
    exact h
  have hdones : dsum d (fun _ ↦ 1) = d := by
    simp [dsum]
  have hvones : val d (fun _ ↦ 1) = 2 ^ d - 1 := by
    unfold val
    simpa only [one_mul] using sum_two_pow d
  have hUA : U + d = 2 ^ d - 1 := by
    have h := sum_a_add_dsum d (fun _ ↦ 1)
    rw [hdones, hvones] at h
    change (∑ i : Fin d, a i.val) + d = 2 ^ d - 1
    rw [Fin.sum_univ_eq_sum_range a d]
    simpa only [one_mul] using h
  have hcoeffmod : A ≡ U + s [MOD 2 ^ d - 1] := by
    apply Nat.ModEq.add_right_cancel' d
    rw [hkA]
    have hperiod : (2 ^ d - 1) + s ≡ s [MOD 2 ^ d - 1] := by
      have hm : (2 ^ d - 1) * 1 + s ≡ s [MOD 2 ^ d - 1] :=
        Nat.ModEq.modulus_mul_add
      simpa only [mul_one] using hm
    have hrhs : U + s + d = (2 ^ d - 1) + s := by omega
    rw [hrhs]
    exact hkval.trans hperiod.symm
  have hcoeffsmul : A • v = (U + s) • v := by
    have hmods : A % (2 ^ d - 1) = (U + s) % (2 ^ d - 1) := hcoeffmod
    rw [← mod_addOrderOf_nsmul v A,
      ← mod_addOrderOf_nsmul v (U + s), hv, hmods]
  refine ⟨k, hksum, ?_⟩
  calc
    (∑ i, k i • h i) =
        (∑ i, k i • (root + a i.val • v)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hnormal]
    _ = ∑ i, (k i • root + k i • (a i.val • v)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [nsmul_add]
    _ = (∑ i, k i • root) + (∑ i, (k i * a i.val) • v) := by
          rw [Finset.sum_add_distrib]
          apply congrArg (fun z ↦ (∑ i, k i • root) + z)
          apply Finset.sum_congr rfl
          intro i _
          rw [mul_comm, mul_nsmul]
    _ = d • root + A • v := by
          have hroot : (∑ i, k i • root) = (∑ i, k i) • root :=
            Finset.sum_nsmul_assoc Finset.univ k root
          have hvsum : (∑ i, (k i * a i.val) • v) = A • v :=
            Finset.sum_nsmul_assoc Finset.univ
              (fun i ↦ k i * a i.val) v
          rw [hroot, hvsum, hksum]
    _ = d • root + (U + s) • v := by rw [hcoeffsmul]
    _ = d • root + U • v + s • v := by rw [add_nsmul]; abel
    _ = Finset.univ.sum
          (fun i : Fin d ↦ root + a (Fin.val i) • v) + s • v := by
          have hroot : (∑ _i : Fin d, root) = d • root := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          have hvsum : (∑ i : Fin d, a (Fin.val i) • v) = U • v :=
            Finset.sum_nsmul_assoc Finset.univ
              (fun i : Fin d ↦ a (Fin.val i)) v
          rw [Finset.sum_add_distrib, hroot, hvsum]
    _ = (∑ i, h i) + s • v := by
          apply congrArg (fun z ↦ z + s • v)
          apply Finset.sum_congr rfl
          intro i _
          rw [hnormal]

/-- Witness form of `exists_mersenneLeaf_exactMultisetRepresentation`. -/
theorem exists_mersenneLeaf_witness
    {d s : ℕ} (hd : 3 ≤ d) (hs0 : 0 < s) (hsq : s < 2 ^ d - 1)
    (root v : G) (hv : addOrderOf v = 2 ^ d - 1)
    (h : Fin d → G) (hnormal : ∀ i, h i = root + a i.val • v) :
    ∃ c : Fin d → ℤ, Witness h (s • v) c := by
  obtain ⟨k, hksum, hkval⟩ :=
    exists_mersenneLeaf_exactMultisetRepresentation
      hd hs0 hsq root v hv h hnormal
  let c : Fin d → ℤ := fun i ↦ (k i : ℤ) - 1
  have hcsum : (∑ i, c i) = 0 := by
    simp only [c, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hcast : (∑ i, (k i : ℤ)) = (d : ℤ) := by
      rw [← Nat.cast_sum, hksum]
    omega
  have hcval : (∑ i, c i • h i) = s • v := by
    calc
      (∑ i, c i • h i) = ∑ i, (k i • h i - h i) := by
        apply Finset.sum_congr rfl
        intro i _
        change ((k i : ℤ) - 1) • h i = k i • h i - h i
        rw [sub_zsmul, one_zsmul, natCast_zsmul]
        exact (sub_eq_add_neg _ _).symm
      _ = (∑ i, k i • h i) - ∑ i, h i := by
        change Finset.univ.sum (fun i : Fin d ↦ k i • h i - h i) =
          Finset.univ.sum (fun i : Fin d ↦ k i • h i) -
            Finset.univ.sum h
        rw [Finset.sum_sub_distrib]
      _ = s • v := by rw [hkval]; abel
  have htarget : s • v ≠ 0 := by
    intro hz
    have hdvd : 2 ^ d - 1 ∣ s := by
      rw [← hv, addOrderOf_dvd_iff_nsmul_eq_zero]
      exact hz
    exact (Nat.not_le_of_lt hsq) (Nat.le_of_dvd hs0 hdvd)
  refine ⟨c, ?_, ?_, hcsum, hcval⟩
  · intro hc
    have hzero : (∑ i, c i • h i) = 0 := by simp [hc]
    exact htarget (hcval.symm.trans hzero)
  · intro i
    dsimp only [c]
    omega

/-- Every nonzero element of a finite cyclic subgroup has a positive natural
representative below the order of its chosen generator. -/
theorem exists_positive_nsmul_eq_of_mem_zmultiples
    {v t : G} {q : ℕ} (hq : 0 < q) (hv : addOrderOf v = q)
    (ht : t ∈ AddSubgroup.zmultiples v) (ht0 : t ≠ 0) :
    ∃ s : ℕ, 0 < s ∧ s < q ∧ t = s • v := by
  obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ht
  let s : ℕ := (z % (q : ℤ)).toNat
  have hqz : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hznonneg : 0 ≤ z % (q : ℤ) :=
    Int.emod_nonneg z (by omega)
  have hscast : (s : ℤ) = z % (q : ℤ) := by
    simpa only [s] using Int.toNat_of_nonneg hznonneg
  have hsltZ : (s : ℤ) < (q : ℤ) := by
    rw [hscast]
    exact Int.emod_lt_of_pos z hqz
  have hslt : s < q := by exact_mod_cast hsltZ
  have heq : z • v = s • v := by
    calc
      z • v = (z % (addOrderOf v : ℤ)) • v :=
        (mod_addOrderOf_zsmul v z).symm
      _ = (z % (q : ℤ)) • v := by rw [hv]
      _ = (s : ℤ) • v := by rw [hscast]
      _ = s • v := by rw [natCast_zsmul]
  have hs0 : 0 < s := by
    by_contra hs
    have hsZero : s = 0 := Nat.eq_zero_of_not_pos hs
    apply ht0
    rw [heq, hsZero]
    simp
  exact ⟨s, hs0, hslt, heq⟩

/-- Extend the leaf witness by zero along an injective pointed leaf map, and
retain the exact support certificate outside the leaf image. -/
theorem exists_mersenneLeaf_ambientWitness_zero_off
    {n d s : ℕ} (hd : 3 ≤ d) (hs0 : 0 < s) (hsq : s < 2 ^ d - 1)
    (root v : G) (hv : addOrderOf v = 2 ^ d - 1)
    (g : Fin n → G) (leaf : Fin d → Fin n)
    (hleaf : Function.Injective leaf) (e : Fin d ≃ Fin d)
    (hnormal : ∀ i,
      g (leaf (e i)) = root + a i.val • v) :
    ∃ c : Fin n → ℤ, Witness g (s • v) c ∧
      ∀ j, j ∉ (Finset.univ : Finset (Fin d)).image leaf → c j = 0 := by
  classical
  let emb : Fin d ↪ Fin n :=
    ⟨fun i ↦ leaf (e i), hleaf.comp e.injective⟩
  obtain ⟨c, hc⟩ := exists_mersenneLeaf_witness
    hd hs0 hsq root v hv (fun i ↦ g (emb i)) hnormal
  refine ⟨Function.extend emb c (fun _ ↦ 0),
    (witness_extend_embedding_iff emb g c).2 hc, ?_⟩
  intro j hj
  apply Function.extend_apply'
  rintro ⟨i, hi⟩
  apply hj
  apply Finset.mem_image.mpr
  refine ⟨e i, Finset.mem_univ _, ?_⟩
  change leaf (e i) = j at hi
  exact hi

/-- Extend the leaf witness by zero along an injective pointed leaf map. -/
theorem exists_mersenneLeaf_ambientWitness
    {n d s : ℕ} (hd : 3 ≤ d) (hs0 : 0 < s) (hsq : s < 2 ^ d - 1)
    (root v : G) (hv : addOrderOf v = 2 ^ d - 1)
    (g : Fin n → G) (leaf : Fin d → Fin n)
    (hleaf : Function.Injective leaf) (e : Fin d ≃ Fin d)
    (hnormal : ∀ i,
      g (leaf (e i)) = root + a i.val • v) :
    ∃ c : Fin n → ℤ, Witness g (s • v) c := by
  obtain ⟨c, hc, _hoff⟩ := exists_mersenneLeaf_ambientWitness_zero_off
    hd hs0 hsq root v hv g leaf hleaf e hnormal
  exact ⟨c, hc⟩

/-- A same-target witness that is nonzero outside a pointed Mersenne leaf is
distinct from the leaf-supported competitor.  Validity therefore forces an
ordered coefficient gap of at least two toward the leaf competitor. -/
theorem exists_mersenneLeaf_competitor_with_gap_of_externalWitness
    {n d : ℕ} (hd : 3 ≤ d)
    (root v : G) (hv : addOrderOf v = 2 ^ d - 1)
    (g : Fin n → G) (hg : ValidTuple g) (leaf : Fin d → Fin n)
    (hleaf : Function.Injective leaf) (e : Fin d ≃ Fin d)
    (hnormal : ∀ i,
      g (leaf (e i)) = root + a i.val • v)
    (t : G) (ht : t ∈ AddSubgroup.zmultiples v) (ht0 : t ≠ 0)
    (u : Fin n → ℤ) (hu : Witness g t u)
    (b : Fin n) (hb : b ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (hub : u b ≠ 0) :
    ∃ s : ℕ, 0 < s ∧ s < 2 ^ d - 1 ∧ t = s • v ∧
      ∃ c : Fin n → ℤ, Witness g t c ∧
        (∀ j, j ∉ (Finset.univ : Finset (Fin d)).image leaf → c j = 0) ∧
        ∃ i : Fin n, i ∈ (Finset.univ : Finset (Fin d)).image leaf ∧
          u i + 2 ≤ c i := by
  have hq : 0 < 2 ^ d - 1 := by
    have hpow : 0 < 2 ^ (d - 3) := pow_pos (by norm_num) _
    rw [show d = 3 + (d - 3) by omega, pow_add]
    norm_num
    omega
  obtain ⟨s, hs0, hsq, htarget⟩ :=
    exists_positive_nsmul_eq_of_mem_zmultiples hq hv ht ht0
  obtain ⟨c, hc, hcoff⟩ := exists_mersenneLeaf_ambientWitness_zero_off
    hd hs0 hsq root v hv g leaf hleaf e hnormal
  have hcTarget : Witness g t c := by simpa only [htarget] using hc
  have hcb : c b = 0 := hcoff b hb
  have huc : u ≠ c := by
    intro hEq
    apply hub
    rw [hEq, hcb]
  obtain ⟨i, hi⟩ := exists_coefficient_add_two_le_of_distinct_witnesses
    g hg hu hcTarget huc
  have hiLeaf : i ∈ (Finset.univ : Finset (Fin d)).image leaf := by
    by_contra hiOutside
    have hci : c i = 0 := hcoff i hiOutside
    have hui := hu.2.1 i
    omega
  exact ⟨s, hs0, hsq, htarget, c, hcTarget, hcoff, i, hiLeaf, hi⟩

/-- Every canonical private row whose owner lies outside the pointed leaf has
a normalized leaf-supported competitor at the same nonzero target and hence
a forced coefficient gap. -/
theorem TwoRetainedCanonicalPrivatePresentation.exists_mersenneLeaf_competitor_with_gap
    {n d : ℕ} (g : Fin n → G) (hg : ValidTuple g)
    (y root v : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (hd : 3 ≤ d) (hv : addOrderOf v = 2 ^ d - 1)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (e : Fin d ≃ Fin d)
    (hnormal : ∀ i,
      g (leaf (e i)) = root + a i.val • v)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (b : ↥B)
    (hb : (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf) :
    ∃ s : ℕ, 0 < s ∧ s < 2 ^ d - 1 ∧
      p.scalar b • y = s • v ∧
      ∃ c : Fin n → ℤ, Witness g (p.scalar b • y) c ∧
        (∀ j, j ∉ (Finset.univ : Finset (Fin d)).image leaf → c j = 0) ∧
        ∃ i : Fin n, i ∈ (Finset.univ : Finset (Fin d)).image leaf ∧
          p.coeff b i + 2 ≤ c i := by
  apply exists_mersenneLeaf_competitor_with_gap_of_externalWitness
    hd root v hv g hg leaf hleaf e hnormal (p.scalar b • y)
  · rw [hcyclic]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples y) _
  · exact p.target_ne_zero b
  · exact p.isWitness b
  · exact hb
  · exact p.owner_ne_zero b

/-- If every leaf except one retained coordinate belongs to the deletion set,
the private-row gap occurs either at that exceptional leaf or at a leaf where
the zero pattern forces the competitor coefficient to be at least two. -/
theorem TwoRetainedCanonicalPrivatePresentation.exists_mersenneLeaf_competitor_with_localized_gap
    {n d : ℕ} (g : Fin n → G) (hg : ValidTuple g)
    (y root v : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (hd : 3 ≤ d) (hv : addOrderOf v = 2 ^ d - 1)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (e : Fin d ≃ Fin d)
    (hnormal : ∀ i,
      g (leaf (e i)) = root + a i.val • v)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (r : Fin n)
    (hdeleted : ∀ i,
      i ∈ (Finset.univ : Finset (Fin d)).image leaf → i ≠ r → i ∈ B)
    (b : ↥B)
    (hb : (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf) :
    ∃ s : ℕ, 0 < s ∧ s < 2 ^ d - 1 ∧
      p.scalar b • y = s • v ∧
      ∃ c : Fin n → ℤ, Witness g (p.scalar b • y) c ∧
        (∀ j, j ∉ (Finset.univ : Finset (Fin d)).image leaf → c j = 0) ∧
        ∃ i : Fin n,
          i ∈ (Finset.univ : Finset (Fin d)).image leaf ∧
          (i = r ∨ 2 ≤ c i) ∧ p.coeff b i + 2 ≤ c i := by
  obtain ⟨s, hs0, hsq, htarget, c, hc, hcoff, i, hiLeaf, hi⟩ :=
    p.exists_mersenneLeaf_competitor_with_gap
      g hg y root v B hd hv leaf hleaf e hnormal hcyclic b hb
  refine ⟨s, hs0, hsq, htarget, c, hc, hcoff, i, hiLeaf, ?_, hi⟩
  by_cases hir : i = r
  · exact Or.inl hir
  · right
    have hiB : i ∈ B := hdeleted i hiLeaf hir
    have hib : i ≠ (b : Fin n) := by
      intro hib
      apply hb
      rw [← hib]
      exact hiLeaf
    have hizero : p.coeff b i = 0 := p.zero_other b i hiB hib
    omega

/-- In the exact-two row geometry, a canonical private row based outside a
Mersenne leaf cannot have owner coefficient `1`.  The reverse coefficient gap
must occur at one of the two retained coordinates; the row sum and witness
floor then contradict either possible retained coordinate. -/
theorem TwoRetainedCanonicalPrivatePresentation.external_owner_eq_neg_one_of_mersenneLeaf
    {n d : ℕ} (g : Fin n → G) (hg : ValidTuple g)
    (y root v : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (hd : 3 ≤ d) (hv : addOrderOf v = 2 ^ d - 1)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (e : Fin d ≃ Fin d)
    (hnormal : ∀ i,
      g (leaf (e i)) = root + a i.val • v)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (b : ↥B)
    (hb : (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (k : ℤ)
    (howner : p.coeff b (b : Fin n) = -1 ∨
      p.coeff b (b : Fin n) = 1)
    (hweight : p.weight b = 2 * k) :
    p.coeff b (b : Fin n) = -1 := by
  rcases howner with hminus | hone
  · exact hminus
  · exfalso
    obtain ⟨_s, _hs0, _hsq, _htarget, c, hc, hcoff,
        _i, _hiLeaf, _hi⟩ :=
      p.exists_mersenneLeaf_competitor_with_gap
        g hg y root v B hd hv leaf hleaf e hnormal hcyclic b hb
    have hcb : c (b : Fin n) = 0 := hcoff (b : Fin n) hb
    have hne : c ≠ p.coeff b := by
      intro heq
      have heqb := congrFun heq (b : Fin n)
      rw [hcb, hone] at heqb
      omega
    obtain ⟨j, hj⟩ := exists_coefficient_add_two_le_of_distinct_witnesses
      g hg hc (p.isWitness b) hne
    have hjNotB : j ∉ B := by
      intro hjB
      by_cases hjb : j = (b : Fin n)
      · subst j
        rw [hcb, hone] at hj
        omega
      · have hjzero : p.coeff b j = 0 := p.zero_other b j hjB hjb
        have hcfloor := hc.2.1 j
        omega
    have hjRetained : j = p.x ∨ j = p.z := by
      have hjComp : j ∈ Finset.univ \ B :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjNotB⟩
      rw [p.complement_eq] at hjComp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hjComp
    have hshape := privateWitness_twoRetained_exactShape
      g (p.isWitness b) B (b : Fin n) b.property (p.zero_other b)
        p.x p.z p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
    have hx : p.coeff b p.x = k := by
      have hw := p.weight_eq b
      rw [hone, hweight] at hw
      norm_num [twoRetainedOwnerNormalization] at hw
      omega
    have hcfloor := hc.2.1 j
    have hjPositive : 1 ≤ p.coeff b j := by omega
    rcases hjRetained with hjx | hjz
    · rw [hjx, hx] at hjPositive
      have hzfloor := (p.isWitness b).2.1 p.z
      rw [hshape.1, hone, hx] at hzfloor
      omega
    · rw [hjz, hshape.1, hone, hx] at hjPositive
      have hxfloor := (p.isWitness b).2.1 p.x
      rw [hx] at hxfloor
      omega

/-- The complete secondary/final partition inherits the sign rigidity: all
five external canonical rows have owner coefficient `-1`. -/
theorem PrimitiveMiddleExactMersenneFiveExternalRows.external_owner_eq_neg_one
    {n d q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y root v : ZMod (2 ^ 6 * q)) (B L : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ) (hd : 3 ≤ d) (hv : addOrderOf v = 2 ^ d - 1)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (e : Fin d ≃ Fin d)
    (hnormal : ∀ i,
      g (leaf (e i)) = root + a i.val • v)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (hL : L = (Finset.univ : Finset (Fin d)).image leaf)
    (hfive : PrimitiveMiddleExactMersenneFiveExternalRows
      g y B L p k₀) :
    ∀ b : ↥B, (b : Fin n) ∉ L →
      p.coeff b (b : Fin n) = -1 := by
  rcases hfive with
    ⟨T, k₁, _t, F, _hTcard, _hTle, _hFle, _hTsub, _htT,
      _hk₁Mem, _hk₁Ne, _hk₁Class, hTrows, _hTexact, _hTadjacent,
      _hTcomplete, _hTseparated, hexternalPartition, _hTFdisjoint,
      _hTFcard, _hprofiles, hFcase, _hcap, _hcrit⟩
  intro b hbL
  have hbLeaf : (b : Fin n) ∉
      (Finset.univ : Finset (Fin d)).image leaf := by
    simpa only [← hL] using hbL
  have hbUnion : (b : Fin n) ∈ T ∪ F := by
    rw [← hexternalPartition]
    exact Finset.mem_sdiff.mpr ⟨b.property, hbL⟩
  rcases Finset.mem_union.mp hbUnion with hbT | hbF
  · have hrow := hTrows b hbT
    exact p.external_owner_eq_neg_one_of_mersenneLeaf
      g hg y root v B hd hv leaf hleaf e hnormal hcyclic b hbLeaf k₁
        hrow.1 hrow.2.1
  · rcases hFcase with hFempty |
        ⟨k₂, _f, _hfF, _hk₂Mem, _hk₂Ne₀, _hk₂Ne₁, _hk₂Class,
          _hOneAdjacent, hFrows, _hFexact, _hFadjacent, _hFcomplete⟩
    · rw [hFempty] at hbF
      simp at hbF
    · have hrow := hFrows b hbF
      exact p.external_owner_eq_neg_one_of_mersenneLeaf
        g hg y root v B hd hv leaf hleaf e hnormal hcyclic b hbLeaf k₂
          hrow.1 hrow.2.1

/-- Once the owner coefficient is `-1`, the normalized row parameter gives
the two retained coefficients exactly. -/
theorem TwoRetainedCanonicalPrivatePresentation.retained_coefficients_of_owner_eq_neg_one
    {n : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (b : ↥B) (k : ℤ)
    (howner : p.coeff b (b : Fin n) = -1)
    (hweight : p.weight b = 2 * k) :
    p.coeff b p.x = -k ∧ p.coeff b p.z = k + 1 := by
  have hshape := privateWitness_twoRetained_exactShape
    g (p.isWitness b) B (b : Fin n) b.property (p.zero_other b)
      p.x p.z p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
  have hx : p.coeff b p.x = -k := by
    have hw := p.weight_eq b
    rw [howner, hweight] at hw
    norm_num [twoRetainedOwnerNormalization] at hw
    omega
  refine ⟨hx, ?_⟩
  rw [hshape.1, howner, hx]
  omega

/-- For a parameter adjacent to the primary middle parameter, the external
private row has nonnegative coefficient at the unique retained leaf. -/
theorem TwoRetainedCanonicalPrivatePresentation.external_insertedCoefficient_nonneg_of_adjacent
    {n : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (b : ↥B) (k₀ k : ℤ) (r : Fin n)
    (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (hadjacent : k = k₀ + 1 ∨ k₀ = k + 1)
    (howner : p.coeff b (b : Fin n) = -1)
    (hweight : p.weight b = 2 * k) :
    0 ≤ p.coeff b r := by
  have hretained := p.retained_coefficients_of_owner_eq_neg_one
    g y B b k howner hweight
  rcases hmiddle with hk₀ | hk₀
  · have hrx : r = p.x := by simpa only [hk₀, if_true] using hr
    rw [hrx, hretained.1]
    rcases hadjacent with hadjacent | hadjacent <;> omega
  · have hk₀Ne : k₀ ≠ -1 := by omega
    have hrz : r = p.z := by simpa only [hk₀Ne, if_false] using hr
    rw [hrz, hretained.2]
    rcases hadjacent with hadjacent | hadjacent <;> omega

/-- Adjacent external parameters cannot use the weak exceptional outcome of
the localized gap: even at the unique retained leaf, the private coefficient
is nonnegative, so the leaf competitor is heavy somewhere. -/
theorem TwoRetainedCanonicalPrivatePresentation.exists_mersenneLeaf_heavy_competitor_of_adjacent
    {n d : ℕ} (g : Fin n → G) (hg : ValidTuple g)
    (y root v : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (hd : 3 ≤ d) (hv : addOrderOf v = 2 ^ d - 1)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (e : Fin d ≃ Fin d)
    (hnormal : ∀ i,
      g (leaf (e i)) = root + a i.val • v)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (k₀ k : ℤ) (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (r : Fin n) (hr : r = if k₀ = -1 then p.x else p.z)
    (hdeleted : ∀ i,
      i ∈ (Finset.univ : Finset (Fin d)).image leaf → i ≠ r → i ∈ B)
    (b : ↥B)
    (hb : (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (hadjacent : k = k₀ + 1 ∨ k₀ = k + 1)
    (howner : p.coeff b (b : Fin n) = -1 ∨
      p.coeff b (b : Fin n) = 1)
    (hweight : p.weight b = 2 * k) :
    ∃ s : ℕ, 0 < s ∧ s < 2 ^ d - 1 ∧
      p.scalar b • y = s • v ∧
      ∃ c : Fin n → ℤ, Witness g (p.scalar b • y) c ∧
        (∀ j, j ∉ (Finset.univ : Finset (Fin d)).image leaf → c j = 0) ∧
        ∃ i : Fin n,
          i ∈ (Finset.univ : Finset (Fin d)).image leaf ∧ 2 ≤ c i := by
  have hownerNeg := p.external_owner_eq_neg_one_of_mersenneLeaf
    g hg y root v B hd hv leaf hleaf e hnormal hcyclic b hb k
      howner hweight
  have hrNonneg := p.external_insertedCoefficient_nonneg_of_adjacent
    g y B b k₀ k r hmiddle hr hadjacent hownerNeg hweight
  obtain ⟨s, hs0, hsq, htarget, c, hc, hcoff, i, hiLeaf,
      hiExceptional, hi⟩ :=
    p.exists_mersenneLeaf_competitor_with_localized_gap
      g hg y root v B hd hv leaf hleaf e hnormal hcyclic r hdeleted b hb
  refine ⟨s, hs0, hsq, htarget, c, hc, hcoff, i, hiLeaf, ?_⟩
  rcases hiExceptional with hir | hiHeavy
  · subst i
    omega
  · exact hiHeavy

end MinModulus

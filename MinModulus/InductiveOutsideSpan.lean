import MinModulus.FullCoverExpansionExtraction

/-!
# Actual smaller coset children and inductive affine generation

Short-sum rigidity and a constant nonzero character construct a valid
zero-adjoined quotient. Beside a subbinary mapped cycle this is an actual
counterexample in strictly fewer dimensions. Alternatively, an extracted
one-coin expansion makes affine and linear spans coincide; dense subset
sums then give the entire quotient. Only this latter induction consumer
assumes lower-dimensional bounds. Affine generation is not a unit-pair
normalization and does not close unrestricted G1, G2, or G3.
-/

namespace MinModulus
open Finset

/-- A one-coin expansion cannot lie in a constant nonzero character
class. This applies in any abelian group, including noncyclic quotients. -/
theorem constant_character_eq_zero_of_one_coin_expansion
    {k : ℕ} {G A : Type*} [AddCommGroup G] [AddCommGroup A]
    (q : Fin k → G) (p : Multiset (Fin k)) (hp : p.card=k+1)
    (hs : (p.map q).sum=∑ i, q i) (φ : G →+ A) (a : A)
    (hconstant : ∀ i, φ (q i)=a) : a=0 := by
  have h := congrArg φ hs
  simp only [map_multiset_sum,Multiset.map_map,Function.comp_def,map_sum,hconstant,
    Multiset.map_const',Multiset.sum_replicate,hp,Finset.sum_const,Finset.card_univ,Fintype.card_fin] at h
  rw [succ_nsmul] at h
  exact add_left_cancel (by simpa only [add_zero] using h : k • a+a=k • a+0)

/-- Short-sum rigidity plus any constant NONZERO character supplies an
ACTUAL valid zero-adjoined quotient, with no conjectural lower bound.
This converts a proper-coset obstruction into a concrete smaller tuple. -/
theorem validTuple_zero_cons_of_short_sum_rigidity_of_constant_character
    {k : ℕ} {G A : Type*} [AddCommGroup G] [AddCommGroup A]
    (q : Fin k → G)
    (hmin : ∀ p : Multiset (Fin k), p.card ≤ k → (p.map q).sum=∑ i, q i →
      p=(Finset.univ : Finset (Fin k)).val)
    (φ : G →+ A) (a : A) (ha : a ≠ 0) (hconstant : ∀ i, φ (q i)=a) :
    ValidTuple (Fin.cons 0 q) := by
  by_contra hnot
  obtain ⟨p,hp,hs⟩ := exists_one_coin_expansion_of_not_valid_zero_cons q hmin hnot
  exact ha (constant_character_eq_zero_of_one_coin_expansion q p hp hs φ a hconstant)

/-- A one-coin expansion makes the affine difference span equal the
linear coordinate span. It constructs the anchor from actual differences,
without assuming a unit coordinate or a cyclic ambient group. -/
theorem closure_differences_eq_closure_range_of_one_coin_expansion
    {k : ℕ} {G : Type*} [AddCommGroup G]
    (q : Fin k → G) (p : Multiset (Fin k)) (hp : p.card=k+1)
    (hs : (p.map q).sum=∑ i, q i) (j : Fin k) :
    AddSubgroup.closure (Set.range (fun i ↦ q i-q j))=AddSubgroup.closure (Set.range q) := by
  let H := AddSubgroup.closure (Set.range (fun i ↦ q i-q j))
  have hmem (i : Fin k) : q i-q j ∈ H := AddSubgroup.subset_closure ⟨i,rfl⟩
  have htotal : (∑ i, (q i-q j)) ∈ H := H.sum_mem (fun i _ ↦ hmem i)
  have hpsum : (p.map (fun i ↦ q i-q j)).sum ∈ H := by
    apply H.multiset_sum_mem
    intro x hx
    obtain ⟨i,_,rfl⟩ := Multiset.mem_map.mp hx
    exact hmem i
  have heq : (∑ i, (q i-q j))-(p.map (fun i ↦ q i-q j)).sum=q j := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      Multiset.sum_map_sub,Multiset.map_const',Multiset.sum_replicate,hp,hs,succ_nsmul]
    abel
  have hj : q j ∈ H := heq ▸ H.sub_mem htotal hpsum
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).mpr
    rintro x ⟨i,rfl⟩
    exact (AddSubgroup.closure (Set.range q)).sub_mem
      (AddSubgroup.subset_closure ⟨i,rfl⟩) (AddSubgroup.subset_closure ⟨j,rfl⟩)
  · apply (AddSubgroup.closure_le _).mpr
    rintro x ⟨i,rfl⟩
    change q i ∈ H
    have h := H.add_mem (hmem i) hj
    simpa only [sub_add_cancel] using h

/-- Any injective subset cube occupying more than half a finite group
generates the entire group. The density is strict and the group need not
be cyclic. -/
theorem closure_range_eq_top_of_dense_injective_subset_cube
    {k : ℕ} {G : Type*} [AddCommGroup G] [Fintype G]
    (q : Fin k → G) (hi : Function.Injective (fun S : Finset (Fin k) ↦ ∑ i ∈ S, q i))
    (hdense : Fintype.card G < 2^(k+1)) : AddSubgroup.closure (Set.range q)=⊤ := by
  classical
  let H := AddSubgroup.closure (Set.range q)
  letI : Fintype H := Fintype.ofFinite H
  let f : Finset (Fin k) → H := fun S ↦ ⟨∑ i ∈ S, q i,
    H.sum_mem (fun i _ ↦ AddSubgroup.subset_closure ⟨i,rfl⟩)⟩
  have hf : Function.Injective f := by
    intro S T h
    exact hi (congrArg Subtype.val h)
  have hlow : 2^k ≤ Nat.card H := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_finset,Fintype.card_fin] using
      Fintype.card_le_of_injective f hf
  by_contra hnot
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
  have hpos : 0 < Nat.card (G ⧸ H) := Nat.card_pos
  have hne : Nat.card (G ⧸ H) ≠ 1 := by
    intro h
    apply hnot
    apply AddSubgroup.eq_top_of_card_eq H
    rw [hcard,h,one_mul]
  have htwo : 2 ≤ Nat.card (G ⧸ H) := by omega
  have hmul := Nat.mul_le_mul htwo hlow
  rw [← hcard,Nat.card_eq_fintype_card] at hmul
  rw [pow_succ'] at hdense
  omega

/-- A constant nonzero character on the outside quotient of an actual
full-cover fibre produces a displayed smaller valid tuple. The construction
is unconditional; the index window makes it an induction counterexample. -/
theorem smaller_valid_zero_cons_of_actual_fibre_cover_constant_character
    {m k d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 2 ≤ m)
    (τ : ZMod M →+ ZMod (d*M)) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*M)) (hg : ValidTuple g) (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z)
    {A : Type*} [AddCommGroup A] (φ : ZMod d →+ A) (a : A) (ha : a ≠ 0)
    (hconstant : ∀ i, φ (ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m i)))=a) :
    ValidTuple (Fin.cons 0 (fun i ↦ ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m i)))) ∧
      k+1 < m+k := by
  constructor
  · apply validTuple_zero_cons_of_short_sum_rigidity_of_constant_character _ ?_ φ a ha hconstant
    intro p hc hsum
    exact quotient_multiset_eq_of_card_le_of_actual_fibre_cover (by omega) τ hτ g hg u hpref hcover
      Finset.univ p (by simpa using hc) hsum
  · omega

/-- Beside an actual subbinary cycle, a constant nonzero outside
character produces an ACTUAL counterexample in strictly fewer dimensions.
The new tuple, its strict global-bound violation, and dimension drop are
all proved without assuming any lower-dimensional or global conjecture. -/
theorem smaller_counterexample_of_subbinary_mapped_cycle_constant_character
    {m k d : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k) [NeZero d] [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (hsmall : d*(2^m-1) < 2^(m+k))
    {A : Type*} [AddCommGroup A] (φ : ZMod d →+ A) (a : A) (ha : a ≠ 0)
    (hconstant : ∀ i, φ (ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m i)))=a) :
    ValidTuple (Fin.cons 0 (fun i ↦ ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m i)))) ∧
      d < globalBound (k+1) ∧ k+1 < m+k := by
  letI : NeZero (d*(2^m-1)) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  obtain ⟨hv,hdim⟩ := smaller_valid_zero_cons_of_actual_fibre_cover_constant_character hm τ hτ g hg
    (fun i : Fin m ↦ ((2^i.val : ℕ) : ZMod (2^m-1))) hpref
    (exists_power_multiset_sum_at_mersenne hm) φ a ha hconstant
  exact ⟨hv,subbinary_cycle_index_lt_outside_succ_globalBound hm hk hsmall,hdim⟩

/-- Under the explicitly stated smaller-dimensional induction hypothesis,
the outsider DIFFERENCES span the whole cycle quotient, from every anchor.
Thus a minimal-dimensional subbinary counterexample containing an actual
cycle cannot hide all outsiders in any proper affine coset. This extracts
affine primitivity; it does not infer a unit pair or a doubling chain. -/
theorem outside_quotient_difference_span_eq_top_of_subbinary_mapped_cycle
    {m k d : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k) [NeZero d] [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (hbound : ∀ {a L : ℕ}, a < m+k → 0 < L → AdmitsValidTuple a L → globalBound a ≤ L)
    (hsmall : d*(2^m-1) < 2^(m+k)) (j : Fin k) :
    AddSubgroup.closure (Set.range (fun i ↦
      ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m i))-
      ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m j))))=⊤ := by
  classical
  letI : NeZero (d*(2^m-1)) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  let π := ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d)
  let q : Fin k → ZMod d := fun i ↦ π (g (Fin.natAdd m i))
  obtain ⟨p,hp,hs,_⟩ := exists_actual_expansion_with_large_head_of_subbinary_mapped_cycle
    hm hk τ hτ g hg hpref hbound hsmall
  have hq : (p.map q).sum=∑ i, q i := by
    simpa only [q,map_multiset_sum,Multiset.map_map,Function.comp_def,map_sum] using congrArg π hs
  change AddSubgroup.closure (Set.range (fun i ↦ q i-q j))=⊤
  rw [closure_differences_eq_closure_range_of_one_coin_expansion q p hp hq j]
  apply closure_range_eq_top_of_dense_injective_subset_cube q
  · intro S T hST
    have hmin (S T : Finset (Fin k)) (hc : S.card ≤ T.card)
        (heq : (∑ i ∈ S, q i)=∑ i ∈ T, q i) : S=T := by
      apply Finset.val_injective
      exact quotient_multiset_eq_of_card_le_of_actual_fibre_cover (by omega) τ hτ g hg
        (fun i : Fin m ↦ ((2^i.val : ℕ) : ZMod (2^m-1))) hpref
        (exists_power_multiset_sum_at_mersenne hm) T S.val hc heq
    rcases le_total S.card T.card with h | h
    · exact hmin S T h hST
    · exact (hmin T S h hST.symm).symm
  · have hwindow := subbinary_cycle_index_lt_outside_succ_globalBound hm hk hsmall
    have hbound' : globalBound (k+1) ≤ 2^(k+1) := Nat.sub_le _ _
    simpa only [ZMod.card] using hwindow.trans_le hbound'

end MinModulus

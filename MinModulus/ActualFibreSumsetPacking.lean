import MinModulus.ActualFibreCoverDeficit

/-!
# Actual-fibre sumset packing and quantitative missing residues

If a nonempty outside subset of size r sums to zero in the quotient,
validity forces |C_m|+|C_r|<=M for the actual fibre's exact coin sumsets.
The proof constructs disjoint reflected translates, not merely a failed
complete-cover test. At index two, any two odd outsiders give r=2.

Validity dissociation injects every subset of at most r translated fibre
differences into C_r. Thus |C_r| >= sum_{j<=r} binom(m-1,j), and in
particular |C_2| >= binom(m,2)+1. An actual even m-entry fibre with two
odd outsiders must therefore miss at least binom(m,2)+1 own-size sums.
No SI structure, criticality, full cover, or zero-entry premise is used.
This strictly excludes the proposed one-hole boundary for m>=2; it does
not assert arbitrary critical cover growth or close unrestricted G1.
-/

namespace MinModulus
open Finset

/-- Exact-K-coin sums of an arbitrary actual fibre. -/
noncomputable def actualFibreCoinCover {m M : ℕ} [NeZero M]
    (u : Fin m → ZMod M) (K : ℕ) : Finset (ZMod M) := by
  classical
  exact Finset.univ.filter (fun z ↦ ∃ s : Multiset (Fin m), s.card=K ∧ (s.map u).sum=z)

/-- An outside zero-sum subset in the quotient gives an actual target
outside the sum of the fibre's own-size and surplus-coin sumsets. -/
theorem not_mem_actual_fibre_cover_add_of_outside_subset
    {m k d M : ℕ} [NeZero M] [NeZero (d*M)]
    (g : Fin (m+k) → ZMod (d*M)) (hg : ValidTuple g)
    (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=zmodScaleHom d M (u i))
    (T : Finset (Fin k)) (hT : T.Nonempty) (w : ZMod M)
    (hw : zmodScaleHom d M w=∑ j ∈ T, g (Fin.natAdd m j))
    (a b : ZMod M) (ha : a ∈ actualFibreOwnSizeCover u)
    (hb : b ∈ actualFibreCoinCover u T.card) : a+b ≠ (∑ i, u i)+w := by
  classical
  intro heq
  obtain ⟨s, hs, hsa⟩ := (Finset.mem_filter.mp ha).2
  obtain ⟨v, hv, hvb⟩ := (Finset.mem_filter.mp hb).2
  let τ := zmodScaleHom d M
  let f : Fin m → Fin (m+k) := Fin.castAdd k
  let e : Fin k → Fin (m+k) := Fin.natAdd m
  let t := (Finset.univ \ T).val.map e
  obtain ⟨j, hj⟩ := hT
  have hcard : m+T.card+t.card=m+k := by
    simp only [t, Multiset.card_map]
    change m+T.card+(Finset.univ \ T).card=m+k
    rw [Finset.card_sdiff, Finset.inter_univ]
    have hle := Finset.card_le_univ T
    simp only [Finset.card_univ, Fintype.card_fin] at hle ⊢
    omega
  have hcover : ∃ r : Multiset (Fin m), r.card=m+T.card ∧ (r.map u).sum=a+b := by
    exact ⟨s+v, by simp [hs, hv], by simp [hsa, hvb]⟩
  have htotal : (∑ i, g i)=τ (∑ i, u i)+(∑ j : Fin k, g (e j)) := by
    rw [Fin.sum_univ_add]
    simp only [hpref, ← map_sum, τ, e]
  have hsum : τ (a+b)+(t.map g).sum=∑ i, g i := by
    rw [heq, map_add, hw, htotal]
    simp only [t, Multiset.map_map, Function.comp_def]
    change τ (∑ i, u i)+(∑ j ∈ T, g (e j))+(∑ j ∈ Finset.univ \ T, g (e j))=_
    rw [← Finset.sum_sdiff (Finset.subset_univ T)]
    abel
  apply not_validTuple_of_actual_mapped_fibre_cover τ u g f hpref (a+b) hcover t hcard hsum
    (e j) ?_ ?_ hg
  · intro i h
    have hval := congrArg Fin.val h
    simp only [f, e, Fin.val_castAdd, Fin.val_natAdd] at hval
    omega
  · intro hmem
    obtain ⟨i, hi, hij⟩ := Multiset.mem_map.mp hmem
    have heq : i=j := by
      apply Fin.ext
      have hval := congrArg Fin.val hij
      simp only [e, Fin.val_natAdd] at hval
      omega
    subst i
    exact (Finset.mem_sdiff.mp hi).2 hj

/-- Any two finite sumsets that avoid a target have total cardinality
at most the cyclic group order, by disjoint reflected translates. -/
theorem card_add_card_le_modulus_of_sum_ne
    {M : ℕ} [NeZero M] (C D : Finset (ZMod M)) (target : ZMod M)
    (havoid : ∀ a ∈ C, ∀ b ∈ D, a+b ≠ target) : C.card+D.card ≤ M := by
  classical
  let R := D.image (fun b ↦ target-b)
  have hinj : Function.Injective (fun b : ZMod M ↦ target-b) := by
    intro a b h
    have h' := congrArg (fun z ↦ target-z) h
    simpa using h'
  have hR : R.card=D.card := Finset.card_image_of_injective D hinj
  have hdisj : Disjoint C R := by
    apply Finset.disjoint_left.mpr
    intro a ha har
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp har
    apply havoid a ha b hb
    rw [← hba]
    abel
  have hcard := Finset.card_le_univ (C ∪ R)
  rw [Finset.card_union_of_disjoint hdisj, hR] at hcard
  simpa only [ZMod.card] using hcard

/-- General actual-fibre packing: any nonempty outside quotient-zero
subset of size r forces |C_m|+|C_r|<=M. All fibre entries are arbitrary. -/
theorem actual_fibre_own_cover_card_add_coin_cover_card_le
    {m k d M : ℕ} [NeZero M] [NeZero (d*M)]
    (g : Fin (m+k) → ZMod (d*M)) (hg : ValidTuple g)
    (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=zmodScaleHom d M (u i))
    (T : Finset (Fin k)) (hT : T.Nonempty)
    (hquot : ZMod.castHom (dvd_mul_right d M) (ZMod d)
      (∑ j ∈ T, g (Fin.natAdd m j))=0) :
    (actualFibreOwnSizeCover u).card+(actualFibreCoinCover u T.card).card ≤ M := by
  obtain ⟨w, hw⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hquot
  exact card_add_card_le_modulus_of_sum_ne _ _ ((∑ i, u i)+w)
    (fun a ha b hb ↦ not_mem_actual_fibre_cover_add_of_outside_subset g hg u hpref T hT w hw a b ha hb)

/-- Two odd outside entries give the two-coin packing constraint in
an arbitrary actual even fibre, in every ambient dimension. -/
theorem actual_even_fibre_own_cover_card_add_two_coin_card_le
    {m k M : ℕ} [NeZero M]
    (g : Fin (m+k) → ZMod (2*M)) (hg : ValidTuple g)
    (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=zmodScaleHom 2 M (u i))
    (j l : Fin k) (hjl : j ≠ l)
    (hj : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.natAdd m j))=1)
    (hl : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.natAdd m l))=1) :
    (actualFibreOwnSizeCover u).card+(actualFibreCoinCover u 2).card ≤ M := by
  classical
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2*M) := ⟨by omega⟩
  have h := actual_fibre_own_cover_card_add_coin_cover_card_le g hg u hpref {j,l}
    (by simp) (by simp only [Finset.sum_pair hjl, map_add, hj, hl]; decide)
  simpa [hjl] using h

/-- An injective nonempty fibre has at least m distinct two-coin sums,
even when its entries and ambient modulus have arbitrary structure. -/
theorem length_le_actual_fibre_two_coin_cover_card
    {m M : ℕ} [NeZero M] (u : Fin m → ZMod M) (hu : Function.Injective u) (i0 : Fin m) :
    m ≤ (actualFibreCoinCover u 2).card := by
  classical
  let f : Fin m → ↥(actualFibreCoinCover u 2) := fun i ↦ ⟨u i0+u i,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨{i0,i}, by simp, by simp⟩⟩⟩
  have hf : Function.Injective f := by
    intro i j h
    exact hu (add_left_cancel (congrArg Subtype.val h))
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- Direct quantitative G1 restriction: an actual m-entry even fibre
with two odd outside entries misses at least m own-size sums. This rules
out every near-full cover with fewer than m holes, without SI or criticality. -/
theorem actual_even_fibre_own_cover_card_add_length_le
    {m k M : ℕ} [NeZero M]
    (g : Fin (m+k) → ZMod (2*M)) (hg : ValidTuple g)
    (u : Fin m → ZMod M) (i0 : Fin m)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=zmodScaleHom 2 M (u i))
    (j l : Fin k) (hjl : j ≠ l)
    (hj : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.natAdd m j))=1)
    (hl : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.natAdd m l))=1) :
    (actualFibreOwnSizeCover u).card+m ≤ M := by
  have hinj : Function.Injective u := by
    intro a b hab
    have heq : g (Fin.castAdd k a)=g (Fin.castAdd k b) := by rw [hpref, hpref, hab]
    have hi := validTuple_injective g hg heq
    apply Fin.ext
    simpa only [Fin.val_castAdd] using congrArg Fin.val hi
  have hsmall := length_le_actual_fibre_two_coin_cover_card u hinj i0
  have hpack := actual_even_fibre_own_cover_card_add_two_coin_card_le g hg u hpref j l hjl hj hl
  omega

/-- Small subsets of translated differences inject into every exact
coin sumset, giving a partial-binomial lower bound with arbitrary budget. -/
theorem sum_choose_le_actual_fibre_coin_cover_card
    {m M : ℕ} [NeZero M] (u : Fin (m+1) → ZMod M) (hu : ValidTuple u) (R : ℕ) :
    (∑ r ∈ Finset.range (R+1), m.choose r) ≤ (actualFibreCoinCover u R).card := by
  classical
  let K : Finset (Finset (Fin m)) := (Finset.range (R+1)).biUnion
    (fun r ↦ (Finset.univ : Finset (Fin m)).powersetCard r)
  have hKcard : K.card=∑ r ∈ Finset.range (R+1), m.choose r := by
    rw [Finset.card_biUnion]
    · simp [Finset.card_powersetCard]
    · intro i _ j _ hij
      exact (Finset.univ : Finset (Fin m)).pairwise_disjoint_powersetCard hij
  let value : Finset (Fin m) → ZMod M := fun S ↦ R • u 0+ssum u S
  have hinj : Function.Injective value := by
    intro S T h
    exact ssum_injective u hu (add_left_cancel h)
  have hmem (S : Finset (Fin m)) (hS : S ∈ K) : value S ∈ actualFibreCoinCover u R := by
    obtain ⟨r, hr, hSr⟩ := Finset.mem_biUnion.mp hS
    have hc : S.card ≤ R := by
      have hrc := (Finset.mem_powersetCard.mp hSr).2
      have hrlt := Finset.mem_range.mp hr
      omega
    let t : Multiset (Fin (m+1)) := S.val.map Fin.succ+Multiset.replicate (R-S.card) 0
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, t, ?_, ?_⟩
    · simp only [t, Multiset.card_add, Multiset.card_map, Multiset.card_replicate]
      change S.card+(R-S.card)=R
      omega
    · simp only [t, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
        Function.comp_def, Multiset.map_replicate, Multiset.sum_replicate]
      change (∑ j ∈ S, u j.succ)+(R-S.card) • u 0=R • u 0+ssum u S
      simp only [ssum, diff, Finset.sum_sub_distrib, Finset.sum_const]
      have hnat : R=(R-S.card)+S.card := by omega
      conv_rhs => rw [hnat, add_nsmul]
      abel
  have hsub : K.image value ⊆ actualFibreCoinCover u R := by
    intro z hz
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hz
    exact hmem S hS
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective K hinj, hKcard] at hc
  exact hc

/-- Two-coin specialization: every valid nonempty fibre has at least
binom(length,2)+1 two-coin sums, without an odd-order hypothesis. -/
theorem choose_two_add_one_le_actual_fibre_two_coin_cover_card_succ
    {m M : ℕ} [NeZero M] (u : Fin (m+1) → ZMod M) (hu : ValidTuple u) :
    (m+1).choose 2+1 ≤ (actualFibreCoinCover u 2).card := by
  have h := sum_choose_le_actual_fibre_coin_cover_card u hu 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose_zero_right, Nat.choose_one_right, zero_add] at h
  rw [Nat.choose_succ_succ' m 1, Nat.choose_one_right]
  change m+m.choose 2+1 ≤ _
  omega

/-- The same quadratic two-coin bound for any nonempty valid fibre. -/
theorem choose_two_add_one_le_actual_fibre_two_coin_cover_card
    {m M : ℕ} [NeZero M] (hm : 0 < m) (u : Fin m → ZMod M) (hu : ValidTuple u) :
    m.choose 2+1 ≤ (actualFibreCoinCover u 2).card := by
  cases m with
  | zero => omega
  | succ m => exact choose_two_add_one_le_actual_fibre_two_coin_cover_card_succ u hu

/-- An arbitrary even fibre with two odd outsiders misses at least
binom(m,2)+1 residues from its own-size sumset. This stronger G1 restriction
combines actual sumset disjointness with validity dissociation. -/
theorem actual_even_fibre_own_cover_card_add_choose_two_add_one_le
    {m k M : ℕ} [NeZero M] (hm : 0 < m)
    (g : Fin (m+k) → ZMod (2*M)) (hg : ValidTuple g)
    (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=zmodScaleHom 2 M (u i))
    (j l : Fin k) (hjl : j ≠ l)
    (hj : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.natAdd m j))=1)
    (hl : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.natAdd m l))=1) :
    (actualFibreOwnSizeCover u).card+m.choose 2+1 ≤ M := by
  have hu : ValidTuple u := by
    apply validTuple_of_comp (zmodScaleHom 2 M)
    have hv := validTuple_embedding ⟨Fin.castAdd k, Fin.castAdd_injective m k⟩ g hg
    change ValidTuple (fun i : Fin m ↦ g (Fin.castAdd k i)) at hv
    simpa only [hpref] using hv
  have hsmall := choose_two_add_one_le_actual_fibre_two_coin_cover_card hm u hu
  have hpack := actual_even_fibre_own_cover_card_add_two_coin_card_le g hg u hpref j l hjl hj hl
  omega

end MinModulus

import MinModulus.SIThreeMultiplierBound

/-!
# Quantitative missing-residue bounds for arbitrary actual fibres

For a valid tuple with an actual m-entry fibre in the subgroup of index d,
let C be its exact-m-coin sumset and let k entries lie outside. Then
d*|C|+2^k <= d*(M+1). In particular, at index two,
|C|+2^(k-1) <= M+1. No SI, complete-cover, zero-entry, criticality, or
unrestricted global-gate hypothesis is used.

Choose a minimum-cardinality outside subset in each quotient bucket.
Every other subset constructs a different residue missing from C;
original-group dissociation makes the charge injective. Actual nonzero
padding is compensated by anchoring outside sums at a fibre coordinate.
This counts genuine uncovered residues, not merely exits from a cube.
The inequality alone is not a validity certificate or a proof of G1.
-/

namespace MinModulus
open Finset

/-- Relative to any actual fibre entry, the outside subset sums are
injective in the original group. This is ordinary validity dissociation. -/
theorem balanced_outside_subset_sum_injective
    {m k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin (m+k) → G) (hg : ValidTuple g) (i0 : Fin m) :
    Function.Injective (fun S : Finset (Fin k) ↦
      ∑ j ∈ S, (g (Fin.natAdd m j)-g (Fin.castAdd k i0))) := by
  let f : Fin (k+1) → Fin (m+k) := Fin.cons (Fin.castAdd k i0) (Fin.natAdd m)
  have hf : Function.Injective f := by
    intro i j
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · refine Fin.cases (by intro; rfl) (fun j ↦ ?_) j
      intro hij
      have hv := congrArg Fin.val hij
      simp only [f, Fin.cons_zero, Fin.cons_succ, Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    · refine Fin.cases ?_ (fun j ↦ ?_) j
      · intro hij
        have hv := congrArg Fin.val hij
        simp only [f, Fin.cons_zero, Fin.cons_succ, Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      · intro hij
        apply congrArg Fin.succ
        apply Fin.ext
        have hv := congrArg Fin.val hij
        simp only [f, Fin.cons_succ, Fin.val_natAdd] at hv
        omega
  have hv := validTuple_embedding ⟨f, hf⟩ g hg
  have hss (S : Finset (Fin k)) : ssum (fun i ↦ g (f i)) S=
      ∑ j ∈ S, (g (Fin.natAdd m j)-g (Fin.castAdd k i0)) := by
    simp [ssum, diff, f]
  intro S T h
  apply ssum_injective (fun i ↦ g (f i)) hv
  rwa [hss, hss]

/-- A quotient subset collision points to a SPECIFIC uncovered residue
of the actual fibre. Padding uses the selected actual entry, not zero. -/
theorem not_validTuple_of_actual_fibre_subset_collision_target
    {m k d M : ℕ} [NeZero M] [NeZero (d*M)]
    (g : Fin (m+k) → ZMod (d*M)) (u : Fin m → ZMod M) (i0 : Fin m)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=zmodScaleHom d M (u i))
    (S T : Finset (Fin k)) (hcard : S.card ≤ T.card) (hne : S ≠ T)
    (w : ZMod M) (hw : zmodScaleHom d M w=
      (∑ j ∈ T, (g (Fin.natAdd m j)-g (Fin.castAdd k i0)))-
      (∑ j ∈ S, (g (Fin.natAdd m j)-g (Fin.castAdd k i0))))
    (hcover : ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=(∑ i, u i)+w) : ¬ ValidTuple g := by
  classical
  let τ := zmodScaleHom d M
  let f : Fin m → Fin (m+k) := Fin.castAdd k
  let e : Fin k → Fin (m+k) := Fin.natAdd m
  let δ := T.card-S.card
  have hTcard : T.card ≤ k := by simpa only [Fintype.card_fin] using Finset.card_le_univ T
  have hnot : ¬ T ⊆ S := by
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub hcard).symm
  obtain ⟨j, hjT, hjS⟩ := Finset.not_subset.mp hnot
  have hef (i : Fin m) (j : Fin k) : f i ≠ e j := by
    intro h; have hv := congrArg Fin.val h
    simp only [f, e, Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have heinj : Function.Injective e := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [e, Fin.val_natAdd] at hv
    omega
  let t : Multiset (Fin (m+k)) := Multiset.replicate δ (f i0)+
    ((Finset.univ \ T).val.map e+S.val.map e)
  have htcard : m+t.card=m+k := by
    simp only [t, Multiset.card_add, Multiset.card_map, Multiset.card_replicate]
    change m+(δ+((Finset.univ \ T).card+S.card))=m+k
    simp only [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    dsimp [δ]; omega
  have htotal : (∑ i, g i)=τ (∑ i, u i)+(∑ j : Fin k, g (e j)) := by
    rw [Fin.sum_univ_add]
    simp only [hpref, ← map_sum, τ, e]
  have hsum : τ ((∑ i, u i)+w)+(t.map g).sum=∑ i, g i := by
    simp only [t, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, Multiset.map_map, Function.comp_def]
    change τ ((∑ i, u i)+w)+(δ • g (f i0)+
      ((∑ j ∈ Finset.univ \ T, g (e j))+(∑ j ∈ S, g (e j))))=_
    rw [map_add, hw, htotal, ← Finset.sum_sdiff (Finset.subset_univ T)]
    simp only [Finset.sum_sub_distrib, Finset.sum_const]
    have hT : T.card=δ+S.card := by dsimp [δ]; omega
    rw [hT, add_nsmul]
    dsimp only [f, e]
    abel
  apply not_validTuple_of_actual_mapped_fibre_cover τ u g f hpref _ hcover t htcard hsum
    (e j) (fun i ↦ hef i j) ?_
  intro hmem
  rcases Multiset.mem_add.mp hmem with hrep | hrest
  · exact hef i0 j ((Multiset.mem_replicate.mp hrep).2.symm)
  · rcases Multiset.mem_add.mp hrest with hT | hS
    · obtain ⟨i, hi, hij⟩ := Multiset.mem_map.mp hT
      have heq : i=j := heinj hij
      subst i
      exact (Finset.mem_sdiff.mp hi).2 hjT
    · obtain ⟨i, hi, hij⟩ := Multiset.mem_map.mp hS
      have heq : i=j := heinj hij
      subst i
      exact hjS hi

/-- A quotient bucket of outside subsets has at most one more member
than the actual fibre's uncovered set. Every other member charges a
DISTINCT missing residue, with no SI or criticality assumption. -/
theorem quotient_bucket_card_le_actual_fibre_holes_add_one
    {m k d M : ℕ} [NeZero M] [NeZero (d*M)]
    (g : Fin (m+k) → ZMod (d*M)) (hg : ValidTuple g)
    (u : Fin m → ZMod M) (i0 : Fin m)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=zmodScaleHom d M (u i))
    (H : Finset (ZMod M))
    (hcover : ∀ z : ZMod M, z ∉ H → ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z)
    (q : ZMod d) :
    (Finset.univ.filter (fun S : Finset (Fin k) ↦
      ZMod.castHom (dvd_mul_right d M) (ZMod d)
        (∑ j ∈ S, (g (Fin.natAdd m j)-g (Fin.castAdd k i0)))=q)).card ≤ H.card+1 := by
  classical
  let τ := zmodScaleHom d M
  let π := ZMod.castHom (dvd_mul_right d M) (ZMod d)
  let B : Finset (Fin k) → ZMod (d*M) := fun S ↦
    ∑ j ∈ S, (g (Fin.natAdd m j)-g (Fin.castAdd k i0))
  let F := Finset.univ.filter (fun S : Finset (Fin k) ↦ π (B S)=q)
  change F.card ≤ H.card+1
  by_cases hF : F.Nonempty
  · obtain ⟨S, hSF, hmin⟩ := F.exists_min_image Finset.card hF
    have hpreimage (T : F) : ∃ w : ZMod M, τ w=B T.val-B S := by
      apply exists_zmodScaleHom_eq_of_castHom_eq_zero
      change π (B T.val-B S)=0
      rw [map_sub, (Finset.mem_filter.mp T.property).2, (Finset.mem_filter.mp hSF).2, sub_self]
    let w : F → ZMod M := fun T ↦ Classical.choose (hpreimage T)
    have hw (T : F) : τ (w T)=B T.val-B S := Classical.choose_spec (hpreimage T)
    let target : F → ZMod M := fun T ↦ (∑ i, u i)+w T
    have hinj : Function.Injective target := by
      intro T U h
      have hwEq : w T=w U := add_left_cancel h
      have hB : B T.val=B U.val := by
        have h := congrArg τ hwEq
        rw [hw, hw] at h
        exact add_right_cancel (by simpa only [sub_eq_add_neg] using h)
      exact Subtype.ext (balanced_outside_subset_sum_injective g hg i0 hB)
    let S0 : F := ⟨S, hSF⟩
    have hmem (T : F) : target T ∈ insert (target S0) H := by
      by_cases hTS : T=S0
      · simp [hTS]
      · apply Finset.mem_insert_of_mem
        by_contra hnot
        have hne : S ≠ T.val := by
          intro heq
          exact hTS (Subtype.ext heq.symm)
        exact not_validTuple_of_actual_fibre_subset_collision_target g u i0 hpref
          S T.val (hmin T.val T.property) hne (w T) (hw T) (hcover (target T) hnot) hg
    let f : F → ↥(insert (target S0) H) := fun T ↦ ⟨target T, hmem T⟩
    have hf : Function.Injective f := fun T U h ↦ hinj (congrArg Subtype.val h)
    have hc := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_coe] at hc
    exact hc.trans (Finset.card_insert_le _ _)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hF]
    simp

/-- Quantitative outside-cube obstruction: h missing residues in an
arbitrary actual m-entry fibre allow at most d*(h+1) outside subsets.
The zero-hole case recovers the earlier full-cover counting theorem. -/
theorem two_pow_le_index_mul_actual_fibre_holes_add_one
    {m k d M : ℕ} [NeZero M] [NeZero (d*M)]
    (g : Fin (m+k) → ZMod (d*M)) (hg : ValidTuple g)
    (u : Fin m → ZMod M) (i0 : Fin m)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=zmodScaleHom d M (u i))
    (H : Finset (ZMod M))
    (hcover : ∀ z : ZMod M, z ∉ H → ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z) :
    2^k ≤ d*(H.card+1) := by
  classical
  letI : NeZero d := ⟨fun hd ↦ NeZero.ne (d*M) (by rw [hd, zero_mul])⟩
  by_contra hbad
  let Q : Finset (Fin k) → ZMod d := fun S ↦
    ZMod.castHom (dvd_mul_right d M) (ZMod d)
      (∑ j ∈ S, (g (Fin.natAdd m j)-g (Fin.castAdd k i0)))
  have hc : Fintype.card (ZMod d)*(H.card+1) < Fintype.card (Finset (Fin k)) := by
    simpa only [ZMod.card, Fintype.card_finset, Fintype.card_fin] using (by omega : d*(H.card+1) < 2^k)
  obtain ⟨q, hq⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card Q hc
  have hbound := quotient_bucket_card_le_actual_fibre_holes_add_one g hg u i0 hpref H hcover q
  exact (not_lt_of_ge hbound) hq

/-- Each actual even fibre with k outside coordinates must miss at
least 2^(k-1)-1 residues from its own-size cover. No SI is assumed. -/
theorem two_pow_pred_le_actual_even_fibre_holes_add_one
    {m k M : ℕ} [NeZero M] (hk : 1 ≤ k)
    (g : Fin (m+k) → ZMod (2*M)) (hg : ValidTuple g)
    (u : Fin m → ZMod M) (i0 : Fin m)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=zmodScaleHom 2 M (u i))
    (H : Finset (ZMod M))
    (hcover : ∀ z : ZMod M, z ∉ H → ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z) :
    2^(k-1) ≤ H.card+1 := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2*M) := ⟨by omega⟩
  have h := two_pow_le_index_mul_actual_fibre_holes_add_one g hg u i0 hpref H hcover
  have hpow : 2^k=2*2^(k-1) := by rw [← pow_succ']; congr 1; omega
  omega

/-- Any sound own-size cover in an arbitrary actual fibre satisfies a
joint capacity bound with the entire outside subset cube. -/
theorem index_mul_actual_fibre_cover_card_add_two_pow_le
    {m k d M : ℕ} [NeZero M] [NeZero (d*M)]
    (g : Fin (m+k) → ZMod (d*M)) (hg : ValidTuple g)
    (u : Fin m → ZMod M) (i0 : Fin m)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=zmodScaleHom d M (u i))
    (C : Finset (ZMod M))
    (hcover : ∀ z ∈ C, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z) :
    d*C.card+2^k ≤ d*(M+1) := by
  classical
  let H := Finset.univ \ C
  have h := two_pow_le_index_mul_actual_fibre_holes_add_one g hg u i0 hpref H
    (by intro z hz; apply hcover z; simpa [H] using hz)
  have hcard : H.card=M-C.card := by
    simp only [H, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, ZMod.card]
  have hC : C.card ≤ M := by simpa only [ZMod.card] using Finset.card_le_univ C
  rw [hcard] at h
  have heq : d*(M-C.card+1)+d*C.card=d*(M+1) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  omega

/-- The actual exact-m-coin sumset, without any assumed cover premise. -/
noncomputable def actualFibreOwnSizeCover {m M : ℕ} [NeZero M]
    (u : Fin m → ZMod M) : Finset (ZMod M) := by
  classical
  exact Finset.univ.filter (fun z ↦ ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z)

/-- Unconditional quantitative G1 restriction on every actual even
fibre: its own-size sumset and the outside cube share the half-modulus
capacity, with no SI, completeness, or criticality hypothesis. -/
theorem actual_even_fibre_cover_card_add_two_pow_pred_le
    {m k M : ℕ} [NeZero M] (hk : 1 ≤ k)
    (g : Fin (m+k) → ZMod (2*M)) (hg : ValidTuple g)
    (u : Fin m → ZMod M) (i0 : Fin m)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=zmodScaleHom 2 M (u i)) :
    (actualFibreOwnSizeCover u).card+2^(k-1) ≤ M+1 := by
  classical
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2*M) := ⟨by omega⟩
  have h := index_mul_actual_fibre_cover_card_add_two_pow_le g hg u i0 hpref (actualFibreOwnSizeCover u)
    (by intro z hz; exact (Finset.mem_filter.mp hz).2)
  have hpow : 2^k=2*2^(k-1) := by rw [← pow_succ']; congr 1; omega
  omega

end MinModulus

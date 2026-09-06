import MinModulus.SIThreeIndexFive

/-!
# Actual-fibre covers and quotient subset sums

An arbitrary actual fibre with a full own-size cover forces all outside
subset sums to be distinct in the quotient. This uses neither SI structure
nor criticality. Applications exclude indices six and seven for coherent
three-extra prefixes in every dimension n >= 8.
-/

namespace MinModulus
open Finset

/-- A full exact-cardinality cover in an ACTUAL fibre rules out a
quotient subset collision with enough excess removed coordinates.
The fibre and all outside entries are arbitrary; no SI premise is used. -/
theorem not_validTuple_of_actual_fibre_cover_subset_collision
    {m k d M r : ℕ} [NeZero M] [NeZero (d*M)] (hm : 0 < m)
    (g : Fin (m+k) → ZMod (d*M)) (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i) = zmodScaleHom d M (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card = m+r ∧ (s.map u).sum = z)
    (S T : Finset (Fin k)) (hcard : S.card+r ≤ T.card) (hne : S ≠ T)
    (hcollision : (∑ j ∈ S, ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m j))) =
      ∑ j ∈ T, ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m j))) : ¬ ValidTuple g := by
  classical
  let τ := zmodScaleHom d M
  let π := ZMod.castHom (dvd_mul_right d M) (ZMod d)
  let f : Fin m → Fin (m+k) := Fin.castAdd k
  let e : Fin k → Fin (m+k) := Fin.natAdd m
  let i0 : Fin m := ⟨0, hm⟩
  let δ := T.card-S.card-r
  have hTcard : T.card ≤ k := by simpa only [Fintype.card_fin] using Finset.card_le_univ T
  have hnot : ¬ T ⊆ S := by
    intro hsub
    have heq : T = S := Finset.eq_of_subset_of_card_le hsub (by omega)
    exact hne heq.symm
  obtain ⟨j, hjT, hjS⟩ := Finset.not_subset.mp hnot
  have hef (i : Fin m) (j : Fin k) : f i ≠ e j := by
    intro h
    have hval := congrArg Fin.val h
    simp only [f, e, Fin.val_castAdd, Fin.val_natAdd] at hval
    omega
  have heinj : Function.Injective e := by
    intro i j h
    apply Fin.ext
    have hval := congrArg Fin.val h
    simp only [e, Fin.val_natAdd] at hval
    omega
  have hker : π ((∑ j ∈ T, g (e j))-(∑ j ∈ S, g (e j)))=0 := by
    rw [map_sub, map_sum, map_sum]
    change (∑ j ∈ T, π (g (e j)))-(∑ j ∈ S, π (g (e j)))=0
    rw [hcollision, sub_self]
  obtain ⟨w, hw⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hker
  let z : ZMod M := (∑ i, u i)+w-δ • u i0
  let t : Multiset (Fin (m+k)) := Multiset.replicate δ (f i0)+
    ((Finset.univ \ T).val.map e + S.val.map e)
  have htcard : (m+r)+t.card = m+k := by
    simp only [t, Multiset.card_add, Multiset.card_replicate, Multiset.card_map]
    change (m+r)+(δ+((Finset.univ \ T).card+S.card))=m+k
    simp only [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    dsimp [δ]
    omega
  have htotal : (∑ i, g i) = τ (∑ i, u i)+(∑ j : Fin k, g (e j)) := by
    rw [Fin.sum_univ_add]
    simp only [hpref, ← map_sum, τ, e]
  have hsum : τ z+(t.map g).sum = ∑ i, g i := by
    simp only [t, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, Multiset.map_map, Function.comp_def]
    change τ z+(δ • g (f i0)+((∑ j ∈ Finset.univ \ T, g (e j))+(∑ j ∈ S, g (e j)))) = _
    rw [show g (f i0)=τ (u i0) from hpref i0]
    dsimp [z]
    rw [map_sub, map_add, map_nsmul, hw, htotal, ← Finset.sum_sdiff (Finset.subset_univ T)]
    abel
  apply not_validTuple_of_actual_mapped_fibre_cover τ u g f hpref z (hcover z) t htcard hsum
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

/-- A full cover with the actual fibre's own number of coins forces
injectivity of all outside-coordinate subset sums in the quotient. -/
theorem quotient_subset_sum_injective_of_actual_fibre_cover
    {m k d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 0 < m)
    (g : Fin (m+k) → ZMod (d*M)) (hg : ValidTuple g) (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i) = zmodScaleHom d M (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z) :
    Function.Injective (fun S : Finset (Fin k) ↦
      ∑ j ∈ S, ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m j))) := by
  intro S T hcollision
  by_contra hne
  rcases le_total S.card T.card with h | h
  · exact not_validTuple_of_actual_fibre_cover_subset_collision (r := 0) hm g u hpref
      hcover S T (by omega) hne hcollision hg
  · exact not_validTuple_of_actual_fibre_cover_subset_collision (r := 0) hm g u hpref
      hcover T S (by omega) (Ne.symm hne) hcollision.symm hg

/-- An arbitrary actual cyclic fibre with a full own-size cover forces
the quotient index to accommodate all 2^k outside subset sums. -/
theorem two_pow_le_index_of_actual_fibre_cover
    {m k d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 0 < m)
    (g : Fin (m+k) → ZMod (d*M)) (hg : ValidTuple g) (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i) = zmodScaleHom d M (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z) :
    2^k ≤ d := by
  letI : NeZero d := ⟨fun hd ↦ NeZero.ne (d*M) (by rw [hd, zero_mul])⟩
  have hi := quotient_subset_sum_injective_of_actual_fibre_cover hm g hg u hpref hcover
  have hc := Fintype.card_le_of_injective _ hi
  simpa only [Fintype.card_finset, Fintype.card_fin, ZMod.card] using hc

/-- In particular, an actual even fibre with two or more outside
coordinates cannot have a full own-size cover. This G1 restriction has
no SI structure or criticality hypothesis. -/
theorem not_validTuple_of_actual_even_fibre_full_cover
    {m k M : ℕ} [NeZero M] (hm : 0 < m) (hk : 2 ≤ k)
    (g : Fin (m+k) → ZMod (2*M)) (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i) = zmodScaleHom 2 M (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z) : ¬ ValidTuple g := by
  intro hg
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2*M) := ⟨by omega⟩
  have hc := two_pow_le_index_of_actual_fibre_cover hm g hg u hpref hcover
  have hp := Nat.pow_le_pow_right (by omega : 1 ≤ (2:ℕ)) hk
  norm_num at hp
  omega

/-- With two odd extras, even an (m+2)-coin cover in the actual even
fibre constructs a full rival. The fibre itself is entirely arbitrary. -/
theorem not_validTuple_of_actual_even_fibre_two_extra_cover
    {m M : ℕ} [NeZero M] (hm : 0 < m)
    (g : Fin (m+2) → ZMod (2*M)) (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g (Fin.castAdd 2 i) = zmodScaleHom 2 M (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m+2 ∧ (s.map u).sum=z)
    (hx : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.last m).castSucc)=1)
    (hy : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.last (m+1)))=1) : ¬ ValidTuple g := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2*M) := ⟨by omega⟩
  apply not_validTuple_of_actual_fibre_cover_subset_collision (r := 2) hm g u hpref hcover
    ∅ Finset.univ (by simp) (by intro h; have hc := congrArg Finset.card h; simp at hc)
  simp only [Finset.sum_empty, Fin.sum_univ_two]
  change (0 : ZMod 2)=ZMod.castHom _ _ (g (Fin.last m).castSucc)+
    ZMod.castHom _ _ (g (Fin.last (m+1)))
  rw [hx, hy]
  decide

/-- In every subbinary coherent three-extra class of index at least six,
the actual prefix covers its subgroup with m coins. Hence the outside
quotient cube is injective, and the index must be at least eight. -/
theorem quotient_cube_of_valid_subbinary_large_index_three_extra_prefix
    {m d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 5 ≤ m) (hd : 6 ≤ d)
    (hupper : d*M < 2^(m+3))
    (g : Fin (m+3) → ZMod (d*M)) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = zmodScaleHom d M (a i.val : ZMod M)) :
    Function.Injective (fun S : Finset (Fin 3) ↦
      ∑ j ∈ S, ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m j))) ∧ 8 ≤ d := by
  have hgrowth := three_mul_le_mersenne_pred hm
  have hpow : 2^m=2*2^(m-1) := by rw [← pow_succ']; congr 1; omega
  have hpow3 : 2^(m+3)=16*2^(m-1) := by rw [pow_add, hpow]; norm_num; ring
  have hM6 : 6*M < 2^(m+3) := (Nat.mul_le_mul_right M hd).trans_lt hupper
  have hMcover : M ≤ (1+2)*(2^(m-1)-1)-(m-2) := by omega
  have hcover (z : ZMod M) : ∃ s : Multiset (Fin m), s.card=m ∧
      (s.map (fun i : Fin m ↦ (a i.val : ZMod M))).sum=z := by
    obtain ⟨s, hs, hsum⟩ := exists_fixed_multiset_sum_of_modulus_le_initial_interval
      (d := 1) (by omega : 2 ≤ m) hMcover z
    exact ⟨s, by omega, hsum⟩
  constructor
  · exact quotient_subset_sum_injective_of_actual_fibre_cover (by omega) g hg
      (fun i : Fin m ↦ (a i.val : ZMod M)) hpref hcover
  · simpa only [show 2^3=(8:ℕ) by norm_num] using
      two_pow_le_index_of_actual_fibre_cover (by omega) g hg (fun i : Fin m ↦ (a i.val : ZMod M)) hpref hcover

/-- Indices six and seven are excluded at once by the general quotient
cube theorem, giving the binary lower bound without quotient enumeration. -/
theorem binary_lower_bound_of_valid_affine_six_or_seven_three_extra_prefix
    {m d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 5 ≤ m) (hd6 : 6 ≤ d) (hd7 : d ≤ 7)
    (g : Fin (m+3) → ZMod (d*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (φ : ZMod (d*M) ≃+ ZMod (d*M)) (b : ZMod (d*M))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = φ (zmodScaleHom d M (a i.val : ZMod M))+b) :
    2^(m+3) ≤ d*M := by
  by_contra h
  have hcube := quotient_cube_of_valid_subbinary_large_index_three_extra_prefix hm hd6 (by omega)
    (fun i ↦ φ.symm (g (e i)-b))
    (validTuple_comp (validTuple_sub_const _ (validTuple_embedding e.toEmbedding g hg) b)
      φ.symm.toAddMonoidHom φ.symm.injective)
    (by intro i; simp only [hpref, add_sub_cancel_right, AddEquiv.symm_apply_apply])
  omega

/-- The two new index classes satisfy global and every stratum threshold,
including odd moduli at index seven, by a single all-arity counting rule. -/
theorem global_and_stratum_lower_bound_of_valid_affine_six_or_seven_three_extra_prefix
    {m d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 5 ≤ m) (hd6 : 6 ≤ d) (hd7 : d ≤ 7)
    (g : Fin (m+3) → ZMod (d*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (φ : ZMod (d*M) ≃+ ZMod (d*M)) (b : ZMod (d*M))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = φ (zmodScaleHom d M (a i.val : ZMod M))+b) :
    globalBound (m+3) ≤ d*M ∧ ∀ s : ℕ, stratumBound (m+3) s ≤ d*M := by
  have h := binary_lower_bound_of_valid_affine_six_or_seven_three_extra_prefix hm hd6 hd7 g hg e φ b hpref
  exact ⟨(Nat.sub_le _ _).trans h, fun s ↦ (Nat.sub_le _ _).trans h⟩

end MinModulus

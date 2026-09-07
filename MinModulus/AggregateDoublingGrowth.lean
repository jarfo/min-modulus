import MinModulus.AllIndexHoleBudget

/-!
# Collective doubling growth beside an actual zero-sum fibre

Distinct actual doubling targets split simultaneously. More generally,
every ranked doubling forest realizes all coin counts up to the sum
of its binary vertex weights. Validity beside a nonempty zero-sum
fibre therefore forces the STRICT aggregate budget sum(2^rank)<m+k.
These statements work in any abelian group without a full-cover premise.

Beside actual mapped cycles, thin covers lift quotient forest edges.
Inverse-permutation first-hit ranks extract the forest automatically
from quotient cube injectivity and any partial doubling permutation.
All components contribute to one budget; separate chain bounds lose
this information. Arbitrary critical structure remains unextracted.
-/

namespace MinModulus
open Finset

/-- Distinct actual doubling targets can all be split once, even
when they lie in different chains. No cycle or full-cover premise. -/
theorem exists_multiset_card_add_of_injective_doubling_targets
    {k : ℕ} {G : Type*} [AddCommGroup G] (q : Fin k → G)
    (S : Finset (Fin k)) (f : Fin k → Fin k) (hf : Set.InjOn f S)
    (hd : ∀ i ∈ S, q (f i)=2 • q i) :
    ∃ t : Multiset (Fin k), t.card=k+S.card ∧ (t.map q).sum=∑ i, q i := by
  classical
  let T := S.image f
  have hTcard : T.card=S.card := Finset.card_image_iff.mpr hf
  have hTsum : (∑ j ∈ T, q j)=2 • (∑ i ∈ S, q i) := by
    rw [show T=S.image f from rfl,Finset.sum_image (by intro i hi j hj heq; exact hf hi hj heq)]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i hi ↦ hd i hi)
  let t := (Finset.univ \ T).val+S.val+S.val
  refine ⟨t,?_,?_⟩
  · simp only [t,Multiset.card_add]
    change (Finset.univ \ T).card+S.card+S.card=k+S.card
    rw [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Fintype.card_fin,hTcard]
    have hc : S.card ≤ k := by simpa using Finset.card_le_univ S
    omega
  · simp only [t,Multiset.map_add,Multiset.sum_add]
    change (∑ j ∈ Finset.univ \ T, q j)+(∑ i ∈ S, q i)+(∑ i ∈ S, q i)=∑ i, q i
    rw [add_assoc,← two_nsmul,← hTsum]
    rw [Finset.sum_sdiff (Finset.subset_univ T)]

/-- Beside ANY nonempty zero-sum fibre, at least m distinct outside
doubling targets would replace the entire fibre. This aggregates
growth across all chains instead of bounding each chain separately. -/
theorem doubling_targets_card_lt_fibre_of_valid_zero_sum_fibre
    {m k : ℕ} (hm : 0 < m) {G : Type*} [AddCommGroup G]
    (g : Fin (m+k) → G) (hg : ValidTuple g)
    (hzero : (∑ i : Fin m, g (Fin.castAdd k i))=0)
    (S : Finset (Fin k)) (f : Fin k → Fin k) (hf : Set.InjOn f S)
    (hd : ∀ i ∈ S, g (Fin.natAdd m (f i))=2 • g (Fin.natAdd m i)) :
    S.card < m := by
  classical
  by_contra hnot
  obtain ⟨T,hTS,hT⟩ := Finset.exists_subset_card_eq (by omega : m ≤ S.card)
  obtain ⟨t,ht,htsum⟩ := exists_multiset_card_add_of_injective_doubling_targets
    (fun i ↦ g (Fin.natAdd m i)) T f (hf.mono hTS) (fun i hi ↦ hd i (hTS hi))
  let a : Fin (m+k) := Fin.castAdd k (⟨0,hm⟩ : Fin m)
  apply not_validTuple_of_multiset_omission g (t.map (Fin.natAdd m))
    (by rw [Multiset.card_map,ht,hT,Nat.add_comm]) ?_ a ?_ hg
  · rw [Fin.sum_univ_add,hzero,zero_add,Multiset.map_map]
    exact htsum
  · intro ha
    obtain ⟨j,_,hja⟩ := Multiset.mem_map.mp ha
    have hv := congrArg Fin.val hja
    simp only [a,Fin.val_natAdd,Fin.val_castAdd] at hv
    omega

/-- Refinement along any ACTUAL ranked doubling forest realizes all
intermediate coin counts. Binary weights track available total growth
across every component simultaneously. -/
theorem exists_multiset_refinement_of_ranked_doubling
    {k : ℕ} {G : Type*} [AddCommGroup G] (q : Fin k → G) (r : Fin k → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ q i=2 • q j)
    (s : Multiset (Fin k)) {K : ℕ} (hK : s.card ≤ K)
    (hW : K ≤ (s.map (fun i ↦ 2^(r i))).sum) :
    ∃ t : Multiset (Fin k), t.card=K ∧ (t.map q).sum=(s.map q).sum ∧
      (t.map (fun i ↦ 2^(r i))).sum=(s.map (fun i ↦ 2^(r i))).sum := by
  induction K, hK using Nat.le_induction with
  | base => exact ⟨s,rfl,rfl,rfl⟩
  | succ K hK ih =>
    obtain ⟨t,ht,hvalue,hweight⟩ := ih (by omega)
    have hpos : ∃ i ∈ t, 0 < r i := by
      by_contra hnone
      push Not at hnone
      have hmap : t.map (fun i ↦ 2^(r i))=Multiset.replicate t.card 1 := by
        rw [← Multiset.map_const']
        apply Multiset.map_congr rfl
        intro i hi
        have hi0 : r i=0 := by have := hnone i hi; omega
        simp [hi0]
      rw [hmap,Multiset.sum_replicate,smul_eq_mul,mul_one,ht] at hweight
      omega
    obtain ⟨i,hi,hir⟩ := hpos
    obtain ⟨j,hr,hq⟩ := hp i hir
    obtain ⟨u,hu⟩ := Multiset.exists_cons_of_mem hi
    have hpow : 2^(r i)=2^(r j)+2^(r j) := by rw [hr,pow_succ']; omega
    refine ⟨j ::ₘ j ::ₘ u,?_,?_,?_⟩
    · rw [hu] at ht
      simp only [Multiset.card_cons] at ht ⊢
      omega
    · rw [hu] at hvalue
      simpa only [Multiset.map_cons,Multiset.sum_cons,hq,two_nsmul,add_assoc] using hvalue
    · rw [hu] at hweight
      simpa only [Multiset.map_cons,Multiset.sum_cons,hpow,add_assoc] using hweight

/-- Aggregate geometric growth of ALL ranked outside chains must
fall short of the actual zero-sum fibre's replacement budget. There
is no cycle, quotient, full-cover, or criticality hypothesis. -/
theorem sum_two_pow_rank_lt_length_of_valid_zero_sum_fibre
    {m k : ℕ} (hm : 0 < m) {G : Type*} [AddCommGroup G]
    (g : Fin (m+k) → G) (hg : ValidTuple g)
    (hzero : (∑ i : Fin m, g (Fin.castAdd k i))=0)
    (r : Fin k → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧
      g (Fin.natAdd m i)=2 • g (Fin.natAdd m j)) :
    (∑ i, 2^(r i)) < m+k := by
  classical
  by_contra hnot
  obtain ⟨t,ht,htsum,_⟩ := exists_multiset_refinement_of_ranked_doubling
    (fun i ↦ g (Fin.natAdd m i)) r hp (Finset.univ : Finset (Fin k)).val
    (K := m+k) (by simp) (by change m+k ≤ ∑ i, 2^(r i); omega)
  let a : Fin (m+k) := Fin.castAdd k (⟨0,hm⟩ : Fin m)
  apply not_validTuple_of_multiset_omission g (t.map (Fin.natAdd m))
    (by rw [Multiset.card_map,ht]) ?_ a ?_ hg
  · rw [Fin.sum_univ_add,hzero,zero_add,Multiset.map_map]
    exact htsum
  · intro ha
    obtain ⟨j,_,hja⟩ := Multiset.mem_map.mp ha
    have hv := congrArg Fin.val hja
    simp only [a,Fin.val_natAdd,Fin.val_castAdd] at hv
    omega

/-- Beside an actual mapped cycle, the aggregate geometric budget
already applies to quotient forests: thin covers lift every ranked
edge, with arbitrary original outside lifts. -/
theorem sum_two_pow_rank_lt_length_of_valid_mapped_cycle
    {m k d : ℕ} (hm : 2 ≤ m) [NeZero d] [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (r : Fin k → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧
      ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m i))=
        2 • ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m j))) :
    (∑ i, 2^(r i)) < m+k := by
  classical
  letI : NeZero (d*(2^m-1)) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  apply sum_two_pow_rank_lt_length_of_valid_zero_sum_fibre (by omega) g hg
  · simp only [hpref,← map_sum]
    rw [← Nat.cast_sum,sum_binary_powers,ZMod.natCast_self,map_zero]
  · intro i hi
    obtain ⟨j,hr,hq⟩ := hp i hi
    refine ⟨j,hr,?_⟩
    apply outside_eq_double_of_valid_mapped_mersenne_cycle hm τ g hg hpref j i
      (by intro heq; rw [heq] at hr; omega)
    apply exists_cyclic_hom_preimage_of_castHom_eq_zero τ hτ
    rw [map_sub,map_nsmul,hq,sub_self]

/-- First-hit ranks in the inverse permutation extract a forest from
ANY partial permutation whose orbits reach the exception set. Roots
are exactly images of exceptions; no proposed chain profile is assumed. -/
theorem exists_ranked_forest_of_perm_hits
    {k : ℕ} (P : Equiv.Perm (Fin k)) (B : Finset (Fin k))
    (hhit : ∀ a, ∃ t : ℕ, (P^t) a ∈ B) :
    ∃ r : Fin k → ℕ, (∀ i, r i=0 ↔ P⁻¹ i ∈ B) ∧
      ∀ i, 0 < r i → r i=r (P⁻¹ i)+1 := by
  classical
  let Q := P⁻¹
  let C := B.image P
  have hex (i : Fin k) : ∃ t : ℕ, (Q^t) i ∈ C := by
    obtain ⟨t,ht⟩ := hhit i
    have hcy : P.SameCycle i ((P^t) i) := ⟨(t : ℤ),by simp⟩
    have hcy' : Q.SameCycle i (P ((P^t) i)) := by
      apply Equiv.Perm.SameCycle.inv
      exact Equiv.Perm.sameCycle_apply_right.mpr hcy
    obtain ⟨s,hs⟩ := hcy'.exists_nat_pow_eq
    exact ⟨s,hs ▸ Finset.mem_image.mpr ⟨_,ht,rfl⟩⟩
  let r : Fin k → ℕ := fun i ↦ Nat.find (hex i)
  have hr (i : Fin k) : (Q^(r i)) i ∈ C := Nat.find_spec (hex i)
  have hleast (i : Fin k) (t : ℕ) (ht : (Q^t) i ∈ C) : r i ≤ t := Nat.find_min' (hex i) ht
  have hroot (i : Fin k) : r i=0 ↔ P⁻¹ i ∈ B := by
    have hC : i ∈ C ↔ P⁻¹ i ∈ B := by
      constructor
      · intro hiC
        obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp hiC
        rw [← hji]
        simpa using hj
      · intro hiB
        exact Finset.mem_image.mpr ⟨P⁻¹ i,hiB,by simp⟩
    constructor
    · intro hz
      have h := hr i
      rw [hz,pow_zero] at h
      exact hC.mp h
    · intro hiB
      have h := hleast i 0 (by simpa using hC.mpr hiB)
      omega
  refine ⟨r,hroot,?_⟩
  intro i hi
  have hpred : r (Q i) ≤ r i-1 := by
    apply hleast
    have he : (Q^(r i-1)) (Q i)=(Q^(r i)) i := by
      rw [← Equiv.Perm.mul_apply,← pow_succ]
      have he : r i-1+1=r i := by omega
      rw [he]
    rw [he]
    exact hr i
  have hsucc : r i ≤ r (Q i)+1 := by
    apply hleast
    rw [pow_succ,Equiv.Perm.mul_apply]
    exact hr (Q i)
  change r i=r (Q i)+1
  omega

/-- The aggregate forest is EXTRACTED from original quotient-cube
injectivity and a partial doubling permutation, not supplied by a
chain hypothesis. All outside indices and the actual root set remain. -/
theorem exists_aggregate_rank_budget_of_valid_mapped_cycle
    {m k d : ℕ} (hm : 2 ≤ m) [NeZero d] [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (hi : Function.Injective (fun S : Finset (Fin k) ↦ ∑ j ∈ S,
      ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m j))))
    (P : Equiv.Perm (Fin k)) (B : Finset (Fin k))
    (hd : ∀ i, i ∉ B →
      ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m (P i)))=
        2 • ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m i))) :
    ∃ r : Fin k → ℕ, (∀ i, r i=0 ↔ P⁻¹ i ∈ B) ∧
      (∀ i, 0 < r i → r i=r (P⁻¹ i)+1) ∧ (∑ i, 2^(r i)) < m+k := by
  obtain ⟨r,hroot,hstep⟩ := exists_ranked_forest_of_perm_hits P B
    (exists_pow_mem_exceptions_of_partial_doubling_perm _ hi P B hd)
  refine ⟨r,hroot,hstep,?_⟩
  apply sum_two_pow_rank_lt_length_of_valid_mapped_cycle hm τ hτ g hg hpref r
  intro i hi
  have hnot : P⁻¹ i ∉ B := fun h ↦ by have := (hroot i).mpr h; omega
  refine ⟨P⁻¹ i,hstep i hi,?_⟩
  simpa using hd (P⁻¹ i) hnot

end MinModulus

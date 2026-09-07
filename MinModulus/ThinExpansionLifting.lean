import MinModulus.EvenHoleParityBudget

/-!
# Thin-fibre lifting of arbitrary outside expansions

Positive coin growth gives forbidden targets in every actual fibre. When
the one-fewer-coin cover misses only the fibre total, every one-coin
quotient expansion lifts exactly. A zero-sum fibre bounds the length of
arbitrary successive squarefree-target rewrites, beyond doubling forests.
-/

namespace MinModulus
open Finset

/-- A multiset with fewer coins than available coordinates omits an
actual coordinate. This exposes the omitted fibre index in thin covers. -/
theorem exists_not_mem_of_multiset_card_lt_fintype
    {m : ℕ} (s : Multiset (Fin m)) (hs : s.card < m) : ∃ a : Fin m, a ∉ s := by
  classical
  by_contra hnot
  push Not at hnot
  have hsub : Finset.univ ⊆ s.toFinset := by
    intro i _
    exact Multiset.mem_toFinset.mpr (hnot i)
  have hc := Finset.card_le_card hsub
  have hle := s.toFinset_card_le
  simp only [Finset.card_univ,Fintype.card_fin] at hc
  omega

/-- Any positive outside coin expansion gives an actual forbidden
thin-cover target. The omitted coordinate lies INSIDE the fibre, so
no outside omission or complete-cover hypothesis is needed. This
applies to arbitrary actual fibres and arbitrary expansion shapes. -/
theorem not_validTuple_of_actual_thin_fibre_expansion_target
    {m k M r : ℕ} (hr : 0 < r) (hrm : r ≤ m) {G : Type*} [AddCommGroup G]
    (τ : ZMod M →+ G) (u : Fin m → ZMod M)
    (g : Fin (m+k) → G)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ (u i))
    (S : Finset (Fin k)) (p : Multiset (Fin k)) (hcard : p.card=S.card+r)
    (z : ZMod M) (hcover : ∃ s : Multiset (Fin m), s.card=m-r ∧ (s.map u).sum=z)
    (hz : τ z=τ (∑ i, u i)+(∑ i ∈ S, g (Fin.natAdd m i))-
      (p.map (fun i ↦ g (Fin.natAdd m i))).sum) : ¬ ValidTuple g := by
  classical
  intro hg
  obtain ⟨s,hs,hsum⟩ := hcover
  obtain ⟨a,ha⟩ := exists_not_mem_of_multiset_card_lt_fintype s (by omega)
  let f : Fin m → Fin (m+k) := Fin.castAdd k
  let e : Fin k → Fin (m+k) := Fin.natAdd m
  let outside : Multiset (Fin k) := (Finset.univ \ S).val+p
  let t : Multiset (Fin (m+k)) := s.map f+outside.map e
  have htcard : t.card=m+k := by
    simp only [t,outside,Multiset.card_add,Multiset.card_map,hs,hcard]
    change m-r+((Finset.univ \ S).card+(S.card+r))=m+k
    rw [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Fintype.card_fin]
    have hle : S.card ≤ k := by simpa using Finset.card_le_univ S
    omega
  have hsf : ((s.map f).map g).sum=τ z := by
    rw [Multiset.map_map]
    change (s.map (fun i ↦ g (Fin.castAdd k i))).sum=τ z
    simp only [hpref]
    simpa only [map_multiset_sum,Multiset.map_map,Function.comp_def] using congrArg τ hsum
  have htsum : (t.map g).sum=∑ i, g i := by
    dsimp only [t]
    rw [Multiset.map_add,Multiset.sum_add,hsf,Multiset.map_map]
    simp only [outside,Multiset.map_add,Multiset.sum_add]
    change τ z+((∑ i ∈ Finset.univ \ S, g (e i))+
      (p.map (fun i ↦ g (e i))).sum)=∑ i, g i
    rw [Fin.sum_univ_add]
    simp only [hpref,← map_sum]
    rw [hz,← Finset.sum_sdiff (Finset.subset_univ S)]
    dsimp only [e]
    abel
  apply not_validTuple_of_multiset_omission g t htcard htsum (f a) ?_ hg
  intro hmem
  rcases Multiset.mem_add.mp hmem with hin | hout
  · obtain ⟨i,hi,heq⟩ := Multiset.mem_map.mp hin
    exact ha ((Fin.castAdd_injective m k heq) ▸ hi)
  · obtain ⟨i,_,heq⟩ := Multiset.mem_map.mp hout
    have hv := congrArg Fin.val heq
    simp only [f,e,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega

/-- ANY one-coin outside expansion lifts to an exact original-group
relation beside an actual fibre whose (m-1)-coin cover misses at most
its own sum. No doubling, cycle, fixed support size, or fibre zero-sum
hypothesis is required. A nonzero discrepancy gives a thin-cover rival. -/
theorem outside_expansion_eq_of_valid_actual_thin_fibre
    {m k M : ℕ} (hm : 0 < m) {G : Type*} [AddCommGroup G]
    (τ : ZMod M →+ G) (u : Fin m → ZMod M)
    (g : Fin (m+k) → G) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ (u i))
    (hcover : ∀ z : ZMod M, z ≠ ∑ i, u i →
      ∃ s : Multiset (Fin m), s.card=m-1 ∧ (s.map u).sum=z)
    (S : Finset (Fin k)) (p : Multiset (Fin k)) (hcard : p.card=S.card+1)
    (hrel : ∃ w : ZMod M, τ w=(∑ i ∈ S, g (Fin.natAdd m i))-
      (p.map (fun i ↦ g (Fin.natAdd m i))).sum) :
    (p.map (fun i ↦ g (Fin.natAdd m i))).sum=∑ i ∈ S, g (Fin.natAdd m i) := by
  classical
  by_contra hnot
  obtain ⟨w,hw⟩ := hrel
  have hwne : w ≠ 0 := by
    intro hz
    rw [hz,map_zero] at hw
    exact hnot (sub_eq_zero.mp hw.symm).symm
  have hz : (∑ i, u i)+w ≠ ∑ i, u i := by
    intro heq
    apply hwne
    exact add_left_cancel (by simpa using heq : (∑ i, u i)+w=(∑ i, u i)+0)
  apply not_validTuple_of_actual_thin_fibre_expansion_target (by omega : 0 < 1) (by omega)
    τ u g hpref S p hcard ((∑ i, u i)+w) (hcover _ hz) ?_ hg
  rw [map_add,hw]
  abel

/-- Canonical quotient equality suffices for general one-coin lifting
through any injectively mapped actual thin fibre. -/
theorem outside_expansion_eq_of_valid_actual_thin_fibre_quotient
    {m k d M : ℕ} (hm : 0 < m) [NeZero M] [NeZero (d*M)]
    (τ : ZMod M →+ ZMod (d*M)) (hτ : Function.Injective τ) (u : Fin m → ZMod M)
    (g : Fin (m+k) → ZMod (d*M)) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ (u i))
    (hcover : ∀ z : ZMod M, z ≠ ∑ i, u i →
      ∃ s : Multiset (Fin m), s.card=m-1 ∧ (s.map u).sum=z)
    (S : Finset (Fin k)) (p : Multiset (Fin k)) (hcard : p.card=S.card+1)
    (hq : (p.map (fun i ↦ ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m i)))).sum=
      ∑ i ∈ S, ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m i))) :
    (p.map (fun i ↦ g (Fin.natAdd m i))).sum=∑ i ∈ S, g (Fin.natAdd m i) := by
  apply outside_expansion_eq_of_valid_actual_thin_fibre hm τ u g hg hpref hcover S p hcard
  apply exists_cyclic_hom_preimage_of_castHom_eq_zero τ hτ
  simp only [map_sub,map_sum,map_multiset_sum,Multiset.map_map,Function.comp_def]
  rw [hq,sub_self]

/-- Every one-coin outside quotient expansion lifts EXACTLY beside
an actual mapped cycle, with no restriction on target support size
or on the multiplicities of the replacement. -/
theorem outside_expansion_eq_of_valid_mapped_cycle_quotient
    {m k d : ℕ} (hm : 2 ≤ m) [NeZero d] [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (S : Finset (Fin k)) (p : Multiset (Fin k)) (hcard : p.card=S.card+1)
    (hq : (p.map (fun i ↦ ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m i)))).sum=
      ∑ i ∈ S, ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m i))) :
    (p.map (fun i ↦ g (Fin.natAdd m i))).sum=∑ i ∈ S, g (Fin.natAdd m i) := by
  letI : NeZero (d*(2^m-1)) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  apply outside_expansion_eq_of_valid_actual_thin_fibre_quotient (by omega) τ hτ
    (fun i : Fin m ↦ ((2^i.val : ℕ) : ZMod (2^m-1))) g hg hpref ?_ S p hcard hq
  intro z hz
  have hsum : (∑ i : Fin m, ((2^i.val : ℕ) : ZMod (2^m-1)))=0 := by
    rw [← Nat.cast_sum,sum_binary_powers,ZMod.natCast_self]
  exact exists_power_multiset_card_pred_of_ne_zero hm z (by simpa only [hsum] using hz)

/-- A local quotient rewrite replaces a SQUAREFREE target subset by
one more coin, leaving an arbitrary current remainder unchanged.
Replacement multiplicities and target sizes are unrestricted. -/
def QuotientExpansionStep {k : ℕ} {Q : Type*} [AddCommGroup Q]
    (q : Fin k → Q) (s t : Multiset (Fin k)) : Prop :=
  ∃ S : Finset (Fin k), ∃ p rest : Multiset (Fin k),
    s=S.val+rest ∧ t=p+rest ∧ p.card=S.card+1 ∧ (p.map q).sum=∑ i ∈ S, q i

/-- Each local rewrite increases the actual multiset count by one. -/
theorem quotientExpansionStep_card
    {k : ℕ} {Q : Type*} [AddCommGroup Q] {q : Fin k → Q}
    {s t : Multiset (Fin k)} (h : QuotientExpansionStep q s t) : t.card=s.card+1 := by
  obtain ⟨S,p,rest,rfl,rfl,hcard,_⟩ := h
  simp only [Multiset.card_add,hcard]
  change S.card+1+rest.card=S.card+rest.card+1
  omega

/-- Local one-coin rewriting preserves the ACTUAL sum beside any
mapped thin fibre, not merely its quotient value. -/
theorem quotientExpansionStep_lifts_of_valid_actual_thin_fibre
    {m k d M : ℕ} (hm : 0 < m) [NeZero M] [NeZero (d*M)]
    (τ : ZMod M →+ ZMod (d*M)) (hτ : Function.Injective τ) (u : Fin m → ZMod M)
    (g : Fin (m+k) → ZMod (d*M)) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ (u i))
    (hcover : ∀ z : ZMod M, z ≠ ∑ i, u i →
      ∃ s : Multiset (Fin m), s.card=m-1 ∧ (s.map u).sum=z)
    {s t : Multiset (Fin k)}
    (h : QuotientExpansionStep (fun i ↦ ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m i))) s t) :
    (t.map (fun i ↦ g (Fin.natAdd m i))).sum=(s.map (fun i ↦ g (Fin.natAdd m i))).sum := by
  obtain ⟨S,p,rest,rfl,rfl,hcard,hq⟩ := h
  simp only [Multiset.map_add,Multiset.sum_add]
  rw [outside_expansion_eq_of_valid_actual_thin_fibre_quotient hm τ hτ u g hg hpref hcover S p hcard hq]
  rfl

/-- Starting with one coin per outsider, m legal quotient expansions
would replace a zero-sum m-fibre entirely. Thus such a rewrite path
cannot exist. This covers arbitrary sequential multi-target patterns,
not just disjoint edges or ranked doubling forests. -/
theorem not_expansion_path_of_valid_zero_sum_thin_fibre
    {m k d M : ℕ} (hm : 0 < m) [NeZero M] [NeZero (d*M)]
    (τ : ZMod M →+ ZMod (d*M)) (hτ : Function.Injective τ) (u : Fin m → ZMod M)
    (g : Fin (m+k) → ZMod (d*M)) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ (u i)) (hzero : (∑ i, u i)=0)
    (hcover : ∀ z : ZMod M, z ≠ ∑ i, u i →
      ∃ s : Multiset (Fin m), s.card=m-1 ∧ (s.map u).sum=z)
    (s : ℕ → Multiset (Fin k)) (hstart : s 0=(Finset.univ : Finset (Fin k)).val)
    (hstep : ∀ j < m, QuotientExpansionStep
      (fun i ↦ ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m i))) (s j) (s (j+1))) : False := by
  have hinv (j : ℕ) (hj : j ≤ m) : (s j).card=k+j ∧
      ((s j).map (fun i ↦ g (Fin.natAdd m i))).sum=∑ i : Fin k, g (Fin.natAdd m i) := by
    induction j with
    | zero =>
      rw [hstart]
      constructor
      · simp
      · rfl
    | succ j ih =>
      obtain ⟨hc,hs⟩ := ih (by omega)
      have h := hstep j (by omega)
      constructor
      · rw [quotientExpansionStep_card h,hc]
        omega
      · exact (quotientExpansionStep_lifts_of_valid_actual_thin_fibre hm τ hτ u g hg hpref hcover h).trans hs
  obtain ⟨hc,hs⟩ := hinv m le_rfl
  let a : Fin (m+k) := Fin.castAdd k (⟨0,hm⟩ : Fin m)
  apply not_validTuple_of_multiset_omission g ((s m).map (Fin.natAdd m))
    (by rw [Multiset.card_map,hc,Nat.add_comm]) ?_ a ?_ hg
  · rw [Multiset.map_map,Fin.sum_univ_add]
    simp only [hpref,← map_sum,hzero,map_zero,zero_add]
    exact hs
  · intro ha
    obtain ⟨j,_,hja⟩ := Multiset.mem_map.mp ha
    have hv := congrArg Fin.val hja
    simp only [a,Fin.val_natAdd,Fin.val_castAdd] at hv
    omega

/-- Any m-step one-coin quotient expansion path contradicts validity
beside an actual mapped m-cycle, at EVERY positive index and with all
original lift bits. The path need not arise from doubling relations. -/
theorem not_expansion_path_of_valid_mapped_cycle
    {m k d : ℕ} (hm : 2 ≤ m) [NeZero d] [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (s : ℕ → Multiset (Fin k)) (hstart : s 0=(Finset.univ : Finset (Fin k)).val)
    (hstep : ∀ j < m, QuotientExpansionStep
      (fun i ↦ ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m i))) (s j) (s (j+1))) : False := by
  letI : NeZero (d*(2^m-1)) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hsum : (∑ i : Fin m, ((2^i.val : ℕ) : ZMod (2^m-1)))=0 := by
    rw [← Nat.cast_sum,sum_binary_powers,ZMod.natCast_self]
  apply not_expansion_path_of_valid_zero_sum_thin_fibre (by omega) τ hτ
    (fun i : Fin m ↦ ((2^i.val : ℕ) : ZMod (2^m-1))) g hg hpref hsum ?_ s hstart hstep
  intro z hz
  exact exists_power_multiset_card_pred_of_ne_zero hm z (by simpa only [hsum] using hz)

end MinModulus

import MinModulus.InductiveOutsideSpan

/-!
# Actual half descent from proper deleted outside spans

An injective K-coordinate subset cube in a finite abelian group of order
less than 3 * 2^(K-1) has only index-two proper one-coordinate-deleted spans.
Beside an actual full-cover cyclic fibre, pulling this subgroup back gives
a genuine retained valid tuple modulo half the parent modulus. Actual
subbinary mapped cycles automatically supply both coverage and the window.

The result removes a structural branch, not the arbitrary G1 obligation.
No induction hypothesis or global lower bound is assumed here.
-/

namespace MinModulus
open Finset

/-- In the strict three-halves window, a proper span after deleting one
coordinate from an injective cube has index exactly TWO. This elementary
density fact works in any finite abelian group. -/
theorem deleted_subset_cube_proper_span_index_two
    {k : ℕ} {G : Type*} [AddCommGroup G] [Fintype G]
    (q : Fin (k+1) → G)
    (hi : Function.Injective (fun S : Finset (Fin (k+1)) ↦ ∑ i ∈ S, q i))
    (hwindow : Fintype.card G < 3*2^k) (j : Fin (k+1))
    (hproper : AddSubgroup.closure (Set.range (fun i : Fin k ↦ q (j.succAbove i))) ≠ ⊤) :
    Nat.card (G ⧸ AddSubgroup.closure (Set.range (fun i : Fin k ↦ q (j.succAbove i))))=2 := by
  classical
  let H := AddSubgroup.closure (Set.range (fun i : Fin k ↦ q (j.succAbove i)))
  letI : Fintype H := Fintype.ofFinite H
  let f : Finset (Fin k) → H := fun S ↦ ⟨∑ i ∈ S, q (j.succAbove i),
    H.sum_mem (fun i _ ↦ AddSubgroup.subset_closure ⟨i,rfl⟩)⟩
  have hf : Function.Injective f := by
    intro S T heq
    apply Finset.map_injective j.succAboveEmb
    apply hi
    simpa only [Finset.sum_map,Fin.coe_succAboveEmb] using congrArg Subtype.val heq
  have hlow : 2^k ≤ Nat.card H := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_finset,Fintype.card_fin] using
      Fintype.card_le_of_injective f hf
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
  have hpos : 0 < Nat.card (G ⧸ H) := Nat.card_pos
  have hne : Nat.card (G ⧸ H) ≠ 1 := by
    intro h
    apply hproper
    apply AddSubgroup.eq_top_of_card_eq H
    rw [hcard,h,one_mul]
  have hupper : Nat.card (G ⧸ H) < 3 := by
    by_contra hnot
    have hmul := Nat.mul_le_mul (by omega : 3 ≤ Nat.card (G ⧸ H)) hlow
    rw [← hcard,Nat.card_eq_fintype_card] at hmul
    omega
  change Nat.card (G ⧸ H)=2
  omega

/-- Any cyclic subgroup homomorphism is killed by the complementary
quotient projection. Injectivity is not required for this direction. -/
theorem castHom_cyclic_subgroup_hom_eq_zero
    {d M : ℕ} [NeZero M] [NeZero (d*M)]
    (τ : ZMod M →+ ZMod (d*M)) (z : ZMod M) :
    ZMod.castHom (dvd_mul_right d M) (ZMod d) (τ z)=0 := by
  have hkill : M • τ z=0 := by
    rw [← map_nsmul]
    have hz : M • z=0 := by simp [nsmul_eq_mul]
    rw [hz,map_zero]
  have hdvd : d*M ∣ M*(τ z).val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [Nat.cast_mul,ZMod.natCast_zmod_val,nsmul_eq_mul] using hkill
  have hd : d ∣ (τ z).val := by
    have h : M*d ∣ M*(τ z).val := (by simpa only [Nat.mul_comm] using hdvd)
    exact Nat.dvd_of_mul_dvd_mul_left (NeZero.pos M) h
  rw [ZMod.castHom_apply,← ZMod.natCast_val,ZMod.natCast_eq_zero_iff]
  exact hd

/-- An actual valid tuple lying in the kernel of a surjection onto a
two-element group gives an ACTUAL valid tuple modulo half the cyclic
order. This is a subgroup construction, not a numerical substitute for
half descent. -/
theorem admitsValidTuple_half_of_surjective_two_element_kernel
    {n N : ℕ} [NeZero N] {A : Type*} [AddCommGroup A] [Fintype A]
    (φ : ZMod N →+ A) (hφ : Function.Surjective φ) (hA : Fintype.card A=2)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hmem : ∀ i, φ (g i)=0) :
    AdmitsValidTuple n (N/2) := by
  let H := φ.ker
  let v : Fin n → H := fun i ↦ ⟨g i,(AddMonoidHom.mem_ker).mpr (hmem i)⟩
  have hv : ValidTuple v := by
    apply validTuple_of_comp H.subtype
    exact hg
  have hquot : Nat.card (ZMod N ⧸ H)=2 := by
    have h := Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).toEquiv
    simpa only [Nat.card_eq_fintype_card,hA] using h
  have hcard : Nat.card H=N/2 := by
    have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
    rw [Nat.card_zmod,hquot] at h
    omega
  letI : IsAddCyclic H := AddSubgroup.isAddCyclic H
  let E : H ≃+ ZMod (Nat.card H) := (zmodAddCyclicAddEquiv (G := H) inferInstance).symm
  have hvalid : AdmitsValidTuple n (Nat.card H) :=
    ⟨fun i ↦ E (v i),validTuple_comp hv E.toAddMonoidHom E.injective⟩
  rwa [hcard] at hvalid

/-- Failure of an outside-deleted span in the strict density window
constructs the required G1 half-modulus child. The fibre is arbitrary,
its cover is actual, and no induction hypothesis, SI shape, cycle, or
critical-witness premise is used. -/
theorem admitsValidTuple_half_of_actual_fibre_cover_proper_deleted_span
    {m k d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 0 < m)
    (τ : ZMod M →+ ZMod (d*M)) (hτ : Function.Injective τ)
    (g : Fin (m+(k+1)) → ZMod (d*M)) (hg : ValidTuple g) (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g (Fin.castAdd (k+1) i)=τ (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z)
    (hwindow : d < 3*2^k) (j : Fin (k+1))
    (hproper : AddSubgroup.closure (Set.range (fun i : Fin k ↦
      ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m (j.succAbove i))))) ≠ ⊤) :
    AdmitsValidTuple (m+k) ((d*M)/2) := by
  classical
  letI : NeZero d := ⟨fun hd ↦ NeZero.ne (d*M) (by simp [hd])⟩
  let π : ZMod (d*M) →+ ZMod d := (ZMod.castHom (dvd_mul_right d M) (ZMod d)).toAddMonoidHom
  let q : Fin (k+1) → ZMod d := fun i ↦ π (g (Fin.natAdd m i))
  let H := AddSubgroup.closure (Set.range (fun i : Fin k ↦ q (j.succAbove i)))
  have hi : Function.Injective (fun S : Finset (Fin (k+1)) ↦ ∑ i ∈ S, q i) := by
    intro S T hST
    have hmin (S T : Finset (Fin (k+1))) (hc : S.card ≤ T.card)
        (heq : (∑ i ∈ S, q i)=∑ i ∈ T, q i) : S=T := by
      apply Finset.val_injective
      exact quotient_multiset_eq_of_card_le_of_actual_fibre_cover hm τ hτ g hg u hpref hcover
        T S.val hc heq
    rcases le_total S.card T.card with h | h
    · exact hmin S T h hST
    · exact (hmin T S h hST.symm).symm
  have hH : Nat.card (ZMod d ⧸ H)=2 :=
    deleted_subset_cube_proper_span_index_two q hi (by simpa only [ZMod.card] using hwindow) j hproper
  let φ : ZMod (d*M) →+ (ZMod d ⧸ H) := (QuotientAddGroup.mk' H).comp π
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨a,rfl⟩ := ZMod.natCast_zmod_surjective x
    exact ⟨(a : ZMod (d*M)),map_natCast (ZMod.castHom (dvd_mul_right d M) (ZMod d)) a⟩
  have hφ : Function.Surjective φ := (QuotientAddGroup.mk'_surjective H).comp hπ
  let e : Fin (m+k) ↪ Fin (m+(k+1)) := finSumFinEquiv.symm.toEmbedding.trans
    (((Function.Embedding.refl (Fin m)).sumMap j.succAboveEmb).trans finSumFinEquiv.toEmbedding)
  have hleft (i : Fin m) : e (Fin.castAdd k i)=Fin.castAdd (k+1) i := by simp [e]
  have hright (i : Fin k) : e (Fin.natAdd m i)=Fin.natAdd m (j.succAbove i) := by simp [e]
  apply admitsValidTuple_half_of_surjective_two_element_kernel φ hφ
    (by simpa only [Nat.card_eq_fintype_card] using hH) (fun i ↦ g (e i))
    (validTuple_embedding e g hg)
  intro i
  refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) i
  · rw [hleft,hpref]
    change (QuotientAddGroup.mk' H) (ZMod.castHom (dvd_mul_right d M) (ZMod d) (τ (u a)))=0
    rw [castHom_cyclic_subgroup_hom_eq_zero,map_zero]
  · rw [hright]
    change (QuotientAddGroup.mk' H) (q (j.succAbove b))=0
    exact (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.subset_closure ⟨b,rfl⟩)

/-- At odd group order the index-two alternative is impossible, so every
one-coordinate-deleted cube spans the whole group in the same strict
window. This needs neither tuple validity nor an odd-stratum conjecture. -/
theorem deleted_span_eq_top_of_odd_dense_subset_cube
    {k : ℕ} {G : Type*} [AddCommGroup G] [Fintype G]
    (q : Fin (k+1) → G)
    (hi : Function.Injective (fun S : Finset (Fin (k+1)) ↦ ∑ i ∈ S, q i))
    (hodd : Odd (Fintype.card G)) (hwindow : Fintype.card G < 3*2^k)
    (j : Fin (k+1)) :
    AddSubgroup.closure (Set.range (fun i : Fin k ↦ q (j.succAbove i)))=⊤ := by
  by_contra hnot
  let H := AddSubgroup.closure (Set.range (fun i : Fin k ↦ q (j.succAbove i)))
  have hindex := deleted_subset_cube_proper_span_index_two q hi hwindow j hnot
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
  change Nat.card (G ⧸ H)=2 at hindex
  rw [hindex,Nat.card_eq_fintype_card] at hcard
  obtain ⟨s,hs⟩ := hodd
  omega

/-- Every subbinary mapped cycle supplies the strict deleted-span
density window, with at least one outsider and no outside-size cutoff. -/
theorem subbinary_cycle_index_lt_three_mul_deleted_cube
    {m k d : ℕ} (hm : 2 ≤ m)
    (hsmall : d*(2^m-1) < 2^(m+(k+1))) : d < 3*2^k := by
  have hmexp : 4 ≤ 2^m := by
    have h := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hm
    simpa using h
  have hratio : 2*2^m ≤ 3*(2^m-1) := by omega
  have hprod := Nat.mul_le_mul_right (2^k) hratio
  have hleft : 2^(m+(k+1)) ≤ (3*2^k)*(2^m-1) := by
    rw [pow_add,pow_succ']
    nlinarith
  by_contra hnot
  have hmul := Nat.mul_le_mul_right (2^m-1) (by omega : 3*2^k ≤ d)
  omega

/-- An actual subbinary cycle supplies the cover and density needed to
turn ANY failed outside-deleted span into the genuine G1 half child.
No induction hypothesis, parity restriction, or named witness is needed. -/
theorem admitsValidTuple_half_of_subbinary_mapped_cycle_proper_deleted_span
    {m k d : ℕ} (hm : 2 ≤ m) [NeZero d] [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+(k+1)) → ZMod (d*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd (k+1) i)=τ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (hsmall : d*(2^m-1) < 2^(m+(k+1))) (j : Fin (k+1))
    (hproper : AddSubgroup.closure (Set.range (fun i : Fin k ↦
      ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m (j.succAbove i))))) ≠ ⊤) :
    AdmitsValidTuple (m+k) ((d*(2^m-1))/2) := by
  letI : NeZero (d*(2^m-1)) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  exact admitsValidTuple_half_of_actual_fibre_cover_proper_deleted_span (by omega) τ hτ g hg
    (fun i : Fin m ↦ ((2^i.val : ℕ) : ZMod (2^m-1))) hpref
    (exists_power_multiset_sum_at_mersenne hm)
    (subbinary_cycle_index_lt_three_mul_deleted_cube hm hsmall) j hproper

/-- Unconditional G1 extraction beside any subbinary mapped cycle:
either an actual half-modulus child already exists, or EVERY outside-
coordinate deletion still spans the whole cycle quotient. This closes
all nonsaturated deleted-span cases in this class, at every index. -/
theorem half_descent_or_all_deleted_outside_spans_top_of_subbinary_mapped_cycle
    {m k d : ℕ} (hm : 2 ≤ m) [NeZero d] [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+(k+1)) → ZMod (d*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd (k+1) i)=τ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (hsmall : d*(2^m-1) < 2^(m+(k+1))) :
    AdmitsValidTuple (m+k) ((d*(2^m-1))/2) ∨
      ∀ j : Fin (k+1), AddSubgroup.closure (Set.range (fun i : Fin k ↦
        ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m (j.succAbove i)))))=⊤ := by
  by_cases h : AdmitsValidTuple (m+k) ((d*(2^m-1))/2)
  · exact Or.inl h
  · right
    intro j
    by_contra hproper
    exact h (admitsValidTuple_half_of_subbinary_mapped_cycle_proper_deleted_span
      hm τ hτ g hg hpref hsmall j hproper)

end MinModulus

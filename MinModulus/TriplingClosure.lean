import MinModulus.TriplingOrder
import MinModulus.ActualFibreSidon
import MinModulus.SITwoMultiplierBound

/-!
# Quotient-by-three descent for affine tripling closure

At odd cyclic moduli, validity makes nonzero differences unique. Hence
tripling has at most one collision pair. A tripling-closed tuple descends
through a factor of three with at most one lost coordinate; the image is
an actual valid subtuple before division. Induction and the exact order of
tripling permutations give `3^(n-1) ≤ N` without conjectural inputs.
-/

namespace MinModulus
open Finset

/-- In a valid tuple with injective doubling, a nonzero difference
determines its ordered pair of coordinates uniquely. -/
theorem pair_eq_of_sub_eq_sub_of_validTuple
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G, x+x=y+y → x=y)
    (g : Fin n → G) (hg : ValidTuple g)
    (a b c d : Fin n) (hab : a≠b)
    (he : g a-g b=g c-g d) : a=c ∧ b=d := by
  have hsum : g a+g d=g c+g b := sub_eq_sub_iff_add_eq_add.mp he
  rcases pair_sum_eq_or_diagonal_of_validTuple g hg a d c b hsum with
    (⟨hac,hdb⟩ | ⟨hab',_⟩) | ⟨had,hcb⟩
  · exact ⟨hac,hdb.symm⟩
  · exact False.elim (hab hab')
  · subst d; subst c
    have h := hinj _ _ hsum
    exact False.elim (hab (validTuple_injective g hg h))

/-- The kernel of tripling modulo 3M consists of zero and the two
opposite multiples of M. -/
theorem eq_zero_or_eq_or_neg_of_three_nsmul_eq_zero
    {M : ℕ} [NeZero M] (u : ZMod (3*M)) (hu : 3 • u=0) :
    u=0 ∨ u=(M:ZMod (3*M)) ∨ u=-(M:ZMod (3*M)) := by
  have hdiv : 3*M ∣ 3*u.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [Nat.cast_mul,ZMod.natCast_zmod_val,nsmul_eq_mul] using hu
  have hMdiv : M ∣ u.val := (Nat.mul_dvd_mul_iff_left (by omega : 0<3)).mp hdiv
  obtain ⟨k,hk⟩ := hMdiv
  have hklt : k<3 := by have := u.val_lt; have := NeZero.pos M; nlinarith
  have hval : u=(M*k : ℕ) := by rw [← hk,ZMod.natCast_zmod_val]
  rcases (show k=0 ∨ k=1 ∨ k=2 by omega) with rfl | rfl | rfl
  · left; simpa using hval
  · right; left; simpa using hval
  · right; right
    rw [hval,eq_neg_iff_add_eq_zero,← Nat.cast_add]
    rw [show M*2+M=3*M by omega]
    exact ZMod.natCast_self (3*M)

/-- At an odd cyclic modulus there is at most one unordered collision
pair under tripling, including moduli divisible by three. -/
theorem tripling_collision_mem_pair_of_valid_zmod
    {n M : ℕ} [NeZero M] (hM : Odd M)
    (g : Fin n → ZMod (3*M)) (hg : ValidTuple g)
    {a b c d : Fin n} (hab : a≠b) (heab : 3 • g a=3 • g b)
    (hcd : c≠d) (hecd : 3 • g c=3 • g d) : c=a ∨ c=b := by
  have hN : Odd (3*M) := (by decide : Odd 3).mul hM
  have pair (i j : Fin n) (hij : i≠j) (he : 3 • g i=3 • g j) :
      g i-g j=(M:ZMod (3*M)) ∨ g i-g j=-(M:ZMod (3*M)) := by
    rcases eq_zero_or_eq_or_neg_of_three_nsmul_eq_zero (g i-g j)
      (by rw [smul_sub,he,sub_self]) with hz | hp
    · exact False.elim (hij (validTuple_injective g hg (sub_eq_zero.mp hz)))
    · exact hp
  have hfirst := pair a b hab heab
  have hsecond := pair c d hcd hecd
  have heq : g c-g d=g a-g b ∨ g c-g d=g b-g a := by
    rcases hfirst with ha | ha <;> rcases hsecond with hc | hc
    · left; exact hc.trans ha.symm
    · right; rw [hc,show g b-g a=-(g a-g b) by abel,ha]
    · right; rw [hc,show g b-g a=-(g a-g b) by abel,ha,neg_neg]
    · left; exact hc.trans ha.symm
  rcases heq with he | he
  · exact Or.inl (pair_eq_of_sub_eq_sub_of_validTuple (add_self_injective_zmod hN)
      g hg c d a b hcd he).1
  · exact Or.inr (pair_eq_of_sub_eq_sub_of_validTuple (add_self_injective_zmod hN)
      g hg c d b a hcd he).1

/-- Tripling loses at most one coordinate of a valid odd cyclic tuple. -/
theorem card_le_tripling_image_card_add_one
    {n M : ℕ} [NeZero M] (hM : Odd M)
    (g : Fin n → ZMod (3*M)) (hg : ValidTuple g) :
    n ≤ (Finset.univ.image (fun i ↦ 3 • g i)).card+1 := by
  classical
  let f : Fin n → ZMod (3*M) := fun i ↦ 3 • g i
  by_cases hi : Function.Injective f
  · rw [Finset.card_image_of_injective _ hi]
    simp
  obtain ⟨a,b,he,hab⟩ : ∃ a b, f a=f b ∧ a≠b := by
    simpa [Function.Injective] using hi
  have hinj : Set.InjOn f (Finset.univ.erase a : Finset (Fin n)) := by
    intro c hc d hd hcd
    by_contra hne
    have hca : c≠a := (Finset.mem_erase.mp hc).1
    have hda : d≠a := (Finset.mem_erase.mp hd).1
    have hcb : c=b := (tripling_collision_mem_pair_of_valid_zmod hM g hg hab he hne hcd).resolve_left hca
    have hdb : d=b := (tripling_collision_mem_pair_of_valid_zmod hM g hg hab he (Ne.symm hne) hcd.symm).resolve_left hda
    exact hne (hcb.trans hdb.symm)
  have hcard := Finset.card_le_card (Finset.image_subset_image (f := f) (Finset.erase_subset a Finset.univ))
  rw [Finset.card_image_iff.mpr hinj] at hcard
  simp only [Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ,Fintype.card_fin] at hcard
  have := a.isLt
  change n ≤ (Finset.univ.image f).card+1
  omega

/-- A tripling-closed valid tuple modulo 3M descends to a displayed valid
tripling-closed tuple modulo M, losing at most one coordinate. -/
theorem exists_valid_tripling_closed_third
    {n M : ℕ} [NeZero M] (hM : Odd M)
    (g : Fin n → ZMod (3*M)) (hg : ValidTuple g)
    (hclosed : ∀ i,∃ j,g j=3 • g i) :
    ∃ m, n ≤ m+1 ∧ m ≤ n ∧ ∃ u : Fin m → ZMod M,
      ValidTuple u ∧ ∀ i,∃ j,u j=3 • u i := by
  classical
  let π := ZMod.castHom (dvd_mul_left M 3) (ZMod M)
  let φ := zmodScaleHom 3 M
  let S := Finset.univ.image (fun i ↦ π (g i))
  let e : Fin S.card ≃ S := by simpa only [Fintype.card_coe] using (Fintype.equivFin S).symm
  let u : Fin S.card → ZMod M := fun i ↦ (e i).val
  have he (i) : u i ∈ S := (e i).property
  have huinj : Function.Injective u := fun _ _ h ↦ e.injective (Subtype.ext h)
  have hφ (i) : φ (π (g i))=3 • g i := zmodScaleHom_castHom (g i)
  have hSimage : S.image φ=Finset.univ.image (fun i ↦ 3 • g i) := by
    rw [Finset.image_image]
    exact Finset.image_congr (fun i _ ↦ hφ i)
  have hScard : S.card=(Finset.univ.image (fun i ↦ 3 • g i)).card := by
    rw [← hSimage,Finset.card_image_of_injective _ zmodScaleHom_injective]
  have hex (i) : ∃ j,g j=φ (u i) := by
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp (he i)
    obtain ⟨b,hb⟩ := hclosed a
    exact ⟨b,by rw [← ha,hφ]; exact hb⟩
  let f : Fin S.card → Fin n := fun i ↦ Classical.choose (hex i)
  have hf (i) : g (f i)=φ (u i) := Classical.choose_spec (hex i)
  have hfi : Function.Injective f := by
    intro i j hij
    apply huinj
    apply zmodScaleHom_injective (d := 3) (M := M)
    exact (hf i).symm.trans ((congrArg g hij).trans (hf j))
  have hu : ValidTuple u := by
    apply validTuple_of_comp φ
    have hv : ValidTuple (fun i ↦ g (f i)) := validTuple_embedding ⟨f,hfi⟩ g hg
    simpa only [hf] using hv
  refine ⟨S.card,?_,?_,u,hu,?_⟩
  · rw [hScard]
    exact card_le_tripling_image_card_add_one hM g hg
  · simpa using (Finset.card_image_le (f := fun i ↦ π (g i)) (s := univ))
  · intro i
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp (he i)
    obtain ⟨b,hb⟩ := hclosed a
    have hmem : 3 • u i ∈ S := by
      apply Finset.mem_image.mpr
      refine ⟨b,mem_univ _,?_⟩
      rw [hb,map_nsmul,ha]
    exact ⟨e.symm ⟨3 • u i,hmem⟩,by simp [u]⟩

/-- The last term alone gives a lower bound for a nonempty ternary sum. -/
theorem three_pow_pred_le_sum_ternary_powers {n : ℕ} (hn : 0<n) :
    3^(n-1) ≤ ∑ i : Fin n,3^i.val := by
  let a : Fin n := ⟨n-1,by omega⟩
  exact Finset.single_le_sum (f := fun i : Fin n ↦ 3^i.val)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)

/-- The binary odd-stratum bound is below the power-of-three bound. -/
theorem two_pow_succ_sub_one_le_three_pow (n : ℕ) : 2^(n+1)-1 ≤ 3^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hpos : 0<3^n := by positivity
    have hpos2 : 0<2^(n+1) := by positivity
    rw [pow_succ (3:ℕ),pow_succ (2:ℕ)]
    omega

/-- Range closure suffices at every odd cyclic modulus: even with
nonbijective tripling, a valid n-tuple forces N at least 3^(n-1). -/
theorem three_pow_pred_le_modulus_of_valid_tripling_closed
    {N n : ℕ} (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hclosed : ∀ i,∃ j,g j=3 • g i) : 3^(n-1) ≤ N := by
  induction N using Nat.strong_induction_on generalizing n with
  | h N ih =>
    letI : NeZero N := ⟨hN.pos.ne'⟩
    by_cases hn : 2≤n
    · by_cases h3 : 3 ∣ N
      · obtain ⟨M,rfl⟩ := h3
        have hM : Odd M := (Nat.odd_mul.mp hN).2
        letI : NeZero M := ⟨hM.pos.ne'⟩
        obtain ⟨m,hmn,_,u,hu,huc⟩ := exists_valid_tripling_closed_third hM g hg hclosed
        have hm : 0 < m := by omega
        have hlt : M<3*M := by have := hM.pos; omega
        have hb := ih M hlt hM u hu huc
        have he : 3^m=3*3^(m-1) := by rw [← pow_succ']; congr 1; omega
        have hpow : 3^(n-1) ≤ 3^m := Nat.pow_le_pow_right (by decide) (by omega)
        rw [he] at hpow
        exact hpow.trans (Nat.mul_le_mul_left 3 hb)
      · have hcop : Nat.Coprime 3 N := (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr h3
        have hunit : IsUnit ((3:ℕ) : ZMod N) := (ZMod.isUnit_iff_coprime 3 N).mpr hcop
        let R : Fin n → Fin n := fun i ↦ Classical.choose (hclosed i)
        have hR (i) : g (R i)=3 • g i := Classical.choose_spec (hclosed i)
        have hRi : Function.Injective R := by
          intro i j he
          apply validTuple_injective g hg
          apply hunit.mul_left_cancel
          simp only [← nsmul_eq_mul,← hR,he]
        let P : Equiv.Perm (Fin n) := Equiv.ofBijective R ⟨hRi,Finite.surjective_of_injective hRi⟩
        exact (three_pow_pred_le_sum_ternary_powers (by omega)).trans
          (sum_ternary_powers_le_modulus_of_valid_tripling hn hN g hg P hR)
    · have he : n-1=0 := by omega
      rw [he,pow_zero]
      exact hN.pos

/-- Every tripling-closed valid tuple satisfies G2 at an odd modulus. -/
theorem odd_stratum_lower_bound_of_tripling_closed
    {N n : ℕ} (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hclosed : ∀ i,∃ j,g j=3 • g i) : 2^n-1 ≤ N := by
  cases n with
  | zero => simp
  | succ n =>
    exact (two_pow_succ_sub_one_le_three_pow n).trans
      (by simpa using three_pow_pred_le_modulus_of_valid_tripling_closed hN g hg hclosed)

/-- Every affine tripling map has a fixed center at odd moduli, so the
power-of-three bound also holds for affine range closure. -/
theorem three_pow_pred_le_modulus_of_valid_affine_tripling_closed
    {N n : ℕ} (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (b : ZMod N) (hclosed : ∀ i,∃ j,g j=3 • g i+b) : 3^(n-1) ≤ N := by
  letI : NeZero N := ⟨hN.pos.ne'⟩
  obtain ⟨t,ht⟩ := (Finite.surjective_of_injective
    (f := fun x : ZMod N ↦ x+x) (add_self_injective_zmod hN)) b
  let u : Fin n → ZMod N := fun i ↦ g i-(-t)
  have hu : ValidTuple u := validTuple_sub_const g hg (-t)
  apply three_pow_pred_le_modulus_of_valid_tripling_closed hN u hu
  intro i
  obtain ⟨j,hj⟩ := hclosed i
  refine ⟨j,?_⟩
  dsimp only [u]
  rw [hj,← ht]
  simp only [three_nsmul]
  abel

/-- Every odd-modulus tuple below the power-of-three threshold escapes
every affine tripling map; in particular this applies to any G2 counterexample. -/
theorem exists_affine_tripling_escape_of_lt_three_pow_pred
    {N n : ℕ} (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hsmall : N<3^(n-1)) (b : ZMod N) : ∃ i,∀ j,g j≠3 • g i+b := by
  classical
  by_contra hn
  push Not at hn
  exact (not_le_of_gt hsmall)
    (three_pow_pred_le_modulus_of_valid_affine_tripling_closed hN g hg b hn)

end MinModulus

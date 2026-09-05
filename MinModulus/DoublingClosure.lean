/-
# Full global bound for affine-doubling-closed valid tuples

Validity forces all doubling orbits to meet, even when doubling is not a
permutation. In a group with at most one nonzero involution, it also permits
at most one collision pair. Starting at a coordinate with no predecessor
then visits the entire tuple: any other branch would create another pair.

Thus a cyclic valid tuple closed under x ↦ 2*x+b is, after translation and
reindexing, one full initial segment of a doubling orbit. Reflect validity
through multiplication by its first entry and apply the proved fixed-set
theorem. This gives the full global lower bound for this structural class,
in every dimension and stratum, with no G1/G2/G3 input. It does not assert
affine doubling closure for arbitrary valid tuples.
-/
import MinModulus.G1DoublingCycleRigidity
import MinModulus.OddOrder
import Mathlib.Dynamics.PeriodicPts.Lemmas

namespace MinModulus
open Finset Function

/-- Every forward orbit in a finite set eventually reaches a periodic point. -/
theorem exists_periodic_iterate_finite
    {α : Type*} [Finite α] (R : α → α) (a : α) :
    ∃ k, R^[k] a ∈ periodicPts R := by
  have h := not_injective_infinite_finite (fun k : ℕ ↦ R^[k] a)
  simp only [Injective, not_forall] at h
  obtain ⟨i, j, hij, hne⟩ := h
  have aux : ∀ i j, i < j → R^[i] a = R^[j] a →
      ∃ k, R^[k] a ∈ periodicPts R := by
    intro i j hlt heq
    refine ⟨i, j - i, by omega, ?_⟩
    change R^[j - i] (R^[i] a) = R^[i] a
    rw [← iterate_add_apply, Nat.sub_add_cancel (by omega)]
    exact heq.symm
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact aux i j hlt hij
  · exact aux j i hgt hij.symm

/-- A doubling permutation on a valid tuple is transitive, including singleton tuples. -/
theorem exists_iterate_eq_of_valid_doubling_perm
    {d : ℕ} {G : Type*} [AddCommGroup G]
    (x : Fin d → G) (hx : ValidTuple x)
    (R : Equiv.Perm (Fin d)) (hd : ∀ i, x (R i) = 2 • x i)
    (a b : Fin d) : ∃ k : ℕ, R^[k] a = b := by
  by_cases hn : 2 ≤ d
  · have hcycle := isCycle_of_valid_doubling hn x hx R hd
    have hab : R.SameCycle a b :=
      ((Equiv.Perm.isCycle_iff_sameCycle (doubling_apply_ne_of_valid hn x hx R hd a)).mp
        hcycle).mpr (doubling_apply_ne_of_valid hn x hx R hd b)
    exact hab.exists_nat_pow_eq
  · refine ⟨0, ?_⟩
    simp only [iterate_zero_apply]
    apply Fin.ext
    omega

/-- All periodic coordinates of a valid doubling-closed tuple lie on one cycle.
No injectivity of the doubling map or restriction on two-torsion is needed. -/
theorem exists_iterate_eq_of_valid_doubling_periodic
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (R : Fin n → Fin n) (hd : ∀ i, g (R i) = 2 • g i)
    {a b : Fin n} (ha : a ∈ periodicPts R) (hb : b ∈ periodicPts R) :
    ∃ k, R^[k] a = b := by
  classical
  let P := periodicPts R
  let d := Fintype.card P
  let e : Fin d ≃ P := (Fintype.equivFin P).symm
  let p : Equiv.Perm P := (bijOn_periodicPts R).equiv R
  let r : Equiv.Perm (Fin d) := e.trans (p.trans e.symm)
  let emb : Fin d ↪ Fin n := e.toEmbedding.trans (Function.Embedding.subtype P)
  have hconj : ∀ i, emb (r i) = R (emb i) := by
    intro i
    simp [emb, r, p, Set.BijOn.equiv]
    rfl
  have hv := validTuple_embedding emb g hg
  have hd' : ∀ i, g (emb (r i)) = 2 • g (emb i) := by
    intro i
    rw [hconj, hd]
  obtain ⟨k, hk⟩ := exists_iterate_eq_of_valid_doubling_perm
    (fun i ↦ g (emb i)) hv r hd' (e.symm ⟨a, ha⟩) (e.symm ⟨b, hb⟩)
  have hiter : ∀ k i, emb (r^[k] i) = R^[k] (emb i) := by
    intro k
    induction k with
    | zero => intro i; rfl
    | succ k ih =>
      intro i
      rw [iterate_succ_apply', hconj, ih, iterate_succ_apply']
  refine ⟨k, ?_⟩
  have heq := congrArg emb hk
  rw [hiter] at heq
  have hea : emb (e.symm ⟨a, ha⟩) = a := by
    change (e (e.symm ⟨a, ha⟩)).val = a
    rw [e.apply_symm_apply]
  have heb : emb (e.symm ⟨b, hb⟩) = b := by
    change (e (e.symm ⟨b, hb⟩)).val = b
    rw [e.apply_symm_apply]
  rwa [hea, heb] at heq

/-- Validity rules out separate doubling components in any abelian group. -/
theorem doubling_orbits_meet_of_valid
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (R : Fin n → Fin n) (hd : ∀ i, g (R i) = 2 • g i)
    (a b : Fin n) : ∃ k l, R^[k] a = R^[l] b := by
  obtain ⟨i, hi⟩ := exists_periodic_iterate_finite R a
  obtain ⟨j, hj⟩ := exists_periodic_iterate_finite R b
  obtain ⟨k, hk⟩ := exists_iterate_eq_of_valid_doubling_periodic g hg R hd hi hj
  exact ⟨k + i, j, by simpa [iterate_add_apply] using hk⟩

/-- With at most one nonzero involution, validity allows only one unordered
pair of distinct coordinates having the same double. -/
theorem doubling_collision_mem_pair_of_valid
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (R : Fin n → Fin n) (hd : ∀ i, g (R i) = 2 • g i)
    {h : G} (hh : h + h = 0)
    (hinv : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    {a b c d : Fin n} (hab : a ≠ b) (hrab : R a = R b)
    (hcd : c ≠ d) (hrcd : R c = R d) : c = a ∨ c = b := by
  have hpair : ∀ {u v : Fin n}, u ≠ v → R u = R v → g u - g v = h := by
    intro u v huv hR
    have hzero : (g u - g v) + (g u - g v) = 0 := by
      have heq : 2 • g u = 2 • g v := (hd u).symm.trans ((congrArg g hR).trans (hd v))
      simp only [two_nsmul] at heq
      rw [show (g u - g v) + (g u - g v) = (g u + g u) - (g v + g v) by abel,
        heq, sub_self]
    rcases hinv _ hzero with hz | heq
    · exact False.elim (huv (validTuple_injective g hg (sub_eq_zero.mp hz)))
    · exact heq
  have hne : h ≠ 0 := by
    rw [← hpair hab hrab]
    exact sub_ne_zero.mpr ((validTuple_injective g hg).ne hab)
  let w : Fin n → ℤ := fun i ↦ (if i = c then 1 else 0) - (if i = d then 1 else 0)
  have hw : Witness g h w := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hw
      have := congrFun hw c
      simp [w, hcd] at this
    · intro i; simp only [w]; split_ifs <;> norm_num
    · simp [w, Finset.sum_sub_distrib]
    · simp only [w, sub_smul, ite_smul, one_smul, zero_smul]
      simpa [Finset.sum_sub_distrib] using hpair hcd hrcd
  have ha := common_touched_of_pair_difference g hg hh hne (hpair hab.symm hrab.symm) w hw
  have hb := common_touched_of_pair_difference g hg hh hne (hpair hab hrab) w hw
  have hacd : a = c ∨ a = d := by
    by_contra hc
    push Not at hc
    exact ha (by simp [w, hc.1, hc.2])
  have hbcd : b = c ∨ b = d := by
    by_contra hc
    push Not at hc
    exact hb (by simp [w, hc.1, hc.2])
  rcases hacd with hac | had
  · exact Or.inl hac.symm
  rcases hbcd with hbc | hbd
  · exact Or.inr hbc.symm
  exact False.elim (hab (had.trans hbd.symm))

/-- A valid doubling-closed tuple in a group with cyclic two-torsion has a
forward orbit containing every coordinate, allowing a tail feeding a cycle. -/
theorem exists_full_doubling_orbit_of_valid
    {n : ℕ} (hn : 0 < n) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (R : Fin n → Fin n) (hd : ∀ i, g (R i) = 2 • g i)
    {h : G} (hh : h + h = 0)
    (hinv : ∀ u : G, u + u = 0 → u = 0 ∨ u = h) :
    ∃ a, ∀ b, ∃ k, R^[k] a = b := by
  classical
  by_cases hR : Injective R
  · let p : Equiv.Perm (Fin n) := Equiv.ofBijective R
      ⟨hR, (Finite.injective_iff_surjective).mp hR⟩
    refine ⟨⟨0, hn⟩, fun b ↦ ?_⟩
    exact exists_iterate_eq_of_valid_doubling_perm g hg p hd _ b
  have hns : ¬ Surjective R := fun hs ↦ hR ((Finite.injective_iff_surjective).mpr hs)
  obtain ⟨a, ha⟩ : ∃ a, ∀ b, R b ≠ a := by simpa [Surjective] using hns
  let A : Set (Fin n) := Set.range (fun k : ℕ ↦ R^[k] a)
  have haA : a ∈ A := ⟨0, rfl⟩
  have hclosed : ∀ b ∈ A, R b ∈ A := by
    rintro b ⟨k, rfl⟩
    exact ⟨k + 1, iterate_succ_apply' R k a⟩
  let rA : A → A := fun b ↦ ⟨R b, hclosed b b.property⟩
  have hnot : ¬ Injective rA := by
    intro hi
    obtain ⟨b, hb⟩ := (Finite.injective_iff_surjective.mp hi) ⟨a, haA⟩
    exact ha b (congrArg Subtype.val hb)
  obtain ⟨u, v, huv, hne⟩ : ∃ u v, rA u = rA v ∧ u ≠ v := by
    simpa [Injective] using hnot
  have huv' : R u.val = R v.val := congrArg Subtype.val huv
  have hne' : u.val ≠ v.val := fun heq ↦ hne (Subtype.ext heq)
  have hback : ∀ b, R b ∈ A → b ∈ A := by
    intro b hb
    by_contra hbA
    obtain ⟨k, hk⟩ := hb
    cases k with
    | zero => exact ha b hk.symm
    | succ k =>
      have hba : b ≠ R^[k] a := fun heq ↦ hbA ⟨k, heq.symm⟩
      have hr : R b = R (R^[k] a) := by
        simpa [iterate_succ_apply'] using hk.symm
      rcases doubling_collision_mem_pair_of_valid g hg R hd hh hinv hne' huv' hba hr with
        heq | heq
      · exact hbA (heq ▸ u.property)
      · exact hbA (heq ▸ v.property)
  have hbackIter : ∀ k b, R^[k] b ∈ A → b ∈ A := by
    intro k
    induction k with
    | zero => intro b hb; exact hb
    | succ k ih =>
      intro b hb
      apply ih b
      apply hback
      simpa [iterate_succ_apply'] using hb
  refine ⟨a, fun b ↦ ?_⟩
  obtain ⟨k, l, hkl⟩ := doubling_orbits_meet_of_valid g hg R hd a b
  exact hbackIter l b ⟨k, hkl⟩

/-- Any reachable point of a finite dynamical system is reached before the
ambient cardinality: a shortest path cannot repeat a coordinate. -/
theorem exists_iterate_lt_card_of_reachable
    {α : Type*} [Fintype α] (R : α → α) (a b : α)
    (hb : ∃ k, R^[k] a = b) :
    ∃ k < Fintype.card α, R^[k] a = b := by
  classical
  let k := Nat.find hb
  have hk : R^[k] a = b := Nat.find_spec hb
  have hmin : ∀ l, R^[l] a = b → k ≤ l := fun l hl ↦ Nat.find_min' hb hl
  have hinj : Injective (fun i : Fin (k + 1) ↦ R^[i.val] a) := by
    have aux : ∀ i j : Fin (k + 1), i.val < j.val → R^[i.val] a ≠ R^[j.val] a := by
      intro i j hij heq
      have heq' : R^[k - j.val + i.val] a = b := by
        rw [iterate_add_apply, heq, ← iterate_add_apply,
          Nat.sub_add_cancel (by omega)]
        exact hk
      have := hmin _ heq'
      omega
    intro i j heq
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with hlt | he | hgt
    · exact False.elim (aux i j hlt heq)
    · exact he
    · exact False.elim (aux j i hgt heq.symm)
  have hcard := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at hcard
  exact ⟨k, by omega, hk⟩

/-- The first `n` iterates enumerate a valid doubling-closed tuple without
repetition, under the cyclic two-torsion hypothesis. -/
theorem exists_doubling_orbit_equiv_of_valid
    {n : ℕ} (hn : 0 < n) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (R : Fin n → Fin n) (hd : ∀ i, g (R i) = 2 • g i)
    {h : G} (hh : h + h = 0)
    (hinv : ∀ u : G, u + u = 0 → u = 0 ∨ u = h) :
    ∃ a, ∃ e : Equiv.Perm (Fin n), ∀ i, g (e i) = 2 ^ i.val • g a := by
  classical
  obtain ⟨a, ha⟩ := exists_full_doubling_orbit_of_valid hn g hg R hd hh hinv
  let f : Fin n → Fin n := fun i ↦ R^[i.val] a
  have hf : Surjective f := by
    intro b
    obtain ⟨k, hk, hkb⟩ := exists_iterate_lt_card_of_reachable R a b (ha b)
    refine ⟨⟨k, by simpa using hk⟩, hkb⟩
  let e : Equiv.Perm (Fin n) := Equiv.ofBijective f
    ⟨Finite.injective_iff_surjective.mpr hf, hf⟩
  have hiter : ∀ k, g (R^[k] a) = 2 ^ k • g a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [iterate_succ_apply', hd, ih, ← mul_nsmul, pow_succ', Nat.mul_comm]
  exact ⟨a, e, fun i ↦ hiter i.val⟩

/-- Cyclic valid doubling-closed tuples are full doubling-orbit segments,
including the non-permutation even-modulus case. -/
theorem exists_doubling_orbit_equiv_of_valid_zmod
    {n N : ℕ} [NeZero N] (hn : 0 < n)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (R : Fin n → Fin n) (hd : ∀ i, g (R i) = 2 • g i) :
    ∃ a, ∃ e : Equiv.Perm (Fin n), ∀ i, g (e i) = 2 ^ i.val • g a := by
  rcases Nat.even_or_odd N with hN | hN
  · obtain ⟨M, hM⟩ := hN
    have hNM : N = 2 * M := by omega
    exact exists_doubling_orbit_equiv_of_valid hn g hg R hd (half_add_half hNM)
      (fun u hu ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hNM u hu)
  · apply exists_doubling_orbit_equiv_of_valid hn g hg R hd (h := 0) (by simp)
    intro u hu
    left
    apply add_self_injective_zmod hN
    simpa using hu

/-- Affine doubling closure becomes ordinary doubling closure after adding
the affine constant to every tuple entry. -/
theorem exists_affine_doubling_orbit_equiv_of_valid
    {n N : ℕ} [NeZero N] (hn : 0 < n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hclosed : ∀ i, ∃ j, g j = 2 • g i + b) :
    ∃ a, ∃ e : Equiv.Perm (Fin n),
      ∀ i, g (e i) + b = 2 ^ i.val • (g a + b) := by
  classical
  let R : Fin n → Fin n := fun i ↦ Classical.choose (hclosed i)
  have hR : ∀ i, g (R i) = 2 • g i + b := fun i ↦ Classical.choose_spec (hclosed i)
  have hv : ValidTuple (fun i ↦ g i + b) := by
    simpa using validTuple_sub_const g hg (-b)
  have hd : ∀ i, g (R i) + b = 2 • (g i + b) := by
    intro i
    rw [hR]
    simp only [two_nsmul]
    abel
  exact exists_doubling_orbit_equiv_of_valid_zmod hn (fun i ↦ g i + b) hv R hd

/-- Converse of `validTuple_fixed_of_valid`: transport group-theoretic
fixed-set validity back to the paper's congruence formulation. -/
theorem valid_fixed_of_validTuple
    {n N : ℕ} (hg : ValidTuple (fun i : Fin n ↦ (a i.val : ZMod N))) :
    Valid n N := by
  intro k hksum hkval i hi
  have hsum : ∑ i : Fin n, k i.val = n := by
    simpa [dsum, Fin.sum_univ_eq_sum_range] using hksum
  have hcast : ((∑ i ∈ range n, k i * a i : ℕ) : ZMod N) =
      ((∑ i ∈ range n, a i : ℕ) : ZMod N) := by
    rwa [ZMod.natCast_eq_natCast_iff]
  have hvalue : ∑ i : Fin n, k i.val • (a i.val : ZMod N) =
      ∑ i : Fin n, (a i.val : ZMod N) := by
    rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range] at hcast
    push_cast at hcast
    simpa only [nsmul_eq_mul] using hcast
  exact hg (fun i ↦ k i.val) hsum hvalue ⟨i, hi⟩

/-- The full conjectured global lower bound holds for every cyclic valid
tuple closed under one affine doubling map. No global conjectural input,
finite-instance restriction, or permutation assumption is used. -/
theorem global_lower_bound_of_valid_affine_doubling_closed
    {n N : ℕ} [NeZero N] (hn : 2 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hclosed : ∀ i, ∃ j, g j = 2 • g i + b) :
    globalBound n ≤ N := by
  obtain ⟨a₀, e, he⟩ := exists_affine_doubling_orbit_equiv_of_valid (by omega) g hg b hclosed
  have hv : ValidTuple (fun i ↦ g (e i) + b) := by
    simpa using validTuple_sub_const (fun i ↦ g (e i))
      (validTuple_embedding e.toEmbedding g hg) (-b)
  have hp : ValidTuple (fun i : Fin n ↦ (2 : ZMod N) ^ i.val) := by
    apply validTuple_of_comp (AddMonoidHom.mulRight (g a₀ + b))
    simpa only [he, AddMonoidHom.mulRight_apply, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      using hv
  have hf : ValidTuple (fun i : Fin n ↦ (a i.val : ZMod N)) := by
    have hs := validTuple_sub_const _ hp (1 : ZMod N)
    convert hs using 1
    funext i
    simp [a, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow]
  have hcard := Fintype.card_le_of_injective g (validTuple_injective g hg)
  simp only [Fintype.card_fin, ZMod.card] at hcard
  exact (nmin_eq hn).2 ⟨by omega, valid_fixed_of_validTuple hf⟩

end MinModulus

/-
# Structure extraction for SI-prefix extensions at the global endpoint

Validity of a doubled coherent prefix forces the extra entry's projection
to be -1 at every even half modulus below the binary threshold. At a
power-gap half modulus this extracts affine doubling closure. Full affine
doubling closure below the binary range in turn extracts a unit-affine
SI normal form.

Consequently, at B(n) for n>=4, a coherent SI prefix of length n-1 under
any multiplier forces the entire valid tuple to be unit-affine SI. The
G3 consumer needs only n-2 coherent SI entries in a valid retained quotient
of length n-1, with all independent upstairs lift bits still allowed.

These are structure conclusions for actual tuples, not assumptions about
arbitrary endpoints. No unrestricted global conjectural input is used.
-/
import MinModulus.SIMultiplierStrata
import Mathlib.GroupTheory.Perm.ViaEmbedding

namespace MinModulus
open Finset

/-- Below the binary range a full scaled SI tuple must have a unit
multiplier: a proper cyclic subgroup would violate the binary bound. -/
theorem isUnit_of_valid_scaled_fixed_lt_two_pow
    {n N : ℕ} [NeZero N] (hn : 0 < n) (hupper : N < 2 ^ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin n)) (c b : ZMod N)
    (hfull : ∀ i, g (e i) = c * (a i.val : ZMod N) + b) : IsUnit c := by
  obtain ⟨d, hd, u, hu, hc⟩ := ZMod.eq_unit_mul_divisor c
  obtain ⟨M, hM⟩ := hd
  subst N
  obtain ⟨v, rfl⟩ := hu
  have hNpos := Nat.pos_of_ne_zero (NeZero.ne (d * M))
  have hdpos := Nat.pos_of_mul_pos_right hNpos
  have hMpos := Nat.pos_of_mul_pos_left hNpos
  letI : NeZero M := ⟨ne_of_gt hMpos⟩
  let φ : ZMod (d * M) ≃+ ZMod (d * M) :=
    (ZMod.AddAutEquivUnits (d * M)).symm (Additive.ofMul v)
  have hv := validTuple_sub_const (fun i ↦ g (e i))
    (validTuple_embedding e.toEmbedding g hg) b
  have hw := validTuple_comp hv φ.symm.toAddMonoidHom φ.symm.injective
  change ValidTuple (fun i ↦ φ.symm (g (e i) - b)) at hw
  have hnorm : ∀ i, φ.symm (g (e i) - b) = ((d * a i.val : ℕ) : ZMod (d * M)) := by
    intro i
    apply φ.injective
    rw [φ.apply_symm_apply, hfull, add_sub_cancel_right, hc]
    change (v : ZMod (d * M)) * d * (a i.val : ZMod (d * M)) =
      (v : ZMod (d * M)) * ((d * a i.val : ℕ) : ZMod (d * M))
    push_cast
    ring
  have hf : ValidTuple (fun i : Fin n ↦ (a i.val : ZMod M)) := by
    apply validTuple_of_comp (zmodScaleHom d M)
    simpa only [zmodScaleHom_natCast, ← hnorm] using hw
  have hbound := two_pow_pred_le_card_of_validTuple _ hf
  simp only [ZMod.card] at hbound
  have hp : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  have hd1 : d = 1 := by nlinarith
  have hdcast : (d : ZMod (d * M)) = 1 := by
    simpa only [Nat.cast_one] using congrArg (fun k : ℕ ↦ (k : ZMod (d * M))) hd1
  rw [hc, hdcast, mul_one]
  exact v.isUnit

/-- Full affine doubling closure below the binary range extracts an
actual unit-affine SI normal form, including in even moduli. -/
theorem exists_unit_affine_fixed_of_valid_affine_doubling_closed_lt_two_pow
    {n N : ℕ} [NeZero N] (hn : 0 < n) (hupper : N < 2 ^ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hclosed : ∀ i, ∃ j, g j = 2 • g i + b) :
    ∃ e : Equiv.Perm (Fin n), ∃ c z : ZMod N,
      IsUnit c ∧ ∀ i, g (e i) = c * (a i.val : ZMod N) + z := by
  obtain ⟨a₀, e, he⟩ := exists_affine_doubling_orbit_equiv_of_valid hn g hg b hclosed
  have hfull : ∀ i, g (e i) = (g a₀ + b) * (a i.val : ZMod N) + g a₀ := by
    intro i
    have h := he i
    simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at h
    simp only [a, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_one]
    linear_combination h
  exact ⟨e, g a₀ + b, g a₀,
    isUnit_of_valid_scaled_fixed_lt_two_pow hn hupper g hg e _ _ hfull, hfull⟩

/-- At the global endpoint in dimension at least four, a divisor-scaled
SI prefix forces the complete tuple to be unit-affine SI. -/
theorem exists_unit_affine_fixed_of_valid_divisor_prefix_at_endpoint
    {m d M : ℕ} [NeZero (d * M)] (hm : 3 ≤ m)
    (hendpoint : d * M = globalBound (m + 1))
    (g : Fin (m + 1) → ZMod (d * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc = ((d * a i.val : ℕ) : ZMod (d * M))) :
    ∃ e : Equiv.Perm (Fin (m + 1)), ∃ c z : ZMod (d * M),
      IsUnit c ∧ ∀ i, g (e i) = c * (a i.val : ZMod (d * M)) + z := by
  have hNpos := Nat.pos_of_ne_zero (NeZero.ne (d * M))
  have hdpos := Nat.pos_of_mul_pos_right hNpos
  have hMpos := Nat.pos_of_mul_pos_left hNpos
  letI : NeZero M := ⟨ne_of_gt hMpos⟩
  have hlog : 2 ≤ Nat.log 2 (m + 1) := by
    apply (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr
    norm_num
    omega
  have hloglt : Nat.log 2 (m + 1) < m + 1 :=
    Nat.log_lt_of_lt_pow (by omega) Nat.lt_two_pow_self
  have hdelta : 4 ≤ 2 ^ Nat.log 2 (m + 1) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hlog
  have hpowpos : 0 < 2 ^ (m + 1) := by positivity
  have hupper : d * M < 2 ^ (m + 1) := by unfold globalBound at hendpoint; omega
  have hcover : d * M ≤ 2 ^ (m + 1) - 3 := by unfold globalBound at hendpoint; omega
  have hd := divisor_le_two_of_valid_divisor_fixed_prefix_lt_two_pow hm g hg hprefix hupper
  interval_cases d
  · have hfull := eq_fixed_of_valid_fixed_prefix_of_modulus_le (by omega) hcover g hg
      (by simpa using hprefix)
    exact ⟨Equiv.refl _, 1, 0, isUnit_one, by intro i; simp [hfull]⟩
  · let t := Nat.log 2 (m + 1) - 1
    have ht : 1 ≤ t := by dsimp [t]; omega
    have htm : t < m := by dsimp [t]; omega
    have hp : 2 ^ Nat.log 2 (m + 1) = 2 * 2 ^ t := by
      rw [← pow_succ']; congr 1; dsimp [t]; omega
    have hM : M = 2 ^ m - 2 ^ t := by
      unfold globalBound at hendpoint
      rw [pow_succ', hp] at hendpoint
      omega
    have hclosed := affine_doubling_closed_of_valid_doubled_fixed_prefix
      (by omega) ht htm hM g hg hprefix
    exact exists_unit_affine_fixed_of_valid_affine_doubling_closed_lt_two_pow
      (by omega) hupper g hg 2 hclosed

/-- An actual coherent SI prefix of length n-1 at B(n), n>=4, forces
the entire valid tuple to be unit-affine SI, even if the given prefix
multiplier is not a unit. This is not classification of arbitrary tuples. -/
theorem exists_unit_affine_fixed_of_valid_scaled_prefix_at_endpoint
    {m N : ℕ} [NeZero N] (hm : 3 ≤ m) (hendpoint : N = globalBound (m + 1))
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 1))) (c b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc) = c * (a i.val : ZMod N) + b) :
    ∃ p : Equiv.Perm (Fin (m + 1)), ∃ u z : ZMod N,
      IsUnit u ∧ ∀ i, g (p i) = u * (a i.val : ZMod N) + z := by
  revert hendpoint
  obtain ⟨d, hd, u, hu, hc⟩ := ZMod.eq_unit_mul_divisor c
  obtain ⟨M, hM⟩ := hd
  subst N
  intro hendpoint
  obtain ⟨v, rfl⟩ := hu
  let φ : ZMod (d * M) ≃+ ZMod (d * M) :=
    (ZMod.AddAutEquivUnits (d * M)).symm (Additive.ofMul v)
  have hv := validTuple_sub_const (fun i ↦ g (e i))
    (validTuple_embedding e.toEmbedding g hg) b
  have hw := validTuple_comp hv φ.symm.toAddMonoidHom φ.symm.injective
  have hnorm : ∀ i : Fin m,
      φ.symm (g (e i.castSucc) - b) = ((d * a i.val : ℕ) : ZMod (d * M)) := by
    intro i
    apply φ.injective
    rw [φ.apply_symm_apply, hprefix, add_sub_cancel_right, hc]
    change (v : ZMod (d * M)) * d * (a i.val : ZMod (d * M)) =
      (v : ZMod (d * M)) * ((d * a i.val : ℕ) : ZMod (d * M))
    push_cast
    ring
  obtain ⟨p, w, z, hwunit, hfull⟩ :=
    exists_unit_affine_fixed_of_valid_divisor_prefix_at_endpoint hm hendpoint
      (fun i ↦ φ.symm (g (e i) - b)) hw hnorm
  refine ⟨p.trans e, (v : ZMod (d * M)) * w, (v : ZMod (d * M)) * z + b,
    v.isUnit.mul hwunit, ?_⟩
  intro i
  have h := congrArg φ (hfull i)
  rw [φ.apply_symm_apply] at h
  change g (e (p i)) - b = (v : ZMod (d * M)) * (w * (a i.val : ZMod (d * M)) + z) at h
  change g (e (p i)) = _
  linear_combination h

/-- G3 needs only n-2 coherent SI entries in an actual valid retained
quotient of length n-1: endpoint rigidity extracts the missing SI entry
and a unit multiplier. All independent upstairs lift bits remain allowed.
The retained quotient's validity is essential and explicit. -/
theorem not_validTuple_exceptional_of_valid_quotient_scaled_short_prefix
    {m : ℕ} (hm : 3 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 2) ≠ m + 2)
    (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1)))
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod (globalBound (m + 1)))
    (hret : ValidTuple (fun i : Fin (m + 1) ↦
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g (e i.castSucc))))
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g (e i.castSucc.castSucc)) = c * (a i.val : ZMod (globalBound (m + 1))) + b) :
    ¬ ValidTuple g := by
  have hB : 2 ≤ globalBound (m + 1) := (nmin_eq (by omega : 2 ≤ m + 1)).1.1
  letI : NeZero (globalBound (m + 1)) := ⟨by omega⟩
  let π := ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
  let f : Fin (m + 1) → ZMod (globalBound (m + 1)) := fun i ↦ π (g (e i.castSucc))
  obtain ⟨p, u, z, hu, hfull⟩ := exists_unit_affine_fixed_of_valid_scaled_prefix_at_endpoint
    hm rfl f hret (Equiv.refl _) c b hprefix
  obtain ⟨v, rfl⟩ := hu
  let φ : ZMod (globalBound (m + 1)) ≃+ ZMod (globalBound (m + 1)) :=
    (ZMod.AddAutEquivUnits (globalBound (m + 1))).symm (Additive.ofMul v)
  let emb : Fin (m + 1) ↪ Fin (m + 2) := ⟨Fin.castSucc, Fin.castSucc_injective (m + 1)⟩
  let E : Equiv.Perm (Fin (m + 2)) := (p.viaEmbedding emb).trans e
  apply not_validTuple_exceptional_of_quotient_affine_fixed_prefix (by omega) hnpow g E φ z
  intro i
  change π (g (e (p.viaEmbedding emb (emb i)))) = _
  rw [Equiv.Perm.viaEmbedding_apply]
  exact hfull i

end MinModulus

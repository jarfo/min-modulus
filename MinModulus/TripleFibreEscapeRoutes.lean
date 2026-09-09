import MinModulus.ExtinctTargetEscapeBudget
import MinModulus.CanonicalCycleTargets

namespace MinModulus
open Finset
open scoped Classical

/-- Every actual length-k walk ends in the kth iterated target set.
Together with walk extraction, this identifies target membership exactly. -/
theorem walk_endpoint_mem_iterated_affine_targets
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (f : ℕ → Fin n) (hstep : ∀ t, t < k → g (f (t+1))+b=2 • (g (f t)+b)) :
    f k ∈ iteratedAffineDoublingTargets g b k := by
  induction k with
  | zero => exact Finset.mem_univ _
  | succ k ih =>
    have hprev := ih (fun t ht ↦ hstep t (by omega))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,f k,hprev,?_⟩
    apply add_right_cancel (b := b)
    calc
      g (f (k+1))+b=2 • (g (f k)+b) := hstep k (by omega)
      _=(2 • g (f k)+b)+b := by simp only [two_nsmul]; abel

/-- A triple fibre excludes every actual length-k walk once n <= 2^k. -/
theorem no_walk_at_power_depth_of_triple_fibre
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (hk : n ≤ 2^k)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (f : ℕ → Fin n) (hstep : ∀ t, t < k → g (f (t+1))+b=2 • (g (f t)+b)) : False := by
  have h := walk_endpoint_mem_iterated_affine_targets g b f hstep
  rw [iterated_affine_targets_eq_empty_of_triple_fibre g hg b z hk htriple] at h
  exact Finset.notMem_empty _ h

/-- Every actual walk at a shift with a triple fibre is shorter than
the ceiling binary logarithm of the original dimension. -/
theorem walk_length_lt_clog_of_triple_fibre
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (f : ℕ → Fin n) (hstep : ∀ t, t < k → g (f (t+1))+b=2 • (g (f t)+b)) :
    k < Nat.clog 2 n := by
  apply (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr
  by_contra hk
  exact no_walk_at_power_depth_of_triple_fibre g hg b z (by omega) htriple f hstep

/-- From every coordinate, a triple fibre supplies an actual doubling
walk to an original escape in fewer than k steps whenever n <= 2^k. -/
theorem exists_short_actual_escape_walk_of_triple_fibre
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (hk : n ≤ 2^k)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (i : Fin n) :
    ∃ t < k, ∃ f : ℕ → Fin n, f 0=i ∧
      (∀ s, s < t → g (f (s+1))+b=2 • (g (f s)+b)) ∧ f t ∈ affineDoublingEscapes g b := by
  classical
  let R : Fin n → Fin n := fun j ↦ if hj : ∃ v, g v=2 • g j+b then Classical.choose hj else j
  have hR (j : Fin n) (hj : j ∉ affineDoublingEscapes g b) : g (R j)=2 • g j+b := by
    have he := affine_double_closed_outside_actual_escapes g b j hj
    simpa only [R,dif_pos he] using Classical.choose_spec he
  let f : ℕ → Fin n := fun t ↦ Nat.rec i (fun _ j ↦ R j) t
  have hf0 : f 0=i := rfl
  have hfsucc (s : ℕ) : f (s+1)=R (f s) := rfl
  have hstep (s : ℕ) (hs : f s ∉ affineDoublingEscapes g b) :
      g (f (s+1))+b=2 • (g (f s)+b) := by
    rw [hfsucc,hR (f s) hs]
    simp only [two_nsmul]
    abel
  have hex : ∃ t, t < k ∧ f t ∈ affineDoublingEscapes g b := by
    by_contra h
    push Not at h
    exact no_walk_at_power_depth_of_triple_fibre g hg b z hk htriple f
      (fun s hs ↦ hstep s (h s hs))
  let P : ℕ → Prop := fun t ↦ t < k ∧ f t ∈ affineDoublingEscapes g b
  letI : DecidablePred P := fun t ↦ Classical.propDecidable (P t)
  have hexP : ∃ t, P t := hex
  let t : ℕ := Nat.find (p := P) hexP
  have ht : t < k ∧ f t ∈ affineDoublingEscapes g b := Nat.find_spec hexP
  refine ⟨t,ht.1,f,hf0,?_,ht.2⟩
  intro s hs
  apply hstep s
  intro hmem
  exact Nat.find_min hexP hs ⟨by omega,hmem⟩

/-- The canonical depth yields an explicit original-escape route
of logarithmic length from every coordinate at a triple-fibre shift. -/
theorem exists_logarithmic_escape_walk_of_triple_fibre
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (i : Fin n) :
    ∃ t < Nat.clog 2 n, ∃ f : ℕ → Fin n, f 0=i ∧
      (∀ s, s < t → g (f (s+1))+b=2 • (g (f s)+b)) ∧ f t ∈ affineDoublingEscapes g b := by
  exact exists_short_actual_escape_walk_of_triple_fibre g hg b z (Nat.le_pow_clog (by decide) n) htriple i

/-- No nonempty affine cycle can occur at a shift with a triple
subset-sum fibre, regardless of cycle size. -/
theorem no_affine_cycle_of_triple_fibre
    {n c : ℕ} (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (E : Fin c ↪ Fin n) (R : Equiv.Perm (Fin c)) : ¬ (∀ i, g (E (R i))=2 • g (E i)+b) := by
  intro hd
  have hmem := affine_cycle_image_subset_iterated_affine_targets g E b R hd (Nat.clog 2 n)
    (Finset.mem_map.mpr ⟨⟨0,hc⟩,Finset.mem_univ _,rfl⟩)
  rw [iterated_affine_targets_eq_empty_of_triple_fibre g hg b z (Nat.le_pow_clog (by decide) n) htriple] at hmem
  exact Finset.notMem_empty _ hmem

end MinModulus

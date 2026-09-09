import MinModulus.BoundaryChainLengthPartition

namespace MinModulus
open Finset
open scoped Classical

/-- A common divisor of all chain lengths divides the smaller balanced
half whenever sharp midpoint boundary equality holds. -/
theorem common_chain_length_divisor_dvd_half_at_midpoint_boundary
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2))
    (d : ℕ) (hd : ∀ a, d ∣ L a) : d ∣ n/2 := by
  obtain ⟨J,hJ⟩ := exists_balanced_chain_length_subfamily_at_midpoint_boundary hn L hL g E x b z hchain hmid hlarge hboundary
  rw [← hJ]
  exact Finset.dvd_sum (fun a _ ↦ hd a)

/-- A divisor at least two of both a number and its floor half must
also divide the exact half: the original number is a multiple of twice
that divisor. -/
theorem twice_dvd_of_dvd_and_dvd_floor_half
    (n d : ℕ) (hd : 2 ≤ d) (hwhole : d ∣ n) (hhalf : d ∣ n/2) : 2*d ∣ n := by
  have hdouble : d ∣ 2*(n/2) := dvd_mul_of_dvd_right hhalf 2
  have hrem : d ∣ n-2*(n/2) := Nat.dvd_sub hwhole hdouble
  have hzero : n-2*(n/2)=0 := Nat.eq_zero_of_dvd_of_lt hrem (by omega)
  obtain ⟨k,hk⟩ := hhalf
  refine ⟨k,?_⟩
  calc
    n=2*(n/2) := by omega
    _=2*(d*k) := by rw [hk]
    _=(2*d)*k := by ac_rfl

/-- At boundary equality, the dimension is divisible by twice any
common chain-length divisor greater than one. -/
theorem twice_common_chain_length_divisor_dvd_dimension_at_boundary
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2))
    (d : ℕ) (hd : 2 ≤ d) (hcommon : ∀ a, d ∣ L a) : 2*d ∣ n := by
  have hhalf := common_chain_length_divisor_dvd_half_at_midpoint_boundary hn L hL g E x b z hchain hmid hlarge hboundary d hcommon
  have htotal : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  apply twice_dvd_of_dvd_and_dvd_floor_half n d hd _ hhalf
  rw [← htotal]
  exact Finset.dvd_sum (fun a _ ↦ hcommon a)

/-- A common chain-length divisor that does not divide the balanced
half forces strict loss above the large-midpoint threshold. -/
theorem balanced_threshold_lt_loss_of_chain_divisor_obstruction
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (d : ℕ) (hcommon : ∀ a, d ∣ L a) (hno : ¬ d ∣ n/2) :
    2^(n/2)+2^(n-n/2) < tupleBinaryCollisionLoss g b+1 := by
  apply balanced_threshold_lt_loss_of_no_balanced_chain_subfamily hn L hL g E x b z hchain hmid hlarge
  intro J hJ
  apply hno
  rw [← hJ]
  exact Finset.dvd_sum (fun a _ ↦ hcommon a)

/-- An odd number of equal-length chains, each of length at least two,
cannot have their common length divide half the total dimension. -/
theorem uniform_odd_chain_length_not_dvd_half
    (r l : ℕ) (hl : 2 ≤ l) (hr : r % 2=1) : ¬ l ∣ (r*l)/2 := by
  intro hhalf
  have htwice : 2*l ∣ r*l := twice_dvd_of_dvd_and_dvd_floor_half (r*l) l hl (dvd_mul_left _ _) hhalf
  have htwo : 2 ∣ r := (Nat.mul_dvd_mul_iff_right (by omega : 0 < l)).mp htwice
  have hz := Nat.mod_eq_zero_of_dvd htwo
  omega

/-- For an odd number of uniform chains of length at least two, every
large midpoint fibre has loss strictly above the balanced threshold,
without tuple validity or cyclicity. -/
theorem balanced_threshold_lt_loss_of_odd_uniform_chains
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β]
    (l : ℕ) (hl : 2 ≤ l) (hr : Fintype.card β % 2=1)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ _a : β, Fin l) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin l), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    2^(n/2)+2^(n-n/2) < tupleBinaryCollisionLoss g b+1 := by
  have htotal : Fintype.card β*l=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin,Finset.sum_const,Finset.card_univ,smul_eq_mul] using Fintype.card_congr E
  apply balanced_threshold_lt_loss_of_chain_divisor_obstruction hn (fun _ : β ↦ l) (fun _ ↦ by omega)
    g E x b z hchain hmid hlarge l (fun _ ↦ dvd_refl _) _
  rw [← htotal]
  exact uniform_odd_chain_length_not_dvd_half _ l hl hr

end MinModulus

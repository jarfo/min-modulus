import research.DensePairModulusBound
import research.SingleRepeatQuadraticCount

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- The complement of the disjointly represented doubled-difference
pairs covers every unrepresented difference and has the exact pair count. -/
theorem disjoint_doubled_difference_pair_complement_data
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) :
    let D := ((Finset.univ : Finset (Fin n)).powersetCard 2)\disjointDoubledDifferencePairs g
    D.card+(disjointDoubledDifferencePairs g).card=n.choose 2 ∧
      (∀ P ∈ D, P.card=2) ∧
      (∀ a b, a≠b → (¬ ∃ p q, 2 • (g a-g b)=g p-g q) →
        ({a,b} : Finset (Fin n)) ∈ D) := by
  classical
  let Pairs := (Finset.univ : Finset (Fin n)).powersetCard 2
  let E := disjointDoubledDifferencePairs g
  let D := Pairs\E
  have hsub : E⊆Pairs := by
    intro P hP
    exact (Finset.mem_filter.mp hP).1
  have htotal : Pairs.card=n.choose 2 := by
    simp only [Pairs,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]
  have hcard : D.card+E.card=n.choose 2 := by
    change (Pairs\E).card+E.card=n.choose 2
    rw [Finset.card_sdiff_add_card_eq_card hsub,htotal]
  have hD : ∀ P ∈ D, P.card=2 := by
    intro P hP
    exact (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp hP).1).2
  have hmissing : ∀ a b, a≠b →
      (¬ ∃ p q, 2 • (g a-g b)=g p-g q) → ({a,b} : Finset (Fin n)) ∈ D := by
    intro a b hab hnot
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,Finset.card_pair hab⟩,?_⟩
    intro hE
    obtain ⟨c,d,p,q,hc,hd,hcd,_,_,_,he⟩ := (Finset.mem_filter.mp hE).2
    simp only [Finset.mem_insert,Finset.mem_singleton] at hc hd
    rcases hc with rfl | rfl
    · rcases hd with rfl | rfl
      · exact hcd rfl
      · exact hnot ⟨p,q,he⟩
    · rcases hd with rfl | rfl
      · apply hnot
        refine ⟨q,p,?_⟩
        have hh := congrArg (fun x : G ↦ -x) he
        simpa only [← smul_neg,neg_sub] using hh
      · exact hcd rfl
  exact ⟨hcard,hD,hmissing⟩

/-- The dense-case obstruction forces the disjoint doubled-difference
sparsity condition in every hypothetical large odd counterexample. -/
theorem disjoint_doubled_difference_sparsity_of_odd_counterexample
    {n N : ℕ} (hn : 144≤n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hgap : N<2^n-1) :
    (n-9)*(disjointDoubledDifferencePairs g).card ≤ (n-12)*n.choose 2 := by
  classical
  let E := disjointDoubledDifferencePairs g
  let D := ((Finset.univ : Finset (Fin n)).powersetCard 2)\E
  obtain ⟨hcard,hD,hmissing⟩ := disjoint_doubled_difference_pair_complement_data g
  change D.card+E.card=n.choose 2 at hcard
  have hden := pair_cover_density_of_valid_odd_modulus_counterexample hn hN g hg D hD hmissing hgap
  have heq : (n-9)*D.card+(n-9)*E.card=(n-12)*n.choose 2+3*n.choose 2 := by
    rw [← Nat.mul_add,hcard,show n-9=(n-12)+3 by omega,Nat.add_mul]
  change (n-9)*E.card ≤ (n-12)*n.choose 2
  omega

/-- Every hypothetical odd counterexample in dimension at least144
already satisfies the absolute quartic repeated-sum bound. The central
degree inequalities are not discharged by this consequence. -/
theorem absolute_quartic_bound_of_large_odd_counterexample
    {n N : ℕ} [NeZero N] (hn : 144≤n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hgap : N<2^n-1) :
    (n+1).choose 2+n.choose 3 ≤ (repeatedCoinCover g 4).card := by
  exact absolute_quartic_bound_of_quadratic_sparsity (by omega) hN g hg
    (disjoint_doubled_difference_sparsity_of_odd_counterexample hn hN g hg hgap)

end MinModulus.Research

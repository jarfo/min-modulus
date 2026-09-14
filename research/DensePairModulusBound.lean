import research.DensePositiveDomainOneEscape
import MinModulus.AlmostDoubling

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- At odd modulus, the dense represented-pair regime proves the sharp
odd min-modulus bound in every dimension at least 144. -/
theorem odd_lower_bound_of_valid_few_missing_pairs
    {n N : ℕ} (hn : 144 ≤ n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (D : Finset (Finset (Fin n)))
    (hD : ∀ P ∈ D, P.card=2)
    (hmissing : ∀ a b, a≠b →
      (¬ ∃ p q, 2 • (g a-g b)=g p-g q) → ({a,b} : Finset (Fin n)) ∈ D)
    (hdense : (n-9)*D.card < 3*n.choose 2) : 2^n-1 ≤ N := by
  letI : NeZero N := ⟨hN.pos.ne'⟩
  obtain ⟨a,b,hclosed⟩ := exists_one_escape_doubling_of_few_missing_pairs
    hn (fun _ _ he ↦ add_self_injective_zmod hN _ _ he) g hg D hD hmissing hdense
  exact odd_lower_bound_of_valid_one_escape_doubling hN g hg a b hclosed

/-- Any odd-modulus counterexample of dimension at least 144 must have
many unrepresented doubled-difference pairs, in every pair cover. -/
theorem pair_cover_density_of_valid_odd_modulus_counterexample
    {n N : ℕ} (hn : 144 ≤ n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (D : Finset (Finset (Fin n)))
    (hD : ∀ P ∈ D, P.card=2)
    (hmissing : ∀ a b, a≠b →
      (¬ ∃ p q, 2 • (g a-g b)=g p-g q) → ({a,b} : Finset (Fin n)) ∈ D)
    (hgap : N < 2^n-1) : 3*n.choose 2 ≤ (n-9)*D.card := by
  by_contra h
  have hdense : (n-9)*D.card < 3*n.choose 2 := by omega
  have hbound := odd_lower_bound_of_valid_few_missing_pairs hn hN g hg D hD hmissing hdense
  omega

end MinModulus.Research

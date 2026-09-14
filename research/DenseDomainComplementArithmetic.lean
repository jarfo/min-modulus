import Mathlib

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- At n at least 144, the missing-pair density hypothesis gives a linear
bound with a coefficient below eight fifths. -/
theorem few_missing_pairs_linear_bound
    (n D : ℕ) (hn : 144 ≤ n) (hD : (n-9)*D < 3*n.choose 2) :
    5*D < 8*n := by
  have hchoose : 2*n.choose 2=n*(n-1) := by
    have hh := Nat.choose_succ_right_eq n 1
    simpa only [Nat.choose_one_right,Nat.mul_comm] using hh
  have hn9 : n=(n-9)+9 := by omega
  have hn1 : n-1=(n-9)+8 := by omega
  have hd : 2*(n-9)*D < 3*((n-9)+9)*((n-9)+8) := by
    nlinarith [hchoose]
  by_contra h
  have hh : 8*((n-9)+9) ≤ 5*D := by omega
  have hm := Nat.mul_le_mul_left (2*(n-9)) hh
  have hk : 120 ≤ n-9 := by omega
  have hk' := Nat.mul_le_mul_left ((n-9)+9) hk
  nlinarith

/-- An averaged outside-pair deficit bound and a roughly half-size
domain force at most twelve outside coordinates under the density bound. -/
theorem dense_domain_averaged_complement_le_twelve
    (n M r D : ℕ) (hn : 144 ≤ n) (hMr : M+r=n)
    (hlarge : n < 2*M+40) (hD : (n-9)*D < 3*n.choose 2)
    (haverage : 2 ≤ r → r*M ≤ 2*D+6*r) : r ≤ 12 := by
  have hd := few_missing_pairs_linear_bound n D hn hD
  have hd' : 8*D < 13*n := by omega
  have hbig : n+24 < 4*M := by omega
  by_contra h
  have hr : 13 ≤ r := by omega
  have ha := haverage (by omega)
  have hm := Nat.mul_lt_mul_of_pos_left hbig (by omega : 0<r)
  have hh := Nat.mul_le_mul_right n hr
  nlinarith

/-- With at most twelve outside coordinates, thirteen represented
neighbors per outside coordinate already force the complement to have
size at most one under the missing-pair density hypothesis. -/
theorem dense_domain_bounded_neighbors_complement_le_one
    (n M r D : ℕ) (hn : 144 ≤ n) (hMr : M+r=n)
    (hr : r ≤ 12) (hD : (n-9)*D < 3*n.choose 2)
    (hmissing : r*M ≤ D+13*r) : r ≤ 1 := by
  have hd := few_missing_pairs_linear_bound n D hn hD
  by_contra h
  have hr2 : 2 ≤ r := by omega
  have hsq := Nat.mul_le_mul_left r hr
  have hp := Nat.mul_le_mul_left (n-25) hr2
  have hn25 : n=(n-25)+25 := by omega
  have he := congrArg (fun x ↦ r*x) hMr
  have he' := congrArg (fun x ↦ r*x) hn25
  nlinarith

end MinModulus.Research

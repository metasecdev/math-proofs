import Mathlib

/-
Research file (Thoughts/Research/LcmChebyshev.lean). Standalone (imports only Mathlib).
Bridge `lcm(1..n) ≤ exp ψ(n)` and explicit Chebyshev bounds `lcm(1..n) ≤ (4 e^4)^n ≤ 219^n`.
Step 3 of the Mahler–Mignotte route toward an explicit irrationality measure for π.
-/

namespace LcmChebyshev
open Finset Real Chebyshev
open ArithmeticFunction hiding id

/-- `∏_{k ≤ n, k prime power} minFac k`; its logarithm is `ψ(n)`. -/
def ppProd (n : ℕ) : ℕ := ∏ k ∈ (Ioc 0 n).filter IsPrimePow, k.minFac

lemma ppProd_pos (n : ℕ) : 0 < ppProd n :=
  Finset.prod_pos fun k _ => Nat.minFac_pos k

/-- `log (ppProd n) = ψ n`. -/
theorem log_ppProd (n : ℕ) : Real.log (ppProd n) = ψ n := by
  rw [ppProd, Nat.cast_prod, Real.log_prod]
  · rw [psi, Nat.floor_natCast, sum_filter]
    refine sum_congr rfl fun k _ => ?_
    rw [vonMangoldt_apply]
  · intro k _
    exact_mod_cast (Nat.minFac_pos k).ne'

theorem ppProd_eq_exp_psi (n : ℕ) : (ppProd n : ℝ) = Real.exp (ψ n) := by
  rw [← log_ppProd, Real.exp_log (by exact_mod_cast ppProd_pos n)]

/-- every `1 ≤ c ≤ n` divides `ppProd n`. -/
theorem dvd_ppProd {n c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ n) : c ∣ ppProd n := by
  have hc0 : c ≠ 0 := by omega
  set v := c.factorization
  set S : Finset ℕ := c.primeFactors.biUnion fun p => (Icc 1 (v p)).image fun j => p ^ j
  have hsub : S ⊆ (Ioc 0 n).filter IsPrimePow := by
    intro k hk
    simp only [S, mem_biUnion, mem_image, mem_Icc] at hk
    obtain ⟨p, hp, j, ⟨hj1, hjv⟩, rfl⟩ := hk
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    simp only [mem_filter, mem_Ioc]
    refine ⟨⟨pow_pos hpp.pos _, ?_⟩, (hpp.isPrimePow.pow (by omega))⟩
    calc p ^ j ≤ p ^ v p := Nat.pow_le_pow_right hpp.pos hjv
      _ ≤ c := Nat.ordProj_le p hc0
      _ ≤ n := h2
  have hS : ∏ k ∈ S, k.minFac = c := by
    rw [prod_biUnion]
    · conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hc0]
      rw [Finsupp.prod, Nat.support_factorization]
      refine prod_congr rfl fun p hp => ?_
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      rw [prod_image]
      · rw [prod_congr rfl (g := fun _ => p)]
        · simp [v]
        · intro j hj
          simp only [mem_Icc] at hj
          exact hpp.pow_minFac (by omega)
      · intro a _ b _ hab
        exact Nat.pow_right_injective hpp.two_le hab
    · intro p hp q hq hpq
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      simp only [mem_image, mem_Icc] at hk1 hk2
      obtain ⟨a, ha, rfl⟩ := hk1
      obtain ⟨b, hb, hb2⟩ := hk2
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hqq : q.Prime := Nat.prime_of_mem_primeFactors hq
      apply hpq
      have e1 := hpp.pow_minFac (k := a) (by omega)
      have e2 := hqq.pow_minFac (k := b) (by omega)
      rw [hb2] at e2
      rw [← e1, ← e2]
  rw [← hS, ppProd]
  exact prod_dvd_prod_of_subset _ _ _ hsub

/-- `lcm(1..n) ∣ ppProd n`. -/
theorem lcm_dvd_ppProd (n : ℕ) : (Icc 1 n).lcm id ∣ ppProd n :=
  Finset.lcm_dvd fun c hc => by
    simp only [mem_Icc] at hc
    exact dvd_ppProd hc.1 hc.2

/-- **Bridge to Chebyshev's ψ**: `lcm(1..n) ≤ exp ψ(n)`. -/
theorem lcm_le_exp_psi (n : ℕ) : (((Icc 1 n).lcm id : ℕ) : ℝ) ≤ Real.exp (ψ n) := by
  rw [← ppProd_eq_exp_psi]
  exact_mod_cast Nat.le_of_dvd (ppProd_pos n) (lcm_dvd_ppProd n)

/-- With Mathlib's `psi_le`: `lcm(1..n) ≤ exp(log 4 · n + 2 √n log n)` (`n ≥ 1`). -/
theorem lcm_le_exp_psi_le (n : ℕ) (hn : 1 ≤ n) :
    (((Icc 1 n).lcm id : ℕ) : ℝ) ≤
      Real.exp (Real.log 4 * n + 2 * Real.sqrt n * Real.log n) :=
  (lcm_le_exp_psi n).trans (Real.exp_le_exp.mpr (psi_le (by exact_mod_cast hn)))

/-- With Mathlib's `psi_le_const_mul_self`: `lcm(1..n) ≤ (4 e^4)^n`. -/
theorem lcm_le_four_exp_four_pow (n : ℕ) :
    (((Icc 1 n).lcm id : ℕ) : ℝ) ≤ (4 * Real.exp 4) ^ n := by
  refine (lcm_le_exp_psi n).trans ?_
  have h := psi_le_const_mul_self (x := (n : ℝ)) (Nat.cast_nonneg n)
  calc Real.exp (ψ n) ≤ Real.exp ((Real.log 4 + 4) * n) := Real.exp_le_exp.mpr h
    _ = (4 * Real.exp 4) ^ n := by
      rw [← Real.exp_log (show (0:ℝ) < 4 * Real.exp 4 by positivity), ← Real.exp_nat_mul,
        Real.log_mul (by norm_num) (Real.exp_pos 4).ne', Real.log_exp]
      ring_nf

lemma four_exp_four_lt : 4 * Real.exp 4 < 219 := by
  have h1 := Real.exp_one_lt_d9
  have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hpos := Real.exp_pos 1
  rw [h4]
  have : Real.exp 1 ^ 4 < (2.7182818286 : ℝ) ^ 4 := by gcongr
  nlinarith

/-- **Explicit integer bound**: `lcm(1..n) ≤ 219^n`. -/
theorem lcm_le_219_pow (n : ℕ) : (Icc 1 n).lcm id ≤ 219 ^ n := by
  have h := (lcm_le_four_exp_four_pow n).trans
    (pow_le_pow_left₀ (by positivity) four_exp_four_lt.le n)
  exact_mod_cast h

end LcmChebyshev

#print axioms LcmChebyshev.log_ppProd
#print axioms LcmChebyshev.lcm_le_exp_psi
#print axioms LcmChebyshev.lcm_le_exp_psi_le
#print axioms LcmChebyshev.lcm_le_four_exp_four_pow
#print axioms LcmChebyshev.lcm_le_219_pow

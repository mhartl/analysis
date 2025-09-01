import Mathlib.Tactic
import Analysis.Section_5_epilogue
import Analysis.Section_6_6

/-!
# Analysis I, Section 6.7: Real exponentiation, part II

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Real exponentiation.

Because the Chapter 5 reals have been deprecated in favor of the Mathlib reals, and Mathlib real
exponentiation is defined without first going through rational exponentiation, we will adopt a
somewhat awkward compromise, in that we will initially accept the Mathlib exponentiation operation
(with all its API) when the exponent is a rational, and use this to define a notion of real
exponentiation which in the epilogue to this chapter we will show is identical to the Mathlib operation.
-/

namespace Chapter6

open Sequence Real

/-- Lemma 6.7.1 (Continuity of exponentiation) -/
lemma ratPow_continuous {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 ((fun n ↦ x^(q n:ℝ)):Sequence).Convergent := by
  -- This proof is rearranged slightly from the original text.
  choose M hM hbound using bounded_of_convergent ⟨ α, hq ⟩
  obtain h | rfl | h := lt_trichotomy x 1
  . sorry
  . simp; exact ⟨ 1, lim_of_const 1 ⟩
  have h': 1 ≤ x := by linarith
  rw [←Cauchy_iff_convergent]
  intro ε hε
  choose K hK hclose using lim_of_roots hx (ε*x^(-M)) (by positivity)
  choose N hN hq using IsCauchy.convergent ⟨ α, hq ⟩ (1/(K+1:ℝ)) (by positivity)
  simp [CloseSeq, dist_eq] at hclose hK hN
  lift N to ℕ using hN
  lift K to ℕ using hK
  specialize hclose K (by simp) (by simp); simp at hclose
  use N, by simp
  intro n hn m hm; simp at hn hm
  specialize hq n (by simp [hn]) m (by simp [hm])
  simp [Close, hn, hm, dist_eq] at hq ⊢
  have : 0 ≤ (N:ℤ) := by simp
  lift n to ℕ using by linarith
  lift m to ℕ using by linarith
  simp at hn hm hq ⊢
  obtain hqq | hqq := le_or_gt (q m) (q n)
  . replace : x^(q m:ℝ) ≤ x^(q n:ℝ) := by rw [rpow_le_rpow_left_iff h]; norm_cast
    rw [abs_of_nonneg (by linarith)]
    calc
      _ = x^(q m:ℝ) * (x^(q n - q m:ℝ) - 1) := by ring_nf; rw [←rpow_add (by linarith)]; ring_nf
      _ ≤ x^M * (x^(1/(K+1:ℝ)) - 1) := by
        gcongr <;> try exact h'
        . rw [sub_nonneg]; apply one_le_rpow h'; norm_cast; linarith
        . specialize hbound m; simp_all [abs_le']
        grind [abs_le']
      _ ≤ x^M * (ε * x^(-M)) := by gcongr; grind [abs_le']
      _ = ε := by rw [mul_comm, mul_assoc, ←rpow_add]; simp; linarith
  replace : x^(q n:ℝ) ≤ x^(q m:ℝ) := by rw [rpow_le_rpow_left_iff h]; norm_cast; linarith
  rw [abs_of_nonpos (by linarith)]
  calc
    _ = x^(q n:ℝ) * (x^(q m - q n:ℝ) - 1) := by ring_nf; rw [←rpow_add]; ring_nf; positivity
    _ ≤ x^M * (x^(1/(K+1:ℝ)) - 1) := by
      gcongr <;> try exact h'
      . rw [sub_nonneg]; apply one_le_rpow h'; norm_cast; linarith
      . specialize hbound n; simp_all [abs_le']
      grind [abs_le']
    _ ≤ x^M * (ε * x^(-M)) := by gcongr; simp_all [abs_le']
    _ = ε := by rw [mul_comm, mul_assoc, ←rpow_add]; simp; positivity


lemma ratPow_lim_uniq {x α:ℝ} (hx: x > 0) {q q': ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α)
 (hq': ((fun n ↦ (q' n:ℝ)):Sequence).TendsTo α) :
 lim ((fun n ↦ x^(q n:ℝ)):Sequence) = lim ((fun n ↦ x^(q' n:ℝ)):Sequence) := by
 -- This proof is written to follow the structure of the original text.
  set r := q - q'
  suffices : (fun n ↦ x^(r n:ℝ):Sequence).TendsTo 1
  . rw [←mul_one (lim ((fun n ↦ x^(q' n:ℝ)):Sequence))]
    rw [lim_eq] at this
    convert (lim_mul (b := (fun n ↦ x^(r n:ℝ):Sequence)) (ratPow_continuous hx hq') this.1).2
    . rw [mul_coe]
      rcongr _ n
      rw [←rpow_add (by linarith)]
      simp [r]
    grind
  intro ε hε
  have h1 := lim_of_roots hx
  have h2 := tendsTo_inv h1 (by norm_num)
  choose K1 hK1 h3 using h1 ε hε
  choose K2 hK2 h4 using h2 ε hε
  simp [Inv.inv] at hK1 hK2
  lift K1 to ℕ using hK1; lift K2 to ℕ using hK2
  simp [inv_coe] at h4
  set K := max K1 K2
  have hr := tendsTo_sub hq hq'
  rw [sub_coe] at hr
  choose N hN hr using hr (1 / (K + 1:ℝ)) (by positivity)
  refine ⟨ N, by simp_all, ?_ ⟩
  intro n hn; simp at hn
  specialize h3 K (by simp [K]); specialize h4 K (by simp [K])
  simp [hn, dist_eq, abs_le', K, -Nat.cast_max] at h3 h4 ⊢
  specialize hr n (by simp [hn])
  simp [Close, hn, abs_le'] at hr
  obtain h | rfl | h := lt_trichotomy x 1
  . sorry
  . simp; linarith
  have h5 : x ^ (r n.toNat:ℝ) ≤ x^(K + 1:ℝ)⁻¹ := by gcongr; linarith; simp_all [r]
  have h6 : (x^(K + 1:ℝ)⁻¹)⁻¹ ≤ x ^ (r n.toNat:ℝ) := by
    rw [←rpow_neg (by linarith)]
    gcongr; linarith
    simp [r]; linarith
  split_ands <;> linarith

theorem Real.eq_lim_of_rat (α:ℝ) : ∃ q: ℕ → ℚ, ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α := by
  choose q hcauchy hLIM using (Chapter5.Real.equivR.symm α).eq_lim; use q
  apply lim_eq_LIM at hcauchy
  simp only [←hLIM, Equiv.apply_symm_apply] at hcauchy
  convert hcauchy; aesop

/-- Definition 6.7.2 (Exponentiation to a real exponent) -/
noncomputable abbrev Real.rpow (x:ℝ) (α:ℝ) :ℝ := lim ((fun n ↦ x^((eq_lim_of_rat α).choose n:ℝ)):Sequence)

lemma Real.rpow_eq_lim_ratPow {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 rpow x α = lim ((fun n ↦ x^(q n:ℝ)):Sequence) :=
   ratPow_lim_uniq hx (eq_lim_of_rat α).choose_spec hq

lemma Real.ratPow_tendsto_rpow {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 ((fun n ↦ x^(q n:ℝ)):Sequence).TendsTo (rpow x α) := by
  rw [lim_eq]
  exact ⟨ ratPow_continuous hx hq, (rpow_eq_lim_ratPow hx hq).symm ⟩

lemma Real.rpow_of_rat_eq_ratPow {x:ℝ} (hx: x > 0) {q: ℚ} :
  rpow x (q:ℝ) = x^(q:ℝ) := by
  convert rpow_eq_lim_ratPow hx (α := q) (lim_of_const _)
  exact (lim_eq.mp (lim_of_const _)).2.symm

/-- Proposition 6.7.3(a) / Exercise 6.7.1 -/
theorem Real.ratPow_nonneg {x:ℝ} (hx: x > 0) (q:ℝ) : rpow x q ≥ 0 := by
  sorry

/-- Proposition 6.7.3(b) -/
theorem Real.ratPow_add {x:ℝ} (hx: x > 0) (q r:ℝ) : rpow x (q+r) = rpow x q * rpow x r := by
  choose q' hq' using eq_lim_of_rat q
  choose r' hr' using eq_lim_of_rat r
  have hq'r' := tendsTo_add hq' hr'
  rw [add_coe] at hq'r'
  convert_to ((fun n ↦ ((q' n + r' n:ℚ):ℝ)):Sequence).TendsTo (q + r) at hq'r'
  . aesop
  have h1 := ratPow_continuous hx hq'
  have h2 := ratPow_continuous hx hr'
  rw [rpow_eq_lim_ratPow hx hq', rpow_eq_lim_ratPow hx hr', rpow_eq_lim_ratPow hx hq'r', ←(lim_mul h1 h2).2, mul_coe]
  rcongr n; rw [←rpow_add]; simp; linarith


/-- Proposition 6.7.3(b) / Exercise 6.7.1 -/
theorem Real.ratPow_ratPow {x:ℝ} (hx: x > 0) (q r:ℝ) : rpow (rpow x q) r = rpow x (q*r) := by
  sorry

/-- Proposition 6.7.3(c) / Exercise 6.7.1 -/
theorem Real.ratPow_neg {x:ℝ} (hx: x > 0) (q:ℝ) : rpow x (-q) = 1 / rpow x q := by
  sorry

/-- Proposition 6.7.3(d) / Exercise 6.7.1 -/
theorem Real.ratPow_mono {x y:ℝ} (hx: x > 0) (hy: y > 0) {q:ℝ} (h: q > 0) : x > y ↔ rpow x q > rpow y q := by
  sorry

/-- Proposition 6.7.3(e) / Exercise 6.7.1 -/
theorem Real.ratPow_mono_of_gt_one {x:ℝ} (hx: x > 1) {q r:ℝ} : rpow x q > rpow x r ↔ q > r := by
  sorry

/-- Proposition 6.7.3(e) / Exercise 6.7.1 -/
theorem Real.ratPow_mono_of_lt_one {x:ℝ} (hx0: 0 < x) (hx: x < 1) {q r:ℝ} : rpow x q < rpow x r ↔ q < r := by
  sorry

/-- Proposition 6.7.3(f) / Exercise 6.7.1 -/
theorem Real.ratPow_mul {x y:ℝ} (hx: x > 0) (hy: y > 0) (q:ℝ) : rpow (x*y) q = rpow x q * rpow y q := by
  sorry

end Chapter6

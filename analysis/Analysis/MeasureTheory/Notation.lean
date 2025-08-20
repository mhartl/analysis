import Mathlib.Tactic

/-!
# Introduction to Measure Theory, Chapter 0: Notation

A companion to Chapter 0 of the book "An introduction to Measure Theory".

We use existing Mathlib constructions, such as `Set.indicator`, `EuclideanSpace`, `ENNReal`,
and `tsum` to describe the concepts defined in Chapter 0.

-/

/-- A version of `Set.indicator` suitable for this text. -/
noncomputable abbrev Set.indicator' {X: Type*} (E: Set X) := indicator E (fun _ ↦ (1:ℝ))

theorem Set.indicator'_apply {X: Type*} (E: Set X) (x: X) [Decidable (x ∈ E)] : indicator' E x = if x ∈ E then 1 else 0 := indicator_apply _ _ _

theorem Set.indicator'_of_mem {X: Type*} {E:Set X} {x:X} (h: x ∈ E) : indicator' E x = 1 := by
  convert indicator_of_mem h (fun _ ↦ (1:ℝ))

theorem Set.indicator'_of_notMem {X: Type*} {E:Set X} {x:X} (h: x ∉ E) : indicator' E x = 0 := by
  convert indicator_of_notMem h (fun _ ↦ (1:ℝ))

/-- A version of `EuclideanSpace` suitable for this text. -/
noncomputable abbrev EuclideanSpace' (n: ℕ) := EuclideanSpace ℝ (Fin n)

theorem EuclideanSpace'.norm_eq {n:ℕ} (x: EuclideanSpace' n) : ‖x‖ = √(∑ i, (x i)^2) := by
  convert EuclideanSpace.norm_eq x using 3 with i
  simp

infix:100 " ⬝ " => inner ℝ

theorem EuclideanSpace'.dot_apply {n:ℕ} (x y: EuclideanSpace' n) : x ⬝ y = ∑ i, (x i)*(y i) := by
  convert PiLp.inner_apply x y using 2 with i
  simp; ring

#check top_add
#check add_top
#check ENNReal.top_mul
#check ENNReal.mul_top
#check lt_top_iff_ne_top

open Filter

theorem ENNReal.upward_continuous {x y:ℕ → ENNReal} (hx: Monotone x) (hy: Monotone y)
 {x₀ y₀ : ENNReal} (hx_lim: atTop.Tendsto x (nhds x₀))
 (hy_lim: atTop.Tendsto y (nhds y₀)) :
  atTop.Tendsto (fun n ↦ x n * y n) (nhds (x₀ * y₀)) := by
  -- This proof is written to follow the structure of the original text.
  have hx_lt (n:ℕ): x n ≤ x₀ := hx.ge_of_tendsto hx_lim n
  have hy_lt (n:ℕ): y n ≤ y₀ := hy.ge_of_tendsto hy_lim n
  have zero_conv : atTop.Tendsto (fun n:ℕ ↦ (0:ENNReal)) (nhds 0) := tendsto_const_nhds
  have top_conv : atTop.Tendsto (fun n:ℕ ↦ (⊤:ENNReal)) (nhds ⊤) := tendsto_const_nhds
  obtain rfl | hx₀ := eq_zero_or_pos x₀
  . simp; convert zero_conv with n
    simp [nonpos_iff_eq_zero.mp (hx_lt n)]
  obtain rfl | hy₀ := eq_zero_or_pos y₀
  . simp; convert zero_conv with n
    simp [nonpos_iff_eq_zero.mp (hy_lt n)]
  have hx_pos : ∃ n, 0 < x n := by
    by_contra!
    have hx0 : x = 0 := by ext n; exact nonpos_iff_eq_zero.mp (this n)
    subst hx0
    have := tendsto_nhds_unique hx_lim zero_conv
    order
  choose nx hnx using hx_pos
  have hy_pos : ∃ n, 0 < y n := by
    by_contra!
    have hy0 : y = 0 := by ext n; exact nonpos_iff_eq_zero.mp (this n)
    subst hy0
    have := tendsto_nhds_unique hy_lim zero_conv
    order
  choose ny hny using hy_pos
  obtain rfl | hx₀' := eq_top_or_lt_top x₀
  . rw [top_mul (by order)]
    obtain hyn' | hyn' := eq_or_ne (y ny) ⊤
    . apply top_conv.congr'
      simp [EventuallyEq, eventually_atTop]
      use nx ⊔ ny; intro n hn; simp at hn
      symm; convert ENNReal.mul_top _
      . have := hy hn.2
        rwa [hyn', ←eq_top_iff] at this
      have := hx hn.1
      order
    have : atTop.Tendsto (fun n ↦ x n * y ny) (nhds ⊤) := by
      convert Tendsto.comp (g := fun z ↦ z * y ny) _ hx_lim
      convert (ENNReal.continuous_mul_const hyn').tendsto ⊤
      rw [top_mul (by order)]
    apply tendsto_nhds_top_mono this
    simp [EventuallyLE, eventually_atTop]
    use ny; intro n hn
    gcongr; exact hy hn
  obtain rfl | hy₀' := eq_top_or_lt_top y₀
  . rw [mul_top (by order)]
    have : atTop.Tendsto (fun n ↦ x nx * y n) (nhds ⊤) := by
      convert Tendsto.comp (g := fun z ↦ (x nx) * z) _ hy_lim
      convert (ENNReal.continuous_const_mul _).tendsto ⊤
      . rw [mul_top (by order)]
      specialize hx_lt nx
      order
    apply tendsto_nhds_top_mono this
    simp [EventuallyLE, eventually_atTop]
    use nx; intro n hn
    gcongr; exact hx hn
  set x' : ℕ → NNReal := fun n ↦ (x n).toNNReal
  set y' : ℕ → NNReal := fun n ↦ (y n).toNNReal
  set x₀' : NNReal := x₀.toNNReal
  set y₀' : NNReal := y₀.toNNReal
  have hxx₀' : x₀ = x₀' := by rw [coe_toNNReal]; order
  have hyy₀' : y₀ = y₀' := by rw [coe_toNNReal]; order
  have hxx' (n:ℕ) : x n = x' n := by rw [coe_toNNReal]; specialize hx_lt n; order
  have hyy' (n:ℕ) : y n = y' n := by rw [coe_toNNReal]; specialize hy_lt n; order
  change atTop.Tendsto (fun n ↦ x n) (nhds x₀) at hx_lim
  change atTop.Tendsto (fun n ↦ y n) (nhds y₀) at hy_lim
  simp [hxx', hyy', hxx₀', hyy₀',←coe_mul] at *
  solve_by_elim [Filter.Tendsto.mul]

example : ∃ (x y:ℕ → ENNReal) (hx: Antitone x) (hy: Antitone y)
 (x₀ y₀:ENNReal) (hx_lim: atTop.Tendsto x (nhds x₀))
 (hy_lim: atTop.Tendsto y (nhds y₀)), ¬ atTop.Tendsto (fun n ↦ x n * y n) (nhds (x₀ * y₀)) := by
 sorry

#check ENNReal.tendsto_nat_tsum

#check ENNReal.tsum_eq_iSup_sum

#check Equiv.tsum_eq

/-- Exercise 0.0.1 -/
example {A:Type} {x : A → ENNReal} (hx: ∑' α, x α < ⊤) :
  ∃ E: Set A, Countable E ∧ ∀ α ∉ E, x α = 0 := by
  sorry

/-- Theorem 0.0.2 (Tonelli's theorem for series)  -/
theorem ENNReal.tsum_of_tsum (x: ℕ → ℕ → ENNReal) : ∑' p:ℕ × ℕ, x p.1 p.2 = ∑' n, ∑' m, x n m := by
  -- This proof is written to largely follow the structure of the original text.
  refine' le_antisymm _ _
  . rw [ENNReal.tsum_eq_iSup_sum]; apply iSup_le; intro F
    have : ∃ N, F ⊆ .range N ×ˢ .range N := by
      have _ : IsOrderBornology ℕ := {
        isBounded_iff_bddBelow_bddAbove s := by
          constructor
          . intro h; simp
            rw [Metric.isBounded_iff_subset_closedBall 0] at h
            choose N hN using h
            rw [bddAbove_def]; use ⌊ N ⌋₊
            intro n hn; specialize hN hn; simp [dist] at hN; exact Nat.le_floor hN
          intro ⟨ h1, h2 ⟩; exact Metric.isBounded_of_bddAbove_of_bddBelow h2 h1
        }
      choose N₁ hN₁ using bddAbove_def.mp F.finite_toSet.isBounded.image_fst.bddAbove
      choose N₂ hN₂ using bddAbove_def.mp F.finite_toSet.isBounded.image_snd.bddAbove
      use N₁ ⊔ N₂ + 1; intro ⟨ n, m ⟩ hnm; simp_all
      specialize hN₁ _ _ hnm; specialize hN₂ _ _ hnm; omega
    choose N hN using this
    calc
      _ ≤ ∑ p ∈ .range N ×ˢ .range N, x p.1 p.2 := Finset.sum_le_sum_of_subset hN
      _ = ∑ n ∈ .range N, ∑ m ∈ .range N, x n m := Finset.sum_product' _ _ _
      _ ≤ ∑' n, ∑ m ∈ .range N, x n m := ENNReal.sum_le_tsum _
      _ ≤ _ := by apply ENNReal.tsum_le_tsum; intro n; apply ENNReal.sum_le_tsum
  apply le_of_tendsto' (tendsto_nat_tsum _); intro N
  apply le_of_tendsto' (f := fun M ↦ ∑ n ∈ .range N, ∑ m ∈ .range M, x n m) (x := atTop)
  . apply tendsto_finset_sum; intro n _; apply tendsto_nat_tsum
  intro M
  calc
    _ = ∑ p ∈ .range N ×ˢ .range M, x p.1 p.2 := by symm; apply Finset.sum_product
    _ ≤ _ := ENNReal.sum_le_tsum _

/-- Theorem 0.0.2 -/
theorem ENNReal.tsum_of_tsum' (x: ℕ → ℕ → ENNReal) : ∑' p:ℕ × ℕ, x p.1 p.2 = ∑' m, ∑' n, x n m := by
  sorry

#check ENNReal.tsum_comm

/-- Exercise 0.0.2 (Tonelli's theorem for series over arbitrary sets)-/
example {A B:Type*} (x: A → B → ENNReal) : ∑' p:A × B, x p.1 p.2 = ∑' a, ∑' b, x a b := by
  sorry

example {A B:Type*} (x: A → B → ENNReal) : ∑' p:A × B, x p.1 p.2 = ∑' b, ∑' a, x a b := by
  sorry

/-- Axiom 0.0.4 (Axiom of choice)-/
noncomputable def Set.choose {A: Type*} {E: A → Type*} (hE: ∀ n, Nonempty (E n)) :
∀ n, E n := fun n ↦ (hE n).some

/-- Corollary 0.0.5 (Axiom of countable choice) -/
noncomputable def Countable.choose {E: ℕ → Type*} (hE: ∀ n, Nonempty (E n)) :
∀ n, E n := Set.choose hE



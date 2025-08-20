import Analysis.MeasureTheory.Notation

/-!
# Introduction to Measure Theory, Section 1.1.1: Elementary measure

A companion to Section 1.1.1 of the book "An introduction to Measure Theory".

-/

/- Definition 1.1.1.  (Intervals) We use the same formalization of intervals used in
Chapter 11 of "Analysis I".  Following the usual Lean preference to admit `junk` values,
we allow for the possibility that `b < a`. -/
inductive BoundedInterval where
  | Ioo (a b:ℝ) : BoundedInterval
  | Icc (a b:ℝ) : BoundedInterval
  | Ioc (a b:ℝ) : BoundedInterval
  | Ico (a b:ℝ) : BoundedInterval

open BoundedInterval

@[coe]
def BoundedInterval.toSet (I: BoundedInterval) : Set ℝ := match I with
  | Ioo a b => .Ioo a b
  | Icc a b => .Icc a b
  | Ioc a b => .Ioc a b
  | Ico a b => .Ico a b

instance BoundedInterval.inst_coeSet : Coe BoundedInterval (Set ℝ) where
  coe := toSet

instance BoundedInterval.instEmpty : EmptyCollection BoundedInterval where
  emptyCollection := Ioo 0 0

@[simp]
theorem BoundedInterval.coe_empty : ((∅ : BoundedInterval):Set ℝ) = ∅ := by
  simp [toSet]

open Classical in
/-- This is to make Finsets of BoundedIntervals work properly -/
noncomputable instance BoundedInterval.decidableEq : DecidableEq BoundedInterval := instDecidableEqOfLawfulBEq

@[simp]
theorem BoundedInterval.set_Ioo (a b:ℝ) : (Ioo a b : Set ℝ) = .Ioo a b := by rfl

@[simp]
theorem BoundedInterval.set_Icc (a b:ℝ) : (Icc a b : Set ℝ) = .Icc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ioc (a b:ℝ) : (Ioc a b : Set ℝ) = .Ioc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ico (a b:ℝ) : (Ico a b : Set ℝ) = .Ico a b := by rfl

/-- Some helpful general lemmas about BoundedInterval -/
theorem Bornology.IsBounded.of_boundedInterval (I: BoundedInterval) : Bornology.IsBounded (I:Set ℝ) := by
  sorry

theorem BoundedInterval.ordConnected_iff (X:Set ℝ) : Bornology.IsBounded X ∧ X.OrdConnected ↔ ∃ I: BoundedInterval, X = I := by
  sorry

theorem BoundedInterval.inter (I J: BoundedInterval) : ∃ K : BoundedInterval, (I:Set ℝ) ∩ (J:Set ℝ) = (K:Set ℝ) := by
  sorry

noncomputable instance BoundedInterval.instInter : Inter BoundedInterval where
  inter I J := (inter I J).choose

@[simp]
theorem BoundedInterval.inter_eq (I J: BoundedInterval) : (I ∩ J : BoundedInterval) = (I:Set ℝ) ∩ (J:Set ℝ)  :=
  (inter I J).choose_spec.symm

instance BoundedInterval.instMembership : Membership ℝ BoundedInterval where
  mem I x := x ∈ (I:Set ℝ)

@[simp]
theorem BoundedInterval.mem_iff (I: BoundedInterval) (x:ℝ) :
  x ∈ I ↔ x ∈ (I:Set ℝ) := by rfl

instance BoundedInterval.instSubset : HasSubset BoundedInterval where
  Subset I J := ∀ x, x ∈ I → x ∈ J

@[simp]
theorem BoundedInterval.subset_iff (I J: BoundedInterval) :
  I ⊆ J ↔ (I:Set ℝ) ⊆ (J:Set ℝ) := by rfl

abbrev BoundedInterval.a (I: BoundedInterval) : ℝ := match I with
  | Ioo a _ => a
  | Icc a _ => a
  | Ioc a _ => a
  | Ico a _ => a

abbrev BoundedInterval.b (I: BoundedInterval) : ℝ := match I with
  | Ioo _ b => b
  | Icc _ b => b
  | Ioc _ b => b
  | Ico _ b => b

theorem BoundedInterval.subset_Icc (I: BoundedInterval) : I ⊆ Icc I.a I.b := match I with
  | Ioo _ _ => by simp [Ioo, Icc, a, b, subset_iff, Set.Ioo_subset_Icc_self]
  | Icc _ _ => by simp [Icc, a, b, subset_iff]
  | Ioc _ _ => by simp [Ioc, Icc, a, b, subset_iff, Set.Ioc_subset_Icc_self]
  | Ico _ _ => by simp [Ico, Icc, a, b, subset_iff, Set.Ico_subset_Icc_self]

theorem BoundedInterval.Ioo_subset (I: BoundedInterval) : Ioo I.a I.b ⊆ I := match I with
  | Ioo _ _ => by simp [Ioo, a, b, subset_iff]
  | Icc _ _ => by simp [Icc, a, b, subset_iff, Set.Ioo_subset_Icc_self]
  | Ioc _ _ => by simp [Ioc, Ioo, a, b, subset_iff, Set.Ioo_subset_Ioc_self]
  | Ico _ _ => by simp [Ico, Ioo, a, b, subset_iff, Set.Ioo_subset_Ico_self]

/-- Definition 1.1.1 (boxes) -/
abbrev BoundedInterval.length (I: BoundedInterval) : ℝ := max (I.b - I.a) 0

/-- Using ||ₗ subscript here to not override || -/
macro:max atomic("|" noWs) a:term noWs "|ₗ" : term => `(BoundedInterval.length $a)

@[ext]
structure Box (d:ℕ) where
  side : Fin d → BoundedInterval

@[coe]
abbrev Box.toSet {d:ℕ} (B: Box d) : Set (EuclideanSpace' d) :=
  Set.univ.pi (fun i ↦ ↑(B.side i))

instance Box.inst_coeSet {d:ℕ} : Coe (Box d) (Set (EuclideanSpace' d)) where
  coe := toSet

/-- Definition 1.1.1 (boxes)-/
abbrev Box.volume {d:ℕ} (B: Box d) : ℝ := ∏ i, |B.side i|ₗ

/-- Using ||ᵥ subscript here to not override || -/
macro:max atomic("|" noWs) a:term noWs "|ᵥ" : term => `(Box.volume $a)

abbrev IsElementary {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop := ∃ S : Finset (Box d), E = ⋃ B ∈ S, ↑B

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.union {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E ∪ F) := by
  sorry

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.inter {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E ∩ F) := by
  sorry


/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.sdiff {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E \ F) := by
  sorry

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.symmDiff {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (symmDiff E F) := by
  sorry

open Pointwise

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.translate {d:ℕ} {E: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (x: EuclideanSpace' d) : IsElementary (E + {x}) := by
  sorry

/-- A sublemma for proving Lemma 1.1.2(i).  It is a geometrically obvious fact but surprisingly annoying to prove formally. -/
theorem BoundedInterval.partition (S: Finset BoundedInterval) : ∃ T: Finset BoundedInterval, T.toSet.PairwiseDisjoint BoundedInterval.toSet ∧ ∀ I ∈ S, ∃ U : Set T, I = ⋃ J ∈ U, J.val.toSet := by
  let endpoints : Finset ℝ := S.image BoundedInterval.a ∪ S.image BoundedInterval.b
  have ha_mem {I:BoundedInterval} (hI: I ∈ S) : I.a ∈ endpoints := by
    simp [endpoints]; left; exact ⟨ I, hI, rfl ⟩
  have hb_mem {I:BoundedInterval} (hI: I ∈ S) : I.b ∈ endpoints := by
    simp [endpoints]; right; exact ⟨ I, hI, rfl ⟩
  let k := endpoints.card
  let sorted : Fin k ≃o endpoints := endpoints.orderIsoOfFin (by rfl)
  let a : ℕ → ℝ := fun n ↦ if h:n < k then sorted ⟨n,h⟩ else 0  -- 0 is a junk value
  let T := Finset.univ.image (fun x:endpoints ↦ BoundedInterval.Icc x x)
    ∪ (Finset.range (k-1)).image (fun n ↦ BoundedInterval.Ioo (a n) (a (n+1)))
  refine' ⟨T,_,_⟩
  . rw [Set.pairwiseDisjoint_iff]
    intro I hI J hJ hIJ
    have := hIJ.some_mem
    simp_all [T]
    obtain ⟨ x, hx, rfl ⟩ | ⟨ n, hn, rfl ⟩ := hI
      <;> obtain ⟨ y, hy, rfl ⟩ | ⟨ m, hm, rfl ⟩ := hJ
      <;> simp at this
    . rw [show x=y by cc]
    . rw [this.1] at this
      set n := sorted.symm ⟨ x, hx ⟩
      have hax : x = sorted n := by simp [n]
      obtain ⟨ n, hn ⟩ := n
      simp [a, show m < k by omega, show m+1 < k by omega, hax] at this
      omega
    . rw [this.2] at this
      set m := sorted.symm ⟨ y, hy ⟩
      have hay : y = sorted m := by simp [m]
      obtain ⟨ m, hm ⟩ := m
      simp [a, show n < k by omega, show n+1 < k by omega, hay] at this
      omega
    have h1 : a n < a (m+1) := this.1.1.trans this.2.2
    have h2 : a m < a (n+1) := this.2.1.trans this.1.2
    simp [a, show n < k by omega, show n+1 < k by omega,
          show m < k by omega, show m+1 < k by omega] at h1 h2
    rw [show n=m by omega]
  intro I hI
  use {J | J.val ⊆ I }
  ext x; simp; constructor
  . intro hx
    by_cases hend : x ∈ endpoints
    . use BoundedInterval.Icc x x
      simp [T, hx, hend]
    let n := sorted.symm ⟨ I.a, ha_mem hI ⟩
    let m := sorted.symm ⟨ I.b, hb_mem hI ⟩
    have hnI : I.a = sorted n := by simp [n]
    have hmI : I.b = sorted m := by simp [m]
    obtain ⟨ m, hm ⟩ := m; obtain ⟨ n, hn ⟩ := n
    apply I.subset_Icc at hx
    simp [hnI, hmI] at hx
    obtain ⟨ hx1, hx2 ⟩ := hx
    have H : ∃ m, x ≤ a m := by use m; simp [a, hm, hx2]
    let r := Nat.find H
    have hrm : r ≤ m := by convert Nat.find_min' H _; simp [a, hm, hx2]
    have hr : r < k := by linarith
    have hxr : x ≤ sorted ⟨ r, hr ⟩ := by convert Nat.find_spec H; simp [r,a,hr]
    have hnr : n < r := by
      by_contra!
      replace : (sorted ⟨r, hr⟩).val ≤ (sorted ⟨n, hn⟩).val := by simp [this]
      simp [show x = sorted ⟨ n, hn ⟩ by order] at hend
    refine' ⟨ BoundedInterval.Ioo (sorted ⟨ r-1, by omega ⟩) (sorted ⟨ r, hr ⟩), _ , _, _ ⟩
    . apply Set.Subset.trans _ I.Ioo_subset
      simp [hnI, hmI]
      apply Set.Ioo_subset_Ioo <;> simp <;> omega
    . simp [T]; refine' ⟨ r-1, by omega, _ ⟩
      simp [a, show r-1 < k by omega, show r < k by omega, show r-1+1=r by omega]
    simp
    have h1 : x ≠ sorted ⟨ r, hr ⟩ := by by_contra!; simp [this] at hend
    have h3 : sorted ⟨ r-1, by omega ⟩ < x := by
      by_contra!
      convert Nat.find_min H (show r-1 < r by omega) _
      simp [a, show r-1 < k by omega, this]
    split_ands <;> order
  rintro ⟨ J, hJI, _, hxJ ⟩; exact hJI hxJ

/-- Lemma 1.1.2(i) -/
theorem Box.partition {d:ℕ} (S: Finset (Box d)) : ∃ T: Finset (Box d), T.toSet.PairwiseDisjoint Box.toSet ∧ ∀ I ∈ S, ∃ U : Set T, I = ⋃ J ∈ U, J.val.toSet := by
  choose T hTdisj hT using BoundedInterval.partition
  let J : Fin d → Finset BoundedInterval := fun i ↦ T (S.image (fun B ↦ B.side i))
  have hJdisj (i:Fin d) : (J i).toSet.PairwiseDisjoint BoundedInterval.toSet :=
    hTdisj (S.image (fun B ↦ B.side i))
  have hJ (i:Fin d) {B: Box d} (hB: B ∈ S) : ∃ U : Set (J i), B.side i = ⋃ K ∈ U, K.val.toSet := by
    apply hT (S.image (fun B ↦ B.side i)) (B.side i); simp; use B
  classical
  refine' ⟨ (Finset.univ.pi J).image (fun I ↦ ⟨ fun i ↦ I i (by simp) ⟩ ) , _, _ ⟩
  . rw [Set.pairwiseDisjoint_iff]
    intro B₁ hB₁ B₂ hB₂ hB₁B₂; simp at hB₁ hB₂
    obtain ⟨ J₁, hJ₁, rfl ⟩ := hB₁
    obtain ⟨ J₂, hJ₂, rfl ⟩ := hB₂
    ext i; simp
    have := hB₁B₂.some_mem
    simp [Box.toSet] at this
    rw [Set.mem_pi, Set.mem_pi] at this
    obtain ⟨ h₁, h₂ ⟩ := this; specialize h₁ i (by simp); specialize h₂ i (by simp)
    specialize hJdisj i; rw [Set.pairwiseDisjoint_iff] at hJdisj
    apply_rules [hJdisj, Set.nonempty_of_mem (x := (hB₁B₂.some i))]
    aesop
  intro B hB
  choose U hU using hJ
  use {B' | ∀ i, ∃ hi : B'.val.side i ∈ J i, ⟨ _, hi ⟩ ∈ U i hB}
  ext x
  simp [Box.toSet]; rw [Set.mem_pi]
  conv => lhs; intro i _; rw [hU i hB]
  conv => rhs; congr; intro a; rhs; rw [Set.mem_pi]
  simp; constructor
  . intro h; choose I hI using h
    use ⟨ I ⟩; simp; and_intros
    . refine' ⟨ _, _ ⟩
      . use fun i _ ↦ I i
        simp
        peel hI with i hi
        have ⟨ hIJ, hIJ' ⟩ := hi.1
        assumption
      peel hI with i hi
      tauto
    aesop
  rintro ⟨ B', ⟨ h1, h2 ⟩, h3 ⟩ i; use B'.side i
  aesop

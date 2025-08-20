import Mathlib.Tactic
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.SetTheory.ZFC.Basic
import Analysis.Tools.ExistsUnique
import Analysis.Section_3_1

/-!
# Analysis I, Chapter 3 epilogue: Connections with ZFSet

In this epilogue we show that the `ZFSet` type in Mathlib (derived as a quotient from the
`PSet` type) can be used to create models of the `SetTheory' class studied in this chapter, so long as we work in a universe of level at
least 1.  The constructions here are due to Edward van de Meent; see
https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Can.20this.20proof.20related.20to.20Set.20replacement.20be.20shorter.3F/near/527305173
-/

universe u

/-- A preliminary lemma about `PSet`: their natural numbers are ordered by membership. -/
lemma PSet.ofNat_mem_ofNat_of_lt (m n : ℕ) : n < m → ofNat n ∈ ofNat m := by
  intro h
  induction h with
  | refl => rw [ofNat]; exact mem_insert _ _
  | step _ ih => rw [ofNat]; exact mem_insert_of_mem _ ih

lemma PSet.mem_ofNat_iff (n m : ℕ) : ofNat n ∈ ofNat m ↔ n < m := by
  refine ⟨ ?_, ofNat_mem_ofNat_of_lt m n ⟩
  contrapose!; rw [le_iff_lt_or_eq]; rintro (h|rfl)
  · exact mem_asymm (ofNat_mem_ofNat_of_lt _ _ h)
  exact mem_irrefl _

/-- Another preliminary lemma: Natural numbers in `PSet` can only be equivalent
if they are equal. -/
lemma PSet.eq_of_ofNat_equiv_ofNat (n m : ℕ): (ofNat.{u} n).Equiv (ofNat.{u} m) → n = m := by
  wlog hmn : m ≤ n generalizing n m
  · intro heq; rw [this _ _ (by order) heq.symm]
  intro h; rw [Equiv.eq, Set.ext_iff] at h
  have : n ≤ m := by specialize h (ofNat m); simpa [mem_irrefl _, mem_ofNat_iff] using h
  order

open PSet in
/-- Using the above lemmas, we can create a bijection between `ZFSet.omega` and
the natural numbers. -/
noncomputable def ZFSet.nat_equiv : ℕ ≃ omega.{u} := Equiv.ofBijective (fun n => ⟨mk (ofNat.{u} n),mk_mem_iff.mpr (Mem.mk _ (ULift.up n))⟩) (by
  constructor
  · intro _ _; simp [eq]; apply eq_of_ofNat_equiv_ofNat
  · rintro ⟨x,hx⟩; rw [←mk_out x, omega, mk_mem_iff, PSet.omega] at hx; obtain ⟨n,hn⟩ := hx
    simp [mk_type, mk_func] at n hn ⊢; use n.down; rw [←mk_out x, eq]; cc
  )

open Classical in
/-- Show that ZFSet obeys the `Chapter3.SetTheory` axioms.  Most of these axioms were
essentially already established in Mathlib and are relatively routine to transfer over;
the equivalence of `ZF.omega` and `Nat` being the trickiest one in content (and the
power set axiom also requiring some technical manipulation). -/
noncomputable instance ZFSet.inst_SetTheory : Chapter3.SetTheory.{u + 1,u + 1} where
  Set := ZFSet
  Object := ZFSet
  set_to_object := { toFun := fun ⦃a₁⦄ => a₁, inj' := fun _ _ h => h}
  mem o s := o ∈ s
  extensionality _ _ := ext
  emptyset := ∅
  emptyset_mem := notMem_empty
  singleton x := {x}
  singleton_axiom _ _ := mem_singleton
  union_pair x y := x ∪ y
  union_pair_axiom _ _ _ := mem_union
  specify A P := ZFSet.sep (fun s ↦ (h : s ∈ A) → P ⟨s,h⟩) A
  specification_axiom := by simp +contextual
  replace A P hp := @(A.sep (fun s ↦ (hs : s ∈ A) → ∃ z, P ⟨s,hs⟩ z)).image (fun s ↦
    if h : ∃ (hs : s ∈ A), ∃ z, P ⟨s,hs⟩ z then h.choose_spec.choose else ∅) (Classical.allZFSetDefinable _)
  replacement_axiom A P hp s := by
    simp; constructor
    · intro ⟨z, ⟨hzA, hz⟩, hz'⟩; use z, hzA; rw [dif_pos (⟨hzA, hz hzA⟩)] at hz'; simp [←hz', Exists.choose_spec]
    · intro ⟨z, hzA, hz'⟩; use z, ⟨hzA,fun _ ↦ ⟨s,hz'⟩⟩
      apply hp ⟨z, hzA⟩; rw [dif_pos ⟨hzA, ⟨s, hz'⟩⟩]; use Exists.choose_spec _
  nat := omega
  nat_equiv := ZFSet.nat_equiv
  regularity_axiom A := by
    simp; intro x hx; obtain ⟨y,hy⟩ := regularity A (by rintro rfl; exact notMem_empty _ hx)
    use y, hy.left; intro z hzA hzy; have : z ∈ A ∩ y := mem_inter.mpr ⟨hzA, hzy⟩; simp_all [hy.right]
  pow X Y := funs Y X
  function_to_object X Y := {
    toFun f := @map (fun s ↦ if h : s ∈ X then f ⟨s,h⟩ else ∅) (Classical.allZFSetDefinable _) X
    inj' := by
      intro x _ h; ext ⟨s, hs⟩
      simp only at h; simp_rw [ZFSet.ext_iff, mem_map] at h; specialize h (s.pair (x ⟨s,hs⟩)); simp_all}
  powerset_axiom X Y F := by
    simp [IsFunc]; constructor
    · intro ⟨hsub,huniq⟩
      use (fun x ↦ ⟨(huniq x x.property).choose,(pair_mem_prod.mp (hsub (huniq x x.property).choose_spec)).right⟩)
      ext; simp; constructor
      · rintro ⟨y,hy,rfl⟩; simp_all [(huniq y hy).choose_spec]
      · intro hf; specialize hsub hf; rw [mem_prod] at hsub; obtain ⟨y,hy,x,hx,rfl⟩ := hsub
        use y,hy; simp_all [←(huniq y hy).choose_eq hf]
    · rintro ⟨f,rfl⟩
      simp; constructor
      · intro _ hs; simp at hs; obtain ⟨y,hy,rfl⟩ := hs; simp_all
      · intro _ hy; simp_all
  union := sUnion
  union_axiom _ _ := by simp [And.comm]

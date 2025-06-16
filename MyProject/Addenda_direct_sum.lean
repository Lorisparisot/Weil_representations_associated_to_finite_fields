import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Data.Set.Disjoint

/-!
# Addenda to the direct sums in mathlib

This file adds some lemmas about direct sums in mathlib.

## Main results
The goal of this file is to formalize the induced representation for finite group and
particular subgroup (commutative one) and the Frobenius reciprocity.

## Contents
+ Adds to `MonoidAlgebra`theory over a group, to create some particular tensor products.
+ `Induced_rep_center.tensor` : the representation induced by the center of a group `G`.
+ Frobenius reciprocity in the case...

-/

/--If two types `β` and `γ` are indexed by a same type `ι`, then we have an `AddEquiv` between
`DirectSum i β` and `DirectSum i γ`.-/
def DirectSum_equiv (ι : Type v) (β : ι → Type w) (γ : ι →  Type w) [(i : ι) → AddCommMonoid (β i)] [(i : ι) → AddCommMonoid (γ i)] (h : ∀ (i : ι), β i ≃+ γ i) :
  DirectSum ι β ≃+ DirectSum ι γ := by
  refine AddEquiv.mk ⟨?_, ?_, ?_, ?_ ⟩ ?_
  · rw[DirectSum, DirectSum]
    intro x
    refine ⟨fun i => (h i) (x.1 i),?_⟩
    have := x.2
    simp only [DFinsupp.toFun_eq_coe, EmbeddingLike.map_eq_zero_iff] at this ⊢
    exact this
  · rw[DirectSum, DirectSum]
    intro x
    refine ⟨fun i => (h i).invFun (x.1 i),?_⟩
    have := x.2
    simp only [DFinsupp.toFun_eq_coe, AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe,
      AddEquiv.coe_toEquiv_symm, EmbeddingLike.map_eq_zero_iff] at this ⊢
    exact this
  · intro x
    simp only [AddEquiv.toEquiv_eq_coe, DFinsupp.toFun_eq_coe, Equiv.invFun_as_coe,
      AddEquiv.coe_toEquiv_symm, eq_mpr_eq_cast, cast_eq, id_eq, DFinsupp.coe_mk', cast_cast]
    congr
    · ext u
      simp only [AddEquiv.symm_apply_apply, DFinsupp.toFun_eq_coe]
    · simp only [DFinsupp.toFun_eq_coe, cast_heq]
  · intro x
    simp only [DFinsupp.toFun_eq_coe, eq_mpr_eq_cast, cast_eq, AddEquiv.toEquiv_eq_coe,
      Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, id_eq, DFinsupp.coe_mk', cast_cast]
    congr
    · ext u
      simp only [AddEquiv.apply_symm_apply, DFinsupp.toFun_eq_coe]
    · simp only [DFinsupp.toFun_eq_coe, cast_heq]
  · simp only [DFinsupp.toFun_eq_coe, eq_mpr_eq_cast, cast_eq, DirectSum.add_apply]
    intro x y
    dsimp
    refine DirectSum.ext_iff.mpr ?_
    intro i
    simp only [DFinsupp.coe_mk', map_add, DirectSum.add_apply]

/--`DirectSum_equiv` as a k linear equivalence.-/
def DirectSum_equiv_linearmap (A : Type) [Semiring A] (ι : Type v) (β : ι → Type w) (γ : ι →  Type w) [(i : ι) → AddCommMonoid (β i)] [(i : ι) → AddCommMonoid (γ i)] [(i : ι) → Module A (β i)]
  [(i : ι) → Module A (γ i)] (h : ∀ (i : ι), β i ≃ₗ[A] γ i) : DirectSum ι β ≃ₗ[A] DirectSum ι γ := by
  refine Equiv.toLinearEquiv ((DirectSum_equiv ι β γ (fun i ↦ (h i).toAddEquiv)).toEquiv) ?_
  refine { map_add := ?_, map_smul := ?_ }
  · intro x y
    simp only [LinearEquiv.coe_toAddEquiv, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, map_add]
  · intro c x
    simp only [LinearEquiv.coe_toAddEquiv, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
    refine Eq.symm (DirectSum.ext γ ?_)
    intro j
    rw[DirectSum_equiv]
    simp only [DFinsupp.toFun_eq_coe, LinearEquiv.coe_addEquiv_apply, eq_mpr_eq_cast, cast_eq,
      AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, AddEquiv.coe_mk,
      Equiv.coe_fn_mk, DFinsupp.coe_mk']
    rw [@DirectSum.smul_apply]
    simp only [DFinsupp.coe_mk']
    rw [← @LinearEquiv.map_smul]
    congr

/--Given a family `x : (i : ι) → β i` of indexed types on a fintype `ι`, we have the identity :
`(∑ (i : ι), (DirectSum.of β i) (x i)) j = x j`.-/
@[simp]
theorem DirectSum_eq_sum_direct (ι : Type*) [hi : Fintype ι] (β : ι → Type w)
  [(i : ι) → AddCommMonoid (β i)] [DecidableEq ι] (x : (i : ι) → β i) (j : ι) :
  (∑ (i : ι), (DirectSum.of β i) (x i)) j = x j  := by
  have := Finset.sum_apply (a := j) (g := fun i ↦ (DirectSum.of β i) (x i)) (s := Finset.univ)
  rw [DFinsupp.finset_sum_apply, Finset.sum_eq_single j]
  · simp only [DirectSum.of_eq_same]
  · intro a _ ha
    exact DirectSum.of_eq_of_ne _ _ _ ha
  · simp only [Finset.mem_univ, not_true_eq_false, DirectSum.of_eq_same, IsEmpty.forall_iff]



#min_imports

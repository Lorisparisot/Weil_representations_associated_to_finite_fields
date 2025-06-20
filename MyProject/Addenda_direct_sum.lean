import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Addenda to the direct sums and tensor products in mathlib

This file adds some lemmas about direct sums and tensor products in mathlib.


## Contents
+ `DirectSum_equiv_linearmap` : if `β ≃ₗ[A] γ` then DirectSum ι β ≃ₗ[A] DirectSum ι γ
+ `DirectSum_eq_sum_direct` : Given a family `x : (i : ι) → β i` of indexed types on a fintype `ι`,
we have the identity : `(∑ (i : ι), (DirectSum.of β i) (x i)) j = x j`.
+ `iso_hom_tens` : isomorphism between $Hom_B(B⊗_AM,N)$ and $Hom_A(M,N)$ for $B$ an `A`-algebra, `M` an `A`-module
and `N` a `B`-module.
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

/--`DirectSum_equiv` as a `k` linear equivalence.-/
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

/--Isomorphism between $Hom_B(B⊗_AM,N)$ and $Hom_A(M,N)$ for $B$ an `A`-algebra, `M` an `A`-module
and `N` a `B`-module.-/
noncomputable def iso_hom_tens (A M N B: Type*) [CommSemiring A] [Semiring B] [Algebra A B] [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N] [Module B N] [IsScalarTower A B N]:
((TensorProduct A B M) →ₗ[B] N) ≃ₗ[A] (M →ₗ[A] N) := by
  refine Equiv.toLinearEquiv ?_ ?_
  · refine Equiv.ofBijective ?_ ?_
    · intro φ
      refine LinearMap.mk ?_ ?_
      · refine AddHom.mk (fun x => φ (TensorProduct.tmul A (1 : B) x)) ?_
        · intro x y
          rw [← @LinearMap.map_add,← @TensorProduct.tmul_add]
      · intro m x
        simp only [TensorProduct.tmul_smul, LinearMap.map_smul_of_tower, RingHom.id_apply]
    · constructor
      · intro x y
        simp only [LinearMap.mk.injEq, AddHom.mk.injEq]
        intro h
        ext u
        simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
          LinearMap.coe_restrictScalars]
        rw [funext_iff] at h
        specialize h u
        exact h
      · intro φ
        let ψ : TensorProduct A B M →ₗ[B] N := by
          have f : B →ₗ[A] M →ₗ[A] N := by
            refine LinearMap.mk ?_ ?_
            · refine AddHom.mk ?_ ?_
              · intro b
                refine LinearMap.mk ?_ ?_
                · refine AddHom.mk (fun x => b • (φ x)) ?_
                  · intro m1 m2
                    simp only [map_add, smul_add]
                · intro a m
                  simp only [map_smul, RingHom.id_apply]
                  exact smul_comm b a (φ m)
              · intro b1 b2
                congr
                simp only [LinearMap.coe_mk, AddHom.coe_mk]
                ext m
                simp only [Pi.add_apply]
                exact Module.add_smul b1 b2 (φ m)
            · intro a b
              simp only [smul_assoc, RingHom.id_apply]
              exact rfl
          refine TensorProduct.AlgebraTensorModule.lift ?_
          refine LinearMap.mk ?_ ?_
          · refine AddHom.mk ?_ ?_
            · intro b
              refine LinearMap.mk ?_ ?_
              · refine AddHom.mk ?_ ?_
                · exact (fun x => b • (φ x))
                · intro m1 m2
                  simp only [map_add, smul_add]
              · intro a m
                simp only [map_smul, RingHom.id_apply]
                exact smul_comm b a (φ m)
            · intro b1 b2
              congr
              simp only [LinearMap.coe_mk, AddHom.coe_mk]
              ext m
              simp only [Pi.add_apply]
              exact Module.add_smul b1 b2 (φ m)
          · intro b1 b2
            simp only [smul_eq_mul, RingHom.id_apply]
            ext m
            simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply]
            exact mul_smul b1 b2 (φ m)
        · use ψ
          ext m
          simp only [LinearMap.coe_mk, AddHom.coe_mk]
          rw [@TensorProduct.AlgebraTensorModule.lift_tmul]
          simp only [LinearMap.coe_mk, AddHom.coe_mk, one_smul]
  · exact { map_add := fun x ↦ congrFun rfl, map_smul := fun c ↦ congrFun rfl }



noncomputable def TensorProduct.map_equiv {R : Type u_1} [CommSemiring R] {M : Type u_5} {N : Type u_6} {P : Type u_7} {Q : Type u_8} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [Module R M] [Module R N] [Module R Q] [Module R P] (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
  TensorProduct R M N ≃ₗ[R] TensorProduct R P Q := by
  exact congr f g

#min_imports

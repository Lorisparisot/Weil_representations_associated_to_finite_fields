import Mathlib.RepresentationTheory.Basic

/-!
# Addendum to the representation theory in mathlib

This file adds some properties about representation theory in mathlib.

## Main results
The goal of this file is to formalize the induced representation for finite group and
particular subgroup (commutative one) and the Frobenius reciprocity.

## Contents
+ Adds to `MonoidAlgebra`theory over a group, to create some particular tensor products.
+ Induced representation in the case...
+ Frobenius reciprocity in the case...

-/

namespace kG_kH_Module

variable (k G : Type*) [inst1 : Field k] [inst2 : Group G]
variable (H : @Subgroup G inst2) [instH : H.IsCommutative]


omit k instH in
/--The trivial map is a homomorphism.-/
instance mulHom_mapHG : H →* G := by
  exact H.subtype

/--The trivial map from `MonoidAlgebra k H` to `MonoidAlgebra k G`, ie elements from
`MonoidAlgebra k H` are seen as `MonoidAlgebra k G`.-/
noncomputable def Map_KHKG : (MonoidAlgebra k H) → (MonoidAlgebra k G) :=
  fun h => MonoidAlgebra.mapDomain (Subgroup.subtype H) h

/--If `H` is commutative, `MonoidAlgebra k H` is a commutative monoid.-/
noncomputable instance KHCommMonoid : CommMonoid (MonoidAlgebra k H) := by
  exact CommMonoidWithZero.toCommMonoid

/--`MonoidAlgebra k H` is a commutative semiring.-/
noncomputable instance KHCommRing : CommSemiring (MonoidAlgebra k H) := by
  exact MonoidAlgebra.commSemiring

/--Scalar multiplication between `MonoidAlgebra k H` and `MonoidAlgebra k G`, ie
classical mulitplication between an element of `MonoidAlgebra k H` seen as an element
of `MonoidAlgebra k G` and an element of `MonoidAlgebra k G`.-/
noncomputable instance SMulKHKG : SMul (MonoidAlgebra k H) (MonoidAlgebra k G) := by
  refine SMul.mk ?_
  intro h
  intro g
  exact (Map_KHKG k G H h)*g

/--Ring morphism from `MonoidAlgebra k H` to `MonoidAlgebra k G`, given by the coercion
of element of `H`into element of `G`.-/
noncomputable def RingMorphism_KH_KG : (MonoidAlgebra k H) →+* (MonoidAlgebra k G) := by
  exact MonoidAlgebra.mapDomainRingHom k (mulHom_mapHG G H)

/--`MonoidAlgebra k G` is a `MonoidAlgebra k (Subgroup.center G)` algebra.-/
noncomputable instance KG_is_Kcenter_Algebra : Algebra (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k G) := by
  refine Algebra.mk (RingMorphism_KH_KG k G (Subgroup.center G)) ?_ ?_
  · intro pH pG
    ext x
    rw[RingMorphism_KH_KG,MonoidAlgebra.mapDomainRingHom_apply, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, Finsupp.mapDomain.addMonoidHom_apply,mulHom_mapHG,Subgroup.coe_subtype,
      @MonoidAlgebra.mul_apply_right,@MonoidAlgebra.mul_apply_left]
    congr
    rw [funext_iff]
    intro g1
    rw[funext_iff]
    intro k1
    rw[Finsupp.mapDomain,Finsupp.sum]
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
    rw [@Finset.mul_sum,@Finset.sum_mul]
    congr
    rw[funext_iff]
    intro x1
    rw[mul_comm,mul_eq_mul_left_iff]
    left
    rw [@Finsupp.single_eq_set_indicator]
    have htriv :  ↑x1 ∈ Subgroup.center G := by
          simp only [SetLike.coe_mem]
    have sub := (@Subgroup.mem_center_iff G _ x1).mp htriv
    by_cases hf : (x * g1⁻¹) = x1
    · have hf1 : (g1⁻¹ * x) = x1 :=by
        rw [@inv_mul_eq_iff_eq_mul,sub,mul_eq_of_eq_mul_inv (id (Eq.symm hf))]
      rw[hf,hf1]
    · push_neg at hf
      rw [← @Finset.not_mem_singleton] at hf
      rw [Set.indicator,@ite_eq_iff]
      right
      constructor
      · refine Set.not_mem_singleton_iff.mpr ?_
        rw [Finset.mem_singleton] at hf
        exact hf
      · rw[Set.indicator,@eq_ite_iff]
        right
        simp only [Set.mem_singleton_iff, and_true]
        by_contra hff
        apply hf
        rw [Finset.mem_singleton,@mul_inv_eq_iff_eq_mul,<-sub,mul_eq_of_eq_inv_mul (id (Eq.symm hff))]
  · intro pH pG
    rw[HSMul.hSMul,instHSMul,RingMorphism_KH_KG,MonoidAlgebra.mapDomainRingHom_apply, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, Finsupp.mapDomain.addMonoidHom_apply]
    exact rfl

end kG_kH_Module
#min_imports




--TensorProduct.leftModule TensorProduct.lift Algebra.ofModule

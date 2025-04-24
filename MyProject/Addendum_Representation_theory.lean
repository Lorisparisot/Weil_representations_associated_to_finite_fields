import Mathlib.RepresentationTheory.Basic

namespace Representation_induced

variable (k G W : Type*) [inst1 : Field k] [inst2 : Group G] [inst3 : AddCommGroup W] [inst4 : Finite G]
[inst5 : Module k W] [inst6 : FiniteDimensional k W]
variable (H : @Subgroup G inst2) [instH : H.IsCommutative]
variable (θ : Representation k H W)

noncomputable def kHModule1 : MonoidAlgebra k H →ₐ[k] Module.End k W := by
  exact Representation.asAlgebraHom θ

#check (MonoidAlgebra k H)
#check (MonoidAlgebra k G)


noncomputable def mapHG : H → G :=
  fun h => (Subgroup.subtype H) h

instance mulHom_mapHG : H →* G := by
  exact H.subtype

@[simp]
theorem mapHG_eval (h : H) : mapHG G H h = ↑h:= by
  rfl

#check mapHG

noncomputable def Map_KHKG : (MonoidAlgebra k H) → (MonoidAlgebra k G) :=
  fun h => MonoidAlgebra.mapDomain (Subgroup.subtype H) h

noncomputable instance KHCommMonoid : CommMonoid (MonoidAlgebra k H) := by
  exact CommMonoidWithZero.toCommMonoid

#check KHCommMonoid

noncomputable instance SMul_KHKG : SMul (MonoidAlgebra k H) (MonoidAlgebra k G) := by
  refine SMul.mk ?_
  intro h
  intro g
  exact (Map_KHKG k G H h)*g

noncomputable instance KHCommRing : CommSemiring (MonoidAlgebra k H) := by
  have h1 := KHCommMonoid k G H
  exact MonoidAlgebra.commSemiring

noncomputable instance SMulKHKG : SMul (MonoidAlgebra k H) (MonoidAlgebra k G) := by
  refine SMul.mk ?_
  intro h
  intro g
  exact (Map_KHKG k G H h)*g

noncomputable def RingMorphism_KH_KG : (MonoidAlgebra k H) →+* (MonoidAlgebra k G) := by
  exact MonoidAlgebra.mapDomainRingHom k (mulHom_mapHG G H)

noncomputable instance KG_is_KH_Algebra : Algebra (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k G) := by
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


def KGModule := TensorProduct (MonoidAlgebra k H) (MonoidAlgebra k G) (Representation.asModule θ)
  sorry
#min_imports

end Representation_induced


--TensorProduct.leftModule TensorProduct.lift Algebra.ofModule

import Mathlib
import MyProject.Addenda_group_theory.lean


/-!
# Addenda to the monoid algebra theory in mathlib

This file adds some properties about monoid algebra theory in mathlib.

## Main results
The goal of this file is to formalize the induced representation for finite group and
particular subgroup (commutative one) and the Frobenius reciprocity.

## Contents
+ Adds to `MonoidAlgebra`theory over a group, to create some particular tensor products.
+ `Induced_rep_center.tensor` : the representation induced by the center of a group `G`.
+ Frobenius reciprocity in the case...

-/

open Classical
variable (k G : Type*) [inst1 : Field k] [inst2 : Group G]
variable (H : @Subgroup G inst2) [instH : IsMulCommutative H]




omit instH in
/--The trivial map from `MonoidAlgebra k H` to `MonoidAlgebra k G`, ie elements from
`MonoidAlgebra k H` are seen as `MonoidAlgebra k G`.-/
noncomputable def Map_KHKG : (MonoidAlgebra k H) →+* (MonoidAlgebra k G) := by
  exact  MonoidAlgebra.mapDomainRingHom k H.subtype

/--`Map_KHKG` is indeed an injective map.-/
instance Map_KHKG_inj : Function.Injective (Map_KHKG k G H) := by
  unfold Map_KHKG
  have h1 := @MonoidAlgebra.mapDomain_injective k H G _ (Subgroup.subtype H) (Subgroup.subtype_injective H )
  exact h1

omit instH in
@[simp]
theorem Map_KhKG_single_apply (h : H) (c :k) : (Map_KHKG k G H) (MonoidAlgebra.single h (c:k)) = MonoidAlgebra.single ↑h (c:k) := by
  unfold Map_KHKG
  simp only [MonoidAlgebra.mapDomainRingHom_apply, Subgroup.coe_subtype, ZeroHom.toFun_eq_coe,
    AddMonoidHom.toZeroHom_coe, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]

omit instH in
/--`Map_KHKG` is indeed a `k` linear map.-/
@[simp]
theorem Map_KHKG_k_linear (c : k) (x : MonoidAlgebra k H): (Map_KHKG k G H) (c • x) = c • ((Map_KHKG k G H) x) := by
    unfold Map_KHKG
    simp only [MonoidAlgebra.mapDomainRingHom_apply, Subgroup.coe_subtype, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, Finsupp.mapDomain.addMonoidHom_apply]
    rw[Finsupp.mapDomain_smul]


omit instH in
/--Coercion from `MonoidAlgebra k H` to `MonoidAlgebra k G` when `H` is a subgroup of `G`-/
noncomputable instance Coe : CoeOut (MonoidAlgebra k H) (MonoidAlgebra k G) := by
  refine { coe := Map_KHKG k G H }

/--If `G`is commutative, then `MonoidAlgebra k G` is a commutative semiring.-/
noncomputable instance KGCommRing [instG : CommGroup G] : CommSemiring (MonoidAlgebra k G) := by
  exact MonoidAlgebra.commSemiring

omit instH in
/--Scalar multiplication between `MonoidAlgebra k H` and `MonoidAlgebra k G`, ie
classical mulitplication between an element of `MonoidAlgebra k H` seen as an element
of `MonoidAlgebra k G` and an element of `MonoidAlgebra k G`.-/
noncomputable instance SMulKHKG : SMul (MonoidAlgebra k H) (MonoidAlgebra k G) := by
  refine SMul.mk (fun h g => (Map_KHKG k G H h)*g)

omit instH in
/--Ring morphism from `MonoidAlgebra k H` to `MonoidAlgebra k G`, given by the coercion
of element of `H`into element of `G`.-/
noncomputable def RingMorphism_KH_KG : (MonoidAlgebra k H) →+* (MonoidAlgebra k G) := by
  exact Map_KHKG k G H

/--`MonoidAlgebra k G` is a `MonoidAlgebra k (Subgroup.center G)` algebra.-/
noncomputable instance KG_is_KcenterG_Algebra : Algebra (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k G) := by
  refine Algebra.mk (RingMorphism_KH_KG k G (Subgroup.center G)) ?_ ?_
  · intro pH pG
    ext x
    rw[RingMorphism_KH_KG,Map_KHKG,MonoidAlgebra.mapDomainRingHom_apply, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, Finsupp.mapDomain.addMonoidHom_apply,Subgroup.coe_subtype,
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
    by_cases hf : (x * g1⁻¹) = x1
    · have hf1 : (g1⁻¹ * x) = x1 :=by
        rw [@inv_mul_eq_iff_eq_mul,((@Subgroup.mem_center_iff G _ x1).mp (SetLike.coe_mem x1)),
        mul_eq_of_eq_mul_inv (id (Eq.symm hf))]
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
        rw [Finset.mem_singleton,@mul_inv_eq_iff_eq_mul,<-((@Subgroup.mem_center_iff G _ x1).mp (SetLike.coe_mem x1)),mul_eq_of_eq_inv_mul (id (Eq.symm hff))]
  · intro pH pG
    rw[HSMul.hSMul,instHSMul,RingMorphism_KH_KG,Map_KHKG,MonoidAlgebra.mapDomainRingHom_apply, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, Finsupp.mapDomain.addMonoidHom_apply]
    exact rfl

/--If we have a homomorphism `H →* Subgroup.center G`, then we have `Algebra (MonoidAlgebra k H) (MonoidAlgebra k G)`. -/
noncomputable instance KG_is_KH_Algebra (ϕ : H →* Subgroup.center G) : Algebra (MonoidAlgebra k H) (MonoidAlgebra k G):= by
  exact Algebra.compHom (MonoidAlgebra k G) (MonoidAlgebra.mapDomainRingHom k ϕ)


/--For every `g:G`, `x : MonoidAlgebra k (Subgroup.center G)` commutes with
`MonoidAlgebra.single g (1:k)`. -/
@[simp]
theorem center_commutes_single (x : MonoidAlgebra k (Subgroup.center G)) (g : G) : Map_KHKG k G (Subgroup.center G) x * MonoidAlgebra.single (g : G) (1:k) = MonoidAlgebra.single (g) (1:k) * x := by
  unfold MonoidAlgebra.single Map_KHKG
  simp
  unfold Finsupp.mapDomain
  rw[Finsupp.sum]
  rw [@MonoidAlgebra.ext_iff]
  intro x1
  simp
  conv => lhs; rhs;intro a;rw[Finsupp.single_apply]
  conv => rhs; rhs; intro a; rw[Finsupp.single_apply]
  congr
  ext a
  have : ↑a = x1 * g⁻¹ ↔ ↑a = g⁻¹ * x1 := by
    constructor
    · intro ha
      exact Addenda_group_theory.center_mul G a x1 g⁻¹ ha
    · intro ha
      exact Addenda_group_theory.center_mul G a g⁻¹ x1 ha
  exact if_ctx_congr this (congrFun rfl) (congrFun rfl)

/--Coercion from `Set (MonoidAlgebra k H)` to `(Set (MonoidAlgebra k G))`.-/
noncomputable instance Set_Coe : CoeOut (Set (MonoidAlgebra k H)) (Set (MonoidAlgebra k G)) := by
  refine { coe := ?_ }
  intro x
  have h := (kG_kH_Module.RingMorphism_KH_KG k G H)
  let xG := {h a | a ∈ x}
  exact xG

/--`(MonoidAlgebra k (Subgroup.center G))` seen as a subset of `MonoidAlgebra k G`
is a `(MonoidAlgebra k (Subgroup.center G))` submodule of `(MonoidAlgebra k (Subgroup.center G))`.-/
noncomputable def center_sub_module : Submodule (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k G) := by
   refine Submodule.mk ?_ ?_
   · refine AddSubmonoid.mk ?_ ?_
     · refine AddSubsemigroup.mk ?_ ?_
       · let h1 := @Set.univ (MonoidAlgebra k (Subgroup.center G))
         have h := (kG_kH_Module.RingMorphism_KH_KG k G (Subgroup.center G))
         let xG := {h a | a ∈ h1}
         exact xG
       · intro a b ha hb
         simp
         simp at ha hb
         obtain ⟨ya, ha⟩ := ha
         obtain ⟨yb, hb⟩ := hb
         use ya+yb
         rw[<-ha,<-hb]
         exact RingHom.map_add (kG_kH_Module.Map_KHKG k G (Subgroup.center G)) ya yb
     · simp only [Set.mem_univ, true_and, Set.mem_setOf_eq]
       use 0
       simp only [map_zero]
   · intro c x
     simp only [Set.mem_univ, true_and, Set.mem_setOf_eq, forall_exists_index]
     intro x1 hx1
     use c*x1
     simp only [map_mul]
     exact congrArg (HMul.hMul ((kG_kH_Module.Map_KHKG k G (Subgroup.center G)) c)) hx1

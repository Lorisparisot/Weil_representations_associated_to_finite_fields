import MyProject.Addenda_group_theory
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Data.Set.Disjoint



/-!
# Addendum to the representation theory in mathlib

This file adds some properties about representation theory in mathlib.

## Main results
The goal of this file is to formalize the induced representation for finite group and
particular subgroup (commutative one) and the Frobenius reciprocity.

## Contents
+ Adds to `MonoidAlgebra`theory over a group, to create some particular tensor products.
+ `Induced_rep_center.tensor` : the representation induced by the center of a group `G`.
+ Frobenius reciprocity in the case...

-/

namespace kG_kH_Module
open Classical
variable (k G : Type*) [inst1 : Field k] [inst2 : Group G]
variable (H : @Subgroup G inst2) [instH : IsMulCommutative H]


theorem center_mul_com (g : G) (h : Subgroup.center G) : h * g = g * h := by
    have := @Subgroup.mem_center_iff G _ h
    simp only [SetLike.coe_mem, true_iff] at this
    exact (this g).symm

@[simp]
theorem center_mul (h : Subgroup.center G) (a b : G) (h1 : h =a *b) : h = b*a := by
  have h2 := mul_inv_eq_of_eq_mul h1
  rw[center_mul_com] at h2
  rw[<-h2]
  simp only [mul_inv_cancel_left]


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
      exact center_mul G a x1 g⁻¹ ha
    · intro ha
      exact center_mul G a g⁻¹ x1 ha
  exact if_ctx_congr this (congrFun rfl) (congrFun rfl)

end kG_kH_Module



namespace Induced_rep_center

variable (k G W : Type*) [inst1 : Field k] [inst2 : Group G] [inst3 : Finite G]
[inst4 : AddCommGroup W] [inst5 : Module k W]

variable (H : @Subgroup G inst2) [instH : IsMulCommutative H]

variable (θ : Representation k (Subgroup.center G) W)



/--Induced representation on `G` by a representation `Representation k (Subgroup.center G) W`
seen as a tensor product. -/
abbrev tensor :=
  TensorProduct (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k G) (θ.asModule)

/--`tensor k G W θ` is an `AddCommMonoid`.-/
noncomputable instance tensor_add_comm_mon : AddCommMonoid (tensor k G W θ) := by
  rw[tensor]
  exact TensorProduct.addCommMonoid

/--`tensor k G W θ` is a `MonoidAlgebra k G` module.-/
noncomputable instance tensor_module : Module (MonoidAlgebra k G) (tensor k G W θ) := by
  unfold tensor
  exact TensorProduct.leftModule

/--Induced representation on `G` by a representation `Representation k (Subgroup.center G) W`
seen as a representation. -/
noncomputable def as_rep := @Representation.ofModule k G _ _ (tensor k G W θ) _ _

/--Subrepresentation of `tensor` as module.-/
def module_sub_rep := TensorProduct (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k (Subgroup.center G)) (θ.asModule)

/--Coercion from `module_sub_rep` to `tensor`. -/
noncomputable instance Coe : CoeOut (module_sub_rep k G W θ) (tensor k G W θ) := by
  refine { coe := ?_ }
  rw[tensor, module_sub_rep]
  intro x
  have h2 : (MonoidAlgebra k ↥(Subgroup.center G)) →ₗ[(MonoidAlgebra k ↥(Subgroup.center G))] (MonoidAlgebra k G) := by
    refine LinearMap.mk ?_ ?_
    · refine AddHom.mk ?_ ?_
      · exact fun a ↦ kG_kH_Module.RingMorphism_KH_KG k G (Subgroup.center G) a
      · intro x1 y1
        simp only [map_add]
    · intro m x
      simp
      unfold kG_kH_Module.RingMorphism_KH_KG
      exact rfl
  have h1 := LinearMap.rTensor θ.asModule h2
  let x1 := h1 x
  exact x1

/--`module_sub_rep` is an additive commutative monoid.-/
noncomputable instance module_sub_rep_addcommmon : AddCommMonoid (module_sub_rep k G W θ) := by
  unfold module_sub_rep
  exact TensorProduct.addCommMonoid

/--`module_sub_rep` is a `MonoidAlgebra k (Subgroup.center G)` module.-/
noncomputable instance module_sub_rep_module :  Module (MonoidAlgebra k ↥(Subgroup.center G)) (module_sub_rep k G W θ) := by
  unfold module_sub_rep
  exact TensorProduct.instModule

/--The tensor product `module_sub_rep` is lineary equivalent to `θ.asModule` (which is a specialization
of a more specific theorem that I should implement : a ⨂ₐ M ≃ M)-/
noncomputable def module_sub_rep_iso : module_sub_rep k G W θ ≃ₗ[MonoidAlgebra k (Subgroup.center G)] θ.asModule := by
  unfold module_sub_rep
  refine LinearEquiv.mk ?_ ?_ ?_ ?_
  · refine LinearMap.mk ?_ ?_
    · refine AddHom.mk ?_ ?_
      · exact (fun g => (TensorProduct.rid (MonoidAlgebra k (Subgroup.center G)) θ.asModule) ((TensorProduct.comm (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k (Subgroup.center G)) θ.asModule) g))
      · simp only [map_add, implies_true]
    · simp only [map_smul, RingHom.id_apply, implies_true]
  · exact (fun g => ((TensorProduct.comm (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k (Subgroup.center G)) θ.asModule).invFun) (((TensorProduct.rid (MonoidAlgebra k (Subgroup.center G)) θ.asModule).invFun) g))
  · intro x
    simp only [LinearEquiv.invFun_eq_symm, LinearEquiv.symm_apply_apply]
  · intro x
    simp only [LinearEquiv.invFun_eq_symm, TensorProduct.rid_symm_apply,
      TensorProduct.comm_symm_tmul, TensorProduct.comm_tmul, TensorProduct.rid_tmul, one_smul]

/-- `tensor k G W θ` is a `MonoidAlgebra k ↥(Subgroup.center G)` module.-/
noncomputable instance tensor_module_sub : Module (MonoidAlgebra k ↥(Subgroup.center G)) (tensor k G W θ) := by
  unfold tensor
  refine Module.mk ?_ ?_
  · intro rc sc x
    exact TensorProduct.add_smul rc sc x
  · intro x
    exact TensorProduct.zero_smul x

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

/--`θ.asModule` is a `(MonoidAlgebra k (Subgroup.center G))` submodule over itself.-/
noncomputable def subrep_sub_module : Submodule (MonoidAlgebra k (Subgroup.center G)) (θ.asModule) := by
  refine Submodule.mk ?_ ?_
  · refine AddSubmonoid.mk ?_ ?_
    · refine AddSubsemigroup.mk ?_ ?_
      · exact (@Set.univ θ.asModule)
      · simp only [Set.mem_univ, imp_self, implies_true]
    · simp only [Set.mem_univ]
  · simp only [Set.mem_univ, imp_self, implies_true]

/--`θ.asModule` is isomorphic to itself seen as a submodule.-/
noncomputable def subrep_sub_module_iso : θ.asModule ≃ₗ[MonoidAlgebra k (Subgroup.center G)] subrep_sub_module k G W θ := by
  refine Equiv.toLinearEquiv ?_ ?_
  · refine Equiv.mk ?_ ?_ ?_ ?_
    · intro x
      unfold subrep_sub_module
      simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_univ]
      refine ⟨x,?_⟩
      simp only
    · intro x
      exact x.1
    · simp only [eq_mpr_eq_cast, cast_eq, id_eq]
      exact congrFun rfl
    · simp only [eq_mpr_eq_cast, cast_eq, id_eq]
      exact congrFun rfl
  · exact { map_add := fun x ↦ congrFun rfl, map_smul := fun c ↦ congrFun rfl }

/--`TensorProduct (MonoidAlgebra k (Subgroup.center G)) θ.asModule` is a `(MonoidAlgebra k (Subgroup.center G))` submodule
of `tensor k G W θ`.-/
noncomputable def is_sub_rep_submodule_iso : Submodule (MonoidAlgebra k (Subgroup.center G)) (tensor k G W θ) := by
  refine Submodule.mk ?_ ?_
  · refine AddSubmonoid.mk ?_ ?_
    · refine AddSubsemigroup.mk ?_ ?_
      · exact (Set.image (TensorProduct.mapIncl (center_sub_module k G) (subrep_sub_module k G W θ)) (Set.univ))
      · simp
        intro a b x1 hx1 x2 hx2
        use (x1+x2)
        simp only [map_add]
        exact Mathlib.Tactic.LinearCombination.add_eq_eq hx1 hx2
    · use 0
      simp only [Set.mem_univ, TensorProduct.mapIncl, map_zero, and_self]
  · simp only [TensorProduct.mapIncl, Set.image_univ, Set.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff]
    intro c a
    use (c • a)
    simp only [map_smul]


#check module_sub_rep k G W θ
#check is_sub_rep_submodule_iso k G W θ

/--The image of `θ.asModule` by `module_sub_rep_iso` is a submodule of `tensor k G W θ`, ie
`θ.asModule` is a subrepresentation of the induced representation-/
noncomputable def subsubsub : Submodule (MonoidAlgebra k (Subgroup.center G)) (tensor k G W θ) := by
  refine Submodule.mk ?_ ?_
  · refine AddSubmonoid.mk ?_ ?_
    · refine AddSubsemigroup.mk ?_ ?_
      · let theta := @Set.univ θ.asModule
        have h := module_sub_rep_iso k G W θ
        unfold module_sub_rep at h
        let theta1 := Set.image (h.invFun) theta
        have : MonoidAlgebra k (Subgroup.center G) →ₗ[MonoidAlgebra k (Subgroup.center G)] MonoidAlgebra k G := by
          exact Algebra.linearMap (MonoidAlgebra k ↥(Subgroup.center G)) (MonoidAlgebra k G)
        have theta2 := @TensorProduct.map (MonoidAlgebra k (Subgroup.center G)) _ (MonoidAlgebra k (Subgroup.center G)) (θ.asModule) (MonoidAlgebra k G) (θ.asModule) _ _ _ _ _ _ _ _ this (LinearMap.id)
        have theta3 := theta2 ∘ h.invFun
        rw [tensor]
        let thetaim := Set.image theta3 (@Set.univ θ.asModule)
        exact thetaim
      · simp
        intro a b thetaA ha thetaB hb
        use (thetaA + thetaB)
        simp
        rw[hb, ha]
    · simp
      use 0
      simp
  · intro c x
    simp
    intro x1 hx1
    rw[<-hx1]
    use (c • x1)
    simp only [map_smul]



noncomputable def subrep : θ.asModule ≃ₗ[MonoidAlgebra k (Subgroup.center G)] subsubsub k G W θ := by
  refine Equiv.toLinearEquiv ?_ ?_
  · refine Equiv.ofBijective ?_ ?_
    · intro x
      unfold subsubsub
      simp
      refine ⟨ ?_, ?_⟩
      ·  exact ((TensorProduct.map (Algebra.linearMap (MonoidAlgebra k ↥(Subgroup.center G)) (MonoidAlgebra k G)) LinearMap.id)
        ((module_sub_rep_iso k G W θ).symm x))
      · use x
        rfl
    · constructor
      · intro x1 x2
        simp
        intro h
        unfold module_sub_rep_iso at h
        simp only [LinearEquiv.invFun_eq_symm, TensorProduct.rid_symm_apply,
          TensorProduct.comm_symm_tmul, id_eq, LinearEquiv.coe_symm_mk, TensorProduct.map_tmul,
          Algebra.linearMap_apply, map_one, LinearMap.id_coe] at h
        sorry
      · intro y
        unfold subsubsub at y
        obtain ⟨hy, hy1⟩ := y
        obtain ⟨ hy2,hy3⟩ := hy1
        use hy2
        simp
        simp at hy3
        sorry
  sorry


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


/--Given `E` a `MonoidAlgebra k G` module, the natural isomorphism between `MonoidAlgebra k G`-linear map from the induced representation `tensor`
 to `E`and `MonoidAlgebra k (Subgroup.center G)`-linear map from our `θ.asModule` seen as tensor product over `MonoidAlgebra k (Subgroup;center G))`
 to `E` : $Hom_{k[G]}(k[G]⊗_{k[Z(G)]}θ, E) ≃ Hom_{k[H]}(θ,E)$. -/
noncomputable def iso_induced_as_tensor (E : Type*) [AddCommMonoid E] [Module (MonoidAlgebra k G) E] [Module (MonoidAlgebra k ↥(Subgroup.center G)) E] [inst6 : IsScalarTower (MonoidAlgebra k ↥(Subgroup.center G)) (MonoidAlgebra k G) E]:
((tensor k G W θ) →ₗ[MonoidAlgebra k G] E) ≃ₗ[MonoidAlgebra k (Subgroup.center G)] ((module_sub_rep k G W θ) →ₗ[MonoidAlgebra k (Subgroup.center G)] E) := by
  unfold tensor module_sub_rep
  exact ((iso_hom_tens (MonoidAlgebra k ↥(Subgroup.center G)) (θ.asModule) E (MonoidAlgebra k G)).trans (iso_hom_tens (MonoidAlgebra k ↥(Subgroup.center G)) θ.asModule E
            (MonoidAlgebra k ↥(Subgroup.center G))).symm)

end Induced_rep_center

namespace Frobenius_reciprocity

variable (k G W : Type) [inst1 : Field k] [inst2 : Group G] [inst3 : Finite G]
[inst4 : AddCommGroup W] [inst5 : Module k W] [inst6 : Module.Finite k W]

variable (H : @Subgroup G inst2) [instH : IsMulCommutative H]

variable (θ : Representation k (Subgroup.center G) W)

instance Finite_H : Finite H := Subgroup.instFiniteSubtypeMem H

noncomputable instance Fintype_G : Fintype G := by
  exact Fintype.ofFinite G

omit inst3 inst5 inst6 in
/--Definition of a class function : given G a group, a class function is a function $f : G → G$
which is contant over the conjugacy classes of $G$.-/
class conj_class_fun where
  Fun :  G → W
  conj_property : ∀ (x : G), ∀ (g : G), Fun (g⁻¹ * x * g) = Fun x


/--Definition of the induced class function of a function-/
noncomputable def Ind_conj_class_fun (f : H → W) : conj_class_fun G W := by
  refine { Fun := ?_, conj_property := ?_ }
  · intro x
    let S := {g : G | g⁻¹ * x * g ∈ H}
    let f' : S → W := fun g ↦ f ⟨g.1⁻¹ * x * g.1, g.2⟩
    exact (1 / Fintype.card H) • (∑ g, f' g)
  · intro x g
    simp only [Set.coe_setOf, Finset.univ_eq_attach]
    ring_nf
    let bij :  {g_1 | g_1⁻¹ * (g⁻¹ * x * g) * g_1 ∈ H} ≃ {g | g⁻¹ * x * g ∈ H} := by
      refine Equiv.mk ?_ ?_ ?_ ?_
      · exact (fun g1 => ⟨ g*g1, by simp only [Set.mem_setOf_eq, mul_inv_rev];simp only [Set.coe_setOf] at g1;let g2:= g1.2; group at g2; group;exact g2⟩)
      · exact (fun u => ⟨ g⁻¹*u, by simp only [Set.mem_setOf_eq, mul_inv_rev, inv_inv];simp only [Set.coe_setOf] at u;group;let h2:= u.2; group at h2;exact h2 ⟩)
      · intro u
        simp only [Set.coe_setOf, Set.mem_setOf_eq, inv_mul_cancel_left, Subtype.coe_eta]
      · intro u
        simp only [Set.coe_setOf, Set.mem_setOf_eq, mul_inv_cancel_left, Subtype.coe_eta]
    refine Mathlib.Tactic.LinearCombination.smul_const_eq ?_ ((1 / Fintype.card ↥H))
    dsimp
    refine Finset.sum_equiv ?_ ?_ ?_
    · exact bij
    · intro i
      simp
    · intro a ha
      unfold bij
      dsimp
      group


/--The character of a representation seen as a `conj_class_fun`.-/
noncomputable instance character_as_conj_class_fun (U : FDRep k G) : conj_class_fun G k := by
  refine { Fun := ?_, conj_property := ?_ }
  · exact U.character
  · intro x g
    rw[FDRep.char_mul_comm,mul_inv_cancel_left]

omit inst3 in
@[simp]
theorem character_as_conj_class_fun_is_character (U : FDRep k G) : (character_as_conj_class_fun k G U).Fun = U.character := by rfl


#check @character_as_conj_class_fun k (Subgroup.center G) _ _ (FDRep.of θ)
#check (Induced_rep_center.as_rep k G W θ)

#check @FDRep.of k G _ _ (RestrictScalars k (MonoidAlgebra k G) (Induced_rep_center.tensor k G W θ)) (sorry) (sorry) (sorry) _

noncomputable instance tensor_addcommgroup_restrictscalars : AddCommGroup (RestrictScalars k (MonoidAlgebra k G) (Induced_rep_center.tensor k G W θ)) := by
  unfold Induced_rep_center.tensor
  exact
    instAddCommGroupRestrictScalars k (MonoidAlgebra k G)
      (TensorProduct (MonoidAlgebra k ↥(Subgroup.center G)) (MonoidAlgebra k G) θ.asModule)

noncomputable instance tensor_module_restrictscalars : Module k (RestrictScalars k (MonoidAlgebra k G) (Induced_rep_center.tensor k G W θ)) := by
  unfold Induced_rep_center.tensor
  exact
    RestrictScalars.module k (MonoidAlgebra k G)
      (TensorProduct (MonoidAlgebra k ↥(Subgroup.center G)) (MonoidAlgebra k G) θ.asModule)

noncomputable instance tensor_module_restrictscalars_isfinite : Module.Finite k (RestrictScalars k (MonoidAlgebra k G) (Induced_rep_center.tensor k G W θ)) := by
  unfold Induced_rep_center.tensor

  sorry

/--`tensor` is a semisimple module.-/
noncomputable instance tensor_semisimple [h : NeZero ↑(Fintype.card G : k)] : IsSemisimpleModule (MonoidAlgebra k G) (Induced_rep_center.tensor k G W θ) := by
  unfold Induced_rep_center.tensor
  exact @MonoidAlgebra.Submodule.complementedLattice k _ G _ (h) _ (TensorProduct (MonoidAlgebra k ↥(Subgroup.center G)) (MonoidAlgebra k G) θ.asModule)
    _ _



#check FDRep.of θ
#check @character_as_conj_class_fun k (Subgroup.center G) _ _ (FDRep.of θ)
#check @Ind_conj_class_fun G k _ _ _ (Subgroup.center G) (@character_as_conj_class_fun k (Subgroup.center G) _ _ (FDRep.of θ)).1

open DirectSum

#check G⧸ H

/-- The fact that `S : Set G` is empty or not is a decidable property.-/
noncomputable instance decidable_empty (S : Set G) : Decidable S.Nonempty := by
  exact Classical.propDecidable S.Nonempty

/--The set of representatives of the classes of `G⧸ (Subgroup.center G)`.-/
abbrev system_of_repr_center_set : Set G := by
  exact Set.range (@Quotient.out G (QuotientGroup.con (Subgroup.center G)).toSetoid )

/--`system_of_rep_center_set` is finite.-/
instance system_of_repr_center_set_is_finite : Finite (system_of_repr_center_set G) := by
  exact Finite.Set.finite_range Quot.out

/--`system_of_rep_center_set` is a system of representatives for the classes, ie `g≠g'` implies
classes are different-/
theorem system_of_repr_center_set_disjoint (g g' : G) (hG : g ∈ (system_of_repr_center_set G)) (hG': g' ∈ system_of_repr_center_set G) :
  (g ≠ g') → {x | (QuotientGroup.con (Subgroup.center G)).toSetoid x g} ∩ {x | (QuotientGroup.con (Subgroup.center G)).toSetoid x g'} = ∅ := by
  contrapose!
  unfold QuotientGroup.con QuotientGroup.leftRel MulAction.orbitRel
  simp
  intro h
  rw[Set.Nonempty] at h
  obtain ⟨x, hg,hg'⟩ := h
  rw[MulAction.mem_orbit_iff] at hg hg'
  obtain ⟨hg,hhg⟩ := hg
  obtain ⟨hg',hhg'⟩ := hg'
  have h1 : hg • g = hg' • g' := by
    rw[hhg,<-hhg']
  have h2 : g ∈ MulAction.orbit ((↥(Subgroup.center G).op)) g' := by
    rw [@MulAction.mem_orbit_iff]
    use (hg⁻¹ * hg')
    rw [@mul_smul,<-h1]
    simp only [inv_smul_smul]
  have := MulAction.orbit_eq_iff.mpr h2
  simp at hG hG'
  sorry

omit inst3 in
theorem system_of_repr_center_set_union : Set.univ = ⋃ (g ∈ system_of_repr_center_set G), {x | (QuotientGroup.con (Subgroup.center G)).toSetoid x g} := by
  simp only [Set.mem_range, Con.rel_eq_coe, Set.iUnion_exists, Set.iUnion_iUnion_eq']
  unfold QuotientGroup.con QuotientGroup.leftRel
  simp
  refine Set.ext ?_
  intro x
  constructor
  · intro hx
    simp
    use Quotient.mk ((QuotientGroup.con (Subgroup.center G)).toSetoid) x
    exact id (Setoid.symm' (QuotientGroup.con (Subgroup.center G)).toSetoid
      (@Quotient.mk_out _ ((QuotientGroup.con (Subgroup.center G)).toSetoid) x))
  · intro hx
    simp only [Set.mem_univ]

open Classical
noncomputable def system_of_repr_center_set_bij : system_of_repr_center_set G ≃ Finset.image (Quotient.mk (QuotientGroup.con (Subgroup.center G)).toSetoid) Finset.univ := by
  unfold system_of_repr_center_set
  simp
  refine Equiv.mk ?_ ?_ ?_ ?_
  · intro x
    obtain ⟨x1,hx1⟩ := x
    simp at hx1
    refine ⟨hx1.choose,?_⟩
    use Quotient.out hx1.choose
    simp only [Quotient.out_eq]
  · intro x
    obtain ⟨x,hx⟩ := x
    refine ⟨x.out,?_⟩
    rw [Set.mem_range]
    use x
  · intro u
    obtain ⟨u,hu⟩ := u
    simp at hu
    simp only [Subtype.mk.injEq]
    conv=> rhs; rw[<-hu.choose_spec]
  · intro u
    obtain ⟨u,hu⟩ := u
    simp only [Quotient.out_inj, choose_eq]


noncomputable instance hmul_g_kH_kG : HMul G (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k G) := by
  refine { hMul := ?_ }
  intro g kH
  exact (MonoidAlgebra.of k G g) * kH

noncomputable instance hmul_g_kG : HMul G (MonoidAlgebra k G) (MonoidAlgebra k G) := by
  refine { hMul := ?_ }
  intro g kH
  exact (MonoidAlgebra.of k G g) * kH

omit inst3 in
theorem hmul_g_kH_kG_simp (g : G) (kH : MonoidAlgebra k (Subgroup.center G)) : (hmul_g_kH_kG k G).hMul g kH = (MonoidAlgebra.single g (1 : k)) * kH := by
  exact rfl

@[simp]
noncomputable instance hmul_g_kH_kG_distrib (g : G) (x y : MonoidAlgebra k (Subgroup.center G)) : g * (x + y) = g*x + g*y := by
  unfold HMul.hMul hmul_g_kH_kG
  simp
  exact
    LeftDistribClass.left_distrib (MonoidAlgebra.single g 1)
      ((kG_kH_Module.Map_KHKG k G (Subgroup.center G)) x)
      ((kG_kH_Module.Map_KHKG k G (Subgroup.center G)) y)


noncomputable def gkh_map (g : G) : MonoidAlgebra k (Subgroup.center G) →ₗ[k] MonoidAlgebra k G := by
 exact @Finsupp.lmapDomain (Subgroup.center G) k k _ _ _ G (fun x => g*x)


omit inst3 in
@[simp]
theorem gkh_map_eq (g : G) (x : MonoidAlgebra k (Subgroup.center G)) : gkh_map k G g x = g * x := by
  unfold gkh_map
  rw[Finsupp.lmapDomain]
  conv => lhs; change (Finsupp.mapDomain (fun (a : Subgroup.center G) => g*a) x)
  rw[Finsupp.mapDomain]
  rw[Finsupp.sum]
  have : ∀ (i : G),∀ (u : MonoidAlgebra k (Subgroup.center G)),∀ (h : Subgroup.center G), MonoidAlgebra.single (i * ↑h) (u h) = MonoidAlgebra.single i (1:k) * MonoidAlgebra.single h (u h) := by
    intro i h u
    simp only [kG_kH_Module.Map_KhKG_single_apply, MonoidAlgebra.single_mul_single, one_mul]
  unfold MonoidAlgebra.single at this
  unfold hmul_g_kH_kG
  simp
  specialize this g x
  conv=> lhs; rhs; intro a; rw[this a]
  rw[<-(Finset.mul_sum (x.support) (fun a => (kG_kH_Module.Map_KHKG k G (Subgroup.center G)) (Finsupp.single a (x a))) (Finsupp.single g 1))]
  simp
  congr


noncomputable instance gkH_map_Injective (g:G) : Function.Injective (gkh_map k G g) := by
  refine Finsupp.mapDomain_injective ?_
  intro x y
  simp only [mul_right_inj, SetLike.coe_eq_coe, imp_self]


/--The set `g*MonoidAlgebra k (Subgroup.center G)` for `g` in `G`.-/
noncomputable def gkH_set (g : G) : Submodule k (MonoidAlgebra k G) := by
  exact LinearMap.range (gkh_map k G g)

omit inst3 in
@[simp]
theorem gkh_map_gkh_set (x : gkH_set k G g) : gkh_map k G g (x.2.choose) = x := by
  simp
  have := x.2.choose_spec
  simp at this
  exact this

/--We have a `k` linear equivalence between `MonoidAlgebra k (Subgroup.center G)` and `gkH_set k G g`
given by the map $x↦ g^{-1}x$.-/
noncomputable def gkH_set_iso_kH_k (g : G) : gkH_set k G g ≃ₗ[k] (MonoidAlgebra k (Subgroup.center G)) := by
  symm
  refine Equiv.toLinearEquiv ?_ ?_
  · refine Equiv.ofBijective ?_ ?_
    · unfold gkH_set gkh_map
      simp
      let h1 := @Finsupp.lmapDomain (Subgroup.center G) k k _ _ _ G (fun x => g*x)
      change ((MonoidAlgebra k (Subgroup.center G)) →ₗ[k] (MonoidAlgebra k G)) at h1
      intro x
      refine ⟨h1 x, ?_⟩
      use x
    · constructor
      · simp
        intro x y
        simp
        conv => lhs; change (Finsupp.mapDomain fun x ↦ g * ↑x) x = (Finsupp.mapDomain fun x ↦ g * ↑x) y
        have := @Finsupp.mapDomain_injective (Subgroup.center G) G k _ (fun x ↦ g * ↑x)
          (by intro x y ; simp)
        exact fun a ↦ this a
      · intro x
        simp
        unfold gkH_set at x
        have : ∃ y, (gkh_map k G g) y = x := by
          refine Set.mem_range.mp ?_
          simp only [Subtype.coe_prop]
        use this.choose
        congr
        unfold gkh_map at this
        exact this.choose_spec
  · refine { map_add := ?_, map_smul := ?_ }
    · intro x y
      simp
      congr
    · intro c x
      simp
      congr


noncomputable instance gkH_set_SMul : SMul (MonoidAlgebra k ↥(Subgroup.center G)) ↥(gkH_set k G g) := by
  refine SMul.mk ?_
  intro x ⟨y,hy⟩
  refine ⟨kG_kH_Module.Map_KHKG k G (Subgroup.center G) x * y,?_⟩
  unfold gkH_set
  simp
  use x*hy.choose
  conv=> lhs;change (g * (kG_kH_Module.Map_KHKG k G (Subgroup.center G)) (x * Exists.choose hy))
  rw[map_mul]
  conv=> rhs;rw[<-hy.choose_spec]
  unfold hmul_g_kG
  simp
  conv=> lhs;rw[<-mul_assoc,<-kG_kH_Module.center_commutes_single k G,mul_assoc]
  conv => rhs;rhs;unfold HMul.hMul hmul_g_kH_kG;simp


noncomputable instance gkH_set_MulAction : MulAction (MonoidAlgebra k ↥(Subgroup.center G)) ↥(gkH_set k G g) := by
  refine MulAction.mk ?_ ?_
  · intro b
    obtain ⟨b,hb⟩ := b
    unfold gkH_set_SMul HSMul.hSMul instHSMul SMul.smul
    simp
  · intro x y ⟨b,hb⟩
    unfold HSMul.hSMul instHSMul SMul.smul gkH_set_SMul
    simp
    rw[mul_assoc]


noncomputable instance gkH_set_DistribMulAction : DistribMulAction (MonoidAlgebra k ↥(Subgroup.center G)) ↥(gkH_set k G g) := by
  refine DistribMulAction.mk ?_ ?_
  · intro a
    unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul gkH_set_MulAction gkH_set_SMul
    simp
  · intro a ⟨b,hb⟩ ⟨c,hc⟩
    unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul gkH_set_MulAction gkH_set_SMul
    simp
    unfold kG_kH_Module.Map_KHKG
    simp
    rw [@left_distrib]

noncomputable instance : Module (MonoidAlgebra k (Subgroup.center G)) (gkH_set k G g) := by
  refine Module.mk ?_ ?_
  · intro r s ⟨x,hx⟩
    unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul DistribMulAction.toMulAction
      gkH_set_DistribMulAction gkH_set_MulAction gkH_set_SMul
    simp
    exact
      RightDistribClass.right_distrib ((kG_kH_Module.Map_KHKG k G (Subgroup.center G)) r)
        ((kG_kH_Module.Map_KHKG k G (Subgroup.center G)) s) x
  · intro ⟨x,hx⟩
    unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul DistribMulAction.toMulAction
      gkH_set_DistribMulAction gkH_set_MulAction gkH_set_SMul
    simp

noncomputable def gkH_set_iso_kH_module (g : G) : gkH_set k G g ≃ₗ[(MonoidAlgebra k (Subgroup.center G))] (MonoidAlgebra k (Subgroup.center G)) := by
  refine (Equiv.toLinearEquiv ?_ ?_).symm
  · refine Equiv.ofBijective ?_ ?_
    · intro x
      refine ⟨g*x,?_⟩
      use x
      simp
    · constructor
      · intro x y
        simp
        rw[<-gkh_map_eq,<-gkh_map_eq]
        intro h
        exact gkH_map_Injective k G g h
      · intro ⟨x,hx⟩
        simp
        use hx.choose
        rw[<-gkh_map_eq]
        exact hx.choose_spec
  · refine { map_add := ?_, map_smul := ?_ }
    · intro x y
      simp
      exact rfl
    · intro c x
      simp
      conv=> rhs; unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul DistribMulAction.toMulAction
             unfold gkH_set_DistribMulAction gkH_set_MulAction gkH_set_SMul SMulZeroClass.toSMul DistribSMul.toSMulZeroClass
             unfold DistribMulAction.toDistribSMul Module.toDistribMulAction MulAction.toSMul DistribMulAction.toMulAction
             unfold instModuleMonoidAlgebraSubtypeMemSubgroupCenterSubmoduleGkH_set gkH_set_DistribMulAction gkH_set_MulAction
             unfold  gkH_set_SMul
      simp
      conv => lhs; change (MonoidAlgebra.single g (1:k) * kG_kH_Module.Map_KHKG k G (Subgroup.center G) (c*x))
      conv=> rhs; rhs; unfold hmul_g_kH_kG; simp
      rw[map_mul,<-mul_assoc,<-mul_assoc,<-kG_kH_Module.center_commutes_single]



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
  · simp only [DFinsupp.toFun_eq_coe, eq_mpr_eq_cast, cast_eq, add_apply]
    intro x y
    dsimp
    refine DirectSum.ext_iff.mpr ?_
    intro i
    simp only [DFinsupp.coe_mk', map_add, add_apply]

/--`DirectSum_equiv` as a k linear equivalence.-/
def DirectSum_equiv_linearmap (A : Type) [Semiring A] (ι : Type v) (β : ι → Type w) (γ : ι →  Type w) [(i : ι) → AddCommMonoid (β i)] [(i : ι) → AddCommMonoid (γ i)] [(i : ι) → Module A (β i)]
  [(i : ι) → Module A (γ i)] (h : ∀ (i : ι), β i ≃ₗ[A] γ i) : DirectSum ι β ≃ₗ[A] DirectSum ι γ := by
  refine Equiv.toLinearEquiv ((DirectSum_equiv ι β γ (fun i ↦ (h i).toAddEquiv)).toEquiv) ?_
  refine { map_add := ?_, map_smul := ?_ }
  · intro x y
    simp only [LinearEquiv.coe_toAddEquiv, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, map_add]
  · intro c x
    simp only [LinearEquiv.coe_toAddEquiv, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
    refine Eq.symm (ext γ ?_)
    intro j
    rw[DirectSum_equiv]
    simp only [DFinsupp.toFun_eq_coe, LinearEquiv.coe_addEquiv_apply, eq_mpr_eq_cast, cast_eq,
      AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, AddEquiv.coe_mk,
      Equiv.coe_fn_mk, DFinsupp.coe_mk']
    rw [@smul_apply]
    simp only [DFinsupp.coe_mk']
    rw [← @LinearEquiv.map_smul]
    congr

/--A function that associates to every element `g:G` the corresponding representative in `system_of_repr_center_set`. -/
noncomputable def G_to_syst: G → ↑(system_of_repr_center_set G) := by
      intro g
      unfold system_of_repr_center_set
      refine ⟨?_, ?_⟩
      · exact Quotient.out (Quotient.mk ((QuotientGroup.con (Subgroup.center G)).toSetoid) g)
      · simp only [Set.mem_range, Quotient.out_inj, exists_eq]

omit inst3 in
@[simp]
theorem G_to_syst_simp (g : G) (h : Subgroup.center G) : G_to_syst G (g * h) = G_to_syst G g := by
  unfold G_to_syst
  simp
  unfold QuotientGroup.con QuotientGroup.leftRel MulAction.orbitRel MulAction.orbit
  simp

/--A function that associates to every element `g:G` the corresponding `z : Subgroup.center G` sucht that
`Quotient.out ↑g = g * z`.-/
noncomputable def G_to_center : G → Subgroup.center G := by
      intro u
      exact ((QuotientGroup.mk_out_eq_mul (Subgroup.center G) u).choose)⁻¹


omit inst3 in
theorem G_to_center_simp (g : G) : g = Quotient.out ((Quotient.mk ((QuotientGroup.con (Subgroup.center G)).toSetoid) g)) * (G_to_center G g) := by
  change g = ⟦g⟧.out * ((QuotientGroup.mk_out_eq_mul (Subgroup.center G) g).choose)⁻¹
  simp
  rw [@eq_mul_inv_iff_mul_eq]
  have := @QuotientGroup.mk_out_eq_mul G _ (Subgroup.center G) g
  rw[<-this.choose_spec]
  congr

omit inst3 in
theorem G_to_center_to_syst_simp (g : G) : g = (G_to_syst G g) * (G_to_center G g) := by
  unfold G_to_syst
  simp
  exact G_to_center_simp G g

omit inst3 in
theorem G_to_center_to_syst_com (g : G) : (G_to_center G g) * (G_to_syst G g).1 = (G_to_syst G g) * (G_to_center G g) := by
  have := @Subgroup.mem_center_iff G _ (G_to_center G g)
  simp at this
  exact (this (G_to_syst G g)).symm

omit inst3 in
theorem G_to_center_syst_simp (g : G) : (G_to_center G g) = g * (G_to_syst G g).1⁻¹ := by
  conv=> rhs;lhs;rw[G_to_center_to_syst_simp G g]
  conv=> rhs;lhs; rw [<-G_to_center_to_syst_com G g]
  group

omit inst3 in
@[simp]
theorem G_to_center_syst_apply_simp (g : system_of_repr_center_set G): G_to_center G (g.1) = 1 := by
  unfold system_of_repr_center_set at g
  conv_lhs => change ((QuotientGroup.mk_out_eq_mul (Subgroup.center G) g).choose)⁻¹
  simp only [inv_eq_one]
  have : ∃ (y :  Quotient (QuotientGroup.con (Subgroup.center G)).toSetoid), y.out = g := by
    refine Set.mem_range.mp ?_
    exact Subtype.coe_prop g
  rw[<-this.choose_spec]
  simp only [Quotient.out_eq, left_eq_mul, OneMemClass.coe_eq_one, choose_eq]

omit inst3 in
@[simp]
theorem G_to_syst_simp_id (g : system_of_repr_center_set G) : G_to_syst G g = g := by
  have := G_to_center_to_syst_simp G g.1
  simp at this
  exact SetCoe.ext (id (Eq.symm this))

omit inst3 in
@[simp]
theorem G_to_center_mul_simp (g : G) (h : Subgroup.center G) : G_to_center G (g * h) = h * G_to_center G g := by
  have h1 := G_to_center_syst_simp G g
  have h2 := G_to_center_syst_simp G (g*h)
  conv at h2 => rhs; rhs; rhs; rhs; rw[G_to_syst_simp G g h]
  conv at h2 => rhs; lhs; rw[<-kG_kH_Module.center_mul_com]
  conv at h2 => rhs;rw[mul_assoc]; rhs; rw[<-h1]
  exact SetLike.coe_eq_coe.mp h2


omit inst3 in
noncomputable def system_of_repr_center_set_center_iso_G : G ≃  Subgroup.center G × system_of_repr_center_set G := by
  refine Equiv.mk (fun g => (G_to_center G g,G_to_syst G g)) (fun g => g.2*g.1.1) ?_ ?_
  · intro g
    simp
    exact Eq.symm (G_to_center_to_syst_simp G g)
  · intro g
    simp

noncomputable def system_of_repr_center_set_center_iso_G_sigma : (_ : ↥(Subgroup.center G)) × ↑(system_of_repr_center_set G) ≃ G := by
  refine (Equiv.mk ?_ ?_ ?_ ?_).symm
  · intro g
    refine Std.Internal.List.Prod.toSigma ?_
    exact system_of_repr_center_set_center_iso_G G g
  · intro g
    exact (system_of_repr_center_set_center_iso_G G).invFun (g.fst,g.snd)
  · intro g
    simp
    unfold system_of_repr_center_set_center_iso_G
    simp
    rw[Std.Internal.List.Prod.toSigma]
    simp
    exact Eq.symm (G_to_center_to_syst_simp G g)
  · intro g
    simp
    exact rfl

omit inst3 in
theorem system_of_repr_center_set_center_eq_G : @Set.univ G = { g.1 * h | (g : system_of_repr_center_set G) (h : Subgroup.center G)} := by
  refine Set.ext ?_
  intro x
  constructor
  · intro hx
    dsimp
    use (G_to_syst G x)
    use (G_to_center G x)
    exact (G_to_center_to_syst_simp G x).symm
  · simp


omit inst3 in
@[simp]
theorem Map_KHKG_single_simp (_ : Subgroup.center G) : (kG_kH_Module.Map_KHKG k G (Subgroup.center G)) (Finsupp.basisSingleOne x) = Finsupp.single (↑x) (1:k) := by
  simp

noncomputable def MonoidAlgebra_MulAction_basis : Basis (system_of_repr_center_set G) (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k G) := by
  refine Basis.mk (v := fun g => MonoidAlgebra.single g.1 (1:k)) ?_ ?_
  · rw [@linearIndependent_iff_injective_finsuppLinearCombination]
    rw[injective_iff_map_eq_zero]
    intro a ha
    simp at ha
    rw[Finsupp.linearCombination_apply,Finsupp.sum] at ha
    conv at ha => lhs;rhs;intro u; rw[<-Basis.sum_repr (@Finsupp.basisSingleOne k (Subgroup.center G) _) (a u)]
    conv at ha => lhs;rhs;intro u; rw[Finset.sum_smul]
    rw[Finset.sum_comm] at ha
    conv at ha => lhs;rhs;intro y; rhs; intro x1;simp only [Finsupp.basisSingleOne_repr,
      LinearEquiv.refl_apply, Finsupp.smul_single, smul_eq_mul, mul_one];
    conv at ha => lhs; rhs; intro u;rhs;intro uy; change ((kG_kH_Module.Map_KHKG k G (Subgroup.center G)) (((a uy) u) • Finsupp.basisSingleOne u) * MonoidAlgebra.single (↑uy.1) (1:k));
                  rw [kG_kH_Module.Map_KHKG_k_linear]; lhs;rhs;
    rw[MonoidAlgebra.ext_iff] at ha
    conv at ha => intro xx; lhs; rw[Finset.sum_apply']; rhs; intro k1; rw[Finset.sum_apply']; rhs;
                  intro k2;simp only [Algebra.smul_mul_assoc]; rw [Map_KHKG_single_simp k G k1];lhs;rhs;
                  lhs; change (MonoidAlgebra.single (k1) (1:k))
    conv at ha => intro xx; lhs; rhs; intro k1; rhs;intro k2; rw[MonoidAlgebra.single_mul_single]
    conv at ha => intro xx; lhs; rw[Finset.sum_sigma'];rhs;intro yy; lhs;rhs;simp
    let hh := Finsupp.linearIndependent_single_one k G
    conv at ha => intro xx; lhs; rw[<-Finset.sum_apply']
    rw[<-MonoidAlgebra.ext_iff] at ha
    change (LinearIndependent k fun (i : G) ↦ MonoidAlgebra.single i (1:k)) at hh
    rw [@linearIndependent_iff_injective_finsuppLinearCombination,injective_iff_map_eq_zero] at hh
    conv at hh => intro aa; lhs;lhs;rw[Finsupp.linearCombination_apply, Finsupp.sum]
    have hf : (@Finset.sum ((_ : ↥(Subgroup.center G)) × ↑(system_of_repr_center_set G)) (G →₀ k) Finsupp.instAddCommMonoid (Finset.univ.sigma fun k1 ↦ a.support) fun k_1 ↦ (a k_1.snd) k_1.fst • MonoidAlgebra.single (k_1.fst * k_1.snd.1) (1:k)) = ∑ (g : G) with  (G_to_syst G g) ∈ a.support, ((a (G_to_syst G g)) (G_to_center G g)) • MonoidAlgebra.single (g) (1:k) := by
      refine Finset.sum_equiv ?_ ?_ ?_
      · exact (system_of_repr_center_set_center_iso_G_sigma G)
      · intro i
        constructor
        · intro hi
          simp
          push_neg
          unfold system_of_repr_center_set_center_iso_G_sigma system_of_repr_center_set_center_iso_G
          simp
          simp at hi
          exact hi
        · intro hi
          simp
          simp at hi
          unfold system_of_repr_center_set_center_iso_G_sigma system_of_repr_center_set_center_iso_G at hi
          simp at hi
          exact hi
      · unfold system_of_repr_center_set_center_iso_G_sigma system_of_repr_center_set_center_iso_G
        simp
        intro i hi
        have : i.fst * i.snd.1 = i.snd.1 * i.fst := by
          have := @Subgroup.mem_center_iff G _ i.fst
          simp only [SetLike.coe_mem, true_iff] at this
          exact (this i.snd.1).symm
        simp [this]
    have hff : ∑ g with G_to_syst G g ∈ a.support, (a (G_to_syst G g)) (G_to_center G g) • MonoidAlgebra.single g (1:k) =0 := by
      rw[<-ha]
      exact hf.symm
    have hfff := ((@linearIndependent_iff' G k (MonoidAlgebra k G) (fun g => MonoidAlgebra.single g (1:k)) _ _ _ ).mp (Basis.linearIndependent (@Finsupp.basisSingleOne k G _))) ({g | G_to_syst G g ∈ a.support}) (fun (g : G) => (a (G_to_syst G g)) (G_to_center G g)) (hff)
    ext u v
    have hffff : ∀ (i : G), (fun g ↦ (a (G_to_syst G g)) (G_to_center G g)) i = 0 := by
      intro i
      by_cases hi : i ∈ {g | G_to_syst G g ∈ a.support}
      · specialize hfff i
        simp at hfff hi
        apply hfff at hi
        exact hi
      · simp at hi ⊢
        rw[hi]
        simp only [Finsupp.coe_zero, Pi.zero_apply]
    specialize hffff ((system_of_repr_center_set_center_iso_G G).invFun (v,u))
    unfold system_of_repr_center_set_center_iso_G at hffff
    simp at hffff ⊢
    exact hffff
  · intro x hx
    rw [@Submodule.mem_span_range_iff_exists_fun]
    let hh : ↑(system_of_repr_center_set G) → MonoidAlgebra k ↥(Subgroup.center G) := by
      intro g
      exact ∑ (i : Subgroup.center G), MonoidAlgebra.single (i) (x (g*i))
    use hh
    unfold hh
    conv => lhs; rhs; intro x1; rw[Finset.sum_smul]
    rw[MonoidAlgebra.ext_iff]
    intro a
    conv => lhs; rw[Finset.sum_apply']; rhs; intro k1; rw[Finset.sum_apply']; rhs;intro k2;lhs;
            change (kG_kH_Module.Map_KHKG k G (Subgroup.center G)) (MonoidAlgebra.single k2 (x (↑k1 * ↑k2))) • MonoidAlgebra.single (k1.1) (1:k)
            lhs;rw[kG_kH_Module.Map_KhKG_single_apply k G (Subgroup.center G) k2]
    conv => lhs;rhs;intro k1;rhs;intro k2; simp; rw[MonoidAlgebra.single_apply]
    have : (∑ (k1 : system_of_repr_center_set G), ∑ (k2 : Subgroup.center G), if ↑k2 * ↑k1.1 = a then x (↑k1.1 * ↑k2) else 0) = ∑ (g : G), if g = a then x a else 0 := by
      rw [Finset.sum_comm,Finset.sum_sigma']
      refine Finset.sum_equiv ?_ ?_ ?_
      · exact (system_of_repr_center_set_center_iso_G_sigma G)
      · intro i
        constructor
        · simp
        · simp
      · intro i
        simp
        unfold system_of_repr_center_set_center_iso_G_sigma system_of_repr_center_set_center_iso_G
        simp
        have : i.fst * i.snd.1 = i.snd.1 * i.fst := by
          have := @Subgroup.mem_center_iff G _ i.fst
          simp only [SetLike.coe_mem, true_iff] at this
          exact (this i.snd.1).symm
        simp[this]
        exact ite_congr rfl (congrArg ⇑x) (congrFun rfl)
    rw[this]
    simp

@[simp]
theorem MonoidAlgebra_single_basis_simp (x1 : system_of_repr_center_set G) : ((MonoidAlgebra_MulAction_basis k G).repr (MonoidAlgebra.single (↑x1) 1)) i = if i = x1 then 1 else 0 :=by
  conv => lhs;lhs;
  have : (((MonoidAlgebra_MulAction_basis k G).repr ((MonoidAlgebra_MulAction_basis k G) x1))) = ((MonoidAlgebra_MulAction_basis k G).repr (MonoidAlgebra.single (↑x1) 1)) := by
    rw [@EquivLike.apply_eq_iff_eq]
    unfold MonoidAlgebra_MulAction_basis
    simp
  rw[<-this]
  simp
  rw[Finsupp.single_apply]
  refine ite_congr ?_ (congrFun rfl) (congrFun rfl)
  conv=> lhs; rw[eq_comm]


/-- Description to add -/
noncomputable def G_to_direct_sum : ((system_of_repr_center_set G) → ⨁ (_ : ↑(system_of_repr_center_set G)), MonoidAlgebra k ↥(Subgroup.center G)) := by
    intro g
    exact @DirectSum.of ↑(system_of_repr_center_set G) (fun g => MonoidAlgebra k (Subgroup.center G)) _
      (by exact Classical.typeDecidableEq ↑(system_of_repr_center_set G)) (G_to_syst G g) ((MonoidAlgebra.single (1: Subgroup.center G) (1:k)))

noncomputable def MonoidAlgebra_direct_sum_linear1 : MonoidAlgebra k G →ₗ[MonoidAlgebra k (Subgroup.center G)] DirectSum (system_of_repr_center_set G) (fun _ => MonoidAlgebra k (Subgroup.center G)) := by
  have := @Basis.constr (DirectSum (system_of_repr_center_set G) (fun g => MonoidAlgebra k (Subgroup.center G))) _ (system_of_repr_center_set G) (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k G)
    _ _ _ (MonoidAlgebra_MulAction_basis k G) _ k _ _ _ ( G_to_direct_sum k G)
  exact this

theorem DirectSum_eq_sum_of (ι : Type*) [Fintype ι] (β : ι → Type w)  [(i : ι) → AddCommMonoid (β i)] [DecidableEq ι] (x : DirectSum ι β) :
  x= ∑ (i : ι), (DirectSum.of β i) (x i)  := by
  exact Eq.symm (sum_univ_of x)

@[simp]
theorem DirectSum_eq_sum_direct (ι : Type*) [hi : Fintype ι] (β : ι → Type w)  [(i : ι) → AddCommMonoid (β i)] [DecidableEq ι] (x : (i : ι) → β i) (j : ι) :
  (∑ (i : ι), (DirectSum.of β i) (x i)) j = x j  := by
  have := Finset.sum_apply (a := j) (g := fun i ↦ (DirectSum.of β i) (x i)) (s := Finset.univ)
  rw [DFinsupp.finset_sum_apply, Finset.sum_eq_single j]
  · simp only [of_eq_same]
  · intro a _ ha
    exact DirectSum.of_eq_of_ne _ _ _ ha
  · simp only [Finset.mem_univ, not_true_eq_false, of_eq_same, IsEmpty.forall_iff]


open DirectSum
/-- Map from `MonoidAlgebra k G` to the direct sum, induced by the values of `G_to_direct_sum` on the
natural basis given by elements of `G`.-/
noncomputable def MonoidAlgebra_direct_sum_1 : MonoidAlgebra k G ≃ₗ[MonoidAlgebra k (Subgroup.center G)] DirectSum (system_of_repr_center_set G) (fun _ => MonoidAlgebra k (Subgroup.center G)) := by
  refine Equiv.toLinearEquiv ?_ ?_
  · refine Equiv.mk ?_ ?_ ?_ ?_
    · exact (MonoidAlgebra_direct_sum_linear1 k G).toFun
    · intro u
      exact ∑ (g : system_of_repr_center_set G), (u g) • (MonoidAlgebra.single g.1 (1:k))
    · intro x
      simp
      apply Basis.ext_elem (MonoidAlgebra_MulAction_basis k G)
      intro i
      simp
      unfold MonoidAlgebra_direct_sum_linear1
      simp
      unfold G_to_direct_sum
      simp
      conv=> lhs;lhs;rhs;intro x1;rw[<-DirectSum.of_smul]
      conv=> lhs;lhs;rhs;intro x1;rhs; simp;rw[<-MonoidAlgebra.one_def,mul_one]
      simp
    · intro x
      simp
      rw[DirectSum.ext_iff]
      intro i
      unfold MonoidAlgebra_direct_sum_linear1
      simp
      unfold G_to_direct_sum
      simp
      conv=> lhs;lhs;rhs;intro x1;rw[<-DirectSum.of_smul]
      conv=> lhs;lhs;rhs;intro x1;rhs; simp;rw[<-MonoidAlgebra.one_def,mul_one]
      simp only [DirectSum.sum_univ_of]
  · simp
    unfold MonoidAlgebra_direct_sum_linear1
    simp
    exact LinearMap.isLinear (((MonoidAlgebra_MulAction_basis k G).constr k) (G_to_direct_sum k G))



/--Given a representative system `S` of `G` quotiented by its center, we have a k linear equivalence beetween
`MonoidAlgebra k G` and the direct sum of `g • (MonoidAlgebra k (Subgroup.center G))` for `g ∈ S`.-/
noncomputable def MonoidAlgebra_direct_sum_system_of_repr_center_set : MonoidAlgebra k G ≃ₗ[MonoidAlgebra k (Subgroup.center G)] DirectSum (system_of_repr_center_set G) (fun g => gkH_set k G g) := by
  have := DirectSum_equiv_linearmap (MonoidAlgebra k (Subgroup.center G)) (system_of_repr_center_set G) (fun g => gkH_set k G g) (fun g => MonoidAlgebra k (Subgroup.center G))
     (fun g => (gkH_set_iso_kH_module k G g))
  exact LinearEquiv.trans (MonoidAlgebra_direct_sum_1 k G) this.symm


set_option pp.proofs true in
/--Given the character of a representation `θ` of `Subgroup.center G` on `k`, the character
of the induced representation `tensor` on `G` is the `Ind_conj_class_fun` of the character of
`θ`.
-/
theorem Induced_character_is_character_induced_center [h : NeZero ↑(Fintype.card G : k)] : character_as_conj_class_fun k G (FDRep.of (Induced_rep_center.as_rep k G W θ)) =
@Ind_conj_class_fun G k _ _ _ (Subgroup.center G) (@character_as_conj_class_fun k (Subgroup.center G) _ _ (FDRep.of θ)).1  := by
  unfold Ind_conj_class_fun
  simp
  unfold character_as_conj_class_fun
  congr
  unfold Induced_rep_center.as_rep
  ext g
  have h1 := tensor_semisimple k G W θ
  have h2 := isSemisimpleModule_iff_exists_linearEquiv_dfinsupp.mp h1
  have h3 := @IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top _ _ _ _ _ h1
  obtain ⟨S, ⟨ϕ, h⟩⟩ := h2
  sorry


end Frobenius_reciprocity

#min_imports




--TensorProduct.leftModule TensorProduct.lift Algebra.ofModule

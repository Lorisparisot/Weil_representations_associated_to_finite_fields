import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Algebra.DirectSum.Ring



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
  exact MonoidAlgebra.mapDomainRingHom k (Subgroup.subtype H)

/--`MonoidAlgebra k G` is a `MonoidAlgebra k (Subgroup.center G)` algebra.-/
noncomputable instance KG_is_KcenterG_Algebra : Algebra (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k G) := by
  refine Algebra.mk (RingMorphism_KH_KG k G (Subgroup.center G)) ?_ ?_
  · intro pH pG
    ext x
    rw[RingMorphism_KH_KG,MonoidAlgebra.mapDomainRingHom_apply, ZeroHom.toFun_eq_coe,
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
    rw[HSMul.hSMul,instHSMul,RingMorphism_KH_KG,MonoidAlgebra.mapDomainRingHom_apply, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, Finsupp.mapDomain.addMonoidHom_apply]
    exact rfl

/--If we have a homomorphism `H →* Subgroup.center G`, then we have `Algebra (MonoidAlgebra k H) (MonoidAlgebra k G)`. -/
noncomputable instance KG_is_KH_Algebra (ϕ : H →* Subgroup.center G) : Algebra (MonoidAlgebra k H) (MonoidAlgebra k G):= by
  exact Algebra.compHom (MonoidAlgebra k G) (MonoidAlgebra.mapDomainRingHom k ϕ)

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
      simp only [MonoidAlgebra.mapDomainRingHom_apply, Subgroup.coe_subtype, ZeroHom.toFun_eq_coe,
        AddMonoidHom.toZeroHom_coe, Finsupp.mapDomain.addMonoidHom_apply]
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
  exact Set.range (@Quot.out G (QuotientGroup.con (Subgroup.center G)).toSetoid )

/--`system_of_rep_center_set` is finite.-/
instance system_of_repr_center_set_is_finite : Finite (system_of_repr_center_set G) := by
  exact Finite.Set.finite_range Quot.out

/--`system_of_rep_center_set` is a system of representatives for the classes, ie `g≠g'` implies
classes are different-/
theorem system_of_repr_center_set_disjoint (g g' : G) (hG : g ∈ (system_of_repr_center_set G)) (hG': g' ∈ system_of_repr_center_set G) :
  (g ≠ g') → {x | (QuotientGroup.con (Subgroup.center G)).toSetoid x g} ∩ {x | (QuotientGroup.con (Subgroup.center G)).toSetoid x g'} = ∅ := by
  contrapose
  push_neg
  unfold QuotientGroup.con QuotientGroup.leftRel MulAction.orbitRel
  simp
  intro h
  simp at hG hG' 
  obtain ⟨yg,hyg⟩ := hG 
  obtain ⟨yg',hyg'⟩ := hG' 
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
  have h3 : g' ∈ MulAction.orbit ((↥(Subgroup.center G).op)) g := by
    rw [@MulAction.mem_orbit_iff]
    use (hg'⁻¹ * hg)
    rw [@mul_smul,h1]
    simp only [inv_smul_smul]
  have : MulAction.orbit ((↥(Subgroup.center G).op)) g = MulAction.orbit ((↥(Subgroup.center G).op)) g' := by
    exact MulAction.orbit_eq_iff.mpr h2
  rw[@MulAction.mem_orbit_iff] at h2 h3
  obtain ⟨xg,hxg⟩ := h2
  obtain ⟨xg',hxg'⟩ := h3
  have hxg1 := hxg
  have hxg'2 := hxg'
  rw[<-hxg'] at hxg
  have h11:= h1
  rw[<-hxg1] at h1
  have h4 : hg • xg = hg' := by
    sorry
  rw[<-hxg'] at h11
  have h5 : hg = hg' • xg' := by
    sorry



  sorry

theorem system_of_repr_center_set_union : Set.univ = ⋃ (g ∈ system_of_repr_center_set G), {x | (QuotientGroup.con (Subgroup.center G)).toSetoid x g} := by
  simp only [Set.mem_range, Con.rel_eq_coe, Set.iUnion_exists, Set.iUnion_iUnion_eq']
  unfold QuotientGroup.con QuotientGroup.leftRel
  simp
  refine Set.ext ?_
  intro x
  constructor
  · intro hx
    simp
    
    sorry
  · intro hx
    simp only [Set.mem_univ]


noncomputable instance hmul_g_kH_kG : HMul G (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k G) := by
  refine { hMul := ?_ }
  intro g kH
  exact (MonoidAlgebra.single g (1 : k)) * kH

noncomputable instance hmul_g_kG : HMul G (MonoidAlgebra k G) (MonoidAlgebra k G) := by
  refine { hMul := ?_ }
  intro g kH
  exact (MonoidAlgebra.single g (1 : k)) * kH

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


/--The set `g*MonoidAlgebra k (Subgroup.center G)` for `g` in `G`.-/
def gkH_set (g : G) : Set (MonoidAlgebra k G) := by
  exact {g * kH | kH : MonoidAlgebra k (Subgroup.center G)}

noncomputable instance hmul_g_set_sub : HMul G ({ x // x ∈ gkH_set k G g }) (MonoidAlgebra k G) := by
  refine { hMul := ?_ }
  intro g kH
  exact (MonoidAlgebra.single g (1 : k)) * kH

noncomputable instance gkH_set_Add (g : G) : Add ↑(gkH_set k G g) := by
  refine Add.mk ?_
  intro x y
  refine ⟨x.1+y.1, ?_⟩
  unfold gkH_set at x y ⊢
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  simp
  use (hx.choose + hy.choose)
  conv => rhs; rw[<-hx.choose_spec, <-hy.choose_spec]
  simp only [hmul_g_kH_kG_distrib]


noncomputable instance gkH_set_AddSemiGroup (g : G) : AddSemigroup ↑(gkH_set k G g) := by
  refine AddSemigroup.mk ?_
  intro a b c
  unfold HAdd.hAdd instHAdd Add.add gkH_set_Add
  obtain ⟨a,ha⟩ := a
  obtain ⟨b,hb⟩ := b
  obtain ⟨c,hc⟩ := c
  simp only [Subtype.mk.injEq]
  exact add_assoc a b c

noncomputable instance gkH_set_Zero (g : G) : Zero ↑(gkH_set k G g) := by
  refine Zero.mk ?_
  refine ⟨ 0, ?_⟩
  use 0
  unfold HMul.hMul hmul_g_kH_kG
  simp only [map_zero, mul_zero]


noncomputable instance gkH_set_AddZeroClass (g : G) : AddZeroClass ↑(gkH_set k G g) := by
  refine AddZeroClass.mk ?_ ?_
  · intro a
    obtain ⟨a,ha⟩ := a
    unfold HAdd.hAdd instHAdd Add.add gkH_set_Add
    simp
    exact rfl
  · intro a
    obtain ⟨a,ha⟩ := a
    unfold HAdd.hAdd instHAdd Add.add gkH_set_Add
    simp
    exact rfl

noncomputable instance gkH_set_AddMonoid (g : G) : AddMonoid ↑(gkH_set k G g):= by
  refine
    { toAddSemigroup := gkH_set_AddSemiGroup k G g, toZero := gkH_set_Zero k G g, zero_add := ?_,
      add_zero := ?_, nsmul := ?_, nsmul_zero := ?_, nsmul_succ := ?_ }
  · intro a
    simp only [zero_add]
  · intro a
    simp only [add_zero]
  · unfold gkH_set
    intro n x
    obtain ⟨x,hx⟩ := x
    refine ⟨nsmulRec n x,?_⟩
    simp only [Set.mem_setOf_eq]
    use nsmulRec n (hx.choose)
    conv => rhs; rw[<-hx.choose_spec]
    unfold HMul.hMul hmul_g_kH_kG
    simp only
    induction n with
    | zero => dsimp[nsmulRec]
              simp only [map_zero, mul_zero]
    | succ n a => dsimp[nsmulRec]
                  conv => lhs; rw[map_add]
                  conv => rhs; rw[<-a]
                  exact LeftDistribClass.left_distrib (MonoidAlgebra.single g 1) ((kG_kH_Module.Map_KHKG k G (Subgroup.center G))               (nsmulRec n (Exists.choose hx)))
                      ((kG_kH_Module.Map_KHKG k G (Subgroup.center G)) (Exists.choose hx))
  · intro x
    obtain ⟨x,hx⟩ := x
    congr
  · intro n x
    obtain ⟨x,hx⟩ := x
    congr

noncomputable instance gkH_set_AddCommMonoid (g : G) : AddCommMonoid ↑(gkH_set k G g) := by
  refine AddCommMonoid.mk ?_
  intro x y
  obtain ⟨x,hx⟩ := x
  obtain ⟨y,hy⟩ := y
  unfold HAdd.hAdd instHAdd Add.add AddSemigroup.toAdd AddMonoid.toAddSemigroup gkH_set_AddMonoid
     gkH_set_AddSemiGroup gkH_set_Add
  simp
  exact AddCommMagma.add_comm x y

noncomputable instance gkH_set_SMul (g : G) : SMul (MonoidAlgebra k ↥(Subgroup.center G)) ↑(gkH_set k G g) := by
  refine {smul := ?_}
  unfold gkH_set
  intro x y
  obtain ⟨y,hy⟩ := y
  simp at hy
  refine ⟨y*x,?_⟩
  use hy.choose*x
  conv => rhs; rw[<-hy.choose_spec]
          conv => lhs; unfold HMul.hMul hmul_g_kH_kG; simp
  conv => lhs; rw [hmul_g_kH_kG_simp]
  rw[map_mul]
  exact
    Eq.symm
      (mul_assoc (MonoidAlgebra.single g 1)
        ((kG_kH_Module.Map_KHKG k G (Subgroup.center G)) hy.choose)
        ((kG_kH_Module.Map_KHKG k G (Subgroup.center G)) x))

omit inst3 in
theorem mul_comm_mono_algebra [h : IsMulCommutative G ] (x y : MonoidAlgebra k G) : x*y=y*x := by
  exact Lean.Grind.CommRing.mul_comm x y

noncomputable instance gkH_set_MulAction_kH (g : G) : MulAction (MonoidAlgebra k ↥(Subgroup.center G)) ↑(gkH_set k G g) := by
  refine MulAction.mk ?_ ?_
  · intro b
    unfold HSMul.hSMul instHSMul SMul.smul gkH_set_SMul
    simp only [Set.coe_setOf, Set.mem_setOf_eq, id_eq, map_one, mul_one, Subtype.coe_eta]
  · intro x y b
    obtain ⟨b,hb⟩ := b
    unfold HSMul.hSMul instHSMul SMul.smul gkH_set_SMul
    simp only [Set.coe_setOf, Set.mem_setOf_eq, id_eq, map_mul, Subtype.mk.injEq]
    rw[mul_assoc,<-map_mul,<-map_mul,@mul_comm_mono_algebra k (Subgroup.center G)]

noncomputable instance gkH_set_DistribMulAction_kH (g : G): DistribMulAction (MonoidAlgebra k ↥(Subgroup.center G)) ↑(gkH_set k G g) := by
  refine DistribMulAction.mk ?_ ?_
  · intro a
    unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul gkH_set_MulAction_kH gkH_set_SMul
    simp only [Set.coe_setOf, Set.mem_setOf_eq, id_eq]
    congr
    conv => lhs
            unfold OfNat.ofNat Zero.toOfNat0 Zero.zero AddZeroClass.toZero AddMonoid.toAddZeroClass
              AddMonoid.toZero gkH_set_AddMonoid gkH_set_Zero
            simp only [zero_mul]
  · intro a x y
    obtain ⟨x,hx1,hx2⟩ := x
    obtain ⟨y,hy1,hy2⟩ := y
    unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul gkH_set_MulAction_kH gkH_set_SMul
    simp only [Set.coe_setOf, Set.mem_setOf_eq, id_eq] at hy1 hy2 hx1 hx2 ⊢
    congr
    conv => lhs; conv => lhs; unfold HAdd.hAdd instHAdd Add.add AddSemigroup.toAdd
                               AddMonoid.toAddSemigroup gkH_set_AddMonoid gkH_set_AddSemiGroup
                               gkH_set_Add;simp
    exact RightDistribClass.right_distrib x y (Finsupp.mapDomain Subtype.val a)

noncomputable instance gkH_set_Module_kH (g : G) : Module (MonoidAlgebra k ↥(Subgroup.center G)) ↑(gkH_set k G g) := by
  refine Module.mk ?_ ?_
  · intro r s x
    obtain ⟨x,hx⟩ := x
    unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul DistribMulAction.toMulAction gkH_set_DistribMulAction_kH
      gkH_set_MulAction_kH gkH_set_SMul
    simp only [Set.coe_setOf, Set.mem_setOf_eq, id_eq, map_add]
    conv => rhs; unfold HAdd.hAdd instHAdd Add.add AddCommMagma.toAdd AddCommSemigroup.toAddCommMagma
              AddSemigroup.toAdd AddCommSemigroup.toAddSemigroup AddCommMonoid.toAddCommSemigroup
              AddMonoid.toAddSemigroup AddCommMonoid.toAddMonoid gkH_set_AddCommMonoid gkH_set_AddMonoid
              gkH_set_AddSemiGroup gkH_set_Add
    congr
    rw [@left_distrib]
  · intro x
    obtain ⟨x,hx1,hx2⟩ := x
    unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul DistribMulAction.toMulAction gkH_set_DistribMulAction_kH
      gkH_set_MulAction_kH gkH_set_SMul
    simp only [Set.coe_setOf, Set.mem_setOf_eq, id_eq, map_zero, mul_zero]
    congr


noncomputable instance HMul_k_kG : HMul k (MonoidAlgebra k G) (MonoidAlgebra k G) := by
  refine HMul.mk ?_
  intro c x
  exact (MonoidAlgebra.single (1:G) c) * x

noncomputable instance HMul_kG_k : HMul (MonoidAlgebra k G) k (MonoidAlgebra k G) := by
  refine HMul.mk ?_
  intro x c
  exact x * (MonoidAlgebra.single (1:G) c)

omit inst3 in
@[simp]
theorem HMul_k_kG_com (x :MonoidAlgebra k G) (c : k): x*c = c*x := by
  unfold HMul_k_kG HMul_kG_k
  simp
  exact Eq.symm (MonoidAlgebra.single_one_comm c x)


noncomputable instance gkH_set_SMul_k (g : G) : SMul k ↑(gkH_set k G g) := by
  unfold gkH_set
  refine SMul.mk ?_
  intro c x
  obtain ⟨x,hx⟩:= x
  simp at hx
  refine ⟨?_,?_⟩
  · exact c*x
  · simp
    use (c * hx.choose)
    conv => rhs;rw[<-hx.choose_spec]
    unfold hmul_g_kH_kG HMul_k_kG
    simp
    rw[<-mul_assoc,<-mul_assoc]
    have : MonoidAlgebra.single g 1 * (kG_kH_Module.Map_KHKG k G (Subgroup.center G)) (MonoidAlgebra.single 1 c)
      = MonoidAlgebra.single 1 c * MonoidAlgebra.single g 1 := by
      unfold kG_kH_Module.Map_KHKG
      simp only [MonoidAlgebra.mapDomainRingHom_apply, Subgroup.coe_subtype, ZeroHom.toFun_eq_coe,
        AddMonoidHom.toZeroHom_coe, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single,
        OneMemClass.coe_one, MonoidAlgebra.single_mul_single, mul_one, one_mul]
    rw[this]


noncomputable instance gkH_set_MulAction_k (g : G) : MulAction k ↑(gkH_set k G g) := by
  refine MulAction.mk ?_ ?_
  · intro x
    obtain ⟨x,hx⟩ := x
    unfold HSMul.hSMul instHSMul SMul.smul gkH_set_SMul_k
    simp only [Set.coe_setOf, Set.mem_setOf_eq, id_eq, Subtype.mk.injEq]
    unfold HMul_k_kG
    simp only
    rw[<-MonoidAlgebra.one_def,one_mul]
  · intro c1 c2 x
    obtain ⟨x,hx⟩ := x
    unfold HSMul.hSMul instHSMul SMul.smul gkH_set_SMul_k
    simp
    unfold HMul_k_kG
    simp only
    rw[<-mul_assoc]
    congr
    rw[MonoidAlgebra.mul_def]
    simp only [mul_one, mul_zero, Finsupp.single_zero, Finsupp.sum_single_index, zero_mul]


noncomputable instance gkH_set_DistribMulAction_k (g : G): DistribMulAction k ↑(gkH_set k G g) := by
  refine DistribMulAction.mk ?_ ?_
  · intro a
    unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul gkH_set_MulAction_k gkH_set_SMul_k
    unfold HMul.hMul HMul_k_kG
    simp only [Set.coe_setOf, Set.mem_setOf_eq, id_eq]
    congr
    exact mul_eq_zero_of_right (MonoidAlgebra.single 1 a) rfl
  · intro c x y
    unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul gkH_set_MulAction_k gkH_set_SMul_k
    unfold HMul.hMul HMul_k_kG
    simp only [Set.coe_setOf, Set.mem_setOf_eq, id_eq]
    congr
    conv => lhs; unfold HAdd.hAdd instHAdd Add.add AddSemigroup.toAdd AddMonoid.toAddSemigroup gkH_set_AddMonoid
            unfold gkH_set_AddSemiGroup gkH_set_Add; simp
    rw [@left_distrib]

noncomputable instance gkH_set_Module_k : Module k ↑(gkH_set k G g) := by
  refine Module.mk ?_ ?_
  · intro r s x
    unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul DistribMulAction.toMulAction
      gkH_set_DistribMulAction_k gkH_set_MulAction_k gkH_set_SMul_k
    simp
    congr
    unfold HMul_k_kG
    obtain ⟨x,hx⟩ := x
    simp
    rw [@NonUnitalNonAssocRing.right_distrib]
  · intro x
    unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul gkH_set_DistribMulAction_k gkH_set_MulAction_k
    unfold gkH_set_SMul_k
    simp
    congr
    unfold HMul_k_kG
    simp


set_option pp.proofs true in
/--We have a `k` linear equivalence between `MonoidAlgebra k (Subgroup.center G)` and `gkH_set k G g`
given by the map $x↦ g^{-1}x$.-/
noncomputable def gkH_set_iso_kH (g : G) : gkH_set k G g ≃ₗ[k] (MonoidAlgebra k (Subgroup.center G)) := by
  symm
  refine Equiv.toLinearEquiv ?_ ?_
  · refine Equiv.ofBijective ?_ ?_
    · unfold gkH_set
      let h1 := @Finsupp.lmapDomain (Subgroup.center G) k k _ _ _ G (fun x => g*x)
      change ((MonoidAlgebra k (Subgroup.center G)) →ₗ[k] (MonoidAlgebra k G)) at h1
      intro x
      refine ⟨?_, ?_⟩
      · exact h1 x
      · simp
        use x
        unfold h1
        conv=> lhs; unfold HMul.hMul hmul_g_kH_kG; simp
        unfold kG_kH_Module.Map_KHKG
        simp
        rw[MonoidAlgebra.single]
        simp only [MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain, Finsupp.sum, Finsupp.single_eq_set_indicator]
        rw [@Finset.mul_sum]
        congr
        simp
    · constructor
      · intro x y
        simp
        have h1 : Function.Injective (fun (x : Subgroup.center G) ↦ g * ↑x) := by
          intro x y
          simp only [mul_right_inj, SetLike.coe_eq_coe, imp_self]
        have := @Finsupp.mapDomain_injective (Subgroup.center G) G k _ (fun x => g*x) h1
        rw[Function.Injective] at this
        exact fun a ↦ this a
      · intro x
        obtain ⟨x,hx⟩ := x
        simp
        use hx.choose
        conv => rhs;rw[<-hx.choose_spec]
        rw [hmul_g_kH_kG_simp]
        unfold kG_kH_Module.Map_KHKG
        simp
        rw[MonoidAlgebra.single]
        simp only [MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain, Finsupp.sum, Finsupp.single_eq_set_indicator]
        rw [@Finset.mul_sum]
        simp
        congr
  · refine { map_add := ?_, map_smul := ?_ }
    · intro x y
      simp
      congr
    · intro c x
      simp
      congr
      rw[HMul_k_kG]
      simp
      ext x_1 : 1
      simp_all only [MonoidAlgebra.single_mul_apply, inv_one, one_mul]
      rfl



set_option pp.proofs true in
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
def DirectSum_equiv_linearmap (ι : Type v) (β : ι → Type w) (γ : ι →  Type w) [(i : ι) → AddCommMonoid (β i)] [(i : ι) → AddCommMonoid (γ i)] [(i : ι) → Module k (β i)]
  [(i : ι) → Module k (γ i)] (h : ∀ (i : ι), β i ≃ₗ[k] γ i) : DirectSum ι β ≃ₗ[k] DirectSum ι γ := by
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

noncomputable def MonoidAlgebra_direct_sum' : MonoidAlgebra k G ≃ₗ[k] DirectSum (system_of_repr_center_set G) (fun g => MonoidAlgebra k (Subgroup.center G)) := by
  refine Equiv.toLinearEquiv ?_ ?_
  · refine (Equiv.ofBijective ?_ ?_).symm
    · intro x  
      sorry
  sorry


/--Given a representative system `S` of `G` quotiented by its center, we have a k linear equivalence beetween
`MonoidAlgebra k G` and the direct sum of `g • (MonoidAlgebra k (Subgroup.center G))` for `g ∈ S`.-/
noncomputable def MonoidAlgebra_direct_sum : MonoidAlgebra k G ≃ₗ[k] DirectSum (system_of_repr_center_set G) (fun g => gkH_set k G g) := by
  have := DirectSum_equiv_linearmap k (system_of_repr_center_set G) (fun g => gkH_set k G g) (fun g => MonoidAlgebra k (Subgroup.center G))
     (fun g => gkH_set_iso_kH k G g)
  exact LinearEquiv.trans (MonoidAlgebra_direct_sum' k G) this.symm

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


/--Frobenius reciprocicty law-/
--theorem Frobenius_center (ψ : FDRep k G) :

end Frobenius_reciprocity

#min_imports




--TensorProduct.leftModule TensorProduct.lift Algebra.ofModule

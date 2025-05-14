import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RepresentationTheory.Character

/-!
# Addendum to the representation theory in mathlib

This file adds some properties about representation theory in mathlib.

## Main results
The goal of this file is to formalize the induced representation for finite group and
particular subgroup (commutative one) and the Frobenius reciprocity.

## Contents
+ Adds to `MonoidAlgebra`theory over a group, to create some particular tensor products.
+ `Induced_rep_center.definition` : the representation induced by the center of a group `G`.
+ Frobenius reciprocity in the case...

-/

namespace kG_kH_Module

variable (k G : Type*) [inst1 : Field k] [inst2 : Group G]
variable (H : @Subgroup G inst2) [instH : H.IsCommutative]


omit instH in
/--The trivial map from `MonoidAlgebra k H` to `MonoidAlgebra k G`, ie elements from
`MonoidAlgebra k H` are seen as `MonoidAlgebra k G`.-/
noncomputable def Map_KHKG : (MonoidAlgebra k H) →+* (MonoidAlgebra k G) := by
  have f : H →*G := by exact H.subtype
  have h1 := MonoidAlgebra.mapDomainRingHom k H.subtype
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

variable (H : @Subgroup G inst2) [instH : H.IsCommutative]

variable (θ : Representation k (Subgroup.center G) W)

/--Induced representation on `G` by a representation `Representation k (Subgroup.center G) W`
seen as a tensor product. -/
def tensor :=
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
        congr


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

variable (H : @Subgroup G inst2) [instH : H.IsCommutative]

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

--set_option pp.proofs true in
/--Definition of the induced of a class function-/
noncomputable def Ind_conj_class_fun (f : conj_class_fun H W) : conj_class_fun G W := by
  refine { Fun := ?_, conj_property := ?_ }
  · intro x
    let S := {g : G | g⁻¹ * x * g ∈ H}.toFinset
    let f' : S → W := fun g ↦ f.1 ⟨g.1⁻¹ * x * g.1, by cases g with
    | mk val property => simp only; rw [@Set.mem_toFinset] at property; exact property ⟩
    let h1 := (1 / Fintype.card H) • (∑ g, f' g)
    exact h1
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
    · simp only [Set.mem_toFinset, Set.mem_setOf_eq]
      exact bij
    · simp only [Finset.mem_attach, eq_mpr_eq_cast, implies_true]
    · intro a ha
      simp
      group
      dsimp

      sorry


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
  sorry

#check FDRep.of θ
#check @character_as_conj_class_fun k (Subgroup.center G) _ _ (FDRep.of θ)
#check @Ind_conj_class_fun G k _ _ _ (Subgroup.center G) (@character_as_conj_class_fun k (Subgroup.center G) _ _ (FDRep.of θ))
set_option pp.proofs true in
/--Given the character of a representation `θ` of `Subgroup.center G` on `k`, the character
of the induced representation `tensor` on `G` is the `Ind_conj_class_fun` of the character of
`θ`.
-/
theorem Induced_character_is_character_induced_center : character_as_conj_class_fun k G (FDRep.of (Induced_rep_center.as_rep k G W θ)) =
@Ind_conj_class_fun G k _ _ _ (Subgroup.center G) (@character_as_conj_class_fun k (Subgroup.center G) _ _ (FDRep.of θ))  := by
  unfold Ind_conj_class_fun
  simp
  unfold character_as_conj_class_fun
  congr
  unfold Induced_rep_center.as_rep
  ext g
  unfold Induced_rep_center.tensor

  sorry

end Frobenius_reciprocity

#min_imports




--TensorProduct.leftModule TensorProduct.lift Algebra.ofModule

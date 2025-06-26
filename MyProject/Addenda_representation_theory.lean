import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke
import MyProject.Addenda_monoid_algebra_theory
import Mathlib.RepresentationTheory.Induced

--import Hammer

/-!
# Addenda to the representation theory in mathlib

This file adds some properties about representation theory in mathlib.

## Main results
The goal of this file is to formalize the induced representation by the center of finite groups and
and the Frobenius reciprocity. We also aim to formalize the formula of the character of
this induced representation.

## Contents
+ `Induced_rep_center.tensor` : the induced representation by `Subgroup.center G` as a tensor
  product.
+ `Induced_rep_center.iso_induced_as_tensor` : given `E` a `MonoidAlgebra k G` module, the natural isomorphism between `MonoidAlgebra k G`-linear map from the induced representation `tensor`
 to `E`and `MonoidAlgebra k (Subgroup.center G)`-linear map from our `θ.asModule` seen as tensor product over `MonoidAlgebra k (Subgroup;center G))`
 to `E` : $Hom_{k[G]}(k[G]⊗_{k[Z(G)]}θ, E) ≃ Hom_{k[H]}(θ,E)$.
+ `Frobenius_reciprocity.Induced_character_is_character_induced_center` : the induced character by
`Subgroup.center G` is equal to the character of the induced representation by `Subgroup.center G`.

-/


namespace Induced_rep_center

variable (k G W : Type) [inst1 : Field k] [inst2 : Group G] [inst3 : Finite G]
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
      · exact fun a ↦ Map_kHkG k G (Subgroup.center G) a
      · intro x1 y1
        simp only [map_add]
    · intro m x
      simp
      unfold Map_kHkG
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
        rw[MonoidAlgebra.one_def] at h
        simp[TensorProduct.tmul] at h
        have := @FreeAddMonoid.of_injective (MonoidAlgebra k G × θ.asModule) (MonoidAlgebra.single 1 1, x1) (MonoidAlgebra.single 1 1, x2)
        sorry
      · intro y
        unfold subsubsub at y
        obtain ⟨hy, hy1⟩ := y
        obtain ⟨ hy2,⟨hy31,hy32⟩⟩ := hy1
        use hy2
        simp at hy32
        simp only [LinearEquiv.invFun_eq_symm,id_eq]
        conv=> rhs;lhs;rw[<-hy32]



        sorry
  sorry



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
open Classical

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


abbrev induced_rep_tensor_direct_sum_component (g : system_of_repr_center.set G) := TensorProduct (MonoidAlgebra k (Subgroup.center G)) (gkH_set k G g) (θ.asModule)

noncomputable instance (g:system_of_repr_center.set G) : Module (MonoidAlgebra k (Subgroup.center G)) (induced_rep_tensor_direct_sum_component k G W θ g) := by
  exact TensorProduct.instModule


/--The induced representation `Induced_rep_center.tensor k G W θ` is isomorphic to a direct sum
of `induced_rep_tensor_direct_sum_component`.-/
noncomputable def induced_rep_tensor_iso_direct_sum : Induced_rep_center.tensor k G W θ ≃ₗ[MonoidAlgebra k (Subgroup.center G)] DirectSum (system_of_repr_center.set G) (fun g => induced_rep_tensor_direct_sum_component k G W θ g):= by
  unfold induced_rep_tensor_direct_sum_component Induced_rep_center.tensor
  let h4 := @TensorProduct.directSumLeft (MonoidAlgebra k (Subgroup.center G)) _ (system_of_repr_center.set G) _
    (fun g ↦ ↥(gkH_set k G ↑g)) θ.asModule _ _ _ _
  let h := TensorProduct.congr (MonoidAlgebra_direct_sum_system_of_repr_center_set k G) (LinearEquiv.refl (MonoidAlgebra k ↥(Subgroup.center G)) θ.asModule)
  refine (Equiv.toLinearEquiv ?_ ?_)
  · refine Equiv.mk (fun x => (h4 ∘ h) x) (fun x => (h.invFun ∘ h4.invFun ) x) ?_ ?_
    · intro x
      simp only [LinearEquiv.invFun_eq_symm, Function.comp_apply, LinearEquiv.symm_apply_apply]
    · intro x
      simp only [LinearEquiv.invFun_eq_symm, Function.comp_apply, LinearEquiv.apply_symm_apply]
  · refine { map_add := ?_, map_smul := ?_ }
    · intro x y
      simp only [Function.comp_apply, LinearEquiv.invFun_eq_symm, Equiv.coe_fn_mk, map_add]
    · intro c x
      simp only [Function.comp_apply, LinearEquiv.invFun_eq_symm, Equiv.coe_fn_mk, map_smul]


noncomputable instance induced_rep_tensor_direct_sum_component_coe (g : system_of_repr_center.set G) : CoeOut (induced_rep_tensor_direct_sum_component k G W θ g) (Induced_rep_center.tensor k G W θ) := by
  refine CoeOut.mk ?_
  unfold induced_rep_tensor_direct_sum_component Induced_rep_center.tensor
  intro x
  have h1 := LinearMap.comp (Algebra.linearMap (MonoidAlgebra k ↥(Subgroup.center G)) (MonoidAlgebra k G)) (gkH_set_iso_kH_module k G g).toLinearMap
  have := TensorProduct.map h1 (@LinearMap.id (MonoidAlgebra k (Subgroup.center G)) (θ.asModule) _ _ _ )
  exact (this) x

noncomputable instance test (g:system_of_repr_center.set G) : CoeOut (induced_rep_tensor_direct_sum_component k G W θ g) ((RestrictScalars k (MonoidAlgebra k G) (Induced_rep_center.tensor k G W θ))) := by
  refine { coe := ?_ }

  sorry

noncomputable def induced_rep_component_perm (g : G) (gbar : system_of_repr_center.set G)  : Set.image ((Induced_rep_center.as_rep k G W θ) g) (induced_rep_tensor_direct_sum_component k G W θ gbar) ≃ induced_rep_tensor_direct_sum_component k G W θ (equiv_perm G gbar) := by
  sorry




/--Given the character of a representation `θ` of `Subgroup.center G` on `k`, the character
of the induced representation `tensor` on `G` is the `Ind_conj_class_fun` of the character of
`θ`.
-/
theorem Induced_character_is_character_induced_center [h : NeZero ↑(Fintype.card G : k)] : character_as_conj_class_fun k G (FDRep.of (Induced_rep_center.as_rep k G W θ)) =
@Ind_conj_class_fun G k _ _ _ (Subgroup.center G) (@character_as_conj_class_fun k (Subgroup.center G) _ _ (FDRep.of θ)).1  := by
  sorry


end Frobenius_reciprocity


namespace representation_theory_general

variable (k G W : Type) [inst1 : Field k] [inst2 : Group G] [inst3 : Finite G]
[inst4 : AddCommGroup W] [inst5 : Module k W] [inst6 : Module.Finite k W]

variable (H : @Subgroup G inst2) [instH : IsMulCommutative H]

variable (θ : Representation k (Subgroup.center G) W)


def test1 (h :G) (h1 : h∈ Subgroup.center G) : Subgroup.center G :=by
  exact ⟨h, by exact⟩
  sorry

instance : Module.Finite k (Representation.IndV (Subgroup.center G).subtype θ) := by
  sorry


theorem test  (h h' : G) (h1 : h ∉ Subgroup.center G) (h2 : ⁅h, h'⁆ ∈ Subgroup.center G) (h3 : FDRep.character (FDRep.of θ) (⟨⁅h, h'⁆, by exact h2⟩ ) ≠ 1)  : (FDRep.character (FDRep.of (Representation.ind ((Subgroup.center G).subtype) θ))).support = Subgroup.center G := by
  rw [@Function.support_eq_iff]
  sorry

theorem testbis : (∀ (h : G), (h ∉ Subgroup.center G ) → ∃ (h' : G), (h1:(⁅h, h'⁆ ∈ Subgroup.center G)) → FDRep.character (FDRep.of θ) (⟨⁅h, h'⁆, by exact h1⟩ ) ≠ 1) → ( (FDRep.character (FDRep.of (Representation.ind ((Subgroup.center G).subtype) θ))).support = Subgroup.center G) := by
  sorry

theorem testbisbis (g : G) (h1 : ∃ g' : G, (⁅g, g'⁆ ∈ Subgroup.center G)) (h2 : FDRep.character (FDRep.of θ) (⟨⁅g, h1.choose⁆,by exact h1.choose_spec⟩) ≠ 1) : (FDRep.character (FDRep.of (Representation.ind ((Subgroup.center G).subtype) θ))).support = Subgroup.center G  := by
sorry

theorem testtest : ∀ (g : G), (∃ g' : G, (⁅g, g'⁆ ∈ Subgroup.center G) ∧ (FDRep.character (FDRep.of θ) (⟨⁅g, g'⁆,by simp⟩) ≠ 1)) → (FDRep.character (FDRep.of (Representation.ind ((Subgroup.center G).subtype) θ))).support = Subgroup.center G  := by
  sorry

end representation_theory_general



#min_imports

import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.LinearAlgebra.FreeProduct.Basic
import MyProject.Addenda_direct_sum
import MyProject.Addenda_group_theory

/-!
# Addenda to the monoid algebra theory in mathlib

This file adds some properties about monoid algebra theory in mathlib.

## Main results
The goal of this file is to add to the monoid algebra theory some preliminary results
to construct the character on the induced representation by the center of a finite group.
The main theorem proved here is the decomposition of `MonoidAlgebra k G` as a direct sum
of `g • MonoidAlgebra k (Subgroup.center G)` indexed by elements of a system of representatives
of `G⧸ (Subgroup.center G)` as defined in `system_of_repr_center_set`.

## Contents
+ Adds to `MonoidAlgebra`theory over a group, to create some particular tensor products.
+ `MonoidAlgebra_MulAction_basis` : a system of representatives `system_of_repr_center_set G` of `G⧸ (Subgroup.center G)`
defines a basis of `MonoidAlgebra k G` on `MonoidAlgebra k (Subgroup.center G)`.
+ `MonoidAlgebra_direct_sum_system_of_repr_center_set ` : given a representative system `system_of_repr_center_set G` of `G⧸ (Subgroup.center G)`,
we have a `MonoidAlgebra k (Subgroup.center G)` linear bijection between
`MonoidAlgebra k G` and the direct sum of `g • (MonoidAlgebra k (Subgroup.center G))` for `g : system_of_repr_center_set G`.
-/

open Classical DirectSum

variable (k G W : Type) [inst1 : Field k] [inst2 : Group G] [inst3 : Finite G]
[inst4 : AddCommGroup W] [inst5 : Module k W] [inst6 : Module.Finite k W]

variable (H : @Subgroup G inst2) [instH : IsMulCommutative H]

instance Finite_H : Finite H := Subgroup.instFiniteSubtypeMem H

noncomputable instance Fintype_G : Fintype G := by
  exact Fintype.ofFinite G


omit instH in
/--The trivial map from `MonoidAlgebra k H` to `MonoidAlgebra k G`, ie elements from
`MonoidAlgebra k H` are seen as `MonoidAlgebra k G`.-/
noncomputable def Map_kHkG : (MonoidAlgebra k H) →+* (MonoidAlgebra k G) := by
  exact  MonoidAlgebra.mapDomainRingHom k H.subtype

/--`Map_kHkG` is indeed an injective map.-/
instance Map_kHkG_inj : Function.Injective (Map_kHkG k G H) := by
  unfold Map_kHkG
  have h1 := @MonoidAlgebra.mapDomain_injective k H G _ (Subgroup.subtype H) (Subgroup.subtype_injective H )
  exact h1

omit instH inst3 in
@[simp]
theorem Map_kHkG_single_apply (h : H) (c :k) : (Map_kHkG k G H) (MonoidAlgebra.single h (c:k)) = MonoidAlgebra.single ↑h (c:k) := by
  unfold Map_kHkG
  simp only [MonoidAlgebra.mapDomainRingHom_apply, Subgroup.coe_subtype, ZeroHom.toFun_eq_coe,
    AddMonoidHom.toZeroHom_coe, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]

omit instH inst3 in
/--`Map_kHkG` is indeed a `k` linear map.-/
@[simp]
theorem Map_kHkG_k_linear (c : k) (x : MonoidAlgebra k H): (Map_kHkG k G H) (c • x) = c • ((Map_kHkG k G H) x) := by
    unfold Map_kHkG
    simp only [MonoidAlgebra.mapDomainRingHom_apply, Subgroup.coe_subtype, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, Finsupp.mapDomain.addMonoidHom_apply]
    rw[Finsupp.mapDomain_smul]


omit instH in
/--Coercion from `MonoidAlgebra k H` to `MonoidAlgebra k G` when `H` is a subgroup of `G`-/
noncomputable instance Coe_kH_kG : CoeOut (MonoidAlgebra k H) (MonoidAlgebra k G) := by
  refine { coe := Map_kHkG k G H }


omit instH in
/--Scalar multiplication between `MonoidAlgebra k H` and `MonoidAlgebra k G`, ie
classical mulitplication between an element of `MonoidAlgebra k H` seen as an element
of `MonoidAlgebra k G` and an element of `MonoidAlgebra k G`.-/
noncomputable instance Smul_kHkG : SMul (MonoidAlgebra k H) (MonoidAlgebra k G) := by
  refine SMul.mk (fun h g => (Map_kHkG k G H h)*g)


/--`MonoidAlgebra k G` is a `MonoidAlgebra k (Subgroup.center G)` algebra.-/
noncomputable instance kG_is_kCenter_Algebra : Algebra (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k G) := by
  refine Algebra.mk (Map_kHkG k G (Subgroup.center G)) ?_ ?_
  · intro pH pG
    ext x
    rw[Map_kHkG,MonoidAlgebra.mapDomainRingHom_apply, ZeroHom.toFun_eq_coe,
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
    rw[HSMul.hSMul,instHSMul,Map_kHkG,MonoidAlgebra.mapDomainRingHom_apply, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, Finsupp.mapDomain.addMonoidHom_apply]
    exact rfl

/--If we have a homomorphism `H →* Subgroup.center G`, then we have `Algebra (MonoidAlgebra k H) (MonoidAlgebra k G)`. -/
noncomputable instance kG_is_kH_Algebra (ϕ : H →* Subgroup.center G) : Algebra (MonoidAlgebra k H) (MonoidAlgebra k G):= by
  exact Algebra.compHom (MonoidAlgebra k G) (MonoidAlgebra.mapDomainRingHom k ϕ)


omit inst3 in
/--For every `g : G`, `x : MonoidAlgebra k (Subgroup.center G)` commutes with
`MonoidAlgebra.single g (1:k)`. -/
@[simp]
theorem center_commutes_single (x : MonoidAlgebra k (Subgroup.center G)) (g : G) : Map_kHkG k G (Subgroup.center G) x * MonoidAlgebra.single (g : G) (1:k) = MonoidAlgebra.single (g) (1:k) * x := by
  unfold MonoidAlgebra.single Map_kHkG
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

/--Coercion from `Set (MonoidAlgebra k H)` to `(Set (MonoidAlgebra k G))`.-/
noncomputable instance Set_Coe : CoeOut (Set (MonoidAlgebra k H)) (Set (MonoidAlgebra k G)) := by
  refine { coe := ?_ }
  intro x
  have h := (Map_kHkG k G H)
  let xG := {h a | a ∈ x}
  exact xG

/--`(MonoidAlgebra k (Subgroup.center G))` seen as a subset of `MonoidAlgebra k G`
is a `(MonoidAlgebra k (Subgroup.center G))` submodule of `(MonoidAlgebra k (Subgroup.center G))`.-/
noncomputable def center_sub_module : Submodule (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k G) := by
   refine Submodule.mk ?_ ?_
   · refine AddSubmonoid.mk ?_ ?_
     · refine AddSubsemigroup.mk ?_ ?_
       · exact {(Map_kHkG k G (Subgroup.center G)) a | a ∈ (@Set.univ (MonoidAlgebra k (Subgroup.center G)))}
       · intro a b ha hb
         simp
         simp at ha hb
         obtain ⟨ya, ha⟩ := ha
         obtain ⟨yb, hb⟩ := hb
         use ya+yb
         rw[<-ha,<-hb]
         exact RingHom.map_add (Map_kHkG k G (Subgroup.center G)) ya yb
     · simp only [Set.mem_univ, true_and, Set.mem_setOf_eq]
       use 0
       simp only [map_zero]
   · intro c x
     simp only [Set.mem_univ, true_and, Set.mem_setOf_eq, forall_exists_index]
     intro x1 hx1
     use c*x1
     simp only [map_mul]
     exact congrArg (HMul.hMul ((Map_kHkG k G (Subgroup.center G)) c)) hx1

/--We define the multiplication of an element `g : G` by `kH : MonoidAlgebra k (Subgroup.center G)`
by `MonoidAlgebra.single g (1:k) * kH`. -/
noncomputable instance hmul_g_kH_kG : HMul G (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k G) := by
  refine { hMul := ?_ }
  intro g kH
  exact (MonoidAlgebra.of k G g) * kH

/--We define the multiplication of an element `g: G` by `kG : MonoidAlgebra k G`
by `MonoidAlgebra.single g (1:k) * kG`. -/
noncomputable instance hmul_g_kG : HMul G (MonoidAlgebra k G) (MonoidAlgebra k G) := by
  refine { hMul := ?_ }
  intro g kH
  exact (MonoidAlgebra.of k G g) * kH

omit inst3 in
theorem hmul_g_kH_kG_simp (g : G) (kH : MonoidAlgebra k (Subgroup.center G)) : (hmul_g_kH_kG k G).hMul g kH = (MonoidAlgebra.single g (1 : k)) * kH := by
  exact rfl

/--The multiplication by an element `g : G` on elements of `MonoidAlgebra k (Subgroup.center G)`
is indeed distributive.-/
@[simp]
noncomputable instance hmul_g_kH_kG_distrib (g : G) (x y : MonoidAlgebra k (Subgroup.center G)) : g * (x + y) = g*x + g*y := by
  unfold HMul.hMul hmul_g_kH_kG
  simp
  exact
    LeftDistribClass.left_distrib (MonoidAlgebra.single g 1)
      ((Map_kHkG k G (Subgroup.center G)) x)
      ((Map_kHkG k G (Subgroup.center G)) y)

/-- Let `g : G`. We define a `k` linear map on `MonoidAlgebra k (Subgroup.center G)`
by `x ↦ g*x`-/
noncomputable def gkH_map (g : G) : MonoidAlgebra k (Subgroup.center G) →ₗ[k] MonoidAlgebra k G := by
 exact @Finsupp.lmapDomain (Subgroup.center G) k k _ _ _ G (fun x => g*x)

omit inst3 in
/--For every `x : MonoidAlgebra k (Subgroup.center G)`, we have `gkH_map k G g x = g * x`.-/
@[simp]
theorem gkH_map_eq (g : G) (x : MonoidAlgebra k (Subgroup.center G)) : gkH_map k G g x = g * x := by
  unfold gkH_map
  rw[Finsupp.lmapDomain]
  conv => lhs; change (Finsupp.mapDomain (fun (a : Subgroup.center G) => g*a) x)
  rw[Finsupp.mapDomain]
  rw[Finsupp.sum]
  have : ∀ (i : G),∀ (u : MonoidAlgebra k (Subgroup.center G)),∀ (h : Subgroup.center G), MonoidAlgebra.single (i * ↑h) (u h) = MonoidAlgebra.single i (1:k) * MonoidAlgebra.single h (u h) := by
    intro i h u
    simp only [Map_kHkG_single_apply, MonoidAlgebra.single_mul_single, one_mul]
  unfold MonoidAlgebra.single at this
  unfold hmul_g_kH_kG
  simp
  specialize this g x
  conv=> lhs; rhs; intro a; rw[this a]
  rw[<-(Finset.mul_sum (x.support) (fun a => (Map_kHkG k G (Subgroup.center G)) (Finsupp.single a (x a))) (Finsupp.single g 1))]
  simp
  congr

/--The map `gkH_map k G g` is injective.-/
noncomputable instance gkH_map_Injective (g:G) : Function.Injective (gkH_map k G g) := by
  refine Finsupp.mapDomain_injective ?_
  intro x y
  simp only [mul_right_inj, SetLike.coe_eq_coe, imp_self]


/--The set of the image of `gKh_map k G g`, or in an equivalent manner the set of elements
`g*MonoidAlgebra k (Subgroup.center G)` for `g` in `G`.-/
noncomputable def gkH_set (g : G) : Submodule k (MonoidAlgebra k G) := by
  exact LinearMap.range (gkH_map k G g)

omit inst3 in
/--`simp` lemma for `gkH_map`.-/
@[simp]
theorem gkH_map_gkh_set (x : gkH_set k G g) : gkH_map k G g (x.2.choose) = x := by
  simp
  have := x.2.choose_spec
  simp at this
  exact this

/--We have a `k` linear equivalence between `MonoidAlgebra k (Subgroup.center G)` and `gkH_set k G g`
given by the map `gkH_map`.-/
noncomputable def gkH_set_iso_kH_k (g : G) : gkH_set k G g ≃ₗ[k] (MonoidAlgebra k (Subgroup.center G)) := by
  symm
  refine Equiv.toLinearEquiv ?_ ?_
  · refine Equiv.ofBijective ?_ ?_
    · let h1 := @Finsupp.lmapDomain (Subgroup.center G) k k _ _ _ G (fun x => g*x)
      change ((MonoidAlgebra k (Subgroup.center G)) →ₗ[k] (MonoidAlgebra k G)) at h1
      intro x
      refine ⟨gkH_map k G g x, ?_⟩
      use x
    · constructor
      · simp
        intro x y
        simp
        conv => lhs; rw[<-gkH_map_eq,<-gkH_map_eq]
        intro h
        exact (gkH_map_Injective k G g) h
      · intro x
        simp
        unfold gkH_set at x
        have : ∃ y, (gkH_map k G g) y = x := by
          refine Set.mem_range.mp ?_
          simp only [Subtype.coe_prop]
        use this.choose
        congr
        have h1:= this.choose_spec
        rw[gkH_map_eq] at h1
        exact h1
  · refine { map_add := ?_, map_smul := ?_ }
    · intro x y
      simp only [gkH_map_eq, id_eq, Equiv.ofBijective_apply, hmul_g_kH_kG_distrib,
        AddMemClass.mk_add_mk]
    · intro c x
      simp only [gkH_map_eq, id_eq, Equiv.ofBijective_apply, SetLike.mk_smul_mk,
        Subtype.mk.injEq]
      unfold hmul_g_kH_kG
      simp only [MonoidAlgebra.of_apply, Map_kHkG_k_linear, Algebra.mul_smul_comm]


noncomputable instance gkH_set_SMul : SMul (MonoidAlgebra k ↥(Subgroup.center G)) ↥(gkH_set k G g) := by
  refine SMul.mk ?_
  intro x ⟨y,hy⟩
  refine ⟨Map_kHkG k G (Subgroup.center G) x * y,?_⟩
  unfold gkH_set
  simp
  use x*hy.choose
  conv=> lhs;change (g * (Map_kHkG k G (Subgroup.center G)) (x * Exists.choose hy))
  rw[map_mul]
  conv=> rhs;rw[<-hy.choose_spec]
  unfold hmul_g_kG
  simp
  conv=> lhs;rw[<-mul_assoc,<-center_commutes_single k G,mul_assoc]
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
    unfold Map_kHkG
    simp
    rw [@left_distrib]

/--`gkH_set k G g` is a `MonoidAlgebra k (Subgroup.center G)` module.-/
noncomputable instance : Module (MonoidAlgebra k (Subgroup.center G)) (gkH_set k G g) := by
  refine Module.mk ?_ ?_
  · intro r s ⟨x,hx⟩
    unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul DistribMulAction.toMulAction
      gkH_set_DistribMulAction gkH_set_MulAction gkH_set_SMul
    simp
    exact
      RightDistribClass.right_distrib ((Map_kHkG k G (Subgroup.center G)) r)
        ((Map_kHkG k G (Subgroup.center G)) s) x
  · intro ⟨x,hx⟩
    unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul DistribMulAction.toMulAction
      gkH_set_DistribMulAction gkH_set_MulAction gkH_set_SMul
    simp

/--We define a `MonoidAlgebra k (Subgroup.center G)` linear equivalence between `gkH_set k G g`
and `MonoidAlgebra k (Subgroup.center G)` by $x ↦ g ⬝ x$. -/
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
        rw[<-gkH_map_eq,<-gkH_map_eq]
        intro h
        exact gkH_map_Injective k G g h
      · intro ⟨x,hx⟩
        simp
        use hx.choose
        rw[<-gkH_map_eq]
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
      conv => lhs; unfold hmul_g_kH_kG; simp
      conv=> rhs; rhs; unfold hmul_g_kH_kG; simp
      rw[<-mul_assoc,<-mul_assoc,<-center_commutes_single]

omit inst3 in
/--Coercion on the natural basis of `MonoidAlgebra k G` when `g : Subgroup.center G`.-/
@[simp]
theorem Map_kHkG_single_simp (_ : Subgroup.center G) : (Map_kHkG k G (Subgroup.center G)) (Finsupp.basisSingleOne x) = Finsupp.single (↑x) (1:k) := by
  simp only [Finsupp.coe_basisSingleOne, Map_kHkG_single_apply]

/-- A system of representatives `system_of_repr_center_set G` of `G⧸ (Subgroup.center G)`
defines a basis of `MonoidAlgebra k G` on `MonoidAlgebra k (Subgroup.center G)`.-/
noncomputable def MonoidAlgebra_MulAction_basis : Basis (system_of_repr_center_set G) (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k G) := by
  refine Basis.mk (v := fun g => MonoidAlgebra.single g.1 (1:k)) ?_ ?_
  · rw [@linearIndependent_iff_injective_finsuppLinearCombination]
    rw[injective_iff_map_eq_zero]
    intro a ha
    rw[Finsupp.linearCombination_apply,Finsupp.sum] at ha
    conv at ha => lhs;rhs;intro u; rw[<-Basis.sum_repr (@Finsupp.basisSingleOne k (Subgroup.center G) _) (a u)]
    conv at ha => lhs;rhs;intro u; rw[Finset.sum_smul]
    rw[Finset.sum_comm] at ha
    conv at ha => lhs;rhs;intro y; rhs; intro x1;simp only [Finsupp.basisSingleOne_repr,
      LinearEquiv.refl_apply, Finsupp.smul_single, smul_eq_mul, mul_one];
    conv at ha => lhs; rhs; intro u;rhs;intro uy; change ((Map_kHkG k G (Subgroup.center G)) (((a uy) u) • Finsupp.basisSingleOne u) * MonoidAlgebra.single (↑uy.1) (1:k));
                  rw [Map_kHkG_k_linear]; lhs;rhs;
    rw[MonoidAlgebra.ext_iff] at ha
    conv at ha => intro xx; lhs; rw[Finset.sum_apply']; rhs; intro k1; rw[Finset.sum_apply']; rhs;
                  intro k2;simp only [Algebra.smul_mul_assoc]; rw [Map_kHkG_single_simp k G k1];lhs;rhs;
                  lhs; change (MonoidAlgebra.single (k1) (1:k))
    conv at ha => intro xx; lhs; rhs; intro k1; rhs;intro k2; rw[MonoidAlgebra.single_mul_single]
    conv at ha => intro xx; lhs; rw[Finset.sum_sigma'];rhs;intro yy; lhs;rhs;simp
    let hh := Finsupp.linearIndependent_single_one k G
    conv at ha => intro xx; lhs; rw[<-Finset.sum_apply']
    rw[<-MonoidAlgebra.ext_iff] at ha
    change (LinearIndependent k fun (i : G) ↦ MonoidAlgebra.single i (1:k)) at hh
    rw [@linearIndependent_iff_injective_finsuppLinearCombination,injective_iff_map_eq_zero] at hh
    conv at hh => intro aa; lhs;lhs;rw[Finsupp.linearCombination_apply, Finsupp.sum]
    have hf : (@Finset.sum ((_ : ↥(Subgroup.center G)) × ↑(system_of_repr_center_set G))
      (G →₀ k) Finsupp.instAddCommMonoid (Finset.univ.sigma fun k1 ↦ a.support)
      fun k_1 ↦ (a k_1.snd) k_1.fst • MonoidAlgebra.single (k_1.fst * k_1.snd.1) (1:k))
      = ∑ (g : G) with  (G_to_syst G g) ∈ a.support, ((a (G_to_syst G g)) (G_to_center G g))
       • MonoidAlgebra.single (g) (1:k) := by
      refine Finset.sum_equiv ?_ ?_ ?_
      · exact (system_of_repr_center_set_center_iso_G_sigma G)
      · intro i
        constructor
        · intro hi
          simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_filter, Finset.mem_univ,
            true_and]
          push_neg
          unfold system_of_repr_center_set_center_iso_G_sigma system_of_repr_center_set_center_iso_G
          simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, G_to_syst_simp, G_to_syst_simp_id,
            ne_eq]
          simp only [Finset.mem_sigma, Finset.mem_univ, Finsupp.mem_support_iff, ne_eq,
            true_and] at hi
          exact hi
        · intro hi
          simp only [Finset.mem_sigma, Finset.mem_univ, Finsupp.mem_support_iff, ne_eq,
            true_and]
          simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_filter, Finset.mem_univ,
            true_and] at hi
          unfold system_of_repr_center_set_center_iso_G_sigma system_of_repr_center_set_center_iso_G at hi
          simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, G_to_syst_simp, G_to_syst_simp_id] at hi
          exact hi
      · unfold system_of_repr_center_set_center_iso_G_sigma system_of_repr_center_set_center_iso_G
        simp only [Finset.mem_sigma, Finset.mem_univ, Finsupp.mem_support_iff, ne_eq, true_and,
          MonoidAlgebra.smul_single, smul_eq_mul, mul_one, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
          G_to_syst_simp, G_to_syst_simp_id, G_to_center_mul_simp, G_to_center_syst_apply_simp]
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
        simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq] at hfff hi
        apply hfff at hi
        exact hi
      · simp only [Finsupp.mem_support_iff, ne_eq, Set.mem_setOf_eq, Decidable.not_not] at hi ⊢
        rw[hi]
        simp only [Finsupp.coe_zero, Pi.zero_apply]
    specialize hffff ((system_of_repr_center_set_center_iso_G G).invFun (v,u))
    unfold system_of_repr_center_set_center_iso_G at hffff
    simp only [G_to_syst_simp, G_to_syst_simp_id, G_to_center_mul_simp, G_to_center_syst_apply_simp,
      mul_one, Finsupp.coe_zero, Pi.zero_apply] at hffff ⊢
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
            change (Map_kHkG k G (Subgroup.center G)) (MonoidAlgebra.single k2 (x (↑k1 * ↑k2))) • MonoidAlgebra.single (k1.1) (1:k)
            lhs;rw[Map_kHkG_single_apply k G (Subgroup.center G) k2]
    conv => lhs;rhs;intro k1;rhs;intro k2; simp only [smul_eq_mul, MonoidAlgebra.single_mul_single,
      mul_one]; rw[MonoidAlgebra.single_apply]
    have : (∑ (k1 : system_of_repr_center_set G), ∑ (k2 : Subgroup.center G), if ↑k2 * ↑k1.1 = a then x (↑k1.1 * ↑k2) else 0) = ∑ (g : G), if g = a then x a else 0 := by
      rw [Finset.sum_comm,Finset.sum_sigma']
      refine Finset.sum_equiv ?_ ?_ ?_
      · exact (system_of_repr_center_set_center_iso_G_sigma G)
      · intro i
        constructor
        · simp only [Finset.univ_sigma_univ, Finset.mem_univ, imp_self]
        · simp only [Finset.mem_univ, Finset.univ_sigma_univ, imp_self]
      · intro i
        simp only [Finset.univ_sigma_univ, Finset.mem_univ, forall_const]
        unfold system_of_repr_center_set_center_iso_G_sigma system_of_repr_center_set_center_iso_G
        simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
        have : i.fst * i.snd.1 = i.snd.1 * i.fst := by
          have := @Subgroup.mem_center_iff G _ i.fst
          simp only [SetLike.coe_mem, true_iff] at this
          exact (this i.snd.1).symm
        simp[this]
        exact ite_congr rfl (congrArg ⇑x) (congrFun rfl)
    rw[this]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/--Given a representative `x1 : system_of_repr_center G`, the coefficients of `x1` in
the basis `MonoidAlgebra_MulAction_basis` is 0 unless on the vector `x1`.-/
@[simp]
theorem MonoidAlgebra_single_basis_simp (x1 : system_of_repr_center_set G) : ((MonoidAlgebra_MulAction_basis k G).repr (MonoidAlgebra.single (↑x1) 1)) i = if i = x1 then 1 else 0 :=by
  conv => lhs;lhs;
  have : (((MonoidAlgebra_MulAction_basis k G).repr ((MonoidAlgebra_MulAction_basis k G) x1))) = ((MonoidAlgebra_MulAction_basis k G).repr (MonoidAlgebra.single (↑x1) 1)) := by
    rw [@EquivLike.apply_eq_iff_eq]
    unfold MonoidAlgebra_MulAction_basis
    simp only [Basis.coe_mk]
  rw[<-this]
  simp only [Basis.repr_self]
  rw[Finsupp.single_apply]
  refine ite_congr ?_ (congrFun rfl) (congrFun rfl)
  conv=> lhs; rw[eq_comm]


/--We define a map between `system_of_repr_center_set G` and `⨁ (_ : ↑(system_of_repr_center_set G)), MonoidAlgebra k ↥(Subgroup.center G))`
 given by `MonoidAlgebra.single 1 1` on the `g`-th component and 0 elsewhere.-/
noncomputable def G_to_direct_sum : ((system_of_repr_center_set G) → ⨁ (_ : ↑(system_of_repr_center_set G)), MonoidAlgebra k ↥(Subgroup.center G)) := by
    intro g
    exact @DirectSum.of ↑(system_of_repr_center_set G) (fun g => MonoidAlgebra k (Subgroup.center G)) _
      (by exact Classical.typeDecidableEq ↑(system_of_repr_center_set G)) (G_to_syst G g) ((MonoidAlgebra.single (1: Subgroup.center G) (1:k)))

/--We define a `MonoidAlgebra k (Subgroup.center G)` linear map by extending the map `G_to_direct_sum k G`
which is define on the basis `MonoidAlgebra_MulAction_basis k G`.-/
noncomputable def MonoidAlgebra_direct_sum_linear : MonoidAlgebra k G →ₗ[MonoidAlgebra k (Subgroup.center G)] DirectSum (system_of_repr_center_set G) (fun _ => MonoidAlgebra k (Subgroup.center G)) := by
  have := @Basis.constr (DirectSum (system_of_repr_center_set G) (fun g => MonoidAlgebra k (Subgroup.center G))) _ (system_of_repr_center_set G) (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k G)
    _ _ _ (MonoidAlgebra_MulAction_basis k G) _ k _ _ _ ( G_to_direct_sum k G)
  exact this

/-- The map `MonoidAlgebra_direct_sum_linear k G` is in fact a linear bijection.-/
noncomputable def MonoidAlgebra_direct_sum_1 : MonoidAlgebra k G ≃ₗ[MonoidAlgebra k (Subgroup.center G)] DirectSum (system_of_repr_center_set G) (fun _ => MonoidAlgebra k (Subgroup.center G)) := by
  refine Equiv.toLinearEquiv ?_ ?_
  · refine Equiv.mk ?_ ?_ ?_ ?_
    · exact (MonoidAlgebra_direct_sum_linear k G).toFun
    · intro u
      exact ∑ (g : system_of_repr_center_set G), (u g) • (MonoidAlgebra.single g.1 (1:k))
    · intro x
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      apply Basis.ext_elem (MonoidAlgebra_MulAction_basis k G)
      intro i
      simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply,
        Pi.smul_apply, MonoidAlgebra_single_basis_simp, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      unfold MonoidAlgebra_direct_sum_linear
      simp only [Basis.constr_apply_fintype, Basis.equivFun_apply]
      unfold G_to_direct_sum
      simp only [G_to_syst_simp_id]
      conv=> lhs;lhs;rhs;intro x1;rw[<-DirectSum.of_smul]
      conv=> lhs;lhs;rhs;intro x1;rhs; simp;rw[<-MonoidAlgebra.one_def,mul_one]
      simp only [DirectSum_eq_sum_direct]
    · intro x
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, map_sum, map_smul]
      rw[DirectSum.ext_iff]
      intro i
      unfold MonoidAlgebra_direct_sum_linear
      simp only [Basis.constr_apply_fintype, Basis.equivFun_apply, MonoidAlgebra_single_basis_simp,
        ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      unfold G_to_direct_sum
      simp only [G_to_syst_simp_id]
      conv=> lhs;lhs;rhs;intro x1;rw[<-DirectSum.of_smul]
      conv=> lhs;lhs;rhs;intro x1;rhs; simp;rw[<-MonoidAlgebra.one_def,mul_one]
      simp only [DirectSum.sum_univ_of]
  · simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Equiv.coe_fn_mk]
    unfold MonoidAlgebra_direct_sum_linear
    exact LinearMap.isLinear (((MonoidAlgebra_MulAction_basis k G).constr k) (G_to_direct_sum k G))


/--Given a representative system `system_of_repr_center_set G` of `G⧸ (Subgroup.center G)`,
we have a `MonoidAlgebra k (Subgroup.center G)` linear bijection between
`MonoidAlgebra k G` and the direct sum of `g • (MonoidAlgebra k (Subgroup.center G))` for `g : system_of_repr_center_set G`.-/
noncomputable def MonoidAlgebra_direct_sum_system_of_repr_center_set : MonoidAlgebra k G ≃ₗ[MonoidAlgebra k (Subgroup.center G)] DirectSum (system_of_repr_center_set G) (fun g => gkH_set k G g) := by
  have := DirectSum_equiv_linearmap (MonoidAlgebra k (Subgroup.center G)) (system_of_repr_center_set G) (fun g => gkH_set k G g) (fun g => MonoidAlgebra k (Subgroup.center G))
     (fun g => (gkH_set_iso_kH_module k G g))
  exact LinearEquiv.trans (MonoidAlgebra_direct_sum_1 k G) this.symm

#min_imports

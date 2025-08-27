import Mathlib.Algebra.Exact
import Mathlib.Algebra.Group.Commutator
import MyProject.convention_dual
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Init


/-!
# Heisenberg's groups over a vector space

This file defines Heisenberg's groups over a vector space and their basic properties.

## Mains results

Let `k`be a field, `V` a finite dimensional vector space over `k`, and `Module.Dual k V` its dual space.
We also take the convention that `V`is in bijection with `Module.Dual k (Module.Dual k V)` by
$(x,y)=-(y,x)$.
We define the group of Heisenberg, some subgroups, and basic properties of these groups.
The main results are :
+ `Heisenberg.two_step_nilpotent` : the Heisenberg group is a two-step nilpotent group.
+ `Heisenberg.anti_iso_Dual`: the Heisenberg group is anti-isomorphic to the Heisenberg group of its dual.
-/


variable (V k : Type*) [Field k] [AddCommGroup  V] [Module k V] --[inst4 : FiniteDimensional k V]

@[ext]
structure Heisenberg where
  z : k
  x : V
  y : Module.Dual k V


namespace Heisenberg


variable {V k}
/--Intern law over `Heisenberg` -/
instance : Mul (Heisenberg V k) where
  mul H1 H2 :=  ⟨H1.z + H2.z + (H1.y H2.x), H1.x + H2.x, H1.y + H2.y⟩

lemma mul_apply (H1 H2 : Heisenberg V k) : H1 * H2 = ⟨H1.z + H2.z + (H1.y H2.x), H1.x + H2.x, H1.y + H2.y⟩ := rfl

instance : One (Heisenberg V k) where
  one := ⟨0, 0, 0⟩

lemma one_eq : (1 : Heisenberg V k) = ⟨0,0,0⟩ := by
  rfl

lemma one_apply (H : Heisenberg V k) : H * 1 = H := by
  ext u
  <;> rw[one_eq,mul_apply]
  <;> simp only [add_zero, map_zero]

/--Inverse of an element of `Heisenberg` by `mul` -/
instance : Inv (Heisenberg V k) where
  inv H := ⟨ -H.z - (H.y (-H.x)), - H.x ,- H.y⟩

lemma inv_apply (H : Heisenberg V k) : H⁻¹ = ⟨ -H.z - (H.y (-H.x)), - H.x ,- H.y⟩ := rfl

/-- Together with `Heisenberg.mul` and `Heisenberg.inverse`, `Heisenberg` forms a group. -/
instance group : Group (Heisenberg V k) := {
  mul_assoc := by
    intro a b c
    ext u
    <;> simp only [mul_apply, LinearMap.add_apply,map_add]
    <;> grind only
  one_mul := by
    intro _
    rw[one_eq, mul_apply]
    simp only [zero_add, LinearMap.zero_apply, add_zero]
  mul_one := by
    intro _
    rw[one_eq,mul_apply]
    simp only [add_zero, map_zero]
  inv_mul_cancel := by
    intro G_eq_G_to_center_G_to_syst_simp
    rw[inv_apply,mul_apply,one_eq]
    simp only [map_neg, sub_neg_eq_add, neg_add_cancel_comm, LinearMap.neg_apply, add_neg_cancel,
      neg_add_cancel]
}


variable (V k)

/--`Heisenberg.center` is a subgroup of `Heisenberg` -/
instance center : Subgroup (Heisenberg V k) :=
{ carrier := {H : Heisenberg V k | H.x = 0 ∧ H.y = 0},
  one_mem' := by
    rw[one_eq]
    constructor
    <;> simp only,
  mul_mem' := by
    intro a b ha hb
    rw[mul_apply]
    simp[Set.mem_setOf_eq,ha.1,hb.1,ha.2,hb.2],
  inv_mem' := by
    intro a ha
    rw[inv_apply]
    simp[ha.1,ha.2]
}


/--The map $(z,x,y) ↦ (z,0,0)$ defines a homorphism from `Heisenberg` to its center `Heisenberg.center`. -/
def Hom_k_to_H : AddMonoidHom k (Additive (Heisenberg V k)) :=by
  refine AddMonoidHom.mk' (fun z => ⟨z,0,0⟩) ?_
  intro a b
  rw [@Additive.ext_iff,toMul_add,mul_apply]
  ext u
  <;>unfold Additive.toMul Additive.ofMul
  <;> simp only [Equiv.coe_fn_symm_mk, LinearMap.zero_apply, add_zero]


/-- The homomorphism `Heisenberg.Hom_k_to_H` is injective. -/
lemma injective_Hom_k_to_H : Function.Injective (Hom_k_to_H V k) := by
  intro k1 k2
  rw[Hom_k_to_H,AddMonoidHom.mk'_apply]
  intro _
  grind only
  --simp only [mk.injEq, and_self, and_true] at h
  --exact h


/-- The map $(z,x,y)↦(x,y)$ defines a homomorphism from `Heisenberg` to $V × V^*$. -/
def Hom_H_to_V_x_Dual : AddMonoidHom (Additive (Heisenberg V k)) (V × Module.Dual k V ):=by
  refine AddMonoidHom.mk' (fun H => (H.x, H.y)) ?_
  intro H1 H2
  simp_all only [Prod.mk_add_mk, Prod.mk.injEq]
  apply And.intro
  · rfl
  · rfl

/--The homomorphism `Heisenberg.Hom_H_to_V_x_Dual` is surjective. -/
lemma surjective_Hom_H_to_V_x_Dual : Function.Surjective (Hom_H_to_V_x_Dual V k) := by
  intro H
  rw[Hom_H_to_V_x_Dual,AddMonoidHom.mk'_apply]
  use ⟨0, H.1, H.2⟩

--Définition de la suite exact 0 → k → Heisenberg → V × V* → 0
/--We have an exact sequence $0 → k → H(V) → V × V^* → 0$ given by `Heisenberg.Hom_k_to_H` and `Heisenberg.Hom_H_to_V_x_Dual`.-/
def exact_sequence :
  Function.Exact (Hom_k_to_H V k) (Hom_H_to_V_x_Dual V k) := by
  refine Function.Exact.of_comp_of_mem_range rfl ?_
  intro H h1
  rw [Set.mem_range]
  rw[Hom_H_to_V_x_Dual] at h1
  use H.z
  rw[Hom_k_to_H]
  change ((H.x, H.y) = (0,0)) at h1
  apply Prod.mk.inj at h1
  rw [AddMonoidHom.mk'_apply,<-h1.1,<-h1.2]
  exact rfl


/--The pull-back of $V$ by `Heisenberg.Hom_H_to_V_x_Dual`is a subgroup. -/
def Hom_H_to_V_x_Dual_sub_V : Subgroup (Heisenberg V k) := by
  refine Subgroup.mk ?_ ?_
  · refine Submonoid.mk ?_ ?_
    · refine Subsemigroup.mk (Set.preimage (Hom_H_to_V_x_Dual V k) ({⟨x,0⟩ | (x : V)})) ?_
      · simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq, forall_exists_index]
        intro a b x1 hx1 x2 hx2
        rw[Hom_H_to_V_x_Dual,AddMonoidHom.mk'_apply, Prod.mk.injEq] at hx1 hx2
        use (a.x + b.x)
        rw[Hom_H_to_V_x_Dual, mul_apply,AddMonoidHom.mk'_apply,Prod.mk.injEq,
          <-hx1.2, <-hx2.2,add_zero,← Prod.mk_inj]
    · simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq]
      use 0
      rw[Hom_H_to_V_x_Dual,Prod.mk_zero_zero, AddMonoidHom.mk'_apply]
      rfl
  · simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq, forall_exists_index]
    intro x x1 h
    use (x⁻¹).x
    rw[Hom_H_to_V_x_Dual,inv_apply,map_neg, sub_neg_eq_add, AddMonoidHom.mk'_apply, Prod.mk.injEq, zero_eq_neg]
    simp only [true_and]
    rw[Hom_H_to_V_x_Dual, AddMonoidHom.mk'_apply, Prod.mk.injEq] at h
    exact h.2.symm

/--The subgroup `Heisenberg.Hom_H_to_V_x_Dual_sub_V` is commutative. -/
instance Hom_H_to_V_x_Dual_sub_V_commutative : IsMulCommutative (Hom_H_to_V_x_Dual_sub_V V k) :=by
  refine IsMulCommutative.mk ?_
  refine { comm := ?_ }
  intro a b
  obtain ⟨a,ha⟩ := a
  obtain ⟨b,hb⟩ := b
  rw [MulMemClass.mk_mul_mk, Subtype.mk.injEq]
  rw[mul_apply]
  simp only [MulMemClass.mk_mul_mk]
  rw[mul_apply]
  simp only [mk.injEq]
  rw [Hom_H_to_V_x_Dual_sub_V] at ha hb
  simp only [Set.preimage_setOf_eq, Subgroup.mem_mk] at ha hb
  obtain ⟨xa, hxa⟩ := ha
  obtain ⟨xb, hxb⟩ := hb
  rw [Hom_H_to_V_x_Dual,AddMonoidHom.mk'_apply, Prod.mk.injEq] at hxa hxb
  rw[<-hxa.2, <- hxb.2]
  simp
  constructor
  · rw [AddCommMonoid.add_comm]
  · rw [AddCommMonoid.add_comm]

/--The subgroup `Heisenberg.Hom_H_to_V_x_Dual_sub_V` is a normal subgroup. -/
instance Hom_H_to_V_x_Dual_sub_V_normal : Subgroup.Normal (Hom_H_to_V_x_Dual_sub_V V k) :=by
  refine Subgroup.Normal.mk ?_
  intro x hx g
  rw[Hom_H_to_V_x_Dual_sub_V,] at hx
  simp only [Set.preimage_setOf_eq, Subgroup.mem_mk] at hx
  rw[Hom_H_to_V_x_Dual_sub_V]
  simp only [Set.preimage_setOf_eq, Subgroup.mem_mk]
  simp at hx ⊢
  rw[Hom_H_to_V_x_Dual,AddMonoidHom.mk'_apply]
  simp only [Prod.mk.injEq, exists_eq_left]
  rw[mul_apply,mul_apply,inv_apply]
  simp only
  obtain ⟨x1, hx1⟩ := hx
  rw[Hom_H_to_V_x_Dual] at hx1
  simp only [AddMonoidHom.mk'_apply, Prod.mk.injEq] at hx1
  grind only



/--The subgroup `Heisenberg.Hom_H_to_V_x_Dual_sub_V` is maximal among the commutative
subgroups of `Heisenberg`-/
theorem Hom_H_to_V_x_Dual_sub_V_maximal (Q : Subgroup (Heisenberg V k)) : IsMulCommutative (Hom_H_to_V_x_Dual_sub_V V k) ∧ (((Hom_H_to_V_x_Dual_sub_V V k) < Q ) → ¬ (IsMulCommutative Q)) := by
  constructor
  · exact Hom_H_to_V_x_Dual_sub_V_commutative V k
  · intro h
    by_contra hf
    rw [SetLike.lt_iff_le_and_exists] at h
    obtain ⟨x,⟨left,right⟩⟩ := h.2
    apply right
    rw [Hom_H_to_V_x_Dual_sub_V]
    simp only [Set.preimage_setOf_eq, Subgroup.mem_mk]
    have h1 : ∀ (b : V), x * (⟨0, b, 0⟩ : Heisenberg V k) = ⟨0, b, 0⟩ * x := by
      intro b
      have h2 : ⟨0, b, 0⟩ ∈ Hom_H_to_V_x_Dual_sub_V V k := by
        rw[Hom_H_to_V_x_Dual_sub_V]
        simp only [Set.preimage_setOf_eq, Subgroup.mem_mk]
        use b
        rw[Hom_H_to_V_x_Dual,AddMonoidHom.mk'_apply]
      exact Subgroup.mul_comm_of_mem_isMulCommutative Q left (h.1 h2)
    conv at h1 => rhs; rw[mul_apply,mul_apply]
    simp only [add_zero, zero_add, LinearMap.zero_apply, mk.injEq, add_eq_left, and_true] at h1
    simp only [Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq]
    rw[Hom_H_to_V_x_Dual,AddMonoidHom.mk'_apply]
    simp only [Prod.mk.injEq, exists_eq_left]
    have h3 :  ∀ (b : V), x.y b = 0 := by
      intro b
      exact (h1 b).1
    apply LinearMap.ext_iff.mpr
    simp only [LinearMap.zero_apply]
    intro x1
    specialize h3 x1
    exact h3.symm



/--The pull-back of $V^*$ by `Heisenberg.Hom_H_to_V_x_Dual`is a subgroup. -/
def Hom_H_to_V_x_Dual_sub_Dual : Subgroup (Heisenberg V k) := by
  refine Subgroup.mk ?_ ?_
  · refine Submonoid.mk ?_ ?_
    · refine Subsemigroup.mk (Set.preimage (Hom_H_to_V_x_Dual V k) ({⟨0,y⟩ | (y : Module.Dual k V)})) ?_
      simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq, forall_exists_index]
      intro a b x1 hx1 x2 hx2
      use (a.y + b.y)
      rw[Hom_H_to_V_x_Dual, mul_apply ,AddMonoidHom.mk'_apply,Prod.mk.injEq]
      rw [Hom_H_to_V_x_Dual] at hx1 hx2
      simp at hx1 hx2
      rw[<-hx1.1, <-hx2.1,add_zero]
      simp only [and_self]
    · simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq]
      use 0
      change ((0, 0) = (Hom_H_to_V_x_Dual V k) ⟨0,0,0⟩)
      rw[Hom_H_to_V_x_Dual,Prod.mk_zero_zero, AddMonoidHom.mk'_apply,Prod.mk_zero_zero]
  · simp
    intro x x1 h
    use ((x⁻¹).y)
    rw[Hom_H_to_V_x_Dual, AddMonoidHom.mk'_apply, Prod.mk.injEq] at h
    rw[Hom_H_to_V_x_Dual,inv_apply,map_neg, sub_neg_eq_add, AddMonoidHom.mk'_apply, Prod.mk.injEq, zero_eq_neg,h.1]
    simp only [and_self]

/--The subgroup `Heisenberg.Hom_H_to_V_x_Dual_sub_Dual` is commutative. -/
instance Hom_H_to_V_x_Dual_sub_Dual_commutative : IsMulCommutative (Hom_H_to_V_x_Dual_sub_Dual V k) :=by
  refine IsMulCommutative.mk ?_
  refine { comm := ?_ }
  intro a b
  obtain ⟨a,ha⟩ := a
  obtain ⟨b,hb⟩ := b
  rw [MulMemClass.mk_mul_mk, Subtype.mk.injEq]
  rw[mul_apply, mk.injEq]
  rw [Hom_H_to_V_x_Dual_sub_Dual] at ha hb
  simp only [Set.preimage_setOf_eq, Subgroup.mem_mk] at ha hb
  obtain ⟨xa, hxa⟩ := ha
  obtain ⟨xb, hxb⟩ := hb
  rw [Hom_H_to_V_x_Dual,AddMonoidHom.mk'_apply, Prod.mk.injEq] at hxa hxb
  rw[<-hxa.2, <- hxb.2, <-hxa.1, <-hxb.1, map_zero, add_zero]
  simp[mul_apply,hxa.1.symm,hxb.1.symm,hxa.2,hxb.2,add_comm]

/--The subgroup `Heisenberg.Hom_H_to_V_x_Dual_sub_Dual` is a normal subgroup. -/
instance Hom_H_to_V_x_Dual_sub_Dual_normal : Subgroup.Normal (Hom_H_to_V_x_Dual_sub_Dual V k) :=by
  refine Subgroup.Normal.mk ?_
  intro x hx g
  rw[Hom_H_to_V_x_Dual_sub_Dual] at hx
  simp only [Set.preimage_setOf_eq, Subgroup.mem_mk] at hx
  rw[Hom_H_to_V_x_Dual_sub_Dual]
  simp only [Set.preimage_setOf_eq, Subgroup.mem_mk]
  simp only [Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq]
  rw[Hom_H_to_V_x_Dual,AddMonoidHom.mk'_apply]
  simp only [Prod.mk.injEq, exists_eq_right]
  rw[mul_apply,mul_apply]
  simp only
  rw[inv_apply,add_neg_cancel_comm]
  obtain ⟨x1, hx1⟩ := hx
  rw[Hom_H_to_V_x_Dual,AddMonoidHom.mk'_apply] at hx1
  simp only [Prod.mk.injEq] at hx1
  exact hx1.1

/--The subgroup `Heisenberg.Hom_H_to_V_x_Dual_sub_Dual` is maximal among the commutative
subgroups of `Heisenberg`-/
instance Hom_H_to_V_x_Dual_sub_Dual_maximal [FiniteDimensional k V] (Q : Subgroup (Heisenberg V k)) : IsMulCommutative (Hom_H_to_V_x_Dual_sub_Dual V k) ∧  (((Hom_H_to_V_x_Dual_sub_Dual V k) < Q ) → ¬ (IsMulCommutative Q)) := by
  constructor
  · exact Hom_H_to_V_x_Dual_sub_Dual_commutative V k
  · intro h
    by_contra hf
    rw [SetLike.lt_iff_le_and_exists] at h
    obtain ⟨x,⟨ left, right⟩ ⟩ := h.2
    apply right
    rw [Hom_H_to_V_x_Dual_sub_Dual]
    simp only [Set.preimage_setOf_eq, Subgroup.mem_mk]
    have h1 : ∀ (b : Module.Dual k V), x * (⟨0, 0, b⟩ : Heisenberg V k) = ⟨0, 0, b⟩ * x := by
      intro b
      have h2 : ⟨0, 0, b⟩ ∈ Hom_H_to_V_x_Dual_sub_Dual V k := by
        rw[Hom_H_to_V_x_Dual_sub_Dual]
        simp only [Set.preimage_setOf_eq, Subgroup.mem_mk]
        use b
        rw[Hom_H_to_V_x_Dual,AddMonoidHom.mk'_apply]
      exact Subgroup.mul_comm_of_mem_isMulCommutative Q left (h.1 h2)
    simp only [mul_apply,add_zero, map_zero, zero_add, mk.injEq, left_eq_add, true_and] at h1
    simp only [Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq, Hom_H_to_V_x_Dual,AddMonoidHom.mk'_apply,Prod.mk.injEq, exists_eq_right]
    symm
    rw[<-Module.forall_dual_apply_eq_zero_iff k]
    intro φ
    simp_all only

variable{V k}


 /--Commutator of two elements of `Heisenberg` -/
 @[simp]
 theorem commutator_of_elements (H1 H2 : Heisenberg V k) :
  ⁅H1, H2⁆ = ⟨ H1.y (H2.x) - H2.y (H1.x), 0, 0 ⟩ := by
  rw [commutatorElement_def]
  --change ((mul (mul (mul H1 H2) (inverse H1)) (inverse H2)) = { z := H1.y H2.x - H2.y H1.x, x := 0, y := 0 })
  rw[mul_apply,mul_apply, mul_apply, inv_apply, inv_apply,map_neg]
  simp only [map_neg, sub_neg_eq_add, LinearMap.add_apply, add_neg_cancel_comm, add_neg_cancel,
    mk.injEq, and_self, and_true]
  ring


/-- The trivial bijection between `Heisenberg`and $k× V× V^*$. -/
instance bij_k_V_Dual : (Heisenberg V k) ≃ (k × V × (Module.Dual k V)) :=by
  refine Equiv.mk (fun a ↦ (a.z, a.x, a.y)) (fun h ↦ ⟨h.1, h.2.1, h.2.2⟩) ?_ ?_
  · intro h
    simp only
  · intro h
    simp only [Prod.mk.eta]

/-- The trivial bijection beetween `Heisenberg.center`and $k$.-/
instance bij_k_center : Heisenberg.center V k ≃ k := by
  refine Equiv.mk (fun h => h.val.z) (fun z => ⟨⟨z, 0, 0⟩, by simp [Heisenberg.center]⟩) ?_ ?_
  · intro h
    simp only
    rw [Subtype.ext_iff_val]
    simp only
    obtain ⟨h1, h2⟩ := h
    simp only
    obtain ⟨h21,h22⟩ := h2
    ext u
    · simp only
    · rw[h21]
    · rw[h22]
  · intro x
    simp only


/-- Cardinal of  `Heisenberg.center` -/
theorem card_center : Nat.card (Heisenberg.center V k) = Nat.card k := by
   rw [Nat.card_congr (bij_k_center)]


------------------------------------------------------------------------------
------------------------------------------------------------------------------

variable [FiniteDimensional k V]
/--`Heisenberg.center` is the center of `Heisenberg` -/
instance center_eq :
  Subgroup.center (Heisenberg V k) = Heisenberg.center V k := by
  ext h
  constructor
  · intro h1
    rw [Subgroup.mem_center_iff] at h1
    have h11 : ∀ (g : Heisenberg V k), ((form_commutator V k) (h.x, h.y)) (g.x, g.y) = 0 ∧ g.x + h.x = h.x + g.x ∧ g.y + h.y = h.y + g.y :=by
      unfold form_commutator
      simp
      intro g
      specialize h1 g
      rw[mul_apply,mul_apply] at h1
      grind only
    have h12 := form_commutator_non_degenerate V k
    rw[LinearMap.BilinForm.Nondegenerate] at h12
    specialize h12 ⟨h.x,h.y⟩
    change ((h.x=0 ∧ h.y =0))
    have h13 : ∀ (g : Heisenberg V k), ((form_commutator V k) (h.x, h.y)) (g.x, g.y) = 0:= by
      intro g
      specialize h11 g
      exact h11.1
    rw[Prod.mk_eq_zero] at h12
    apply h12
    intro n
    specialize h13 ⟨0, n.1, n.2⟩
    simp at h13
    rw[<-h13]
  · intro H
    rw[Subgroup.mem_center_iff]
    intro g
    rw[mul_apply,mul_apply]
    simp only [mk.injEq]
    rw[H.1, H.2]
    simp only [map_zero, add_zero, LinearMap.zero_apply, zero_add, and_self, and_true]
    rw [AddCommMonoidWithOne.add_comm]



/--Caracterisation of elements in the commutator of `Heisenberg` -/
theorem commutator_caracterisation (p : Heisenberg V k) : p ∈ (commutator (Heisenberg V k)) → (p.x=0 ∧ p.y=0) :=by
  intro h
  rw [commutator_def,← SetLike.mem_coe,Subgroup.commutator_def,Subgroup.closure] at h
  simp only [Subgroup.mem_top, true_and, Subgroup.coe_sInf, Set.mem_setOf_eq, Set.mem_iInter,
    SetLike.mem_coe] at h
  specialize h (Subgroup.center (Heisenberg V k))
  rw[Heisenberg.center_eq,center,Subgroup.coe_set_mk, Subgroup.mem_mk] at h
  simp at h
  apply h
  intro a x x1 hh
  grind only

/-- $H(V)$ is in bijection with $H(V*)$. -/
noncomputable def equiv_Dual:
  Heisenberg V k ≃ Heisenberg (Module.Dual k V) k := by
  refine Equiv.mk (fun a ↦ ⟨a.z, a.y , ((convention_eval_iso V k).toFun (-a.x)) ⟩ ) (fun a ↦ ⟨a.z, ((convention_eval_iso V k).invFun (-a.y)) , a.x⟩) ?_ ?_
  · intro H
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe, map_neg, neg_neg,
      LinearEquiv.invFun_eq_symm, LinearEquiv.symm_apply_apply]
  · intro H
    simp only [LinearEquiv.invFun_eq_symm, map_neg, neg_neg, AddHom.toFun_eq_coe,
      LinearMap.coe_toAddHom, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/--With the convention $(x,y)=-(y,x)$, $H(V)$ is antiisomorphic to $H(V*)$. -/
noncomputable def anti_iso_Dual : Heisenberg V k ≃* (Heisenberg (Module.Dual k V) k)ᵐᵒᵖ := by
  refine MulEquiv.mk (Equiv.trans (equiv_Dual) (MulOpposite.opEquiv)) ?_
  intro H1 H2
  simp only [Equiv.toFun_as_coe, Equiv.trans_apply, MulOpposite.opEquiv_apply]
  rw [← MulOpposite.op_mul,MulOpposite.op_inj]
  rw[equiv_Dual,mul_apply,mul_apply]
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe, map_neg,
    LinearEquiv.invFun_eq_symm, Equiv.coe_fn_mk, map_add, neg_add_rev, LinearMap.neg_apply,
    convention_eval_iso_apply, neg_neg, mk.injEq, add_left_inj, and_true]
  constructor
  · rw [AddCommMonoid.add_comm]
  · rw [AddCommMonoid.add_comm]


variable [inst5 : Nontrivial V]
/--The commutator subgroup of `Heisenberg` is non trivial -/
 theorem commutator_ne_bot : lowerCentralSeries (Heisenberg V k) 1 ≠ ⊥ :=by
  simp
  rw[_root_.commutator]
  by_contra hf
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer,Subgroup.coe_top, top_le_iff, Subgroup.centralizer_eq_top_iff_subset,
    Set.univ_subset_iff, Subgroup.coe_eq_univ,Subgroup.eq_top_iff'] at hf
  obtain ⟨h11,h12⟩ := (nontrivial_iff_exists_ne 0).mp inst5
  specialize hf ⟨0,h11,0⟩
  rw[Heisenberg.center_eq,Heisenberg.center,Subgroup.mem_mk] at hf
  simp only [Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq, and_true] at hf
  contradiction

/-- `Heisenberg` is a twostep nilpotent group -/
theorem two_step_nilpotent : lowerCentralSeries (Heisenberg V k) 1 ≠ ⊥ ∧ lowerCentralSeries (Heisenberg V k) 2 = ⊥ :=by
  constructor
  · exact commutator_ne_bot
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [mem_lowerCentralSeries_succ_iff] at hx
    simp at hx
    rw[_root_.commutator] at hx
    change( x ∈ Subgroup.closure {x | ∃ p ∈ ⁅⊤, ⊤⁆, ∃ q, ⁅p, q⁆ = x}) at hx
    rw[Subgroup.closure,Subgroup.mem_sInf] at hx
    simp only [Set.mem_setOf_eq] at hx
    specialize hx ⊥
    rw [← Subgroup.mem_bot]
    apply hx
    intro u hu
    obtain ⟨p, hp, q, hq⟩ := hu
    rw[Heisenberg.commutator_of_elements] at hq
    simp
    change (u = ⟨0,0,0⟩)
    rw[<-hq,mk.injEq]
    simp only [and_self, and_true]
    rw[((Heisenberg.commutator_caracterisation p) hp).1, ((Heisenberg.commutator_caracterisation p) hp).2]
    simp

omit inst5 in
/-- Cardinal of `Heisenberg` when $k$ is a finite field -/
theorem card_H [Fintype k] : Nat.card (Heisenberg V k) = (Nat.card k)*(Nat.card V)^2 := by
  rw[Nat.card_congr (bij_k_V_Dual),Nat.pow_two]
  simp only [Nat.card_prod, Nat.card_eq_fintype_card, mul_eq_mul_left_iff, Fintype.card_ne_zero,
    or_false]
  left
  obtain ⟨h⟩ := (Basis.linearEquiv_dual_iff_finiteDimensional (V := V) (K := k)).mpr inferInstance
  apply LinearEquiv.toEquiv at h
  rw [Nat.card_congr h]

omit inst5 in
/--The index of the center of `Heisenberg` is equal to the cardinal of $V$ to the square.-/
theorem ord_V [Fintype k] : (Subgroup.index (Subgroup.center (Heisenberg V k))) = (Nat.card V)^2 :=by
  have h3 : (Nat.card k)*(Nat.card V)^2 / (Nat.card k) = (Nat.card V)^2 := by
    simp only [Nat.card_eq_fintype_card, ne_eq, Fintype.card_ne_zero, not_false_eq_true,
      mul_div_cancel_left₀]
  rw[<-h3,<-card_H,<-Subgroup.index_mul_card (Subgroup.center (Heisenberg V k))]
  have h4 : Nat.card (Subgroup.center (Heisenberg V k)) = Nat.card k := by
    rw[center_eq, center]
    simp only [Subgroup.mem_mk]
    exact card_center (V:= V) (k := k)
  rw[h4]
  simp only [Nat.card_eq_fintype_card, ne_eq, Fintype.card_ne_zero, not_false_eq_true,
    mul_div_cancel_right₀]

#min_imports

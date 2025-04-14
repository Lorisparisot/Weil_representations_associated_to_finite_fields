import Mathlib.Algebra.Exact
import Mathlib.Algebra.Group.Commutator
import MyProject.convention_dual
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Group.Subgroup.Defs


variable (V k : Type*) [inst1 : Field k] [inst2 : AddCommGroup V] [inst3 : Module k V] [inst4 : FiniteDimensional k V]

--local notation "q" => Fintype.card k

/- On trouvera ici les propriétés relatives aux groupes d'Heisenberg-/

@[ext]
structure Heisenberg where
  z : k
  x : V
  y : Module.Dual k V

#check Heisenberg
namespace Heisenberg

--Loi de groupe sur Heisenberg
variable {V k}
def mul
  (H1 H2 : Heisenberg V k) : Heisenberg V k:=
  ⟨H1.z + H2.z + (H1.y H2.x), H1.x + H2.x, H1.y + H2.y⟩

--Inverse d'un élément d'Heisenberg
def inverse (H : Heisenberg V k) : Heisenberg V k :=
  ⟨ -H.z - (H.y (-H.x)), - H.x ,- H.y⟩

--Instance de groupe
instance group : Group (Heisenberg V k) := {
  mul := mul,
  mul_assoc := by
    intro a b c
    change (mul (mul a b) c = mul a (mul b c))
    rw [mul, mul, mul, mul]
    ext
    simp
    · ring
    · simp
      exact add_assoc a.x b.x c.x
    · simp
      ring
  one := ⟨0, 0, 0⟩,
  one_mul := by
    intro a
    change (mul ⟨0, 0, 0⟩ a = a)
    rw [mul]
    simp
  mul_one := by
    intro a
    change (mul a ⟨0, 0, 0⟩ = a)
    rw [mul]
    simp
  inv := inverse,
  inv_mul_cancel := by
    intro a
    change (mul (inverse a) a = ⟨0, 0, 0⟩)
    rw [mul, inverse]
    simp
}

--Centre du groupe d'Heisenberg
variable (V k)
def center := {H : Heisenberg V k | H.x = 0 ∧ H.y = 0}
#check center


--Le centre du groupe d'Heisenberg définit ci-dessus est un sous-groupe de Heisenberg
instance center_is_subgroup : Subgroup (Heisenberg V k) :=
{ carrier := center V k,
  one_mem' := by
    change ⟨0,0,0⟩ ∈ center V k
    constructor
    · simp
    · simp,
  mul_mem' := by
    intro a b ha hb
    change (mul a b ∈ center V k)
    unfold mul
    constructor
    · simp
      rw [ha.1, hb.1]
      simp
    · simp
      rw [ha.2, hb.2]
      simp,
  inv_mem' := by
    intro a ha
    change (inverse a ∈ center V k)
    unfold inverse
    constructor
    · simp
      rw [ha.1]
    · simp
      rw [ha.2]
}

--Le centre définit ci-dessus est bien le centre du groupe d'Heisenberg
instance center_eq :
  Subgroup.center (Heisenberg V k) = Heisenberg.center_is_subgroup V k := by
  ext h
  constructor
  · intro h1
    rw [Subgroup.mem_center_iff] at h1
    change ( ∀ (g : Heisenberg V k), mul g h = mul h g) at h1
    unfold mul at h1
    simp at h1
    ring_nf at h1
    simp at h1
    have h11 : ∀ (g : Heisenberg V k), ((form_commutator V k) (h.x, h.y)) (g.x, g.y) = 0 ∧ g.x + h.x = h.x + g.x ∧ g.y + h.y = h.y + g.y :=by
      unfold form_commutator
      simp
      intro g
      specialize h1 g
      constructor
      · exact add_eq_zero_iff_neg_eq.mpr (congrArg Neg.neg (id (Eq.symm h1.left)))
      · exact h1.right
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
    change (mul g h = mul h g)
    unfold mul
    simp
    rw[H.1, H.2]
    simp
    rw [@AddCommMonoidWithOne.add_comm]


--Morphisme de k dans Heisenberg
def Hom_k_to_H : AddMonoidHom k (Additive (Heisenberg V k)) :=by
  refine AddMonoidHom.mk' (fun z => ⟨z,0,0⟩) ?_
  intro a b
  simp only
  change ((⟨a + b, 0, 0⟩ : Heisenberg V k) = mul ⟨a, 0, 0⟩ ⟨b, 0, 0⟩)
  simp only [mul,LinearMap.zero_apply, add_zero]

-- Injectivité de Hom_k_to_H
instance injective_Hom_k_to_H : Function.Injective (Hom_k_to_H V k) := by
  intro k1 k2
  rw[Hom_k_to_H,AddMonoidHom.mk'_apply]
  intro h
  change ((⟨k1,0,0⟩ : Heisenberg V k) = ⟨k2,0,0⟩) at h
  simp only [mk.injEq, and_self, and_true] at h
  exact h


--Morphisme de Heisenberg dans V × V*
def Hom_H_to_V_x_Dual : AddMonoidHom (Additive (Heisenberg V k)) (V × Module.Dual k V ):=by
  refine AddMonoidHom.mk' (fun H => (H.x, H.y)) ?_
  intro H1 H2
  rw [Prod.mk_add_mk, Prod.mk.injEq]
  change ((mul H1 H2).x = H1.x + H2.x ∧ (mul H1 H2).y = H1.y + H2.y)
  rw[mul]
  simp only [and_self]

--Surjectivité de Hom_H_to_V_x_Dual
instance surjective_Hom_H_to_V_x_Dual : Function.Surjective (Hom_H_to_V_x_Dual V k) := by
  intro H
  rw[Hom_H_to_V_x_Dual,AddMonoidHom.mk'_apply]
  use ⟨0, H.1, H.2⟩

--Définition de la suite exact 0 → k → Heisenberg → V × V* → 0
def exact_sequence :
  Function.Exact (Hom_k_to_H V k) (Hom_H_to_V_x_Dual V k) := by
  refine Function.Exact.of_comp_of_mem_range rfl ?_
  intro H h1
  rw [@Set.mem_range]
  rw[Hom_H_to_V_x_Dual] at h1
  use H.z
  rw[Hom_k_to_H]
  change ((H.x, H.y) = (0,0)) at h1
  apply Prod.mk.inj at h1
  rw [AddMonoidHom.mk'_apply]
  rw[<-h1.1,<-h1.2]
  exact rfl


--Sous-groupe définie par ψ⁻¹(V).
def Hom_H_to_V_x_Dual_sub_V : Subgroup (Heisenberg V k) := by
  refine Subgroup.mk ?_ ?_
  · refine Submonoid.mk ?_ ?_
    · refine Subsemigroup.mk (Set.preimage (Hom_H_to_V_x_Dual V k) ({⟨x,0⟩ | (x : V)})) ?_
      · simp
        intro a b x1 hx1 x2 hx2
        rw[Hom_H_to_V_x_Dual,AddMonoidHom.mk'_apply, Prod.mk.injEq] at hx1 hx2
        use (a.x + b.x)
        change ((a.x + b.x, 0) = (Hom_H_to_V_x_Dual V k) (mul a b))
        rw[Hom_H_to_V_x_Dual, mul,AddMonoidHom.mk'_apply,Prod.mk.injEq]
        simp only [true_and]
        rw[<-hx1.2, <-hx2.2,add_zero]
    · simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq]
      use 0
      change ((0, 0) = (Hom_H_to_V_x_Dual V k) ⟨0,0,0⟩)
      rw[Hom_H_to_V_x_Dual,Prod.mk_zero_zero, AddMonoidHom.mk'_apply,Prod.mk_zero_zero]
  · simp
    intro x x1 h
    use ((inverse x).x)
    change ((x.inverse.x, 0) = (Hom_H_to_V_x_Dual V k) x.inverse)
    rw[Hom_H_to_V_x_Dual,inverse,map_neg, sub_neg_eq_add, AddMonoidHom.mk'_apply, Prod.mk.injEq, zero_eq_neg]
    simp only [true_and]
    rw[Hom_H_to_V_x_Dual, AddMonoidHom.mk'_apply, Prod.mk.injEq] at h
    exact h.2.symm

--C'est un sous-groupe commutatif
instance Hom_H_to_V_x_Dual_sub_V_commutative : CommGroup (Hom_H_to_V_x_Dual_sub_V V k) :=by
  refine CommGroup.mk ?_
  intro a b
  obtain ⟨a,ha⟩ := a
  obtain ⟨b,hb⟩ := b
  rw [MulMemClass.mk_mul_mk, Subtype.mk.injEq]
  change (mul a b = mul b a)
  rw[mul, mul, mk.injEq]
  rw [Hom_H_to_V_x_Dual_sub_V] at ha hb
  simp only [Set.preimage_setOf_eq, Subgroup.mem_mk, Set.mem_setOf_eq] at ha hb
  obtain ⟨xa, hxa⟩ := ha
  obtain ⟨xb, hxb⟩ := hb
  rw [Hom_H_to_V_x_Dual,AddMonoidHom.mk'_apply, Prod.mk.injEq] at hxa hxb
  rw[<-hxa.2, <- hxb.2]
  simp
  constructor
  · rw [@AddCommMonoid.add_comm]
  · rw [@AddCommMonoid.add_comm]

--C'est un sous-groupe distingué
instance Hom_H_to_V_x_Dual_sub_V_normal : Subgroup.Normal (Hom_H_to_V_x_Dual_sub_V V k) :=by
  refine Subgroup.Normal.mk ?_
  intro x hx g
  rw[Hom_H_to_V_x_Dual_sub_V,] at hx
  simp only [Set.preimage_setOf_eq, Subgroup.mem_mk, Set.mem_setOf_eq] at hx
  rw[Hom_H_to_V_x_Dual_sub_V]
  simp only [Set.preimage_setOf_eq, Subgroup.mem_mk, Set.mem_setOf_eq]
  rw[Hom_H_to_V_x_Dual,AddMonoidHom.mk'_apply]
  simp only [Prod.mk.injEq, exists_eq_left]
  change (0 = (mul (mul g x) (inverse g)).y)
  rw[mul,mul]
  simp only
  rw[inverse,add_neg_cancel_comm]
  obtain ⟨x1, hx1⟩ := hx
  rw[Hom_H_to_V_x_Dual] at hx1
  simp only [AddMonoidHom.mk'_apply, Prod.mk.injEq] at hx1
  exact hx1.2

--C'est un sous-groupe maximal.
--instance Hom_H_to_V_x_Dual_sub_V_maximal (Q : Subgroup (Heisenberg V k)): ((Hom_H_to_V_x_Dual_sub_V V k) ≤ Q ∧ Q ≠ ⊤ )→ Q = (Hom_H_to_V_x_Dual_sub_V V k) := by
  --sorry


--Sous-groupe définie par ψ⁻¹(V*).
def Hom_H_to_V_x_Dual_sub_Dual : Subgroup (Heisenberg V k) := by
  refine Subgroup.mk ?_ ?_
  · refine Submonoid.mk ?_ ?_
    · refine Subsemigroup.mk (Set.preimage (Hom_H_to_V_x_Dual V k) ({⟨0,y⟩ | (y : Module.Dual k V)})) ?_
      simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq, forall_exists_index]
      intro a b x1 hx1 x2 hx2
      use (a.y + b.y)
      change ((0, a.y + b.y) = (Hom_H_to_V_x_Dual V k) (mul a b))
      rw[Hom_H_to_V_x_Dual, mul,AddMonoidHom.mk'_apply,Prod.mk.injEq]
      simp only [true_and]
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
    use ((inverse x).y)
    change ((0, x.inverse.y) = (Hom_H_to_V_x_Dual V k) x.inverse)
    rw[Hom_H_to_V_x_Dual,inverse,map_neg, sub_neg_eq_add, AddMonoidHom.mk'_apply, Prod.mk.injEq, zero_eq_neg]
    simp only [true_and]
    rw[Hom_H_to_V_x_Dual, AddMonoidHom.mk'_apply, Prod.mk.injEq] at h
    rw[h.1]
    simp only [and_self]

--C'est un sous-groupe commutatif
instance Hom_H_to_V_x_Dual_sub_Dual_commutative : CommGroup (Hom_H_to_V_x_Dual_sub_Dual V k) :=by
  refine CommGroup.mk ?_
  intro a b
  obtain ⟨a,ha⟩ := a
  obtain ⟨b,hb⟩ := b
  rw [MulMemClass.mk_mul_mk, Subtype.mk.injEq]
  change (mul a b = mul b a)
  rw[mul, mul, mk.injEq]
  rw [Hom_H_to_V_x_Dual_sub_Dual] at ha hb
  simp only [Set.preimage_setOf_eq, Subgroup.mem_mk, Set.mem_setOf_eq] at ha hb
  obtain ⟨xa, hxa⟩ := ha
  obtain ⟨xb, hxb⟩ := hb
  rw [Hom_H_to_V_x_Dual,AddMonoidHom.mk'_apply, Prod.mk.injEq] at hxa hxb
  rw[<-hxa.2, <- hxb.2, <-hxa.1, <-hxb.1, map_zero, add_zero]
  simp only [true_and]
  constructor
  · rw [map_zero, add_zero]
    rw [@AddCommMonoidWithOne.add_comm]
  · rw [@AddCommMonoid.add_comm]

--C'est un sous-groupe distingué
instance Hom_H_to_V_x_Dual_sub_Dual_normal : Subgroup.Normal (Hom_H_to_V_x_Dual_sub_Dual V k) :=by
  refine Subgroup.Normal.mk ?_
  intro x hx g
  rw[Hom_H_to_V_x_Dual_sub_Dual] at hx
  simp only [Set.preimage_setOf_eq, Subgroup.mem_mk, Set.mem_setOf_eq] at hx
  rw[Hom_H_to_V_x_Dual_sub_Dual]
  simp only [Set.preimage_setOf_eq, Subgroup.mem_mk, Set.mem_setOf_eq]
  rw[Hom_H_to_V_x_Dual,AddMonoidHom.mk'_apply]
  simp only [Prod.mk.injEq, exists_eq_right]
  change (0 = (mul (mul g x) (inverse g)).x)
  rw[mul,mul]
  simp only
  rw[inverse,add_neg_cancel_comm]
  obtain ⟨x1, hx1⟩ := hx
  rw[Hom_H_to_V_x_Dual,AddMonoidHom.mk'_apply] at hx1
  simp only [Prod.mk.injEq] at hx1
  exact hx1.1

variable{V k}
--Définition du commutateur de deux éléments
 omit [FiniteDimensional k V] in theorem commutator_of_elements (H1 H2 : Heisenberg V k) :
  ⁅H1, H2⁆ = ⟨ H1.y (H2.x) - H2.y (H1.x), 0, 0 ⟩ := by
  rw [@commutatorElement_def]
  change ((mul (mul (mul H1 H2) (inverse H1)) (inverse H2)) = { z := H1.y H2.x - H2.y H1.x, x := 0, y := 0 })
  rw[mul,mul, mul, inverse, inverse,map_neg]
  simp only [map_neg, sub_neg_eq_add, LinearMap.add_apply, add_neg_cancel_comm, add_neg_cancel,
    mk.injEq, and_self, and_true]
  ring

variable (V k) [inst5 : Nontrivial V]
--Le sous-groupe engendré par les commutateurs est non trivial.
 theorem commutator_ne_bot : lowerCentralSeries (Heisenberg V k) 1 ≠ ⊥ :=by
  simp
  rw[_root_.commutator]
  by_contra hf
  rw [@Subgroup.commutator_eq_bot_iff_le_centralizer,Subgroup.coe_top, top_le_iff, Subgroup.centralizer_eq_top_iff_subset,
    Set.univ_subset_iff, Subgroup.coe_eq_univ,@Subgroup.eq_top_iff'] at hf
  obtain ⟨h11,h12⟩ := (nontrivial_iff_exists_ne 0).mp inst5
  specialize hf ⟨0,h11,0⟩
  rw[Heisenberg.center_eq,Heisenberg.center_is_subgroup,Subgroup.mem_mk,Heisenberg.center,Set.mem_setOf_eq] at hf
  simp only [and_true] at hf
  contradiction

-- Si p est dans le commutateur, alors il est de la forme (z,0,0)
variable {V k}
omit inst5 in theorem commutator_caracterisation (p : Heisenberg V k) : p ∈ (commutator (Heisenberg V k)) → (p.x=0 ∧ p.y=0) :=by
  intro h
  rw [commutator_def,← @SetLike.mem_coe,@Subgroup.commutator_def,Subgroup.closure] at h
  simp only [Subgroup.mem_top, true_and, Subgroup.coe_sInf, Set.mem_setOf_eq, Set.mem_iInter,
    SetLike.mem_coe] at h
  specialize h (Subgroup.center (Heisenberg V k))
  rw[Heisenberg.center_eq,center_is_subgroup,Subgroup.coe_set_mk, Subgroup.mem_mk,center] at h
  simp only [Set.setOf_subset_setOf, forall_exists_index, Set.mem_setOf_eq] at h
  apply h
  intro a x x1
  rw[Heisenberg.commutator_of_elements]
  intro h
  rw[<-h]
  simp only [and_self]

--Heisenberg est un groupe nilpotent d'ordre 2
theorem two_step_nilpotent : lowerCentralSeries (Heisenberg V k) 1 ≠ ⊥ ∧ lowerCentralSeries (Heisenberg V k) 2 = ⊥ :=by
  constructor
  · exact commutator_ne_bot V k
  · rw [@Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [@mem_lowerCentralSeries_succ_iff] at hx
    simp at hx
    rw[_root_.commutator] at hx
    change( x ∈ Subgroup.closure {x | ∃ p ∈ ⁅⊤, ⊤⁆, ∃ q, ⁅p, q⁆ = x}) at hx
    rw[Subgroup.closure,Subgroup.mem_sInf] at hx
    simp only [Set.mem_setOf_eq] at hx
    specialize hx ⊥
    rw [← @Subgroup.mem_bot]
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

variable (V k)
--H(V) est en bijection avec H(V*)
noncomputable def equiv_Dual:
  Heisenberg V k ≃ Heisenberg (Module.Dual k V) k := by
  refine Equiv.mk (fun a ↦ ⟨a.z, a.y , ((convention_eval_iso V k).toFun (-a.x)) ⟩ ) (fun a ↦ ⟨a.z, ((convention_eval_iso V k).invFun (-a.y)) , a.x⟩) ?_ ?_
  · intro H
    simp
  · intro H
    simp

--Cette bijection est un antiisomorphisme pour les conventions de l'article
noncomputable def anti_iso_Dual : Heisenberg V k ≃* (Heisenberg (Module.Dual k V) k)ᵐᵒᵖ := by
  refine MulEquiv.mk (Equiv.trans (equiv_Dual V k) (MulOpposite.opEquiv)) ?_
  intro H1 H2
  simp only [Equiv.toFun_as_coe, Equiv.trans_apply, MulOpposite.opEquiv_apply]
  rw [← @MulOpposite.op_mul,MulOpposite.op_inj]
  change ((equiv_Dual V k) (mul H1 H2) = mul ((equiv_Dual V k) H2) ((equiv_Dual V k) H1))
  rw[equiv_Dual,mul,mul]
  simp
  constructor
  · rw[eq_add_neg_iff_add_eq]
    rw[convention_eval_iso_apply]
    simp
    rw [@AddCommMonoidWithOne.add_comm]
  · rw [@AddCommMonoid.add_comm]

#min_imports

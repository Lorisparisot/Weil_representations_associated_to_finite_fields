import Mathlib

variable (V k : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V]

local notation "q" => Fintype.card k


@[ext]
structure Heisenberg (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V] where
  z : k
  x : V
  y : Module.Dual k V

variable {k V}

def Heisen_mul
  (H1 H2 : Heisenberg k V) : Heisenberg k V :=
  ⟨H1.z + H2.z + (H1.y H2.x), H1.x + H2.x, H1.y + H2.y⟩

#check Heisen_mul

def Heisen_mul_invdef {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V] (H : Heisenberg k V) : Heisenberg k V :=
  ⟨ -H.z - (H.y (-H.x)), - H.x ,- H.y⟩

instance Heisen_group (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V] : Group (Heisenberg k V) := {
  mul := Heisen_mul,
  mul_assoc := by
    intro a b c
    change (Heisen_mul (Heisen_mul a b) c = Heisen_mul a (Heisen_mul b c))
    rw [Heisen_mul, Heisen_mul, Heisen_mul, Heisen_mul]
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
    change (Heisen_mul ⟨0, 0, 0⟩ a = a)
    rw [Heisen_mul]
    simp
  mul_one := by
    intro a
    change (Heisen_mul a ⟨0, 0, 0⟩ = a)
    rw [Heisen_mul]
    simp
  inv := Heisen_mul_invdef,
  inv_mul_cancel := by
    intro a
    change (Heisen_mul (Heisen_mul_invdef a) a = ⟨0, 0, 0⟩)
    rw [Heisen_mul, Heisen_mul_invdef]
    simp
}

def Heisen_center (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V] := {H : Heisenberg k V | H.x = 0 ∧ H.y = 0}

instance Heisen_center.is_subgroup {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V] :
  Subgroup (Heisenberg k V) :=
{ carrier := Heisen_center k V,
  one_mem' := by
    change (⟨0,0,0⟩  ∈ Heisen_center k V)
    constructor
    · simp
    · simp,
  mul_mem' := by
    intro a b ha hb
    change (Heisen_mul a b ∈ Heisen_center k V)
    unfold Heisen_mul
    constructor
    · simp
      rw [ha.1, hb.1]
      simp
    · simp
      rw [ha.2, hb.2]
      simp,
  inv_mem' := by
    intro a ha
    change (Heisen_mul_invdef a ∈ Heisen_center k V)
    unfold Heisen_mul_invdef
    constructor
    · simp
      rw [ha.1]
    · simp
      rw [ha.2]
}

def form_commutator_H (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V]
  (H1 : V × Module.Dual k V) (H2 : V × Module.Dual k V) : k :=
  H1.2.toFun H2.1 - H2.2.toFun H1.1

def form_commutator_H1 (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V] :
  (V × Module.Dual k V) →ₗ[k] (V × Module.Dual k V) →ₗ[k] k := by
  refine LinearMap.mk₂ k (form_commutator_H k V) ?_ ?_ ?_ ?_
  · intro m1 m2 n
    unfold form_commutator_H
    simp
    ring
  · intro c m n
    unfold form_commutator_H
    simp
    ring
  · intro m n1 n2
    unfold form_commutator_H
    simp
    ring
  · intro c m n
    unfold form_commutator_H
    simp
    ring

theorem ortho_dual (k V : Type*) (x : V) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
  (∀ (ϕ : Module.Dual k V), ϕ x = 0 )→ x = 0 := by
  intro ϕ
  let hbase := Module.finBasis k V
  rw[<-(Basis.sum_repr hbase x)]
  have h1 : ∀ (i : Fin (Module.finrank k V)), ∑ j, (hbase.repr x) j * (hbase.dualBasis i) (hbase j) = (hbase.repr x) i :=by
    intro i
    rw [Finset.sum_eq_single i]
    · have h2 : (hbase.dualBasis i) (hbase i) =1 := by
        rw [@Basis.dualBasis_apply_self _ _ _ _ _ _ _ hbase _]
        simp
      rw[h2]
      simp
    · intro b hb hbi
      have h2 : (hbase.dualBasis i) (hbase b) =0 := by
        rw [(@Basis.dualBasis_apply_self _ _ _ _ _ _ _ hbase _ i b)]
        simp
        push_neg
        exact hbi
      rw[h2]
      simp
    · intro hi
      simp
      rw [← @Finsupp.not_mem_support_iff]
      rw[<-List.toFinset_finRange] at hi
      simp at hi
  have h3 : ∀ (i : Fin (Module.finrank k V)), (hbase.repr x) i = 0 := by
        intro J
        specialize h1 J
        rw[<- h1]
        specialize ϕ (hbase.dualBasis J)
        rw[<-ϕ]
        have this : ∑ j, (hbase.repr x) j * (hbase.dualBasis J) (hbase j) = (hbase.dualBasis J) (∑ i, (hbase.repr x) i • hbase i):= by
            simp only [map_sum, map_smul, smul_eq_mul]
        rw[this, (Basis.sum_repr hbase x)]
  rw [(Basis.forall_coord_eq_zero_iff hbase).mp h3]
  simp

instance non_degenerate_form_H (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]:
  LinearMap.BilinForm.Nondegenerate (form_commutator_H1 k V) := by
  rw[LinearMap.BilinForm.Nondegenerate ]
  by_contra hf
  push_neg at hf
  obtain ⟨m, hm⟩ := hf
  cases hm with
  | intro left right =>
    unfold form_commutator_H1 form_commutator_H at left
    simp at left
    have left1 := left
    rw[forall_comm] at left
    specialize left 0
    simp at left
    have hh : m.2 = 0 := by
      exact LinearMap.ext_iff.mpr left
    rw[hh] at left1
    simp at left1
    have hhhh : m.1 = 0:= by
      exact (ortho_dual k V m.1) left1
    apply right
    exact Prod.ext hhhh hh

theorem Heisen_center_eq {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]:
  Subgroup.center (Heisenberg k V) = Heisen_center k V := by
  ext h
  constructor
  · intro h1
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at h1
    change ( ∀ (g : Heisenberg k V), Heisen_mul g h = Heisen_mul h g) at h1
    unfold Heisen_mul at h1
    simp at h1
    ring_nf at h1
    simp at h1
    have h11 : ∀ (g : Heisenberg k V), ((form_commutator_H1 k V) (h.x, h.y)) (g.x, g.y) = 0 ∧ g.x + h.x = h.x + g.x ∧ g.y + h.y = h.y + g.y :=by
      unfold form_commutator_H1 form_commutator_H
      simp
      intro g
      specialize h1 g
      rw[sub_eq_zero]
      exact
        (and_symm_left (g.y h.x) (h.y g.x) (g.x + h.x = h.x + g.x ∧ g.y + h.y = h.y + g.y)).mp h1
    have h12 := non_degenerate_form_H k V
    rw[LinearMap.BilinForm.Nondegenerate] at h12
    specialize h12 ⟨h.x,h.y⟩
    change ((h.x=0 ∧ h.y =0))
    have h13 : ∀ (g : Heisenberg k V), ((form_commutator_H1 k V) (h.x, h.y)) (g.x, g.y) = 0:= by
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
    simp
    rw[Subgroup.mem_center_iff]
    intro g
    change (Heisen_mul g h = Heisen_mul h g)
    unfold Heisen_mul
    simp
    rw[H.1, H.2]
    simp
    rw [@AddCommMonoidWithOne.add_comm]


def kHV_map (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
  k → Heisenberg k V := fun z => ⟨ z, 0, 0⟩

def HVVVstar_map (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
  Heisenberg k V → V × Module.Dual k V := fun H => ⟨H.x, H.y⟩

def Heisen_exact_sequence (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
  Function.Exact (kHV_map k V) (HVVVstar_map k V) := by
  refine Function.Exact.of_comp_of_mem_range rfl ?_
  intro H h1
  rw [@Set.mem_range]
  rw[HVVVstar_map] at h1
  use H.z
  rw[kHV_map]
  change ((H.x, H.y) = (0,0)) at h1
  apply Prod.mk.inj at h1
  ext
  · simp
  · rw[h1.1]
  · rw[h1.2]


noncomputable def Heisen_isoFun (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Module.IsReflexive k V] (H : Heisenberg k V) : Heisenberg k (Module.Dual k V) :=
  ⟨H.z, H.y , ((Module.evalEquiv k V).toFun (-H.x)) ⟩

noncomputable def Heisen_isoFunInv (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Module.IsReflexive k V] (H : Heisenberg k (Module.Dual k V)) : Heisenberg k V:=
  ⟨H.z, ((Module.evalEquiv k V).invFun (-H.y)) , H.x⟩

noncomputable def Heisen_equiv_dual (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Module.IsReflexive k V] :
  Heisenberg k V ≃Heisenberg k (Module.Dual k V) := by
  refine Equiv.mk (fun a ↦ Heisen_isoFun k V a ) (fun a ↦ Heisen_isoFunInv k V a) ?_ ?_
  · intro H
    simp
    rw[Heisen_isoFun, Heisen_isoFunInv]
    simp
    ext
    · simp
    · rw[<-Module.evalEquiv_toLinearMap,@LinearEquiv.symm_apply_eq]
      simp
    · simp
  · intro H
    simp
    rw[Heisen_isoFun, Heisen_isoFunInv]
    simp
    ext
    · simp
    · rw[<-Module.evalEquiv_toLinearMap]
    · simp

noncomputable def Heisen_mul_equiv_dual_opp (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Module.IsReflexive k V] :
  Heisenberg k V ≃* (Heisenberg k (Module.Dual k V))ᵐᵒᵖ := by
  refine MulEquiv.mk (Equiv.trans (Heisen_equiv_dual k V) (MulOpposite.opEquiv)) ?_
  intro H1 H2
  simp
  rw [← @MulOpposite.op_mul,MulOpposite.op_inj]
  change ((Heisen_equiv_dual k V) (Heisen_mul H1 H2) = Heisen_mul ((Heisen_equiv_dual k V) H2) ((Heisen_equiv_dual k V) H1))
  rw[Heisen_equiv_dual]
  simp
  rw[Heisen_isoFun,Heisen_isoFun,Heisen_isoFun]
  rw[Heisen_mul, Heisen_mul]
  simp
  constructor
  ·
    sorry
  · rw [@AddCommMonoid.add_comm]

theorem Heisenberg_commutator {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] (H1 H2 : Heisenberg k V) :
  ⁅H1, H2⁆ = ⟨ H1.y (H2.x) - H2.y (H1.x), 0, 0 ⟩ := by
  rw [@commutatorElement_def]
  change ((Heisen_mul (Heisen_mul (Heisen_mul H1 H2) (Heisen_mul_invdef H1)) (Heisen_mul_invdef H2)) = { z := H1.y H2.x - H2.y H1.x, x := 0, y := 0 })
  rw[Heisen_mul,Heisen_mul, Heisen_mul, Heisen_mul_invdef, Heisen_mul_invdef]
  simp
  ring

theorem Heisenberg_commutator_set_ne_zero (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]:
  lowerCentralSeries (Heisenberg k V) 1 ≠ ⊥ :=by
  rw[lowerCentralSeries,lowerCentralSeries_zero,<-commutator_def,commutator_eq_normalClosure,Subgroup.normalClosure]
  simp
  use ⟨1, 0, 0⟩
  constructor
  · rw[commutatorSet, Group.conjugatesOfSet]
    simp
    use ⟨0,0,0⟩
    have h1 : ∃ (y : Module.Dual k V), - y 0 = 1 := by
      sorry
    obtain ⟨h11,h12⟩ := h1
    use ⟨ 0,0, h11⟩
    unfold conjugatesOf IsConj SemiconjBy
    refine Set.mem_setOf.mpr ?_
    use 1
    simp
    rw[Heisenberg_commutator]
    ring_nf
    rw [← h12]
    simp
  · push_neg
    by_contra hf
    sorry


--def tau (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ζ : (FDRep k ↥(Subgroup.center (Heisenberg k V))).character) (hζ : ζ ≠ 1):
  --AddChar k (k) := by

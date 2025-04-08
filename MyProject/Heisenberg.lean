import MyProject.convention_dual
import Mathlib

variable (V k : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Module.IsReflexive k V]

local notation "q" => Fintype.card k

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

variable {V K}
--Le centre du groupe d'Heisenberg définit ci-dessus est un sous-groupe de Heisenberg
instance center_is_subgroup : Subgroup (Heisenberg V k) :=
{ carrier := center V k,
  one_mem' := by
    simp
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
  Subgroup.center (Heisenberg V k) = center V k := by
  ext h
  constructor
  · intro h1
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at h1
    change ( ∀ (g : Heisenberg V k), mul g h = mul h g) at h1
    unfold mul at h1
    simp at h1
    ring_nf at h1
    simp at h1
    have h11 : ∀ (g : Heisenberg V k), ((form_commutator_H1 k V) (h.x, h.y)) (g.x, g.y) = 0 ∧ g.x + h.x = h.x + g.x ∧ g.y + h.y = h.y + g.y :=by
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
    have h13 : ∀ (g : Heisenberg V k), ((form_commutator_H1 k V) (h.x, h.y)) (g.x, g.y) = 0:= by
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
    change (mul g h = mul h g)
    unfold mul
    simp
    rw[H.1, H.2]
    simp
    rw [@AddCommMonoidWithOne.add_comm]

variable (V)
--Fonction de k dans Heisenberg
def kHV_map :
  k → Heisenberg V k := fun z => ⟨z, 0, 0⟩

--Fonction de Heisenberg dans V × V*
def HVVVstar_map :
  Heisenberg V k → V × Module.Dual k V := fun H => ⟨H.x, H.y⟩

--Définition de la suite exact 0 → k → Heisenberg → V × V* → 0
def Heisen_exact_sequence :
  Function.Exact (kHV_map V k) (HVVVstar_map V k) := by
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

variable{V k}
--Définition du commutateur de deux éléments
theorem commutator (H1 H2 : Heisenberg V k) :
  ⁅H1, H2⁆ = ⟨ H1.y (H2.x) - H2.y (H1.x), 0, 0 ⟩ := by
  rw [@commutatorElement_def]
  change ((mul (mul (mul H1 H2) (inverse H1)) (inverse H2)) = { z := H1.y H2.x - H2.y H1.x, x := 0, y := 0 })
  rw[mul,mul, mul, inverse, inverse]
  simp
  ring

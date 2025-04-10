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
    rw[Subgroup.mem_center_iff]
    intro g
    change (mul g h = mul h g)
    unfold mul
    simp
    rw[H.1, H.2]
    simp
    rw [@AddCommMonoidWithOne.add_comm]


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
 omit [FiniteDimensional k V] in theorem commutator_of_elements (H1 H2 : Heisenberg V k) :
  ⁅H1, H2⁆ = ⟨ H1.y (H2.x) - H2.y (H1.x), 0, 0 ⟩ := by
  rw [@commutatorElement_def]
  change ((mul (mul (mul H1 H2) (inverse H1)) (inverse H2)) = { z := H1.y H2.x - H2.y H1.x, x := 0, y := 0 })
  rw[mul,mul, mul, inverse, inverse]
  simp
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
  simp at hf
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
  simp

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
    rw[Subgroup.closure] at hx
    simp at hx
    specialize hx ⊥
    rw [← @Subgroup.mem_bot]
    apply hx
    intro u hu
    obtain ⟨p, hp, q, hq⟩ := hu
    rw[Heisenberg.commutator_of_elements] at hq
    simp
    change (u = ⟨0,0,0⟩)
    rw[<-hq]
    simp
    rw[((Heisenberg.commutator_caracterisation p) hp).1, ((Heisenberg.commutator_caracterisation p) hp).2]
    simp


#min_imports

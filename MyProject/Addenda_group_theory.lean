import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.MulOppositeLemmas
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic.Group


/-!
# Addenda to the group theory in mathlib

This file adds some basic results about group theory and more specificially finite group
quotiented by their center.


## Main results
We create the set of representatives of `G⧸ (Subgroup.center G)` and verify the properties that this
set is suppose to satisfy.
We then introduce two maps `G_to_syst` and `G_to_center` that associated to every `g : G` its
representatives and its `Subgroup.center G` parts.

## Contents
+ `system_of_repr_center.set G` : the set of representatives of `G⧸ (Subgroup.center G)`.
+ `G_to_syst G` : the map that associated to every `g : G` its representative.
+ `G_to_center G` : the map that associated to every `g : G` the elements `h : Subgroup.center G` such
   that `g = gg*h` where `gg : system_of_repr_center.set G`.
+ `system_of_repr_center.set_center_iso_G` and `system_of_repr_center.set_center_iso_G_sigma` which are
   bijections between `G` and the cartesian product of `system_of_repr_center.set G` and `Subgroup.center G`
   as a cartesian product and as a `Sigma` type.
-/

open Classical
variable (k G : Type*) [Field k] [Group G]
variable (H : Subgroup G) [IsMulCommutative H]

/--An element of type `Subgroup.center G` commutes with every element of type `G`.-/
theorem center_mul_comm (g : G) (h : Subgroup.center G) : h * g = g * h := by
    have := @Subgroup.mem_center_iff G _ h
    simp only [SetLike.coe_mem, true_iff] at this
    exact (this g).symm

/--`simp` lemma associated to `center_mul_comm`.-/
@[simp]
theorem center_mul (h : Subgroup.center G) (a b : G) (h1 : h =a * b) : h = b*a := by
  have h2 := mul_inv_eq_of_eq_mul h1
  rw[center_mul_comm] at h2
  rw[<-h2]
  simp only [mul_inv_cancel_left]


namespace system_of_repr_center

abbrev set: Set G := by
  exact Set.range (@Quotient.out G (QuotientGroup.con (Subgroup.center G)).toSetoid )

/--A set of representatives of the classes of `G⧸ (Subgroup.center G)`.-/
noncomputable instance [Finite G] : Fintype G := by
  exact Fintype.ofFinite G

instance [Finite G] : Finite H := Subgroup.instFiniteSubtypeMem H

/--`system_of_rep_center_set` is finite.-/
instance finite (h : Finite G) : Finite (system_of_repr_center.set G) := by
  exact Finite.Set.finite_range Quot.out

/-`system_of_rep_center_set` is a system of representatives for the classes, ie `g≠g'` implies
classes are different-/
theorem classes_disjoint (g g' : G) (hG : g ∈ (system_of_repr_center.set G)) (hG': g' ∈ system_of_repr_center.set G) :
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
    rw [MulAction.mem_orbit_iff]
    use (hg⁻¹ * hg')
    rw [mul_smul,<-h1]
    simp only [inv_smul_smul]
  have := MulAction.orbit_eq_iff.mpr h2
  obtain ⟨yg,hG⟩ := hG
  obtain ⟨yg',hG'⟩ := hG'
  rw[<-hG,<-hG'] at this
  rw[<-hG,<-hG']
  rw[Quotient.out_inj]
  refine Quotient.out_equiv_out.mp ?_
  rw[hG,hG']
  exact h2



/--Union of the classes of elements of `system_of_repr_center.set` is the whole group.-/
theorem classes_union_eq_univ : Set.univ = ⋃ (g ∈ system_of_repr_center.set G), {x | (QuotientGroup.con (Subgroup.center G)).toSetoid x g} := by
  simp only [Set.mem_range, Con.rel_eq_coe, Set.iUnion_exists, Set.iUnion_iUnion_eq']
  unfold QuotientGroup.con QuotientGroup.leftRel
  simp
  refine Set.ext ?_
  intro x
  constructor
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    use Quotient.mk ((QuotientGroup.con (Subgroup.center G)).toSetoid) x
    exact id (Setoid.symm' (QuotientGroup.con (Subgroup.center G)).toSetoid
      (@Quotient.mk_out _ ((QuotientGroup.con (Subgroup.center G)).toSetoid) x))
  · intro hx
    simp only [Set.mem_univ]

/--`system_of_repr_center G` is equivalent to the image of the application `G → G⧸ (Subgroup.center G)`. -/
noncomputable def set_bij [Finite G] : system_of_repr_center.set G ≃ Finset.image (Quotient.mk (QuotientGroup.con (Subgroup.center G)).toSetoid) Finset.univ := by
  unfold system_of_repr_center.set
  simp
  refine Equiv.mk ?_ ?_ ?_ ?_
  · intro x
    obtain ⟨x1,hx1⟩ := x
    simp only [Set.mem_range] at hx1
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
    simp only [Set.mem_range] at hu
    simp only [Subtype.mk.injEq]
    conv=> rhs; rw[<-hu.choose_spec]
  · intro u
    obtain ⟨u,hu⟩ := u
    simp only [Quotient.out_inj, choose_eq]

/--A function that associates to every element `g:G` the corresponding representative in `system_of_repr_center.set`. -/
noncomputable def G_to_syst: G → ↑(system_of_repr_center.set G) := by
      intro g
      unfold system_of_repr_center.set
      refine ⟨ Quotient.out (Quotient.mk ((QuotientGroup.con (Subgroup.center G)).toSetoid) g), by simp⟩


/--If `h : Subgroup.center G`, then `G_to_syst G (g*h) = G_to_syst G g` for every `g:G`.-/
@[simp]
theorem G_to_syst_simp (g : G) (h : Subgroup.center G) : G_to_syst G (g * h) = G_to_syst G g := by
  unfold G_to_syst
  simp only [id_eq, Subtype.mk.injEq, Quotient.out_inj, Quotient.eq, Con.rel_eq_coe]
  unfold QuotientGroup.con QuotientGroup.leftRel MulAction.orbitRel MulAction.orbit
  simp only [Set.mem_range, Subtype.exists, Subgroup.mk_smul, MulOpposite.smul_eq_mul_unop,
    Subgroup.mem_op, exists_prop, MulOpposite.exists, MulOpposite.unop_op, Con.rel_mk,
    mul_right_inj, exists_eq_right, SetLike.coe_mem]


/--A function that associates to every element `g:G` the corresponding `z : Subgroup.center G` sucht that
`Quotient.out ↑g = g * z`.-/
noncomputable def G_to_center : G → Subgroup.center G := by
      intro u
      exact ((QuotientGroup.mk_out_eq_mul (Subgroup.center G) u).choose)⁻¹


/--Decomposition of an element `g:G` into a product of an element of `Subgroup.center G` by an element of `G`.-/
theorem G_to_center_simp (g : G) : g = Quotient.out ((Quotient.mk ((QuotientGroup.con (Subgroup.center G)).toSetoid) g)) * (G_to_center G g) := by
  change g = ⟦g⟧.out * ((QuotientGroup.mk_out_eq_mul (Subgroup.center G) g).choose)⁻¹
  simp
  rw [eq_mul_inv_iff_mul_eq]
  have := QuotientGroup.mk_out_eq_mul (Subgroup.center G) g
  rw[<-this.choose_spec]
  congr



/--`G_to_center_simp` written with `G_to_syst` and `G_to_center`.-/
theorem G_eq_G_to_center_G_to_syst_simp (g : G) : g = (G_to_syst G g) * (G_to_center G g) := by
  unfold G_to_syst
  simp
  exact G_to_center_simp G g


/--Commutativity of the product of `G_to_center G g` and `G_to_syst G g` for every `g : G`.-/
theorem G_to_center_to_syst_comm (g : G) : (G_to_center G g) * (G_to_syst G g).1 = (G_to_syst G g) * (G_to_center G g) := by
  exact center_mul_comm G (↑(G_to_syst G g)) (G_to_center G g)


/--`G_to_center_to_syst_simp` written with `G_to_center` on the right side of the equality.-/
theorem G_to_center_eq_G_G_to_syst_simp (g : G) : (G_to_center G g) = g * (G_to_syst G g).1⁻¹ := by
  conv=> rhs;lhs;rw[G_eq_G_to_center_G_to_syst_simp G g]
  conv=> rhs;lhs; rw [<-G_to_center_to_syst_comm G g]
  group



/--If `g : system_of_repr_center.set G` then `G_to_center G g.1` is equal to the neutral of the
group. -/
@[simp]
theorem G_to_center_syst_apply_simp (g : system_of_repr_center.set G): G_to_center G (g.1) = 1 := by
  unfold system_of_repr_center.set at g
  conv_lhs => change ((QuotientGroup.mk_out_eq_mul (Subgroup.center G) g).choose)⁻¹
  simp only [inv_eq_one]
  have : ∃ (y :  Quotient (QuotientGroup.con (Subgroup.center G)).toSetoid), y.out = g := by
    refine Set.mem_range.mp ?_
    exact Subtype.coe_prop g
  rw[<-this.choose_spec]
  simp only [Quotient.out_eq, left_eq_mul, OneMemClass.coe_eq_one, choose_eq]


/--If `g : system_of_repr_center.set G` then `G_to_syst G g` is equal to `g`. -/
@[simp]
theorem G_to_syst_simp_id (g : system_of_repr_center.set G) : G_to_syst G g = g := by
  have := G_eq_G_to_center_G_to_syst_simp G g.1
  simp only [G_to_center_syst_apply_simp, OneMemClass.coe_one, mul_one] at this
  exact SetCoe.ext (id (Eq.symm this))


/--For every `g:G` and `h : Subgroup.center G`, we have the following identity :
`G_to_center G (g*h) = h * G_to_center G g`. -/
@[simp]
theorem G_to_center_mul_simp (g : G) (h : Subgroup.center G) : G_to_center G (g * h) = h * G_to_center G g := by
  have h1 := G_to_center_eq_G_G_to_syst_simp G g
  have h2 := G_to_center_eq_G_G_to_syst_simp G (g*h)
  conv at h2 => rhs; rhs; rhs; rhs; rw[G_to_syst_simp G g h]
  conv at h2 => rhs; lhs; rw[<-center_mul_comm]
  conv at h2 => rhs;rw[mul_assoc]; rhs; rw[<-h1]
  exact SetLike.coe_eq_coe.mp h2



theorem G_to_syst_mul (g : G) (gbar : system_of_repr_center.set G) : G_to_syst G (g * gbar) = G_to_syst G (G_to_syst G g * gbar) := by
  conv=> lhs; rhs; lhs; rw[G_eq_G_to_center_G_to_syst_simp G g]
  conv=> lhs;rhs; lhs; rw[<-center_mul_comm]
  conv=> lhs;rhs;rw[mul_assoc];rw[center_mul_comm]
  conv=>lhs; rw[G_to_syst_simp]



/--`G` is equivalent to the cartesian product of its center and `system_of_repr_center.set G`.-/
noncomputable def set_center_iso_G : G ≃  Subgroup.center G × system_of_repr_center.set G := by
  refine Equiv.mk (fun g => (G_to_center G g,G_to_syst G g)) (fun g => g.2*g.1.1) ?_ ?_
  · intro g
    exact Eq.symm (G_eq_G_to_center_G_to_syst_simp G g)
  · intro g
    simp only [G_to_center_mul_simp, G_to_center_syst_apply_simp, mul_one, G_to_syst_simp,
      G_to_syst_simp_id, Prod.mk.eta]

/--`system_of_repr_center.set_center_iso_G` written for `Sigma` types instead of cartesian product.-/
noncomputable def set_center_iso_G_sigma : (_ : ↥(Subgroup.center G)) × ↑(system_of_repr_center.set G) ≃ G := by
  refine (Equiv.mk ?_ ?_ ?_ ?_).symm
  · intro g
    refine Std.Internal.List.Prod.toSigma ?_
    exact system_of_repr_center.set_center_iso_G G g
  · intro g
    exact (system_of_repr_center.set_center_iso_G G).invFun (g.fst,g.snd)
  · intro g
    simp only [Equiv.invFun_as_coe]
    unfold system_of_repr_center.set_center_iso_G
    simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
    rw[Std.Internal.List.Prod.toSigma]
    exact Eq.symm (G_eq_G_to_center_G_to_syst_simp G g)
  · intro g
    simp only [Equiv.invFun_as_coe, Equiv.apply_symm_apply]
    exact rfl


/--`system_of_repr_center.set_center_iso_G` written as sets.-/
theorem set_center_eq_G : @Set.univ G = { g.1 * h | (g : system_of_repr_center.set G) (h : Subgroup.center G)} := by
  refine Set.ext ?_
  intro x
  constructor
  · intro hx
    dsimp
    use (G_to_syst G x)
    use (G_to_center G x)
    exact (G_eq_G_to_center_G_to_syst_simp G x).symm
  · simp only [Subtype.exists, exists_prop, Set.mem_range, exists_exists_eq_and, Set.mem_setOf_eq,
    Set.mem_univ, implies_true]

noncomputable def equiv_perm_fun (g : G) : (system_of_repr_center.set G) → (system_of_repr_center.set G):= by
  exact (fun gi => G_to_syst G (g*gi))


theorem equiv_perm_fun_apply (g : G) : ∀ (gi : system_of_repr_center.set G), g*gi.1 = equiv_perm_fun G g gi * G_to_center G (g*gi.1) := by
  intro gi
  unfold equiv_perm_fun
  exact G_eq_G_to_center_G_to_syst_simp G (g*gi)

noncomputable def equiv_perm (g : G) : Equiv.Perm (system_of_repr_center.set G) := by
  unfold Equiv.Perm
  refine Equiv.mk ?_ ?_ ?_ ?_
  · exact equiv_perm_fun G g
  · exact (fun gbar => G_to_syst G (g⁻¹*gbar))
  · intro x
    simp
    have := equiv_perm_fun_apply G g x
    have : ↑(equiv_perm_fun G g x) = g * ↑x * (↑(G_to_center G (g * ↑x)))⁻¹ := by
      rw[this]
      simp only [G_to_center_mul_simp, G_to_center_syst_apply_simp, mul_one, mul_inv_cancel_right]
    rw[this]
    group
    simp only [Int.reduceNeg, zpow_neg, zpow_one]
    have  h1 := G_to_syst_simp G x ((↑(G_to_center G (g * ↑x)))⁻¹)
    rw[<-G_to_syst_simp_id G x]
    conv => rhs; rw[<-h1]
    simp only [G_to_syst_simp_id, InvMemClass.coe_inv]
  · intro x
    have := equiv_perm_fun_apply G g ((G_to_syst G (g⁻¹ * ↑x)))
    unfold equiv_perm_fun
    have h2 :  g⁻¹ * ↑x * ↑(G_to_center G (g⁻¹ * ↑x))⁻¹ = ↑(G_to_syst G (g⁻¹ * ↑x)):= by
      rw[(G_eq_G_to_center_G_to_syst_simp G ((g⁻¹ * ↑x)))]
      simp only [G_to_center_mul_simp, G_to_center_syst_apply_simp, mul_one, InvMemClass.coe_inv,
        mul_inv_cancel_right, G_to_syst_simp, G_to_syst_simp_id]
    conv=> lhs; rhs;rhs; rw[<-h2]
    conv=> lhs;rhs;rw[<-mul_assoc];simp only [mul_inv_cancel_left, InvMemClass.coe_inv]
    have := G_to_syst_simp G x (↑(G_to_center G (g⁻¹ * ↑x)))⁻¹
    conv=> rhs;rw[<-G_to_syst_simp_id G x]
    rw[<-this]
    simp only [InvMemClass.coe_inv]

theorem equiv_perm_exists (g : G) : ∃ (σ : Equiv.Perm (system_of_repr_center.set G)), ∀ (gbar : system_of_repr_center.set G), g*gbar= (σ gbar) * G_to_center G (g*gbar) := by
  use equiv_perm G g
  intro gbar
  exact equiv_perm_fun_apply G g gbar

#min_imports

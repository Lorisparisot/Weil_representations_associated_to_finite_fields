import Mathlib.Algebra.AddTorsor.Defs
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.FreeModule.PID

variable (V k : Type*) [Field k] [AddCommGroup V] [Module k V]

--local notation "q" => Fintype.card k

/- Ce projet LEAN se veut être une tentative de formalisation du papier
"Weil representations associated to finite fields" de Paul Gérardin.
Ce premier fichier contient les conventions de l'auteur sur le dual ainsi que
diverses propriétés à ce propos.
-/

--On définie la forme bilinéaire (V* x V**) → k, (y,x) ↦ - x y
def convention_dual : Module.Dual k (Module.Dual k V) →ₗ[k] (Module.Dual k V) →ₗ[k] k := by
  refine LinearMap.mk₂ k (fun x y => - x y) ?_ ?_ ?_ ?_
  · intro m n f
    simp
    ring
  · intro c m n
    simp
  · intro m n1 n2
    simp
    ring
  · intro c m n
    simp

--ajout d'un lemme simp pour faciliter les calculs.
@[simp]
theorem convention (v : Module.Dual k V) (φ : Module.Dual k (Module.Dual k V)) :
  convention_dual V k φ v = - φ v := by
  unfold convention_dual
  simp

--On définit l'application V → V**
def convention_eval : V →ₗ[k] Module.Dual k (Module.Dual k V):=by
  refine LinearMap.mk ?_ ?_
  · refine AddHom.mk ?_ ?_
    · exact fun x => - LinearMap.id.flip x
    · intro x y
      rw [map_add, neg_add_rev,@eq_add_neg_iff_add_eq,neg_add_cancel_comm]
  · intro m v
    simp

--Lemme simp pour faciliter les calculs
@[simp]
theorem convention_eval_apply (v : V) (φ :(Module.Dual k V)) : ((convention_eval V k) v) φ = - φ v := by
  rw[convention_eval]
  simp

--V est isomorphe à V** par l'application convention_eval
/-- The bijection between a reflexive module and its double dual such that (x,y)=-(y,x), bundled as a `LinearEquiv`. -/
noncomputable def convention_eval_iso [Module.IsReflexive k V] : V ≃ₗ[k] Module.Dual k (Module.Dual k V) := by
  refine LinearEquiv.mk ?_ ?_ ?_ ?_
  · exact convention_eval V k
  · exact (fun x => - ((Module.evalEquiv k V).invFun (x)))
  · intro x
    rw [@neg_eq_iff_eq_neg]
    simp
    symm
    refine (LinearEquiv.eq_symm_apply (Module.evalEquiv k V)).mpr ?_
    rw[convention_eval]
    simp
    rw[Module.Dual.eval]
  · intro x
    simp
    rw[convention_eval]
    simp
    rw [@LinearMap.ext_iff]
    intro φ
    simp

--Lemme simp pour faciliter les calculs
@[simp]
theorem convention_eval_iso_apply [FiniteDimensional k V] (v : V) (φ :(Module.Dual k V)) : ((convention_eval_iso V k) v) φ = - φ v := by
  rw [← convention_eval_apply]
  exact rfl

--alias de Module.evalEquiv pour notre convention

noncomputable def form_commutator [Module.IsReflexive k V] : (V × Module.Dual k V) →ₗ[k] (V × Module.Dual k V) →ₗ[k] k := by
  refine LinearMap.mk₂ k (fun H1 H2 => H1.2.toFun H2.1 + (convention_dual V k ((Module.evalEquiv k V).toFun (H1.1)) H2.2)) ?_ ?_ ?_ ?_
  · intro m1 m2 n
    simp
    ring
  · intro c m n
    simp
    ring
  · intro m n1 n2
    simp
    ring
  · intro c m n
    simp
    ring

instance form_commutator_non_degenerate [Module.IsReflexive k V]:
  LinearMap.BilinForm.Nondegenerate (form_commutator V k) := by
  rw[LinearMap.BilinForm.Nondegenerate ]
  by_contra hf
  push_neg at hf
  obtain ⟨m, hm⟩ := hf
  cases hm with
  | intro left right =>
    unfold form_commutator at left
    simp at left
    have left1 := left
    rw[forall_comm] at left
    specialize left 0
    simp at left
    have hh : m.2 = 0 := by
      exact LinearMap.ext_iff.mpr left
    rw[hh] at left1
    simp only [LinearMap.zero_apply, zero_add, forall_const] at left1
    have hhhh : m.1 = 0:= by
      rw[<-Module.forall_dual_apply_eq_zero_iff k]
      intro φ
      specialize left1 φ
      rw [neg_eq_zero] at left1
      exact left1
    apply right
    exact Prod.ext hhhh hh

/-def form_commutator_H (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
  (H1 : V × Module.Dual k V) (H2 : V × Module.Dual k V) : k :=
  H1.2.toFun H2.1 - H2.2.toFun H1.1

def form_commutator_H1 (k V : Type*) [Field k] [AddCommGroup V] [Module k V] :
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

instance non_degenerate_form_H (k V : Type*) [Field k]  [AddCommGroup V] [Module k V] [FiniteDimensional k V]:
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
      rw[<-Module.forall_dual_apply_eq_zero_iff k]
      exact left1
    apply right
    exact Prod.ext hhhh hh
-/

import Mathlib.Algebra.AddTorsor.Defs
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.FreeModule.PID

variable (V k : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Module.IsReflexive k V]

local notation "q" => Fintype.card k

/- Ce projet LEAN se veut être une tentative de formalisation du papier
"Weil representations associated to finite fields" de Paul Gérardin.
Ce premier fichier contient les conventions de l'auteur sur le dual ainsi que
diverses propriétés à ce propos.
-/



def bracket_bilinear : (Module.Dual k V) →ₗ[k] (Module.Dual k (Module.Dual k V)) →ₗ[k] k := by
  refine LinearMap.mk₂ k (fun y x => - x y) ?_ ?_ ?_ ?_
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

--def bracketbis : LinearMap.BilinForm k ((Module.Dual k V)) := by



#check bracket_bilinear

--def identification : Module.Dual k V ≃ₗ[k] Module.Dual k (Module.Dual k V) := by


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
      rw[<-Module.forall_dual_apply_eq_zero_iff k]
      exact left1
    apply right
    exact Prod.ext hhhh hh

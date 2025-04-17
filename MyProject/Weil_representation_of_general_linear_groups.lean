import MyProject.convention_dual
import MyProject.Heisenberg
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Character
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Group.AddChar


variable (V k : Type u) [inst1 : Field k] [inst2 : AddCommGroup V] [inst3 : Module k V] [inst4 : FiniteDimensional k V]

def Hom_k_to_center : AddChar k ((Subgroup.center (Heisenberg V k))) := by
    refine AddChar.mk ?_ ?_ ?_
    · exact (fun z => ⟨⟨z, 0, 0⟩, by
        rw [Heisenberg.center_eq, Heisenberg.center_is_subgroup]; simp; rw[Heisenberg.center]; simp ⟩ )
    · simp
      ext u
      simp
      · change (0 = Heisenberg.z ⟨0,0,0⟩)
        simp
      · change (0 = Heisenberg.x ⟨0,0,0⟩)
        simp
      · simp
        change (0 = (Heisenberg.y ⟨0,0,0⟩) u)
        simp
    sorry

def tau (ζ : MonoidHom (Subgroup.center (Heisenberg V k)) Complex) (h : ζ ≠ 1) : AddHom k k := by
  refine AddHom.mk ?_ ?_
  · exact (fun z => ζ ⟨(Hom_k_to_center z), by
      -- Prove that Hom_k_to_center z belongs to the center
      simp [Subgroup.center, Heisenberg.center]
    ⟩)
  · intro a b
    simp

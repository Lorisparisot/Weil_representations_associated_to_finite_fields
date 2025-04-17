import MyProject.convention_dual
import MyProject.Heisenberg
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Character

variable (V k : Type*) [inst1 : Field k] [inst2 : AddCommGroup V] [inst3 : Module k V] [inst4 : FiniteDimensional k V]
x&
instance k_addgroup : AddCommGroup k := by
    exact AddCommGroupWithOne.toAddCommGroup




def tau (a : k) (A : FDRep k (Heisenberg k V)) (ζ : FDRep.character k (↥Subgroup.center (Heisenberg V k))) [hζ : Nontrivial ζ] :
    (FDRep k k).character := by

sorry

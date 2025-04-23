import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib


variable (k G W : Type*) [inst1 : Field k] [inst2 : Group G] [inst3 : AddCommGroup W] [inst4 : Finite G]
[inst5 : Module k W] [inst6 : FiniteDimensional k W]
variable (H : @Subgroup G inst2)
variable (θ : Representation k H W)

namespace Representation_induced

noncomputable def kHModule1 : MonoidAlgebra k H →ₐ[k] Module.End k W := by
  exact Representation.asAlgebraHom θ

#check (MonoidAlgebra k H)
#check (MonoidAlgebra k G)

-- Si H est subgroup de G, alors on a une SMul de MonoidAlgebra k H sur MonoidAlgebra k G
/-noncomputable instance SMulKHKG : SMul (MonoidAlgebra k H) (MonoidAlgebra k G) := by
  refine SMul.mk ?_
  intro ph pg
  let f := Finsupp.sum ph fun (a₁ : H) (b₁ : k) => Finsupp.sum pg fun (a₂ : G) (b₂ : k) => MonoidAlgebra.single (((Subgroup.subtype H ) a₁) * a₂) (b₁ * b₂)
  exact f-/


noncomputable def mapHG : H → G :=
  fun h => (Subgroup.subtype H) h

@[simp]
theorem mapHG_eval (h : H) : mapHG G H h = ↑h:= by
  rfl

#check mapHG

noncomputable def Map_KHKG : (MonoidAlgebra k H) → (MonoidAlgebra k G) := by
  intro h
  have h1 := MonoidAlgebra.mapDomain (mapHG G H) h
  exact h1

noncomputable def test : (MonoidAlgebra k H) →+* (MonoidAlgebra k G) := by
  refine RingHom.mk ?_ ?_ ?_
  · refine MonoidHom.mk ?_ ?_
    · refine OneHom.mk (Map_KHKG k G H) ?_
      · rw [@MonoidAlgebra.one_def]
        rw [@MonoidAlgebra.one_def]
        rw[Map_KHKG, MonoidAlgebra.mapDomain]
        simp
    · simp
      intro x y
      rw [@MonoidAlgebra.mul_def,@MonoidAlgebra.mul_def]
      rw[Map_KHKG,Map_KHKG, Map_KHKG, MonoidAlgebra.mapDomain,MonoidAlgebra.mapDomain,MonoidAlgebra.mapDomain]
      simp
      rw[Finsupp.sum,Finsupp.sum,Finsupp.mapDomain,Finsupp.mapDomain,Finsupp.mapDomain]
      simp
      unfold Finsupp.sum
      simp

      sorry
  · simp
    rw[Map_KHKG]
    simp
  · intro x y
    simp
    rw [@MonoidAlgebra.ext_iff]
    intro g
    rw[Map_KHKG,Map_KHKG,Map_KHKG]
    rw[MonoidAlgebra.mapDomain,MonoidAlgebra.mapDomain,MonoidAlgebra.mapDomain]
    rw[Finsupp.mapDomain,Finsupp.mapDomain,Finsupp.mapDomain]
    simp
    rw[Finsupp.sum,Finsupp.sum,Finsupp.sum]

    sorry



noncomputable instance SMulKHKG1 : SMul (MonoidAlgebra k H) (MonoidAlgebra k G) := by
  refine SMul.mk ?_
  intro h
  intro g
  exact (Map_KHKG k G H h)*g



noncomputable instance HMulKHKG1 : MulAction (MonoidAlgebra k H) (MonoidAlgebra k G) := by
  refine MulAction.mk ?_ ?_
  · intro b
    rw[@HSMul.hSMul,instHSMul,SMul.smul,SMulKHKG1]
    simp
    rw[Map_KHKG,@MonoidAlgebra.one_def]
    simp
    rw [@MonoidAlgebra.ext_iff]
    intro x
    rw [@MonoidAlgebra.single_one_mul_apply,one_mul]
  · intro x y b
    rw [@MonoidAlgebra.mul_def]
    simp
    rw[HSMul.hSMul,instHSMul,SMul.smul,SMulKHKG1]
    simp
    rw[Map_KHKG,Map_KHKG,Map_KHKG,MonoidAlgebra.mapDomain,MonoidAlgebra.mapDomain,MonoidAlgebra.mapDomain]
    rw[Finsupp.mapDomain,Finsupp.mapDomain,Finsupp.mapDomain]
    simp
    rw[Finsupp.sum,Finsupp.sum,Finsupp.sum,Finsupp.sum]
    rw [@MonoidAlgebra.mul_def,@MonoidAlgebra.mul_def,@MonoidAlgebra.mul_def]
    simp
    rw[Finsupp.sum,Finsupp.sum,Finsupp.sum]
    simp
    sorry


noncomputable instance MulActionKHKG : MulAction (MonoidAlgebra k H) (MonoidAlgebra k G) := by
  refine MulAction.mk ?_ ?_
  · intro b
    rw[@HSMul.hSMul]
    rw[instHSMul]
    simp
    rw[SMul.smul]
    rw[SMulKHKG]
    simp
    rw [@MonoidAlgebra.one_def]
    simp
    rw[Finsupp.sum]
    rw[Finsupp.support]
    change ((∑ a ∈ b.support, Finsupp.single a 1 * Finsupp.single a (b a)) = b)
    rw [@MonoidAlgebra.ext_iff]
    intro x
    rw[Finsupp.finset_sum_apply]
    change (∑ i ∈ b.support, (((Finsupp.single i 1) x) * ((Finsupp.single i (b i)) x) )  = b x)
    by_cases h1 : x=1
    rw[h1]
    change (∑ i ∈ b.support, ((Finsupp.single i 1) 1) * (fun₀ | i => b i) 1 = b 1)
    have h2 : ∀ i ∈ b.support, Decidable (i = 1) := by
      intro i hi
      exact Classical.propDecidable (i = 1)
    have h3 := ∀ i ∈ b.support, Decidable (i = 1) → ((Finsupp.single i 1) 1 = if i = 1 then 1 else 0) := by
      sorry

      sorry
    sorry
  · intro x y b
    rw[@HSMul.hSMul]
    rw[instHSMul]
    simp
    rw[SMul.smul]
    rw[SMulKHKG]
    simp
    rw[Finsupp.sum]
    rw [@MonoidAlgebra.mul_def]
    simp
    rw [@Finsupp.sum_comm]

    sorry


noncomputable instance DistribMulActionKHKG : DistribMulAction (MonoidAlgebra k H) (MonoidAlgebra k G) := by
  refine DistribMulAction.mk ?_ ?_
  · intro a
    rw[@HSMul.hSMul]
    rw[instHSMul]
    simp
    rw[SMul.smul]
    rw[MulAction.toSMul, MulActionKHKG]
    simp
    rw[SMulKHKG]
    simp
  · intro a x y
    rw[@HSMul.hSMul]
    rw[instHSMul]
    simp
    rw[SMul.smul]
    rw[MulAction.toSMul, MulActionKHKG]
    simp
    rw[SMulKHKG]
    simp
    rw[Finsupp.sum]
    sorry


noncomputable instance KGisKHmodule : Module (MonoidAlgebra k H) (MonoidAlgebra k G) := by
  refine Module.mk ?_ ?_
  · intro r s x
    rw[@HSMul.hSMul]
    rw[instHSMul]
    simp
    rw[SMul.smul]
    rw[MulAction.toSMul]
    rw[DistribMulAction.toMulAction, DistribMulActionKHKG]
    simp
    rw[MulActionKHKG]
    simp
    rw[SMulKHKG]
    simp
    rw[Finsupp.sum]
    sorry
  · intro x
    rw[@HSMul.hSMul]
    rw[instHSMul]
    simp
    rw[SMul.smul]
    rw[MulAction.toSMul]
    rw[DistribMulAction.toMulAction,DistribMulActionKHKG]
    simp
    rw[MulActionKHKG]
    simp
    rw[SMulKHKG]
    simp

instance KHisRing : Ring (MonoidAlgebra k h) := by

sorry

def KGModule := TensorProduct (MonoidAlgebra k H) (MonoidAlgebra k G) (Representation.asModule θ)
  sorry

end Representation_induced

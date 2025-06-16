import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Data.Set.Disjoint

namespace kG_kH_Module

variable (k G : Type*) [inst1 : Field k] [inst2 : Group G]
variable (H : @Subgroup G inst2) [instH : IsMulCommutative H]


omit instH in
/--The trivial map from `MonoidAlgebra k H` to `MonoidAlgebra k G`, ie elements from
`MonoidAlgebra k H` are seen as `MonoidAlgebra k G`.-/
noncomputable def Map_KHKG : (MonoidAlgebra k H) →+* (MonoidAlgebra k G) := by
  exact  MonoidAlgebra.mapDomainRingHom k H.subtype


theorem center_mul_com (g : G) (h : Subgroup.center G) : h * g = g * h := by
    have := @Subgroup.mem_center_iff G _ h
    simp only [SetLike.coe_mem, true_iff] at this
    exact (this g).symm



/--`Map_KHKG` is indeed an injective map.-/
instance Map_KHKG_inj : Function.Injective (Map_KHKG k G H) := by
  unfold Map_KHKG
  have h1 := @MonoidAlgebra.mapDomain_injective k H G _ (Subgroup.subtype H) (Subgroup.subtype_injective H )
  exact h1

omit instH in
/--`Map_KHKG` is indeed a `k` linear map.-/
@[simp]
theorem Map_KHKG_k_linear (c : k) (x : MonoidAlgebra k H): (Map_KHKG k G H) (c • x) = c • ((Map_KHKG k G H) x) := by
    unfold Map_KHKG
    simp only [MonoidAlgebra.mapDomainRingHom_apply, Subgroup.coe_subtype, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, Finsupp.mapDomain.addMonoidHom_apply]
    rw[Finsupp.mapDomain_smul]

omit instH in
@[simp]
theorem Map_KhKG_single_apply (h : H) (c:k) : (Map_KHKG k G H) (MonoidAlgebra.single h c) = MonoidAlgebra.single ↑h c := by
  unfold Map_KHKG
  simp only [MonoidAlgebra.mapDomainRingHom_apply, Subgroup.coe_subtype, ZeroHom.toFun_eq_coe,
    AddMonoidHom.toZeroHom_coe, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]


omit instH in
/--Coercion from `MonoidAlgebra k H` to `MonoidAlgebra k G` when `H` is a subgroup of `G`-/
noncomputable instance Coe : CoeOut (MonoidAlgebra k H) (MonoidAlgebra k G) := by
  refine { coe := Map_KHKG k G H }

/--If `G`is commutative, then `MonoidAlgebra k G` is a commutative semiring.-/
noncomputable instance KGCommRing [instG : CommGroup G] : CommSemiring (MonoidAlgebra k G) := by
  exact MonoidAlgebra.commSemiring

omit instH in
/--Scalar multiplication between `MonoidAlgebra k H` and `MonoidAlgebra k G`, ie
classical mulitplication between an element of `MonoidAlgebra k H` seen as an element
of `MonoidAlgebra k G` and an element of `MonoidAlgebra k G`.-/
noncomputable instance SMulKHKG : SMul (MonoidAlgebra k H) (MonoidAlgebra k G) := by
  refine SMul.mk (fun h g => (Map_KHKG k G H h)*g)

omit instH in
/--Ring morphism from `MonoidAlgebra k H` to `MonoidAlgebra k G`, given by the coercion
of element of `H`into element of `G`.-/
noncomputable def RingMorphism_KH_KG : (MonoidAlgebra k H) →+* (MonoidAlgebra k G) := by
  exact Map_KHKG k G H

/--`MonoidAlgebra k G` is a `MonoidAlgebra k (Subgroup.center G)` algebra.-/
noncomputable instance KG_is_KcenterG_Algebra : Algebra (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k G) := by
  refine Algebra.mk (RingMorphism_KH_KG k G (Subgroup.center G)) ?_ ?_
  · intro pH pG
    ext x
    rw[RingMorphism_KH_KG,Map_KHKG,MonoidAlgebra.mapDomainRingHom_apply, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, Finsupp.mapDomain.addMonoidHom_apply,Subgroup.coe_subtype,
      @MonoidAlgebra.mul_apply_right,@MonoidAlgebra.mul_apply_left]
    congr
    rw [funext_iff]
    intro g1
    rw[funext_iff]
    intro k1
    rw[Finsupp.mapDomain,Finsupp.sum]
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
    rw [@Finset.mul_sum,@Finset.sum_mul]
    congr
    rw[funext_iff]
    intro x1
    rw[mul_comm,mul_eq_mul_left_iff]
    left
    rw [@Finsupp.single_eq_set_indicator]
    by_cases hf : (x * g1⁻¹) = x1
    · have hf1 : (g1⁻¹ * x) = x1 :=by
        rw [@inv_mul_eq_iff_eq_mul,((@Subgroup.mem_center_iff G _ x1).mp (SetLike.coe_mem x1)),
        mul_eq_of_eq_mul_inv (id (Eq.symm hf))]
      rw[hf,hf1]
    · push_neg at hf
      rw [← @Finset.not_mem_singleton] at hf
      rw [Set.indicator,@ite_eq_iff]
      right
      constructor
      · refine Set.not_mem_singleton_iff.mpr ?_
        rw [Finset.mem_singleton] at hf
        exact hf
      · rw[Set.indicator,@eq_ite_iff]
        right
        simp only [Set.mem_singleton_iff, and_true]
        by_contra hff
        apply hf
        rw [Finset.mem_singleton,@mul_inv_eq_iff_eq_mul,<-((@Subgroup.mem_center_iff G _ x1).mp (SetLike.coe_mem x1)),mul_eq_of_eq_inv_mul (id (Eq.symm hff))]
  · intro pH pG
    rw[HSMul.hSMul,instHSMul,RingMorphism_KH_KG,Map_KHKG,MonoidAlgebra.mapDomainRingHom_apply, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, Finsupp.mapDomain.addMonoidHom_apply]
    exact rfl

/--If we have a homomorphism `H →* Subgroup.center G`, then we have `Algebra (MonoidAlgebra k H) (MonoidAlgebra k G)`. -/
noncomputable instance KG_is_KH_Algebra (ϕ : H →* Subgroup.center G) : Algebra (MonoidAlgebra k H) (MonoidAlgebra k G):= by
  exact Algebra.compHom (MonoidAlgebra k G) (MonoidAlgebra.mapDomainRingHom k ϕ)

open Classical
@[simp]
theorem center_commutes_single (x : MonoidAlgebra k (Subgroup.center G)) (g : G) : Map_KHKG k G (Subgroup.center G) x * MonoidAlgebra.single (g : G) (1:k) = MonoidAlgebra.single (g) (1:k) * x := by
  unfold MonoidAlgebra.single Map_KHKG
  simp
  unfold Finsupp.mapDomain
  rw[Finsupp.sum]
  rw [@MonoidAlgebra.ext_iff]
  intro x1
  simp
  conv => lhs; rhs;intro a;rw[Finsupp.single_apply]
  conv => rhs; rhs; intro a; rw[Finsupp.single_apply]
  congr
  ext a
  have : ↑a = x1 * g⁻¹ ↔ ↑a = g⁻¹ * x1 := by
    constructor
    · intro ha
      exact center_mul G a x1 g⁻¹ ha
    · intro ha
      exact center_mul G a g⁻¹ x1 ha
  exact if_ctx_congr this (congrFun rfl) (congrFun rfl)

end kG_kH_Module

namespace test

variable (k G W : Type*) [inst1 : Field k] [inst2 : Group G] [inst3 : Finite G]
[inst4 : AddCommGroup W] [inst5 : Module k W]

variable (H : @Subgroup G inst2) [instH : IsMulCommutative H]

variable (θ : Representation k (Subgroup.center G) W)

open DirectSum

#check G⧸ H

/-- The fact that `S : Set G` is empty or not is a decidable property.-/
noncomputable instance decidable_empty (S : Set G) : Decidable S.Nonempty := by
  exact Classical.propDecidable S.Nonempty

/--The set of representatives of the classes of `G⧸ (Subgroup.center G)`.-/
abbrev system_of_repr_center_set : Set G := by
  exact Set.range (@Quotient.out G (QuotientGroup.con (Subgroup.center G)).toSetoid )


/--`system_of_rep_center_set` is finite.-/
instance system_of_repr_center_set_is_finite : Finite (system_of_repr_center_set G) := by
  exact Finite.Set.finite_range Quot.out

/--`system_of_rep_center_set` is a system of representatives for the classes, ie `g≠g'` implies
classes are different-/
theorem system_of_repr_center_set_disjoint (g g' : G) (hG : g ∈ (system_of_repr_center_set G)) (hG': g' ∈ system_of_repr_center_set G) :
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
    rw [@MulAction.mem_orbit_iff]
    use (hg⁻¹ * hg')
    rw [@mul_smul,<-h1]
    simp only [inv_smul_smul]
  have := MulAction.orbit_eq_iff.mpr h2
  simp at hG hG'
  sorry

omit inst3 in
theorem system_of_repr_center_set_union : Set.univ = ⋃ (g ∈ system_of_repr_center_set G), {x | (QuotientGroup.con (Subgroup.center G)).toSetoid x g} := by
  simp only [Set.mem_range, Con.rel_eq_coe, Set.iUnion_exists, Set.iUnion_iUnion_eq']
  unfold QuotientGroup.con QuotientGroup.leftRel
  simp
  refine Set.ext ?_
  intro x
  constructor
  · intro hx
    simp
    use Quotient.mk ((QuotientGroup.con (Subgroup.center G)).toSetoid) x
    exact id (Setoid.symm' (QuotientGroup.con (Subgroup.center G)).toSetoid
      (@Quotient.mk_out _ ((QuotientGroup.con (Subgroup.center G)).toSetoid) x))
  · intro hx
    simp only [Set.mem_univ]

open Classical
noncomputable def system_of_repr_center_set_bij : system_of_repr_center_set G ≃ Finset.image (Quotient.mk (QuotientGroup.con (Subgroup.center G)).toSetoid) Finset.univ := by
  unfold system_of_repr_center_set
  simp
  refine Equiv.mk ?_ ?_ ?_ ?_
  · intro x
    obtain ⟨x1,hx1⟩ := x
    simp at hx1
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
    simp at hu
    simp only [Subtype.mk.injEq]
    conv=> rhs; rw[<-hu.choose_spec]
  · intro u
    obtain ⟨u,hu⟩ := u
    simp only [Quotient.out_inj, choose_eq]


noncomputable instance hmul_g_kH_kG : HMul G (MonoidAlgebra k (Subgroup.center G)) (MonoidAlgebra k G) := by
  refine { hMul := ?_ }
  intro g kH
  exact (MonoidAlgebra.of k G g) * kH

noncomputable instance hmul_g_kG : HMul G (MonoidAlgebra k G) (MonoidAlgebra k G) := by
  refine { hMul := ?_ }
  intro g kH
  exact (MonoidAlgebra.of k G g) * kH

omit inst3 in
theorem hmul_g_kH_kG_simp (g : G) (kH : MonoidAlgebra k (Subgroup.center G)) : (hmul_g_kH_kG k G).hMul g kH = (MonoidAlgebra.single g (1 : k)) * kH := by
  exact rfl

@[simp]
noncomputable instance hmul_g_kH_kG_distrib (g : G) (x y : MonoidAlgebra k (Subgroup.center G)) : g * (x + y) = g*x + g*y := by
  unfold HMul.hMul hmul_g_kH_kG
  simp
  exact
    LeftDistribClass.left_distrib (MonoidAlgebra.single g 1)
      ((kG_kH_Module.Map_KHKG k G (Subgroup.center G)) x)
      ((kG_kH_Module.Map_KHKG k G (Subgroup.center G)) y)


noncomputable def gkh_map (g : G) : MonoidAlgebra k (Subgroup.center G) →ₗ[k] MonoidAlgebra k G := by
 exact @Finsupp.lmapDomain (Subgroup.center G) k k _ _ _ G (fun x => g*x)

/--The set `g*MonoidAlgebra k (Subgroup.center G)` for `g` in `G`.-/
noncomputable def gkH_set (g : G) : Submodule k (MonoidAlgebra k G) := by
  exact LinearMap.range (gkh_map k G g)

omit inst3 in
@[simp]
theorem gkh_map_eq (g : G) (x : MonoidAlgebra k (Subgroup.center G)) : gkh_map k G g x = g * x := by
  unfold gkh_map
  rw[Finsupp.lmapDomain]
  conv => lhs; change (Finsupp.mapDomain (fun (a : Subgroup.center G) => g*a) x)
  rw[Finsupp.mapDomain]
  rw[Finsupp.sum]
  have : ∀ (i : G),∀ (u : MonoidAlgebra k (Subgroup.center G)),∀ (h : Subgroup.center G), MonoidAlgebra.single (i * ↑h) (u h) = MonoidAlgebra.single i (1:k) * MonoidAlgebra.single h (u h) := by
    intro i h u
    simp only [kG_kH_Module.Map_KhKG_single_apply, MonoidAlgebra.single_mul_single, one_mul]
  unfold MonoidAlgebra.single at this
  unfold hmul_g_kH_kG
  simp
  specialize this g x
  conv=> lhs; rhs; intro a; rw[this a]
  rw[<-(Finset.mul_sum (x.support) (fun a => (kG_kH_Module.Map_KHKG k G (Subgroup.center G)) (Finsupp.single a (x a))) (Finsupp.single g 1))]
  simp
  congr


noncomputable instance (g:G) : Function.Injective (gkh_map k G g) := by
  refine Finsupp.mapDomain_injective ?_
  intro x y
  simp only [mul_right_inj, SetLike.coe_eq_coe, imp_self]


/--The set `g*MonoidAlgebra k (Subgroup.center G)` for `g` in `G`.-/
noncomputable def gkH_set (g : G) : Submodule k (MonoidAlgebra k G) := by
  exact LinearMap.range (gkh_map k G g)

omit inst3 in
@[simp]
theorem gkh_map_gkh_set (x : gkH_set k G g) : gkh_map k G g (x.2.choose) = x := by
  simp
  have := x.2.choose_spec
  simp at this
  exact this
#check MonoidAlgebra k G

noncomputable instance gkH_set_SMul : SMul (MonoidAlgebra k ↥(Subgroup.center G)) ↥(gkH_set k G g) := by
  refine SMul.mk ?_
  intro x ⟨y,hy⟩
  refine ⟨kG_kH_Module.Map_KHKG k G (Subgroup.center G) x * y,?_⟩
  unfold gkH_set
  simp
  use x*hy.choose
  conv=> lhs;change (g * (kG_kH_Module.Map_KHKG k G (Subgroup.center G)) (x * Exists.choose hy))
  rw[map_mul]
  conv=> rhs;rw[<-hy.choose_spec]
  unfold hmul_g_kG
  simp
  conv=> lhs;rw[<-mul_assoc,<-kG_kH_Module.center_commutes_single k G,mul_assoc]
  conv => rhs;rhs;unfold HMul.hMul hmul_g_kH_kG;simp


noncomputable instance gkH_set_MulAction : MulAction (MonoidAlgebra k ↥(Subgroup.center G)) ↥(gkH_set k G g) := by
  refine MulAction.mk ?_ ?_
  · intro b
    obtain ⟨b,hb⟩ := b
    unfold gkH_set_SMul HSMul.hSMul instHSMul SMul.smul
    simp
  · intro x y ⟨b,hb⟩
    unfold HSMul.hSMul instHSMul SMul.smul gkH_set_SMul
    simp
    rw[mul_assoc]


noncomputable instance gkH_set_DistribMulAction : DistribMulAction (MonoidAlgebra k ↥(Subgroup.center G)) ↥(gkH_set k G g) := by
  refine DistribMulAction.mk ?_ ?_
  · intro a
    unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul gkH_set_MulAction gkH_set_SMul
    simp
  · intro a ⟨b,hb⟩ ⟨c,hc⟩
    unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul gkH_set_MulAction gkH_set_SMul
    simp
    unfold kG_kH_Module.Map_KHKG
    simp
    rw [@left_distrib]

noncomputable instance : Module (MonoidAlgebra k (Subgroup.center G)) (gkH_set k G g) := by
  refine Module.mk ?_ ?_
  · intro r s ⟨x,hx⟩
    unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul DistribMulAction.toMulAction
      gkH_set_DistribMulAction gkH_set_MulAction gkH_set_SMul
    simp
    exact
      RightDistribClass.right_distrib ((kG_kH_Module.Map_KHKG k G (Subgroup.center G)) r)
        ((kG_kH_Module.Map_KHKG k G (Subgroup.center G)) s) x
  · intro ⟨x,hx⟩
    unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul DistribMulAction.toMulAction
      gkH_set_DistribMulAction gkH_set_MulAction gkH_set_SMul
    simp


end test

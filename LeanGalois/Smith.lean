import LeanGalois.Lemma4
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# Smith-steget: varje övertorus nås med lyft och basbyte

`lattice_smith`: varje delgitter `Λ ⊆ ℤ²` av rang 2 är `φ(d₁ℤ × d₂ℤ)` för en basbyte `φ ∈ GL₂(ℤ)` och
`d₁, d₂ ≥ 1` (Smiths normalform, ur Mathlib).

`cover_reachable`: nätet på `T_Λ`, i Smith-koordinater `φ ∘ (lyft d₂ i Z) ∘ (lyft d₁ i X) ∘ φ⁻¹`, nås från
`G` med `CoverStep`. Lyft i `Z` är lyft i `X` mellan två koordinatbyten.
-/

noncomputable section

open Module

/-- **Smiths normalform för delgitter i `ℤ²`.** -/
theorem lattice_smith (Λ : Submodule ℤ (ℤ × ℤ)) (h : finrank ℤ Λ = 2) :
    ∃ φ : ℤ × ℤ ≃+ ℤ × ℤ, ∃ d₁ d₂ : ℕ, d₁ ≠ 0 ∧ d₂ ≠ 0 ∧
      ∀ v, v ∈ Λ ↔ ∃ x y : ℤ, v = φ (d₁ * x, d₂ * y) := by
  have h' : finrank ℤ Λ = finrank ℤ (ℤ × ℤ) := by rw [h]; simp
  obtain ⟨b', a, ab', hab⟩ := Submodule.exists_smith_normal_form_of_rank_eq (Basis.finTwoProd ℤ) h'
  let ψ : (ℤ × ℤ) ≃ₗ[ℤ] (ℤ × ℤ) := (Basis.finTwoProd ℤ).equiv b' (Equiv.refl _)
  have hψ : ∀ x y : ℤ, ψ (x, y) = x • b' 0 + y • b' 1 := by
    intro x y
    have : ((x, y) : ℤ × ℤ) = x • (Basis.finTwoProd ℤ) 0 + y • (Basis.finTwoProd ℤ) 1 := by simp
    rw [this, map_add, map_zsmul, map_zsmul]
    simp only [ψ, Basis.equiv_apply, Equiv.refl_apply]
  have ha : ∀ i, a i ≠ 0 := by
    intro i hi
    have h0 : (ab' i : ℤ × ℤ) = 0 := by rw [hab, hi, zero_smul]
    exact ab'.ne_zero i (Subtype.ext h0)
  refine ⟨ψ.toAddEquiv, (a 0).natAbs, (a 1).natAbs, Int.natAbs_ne_zero.2 (ha 0),
    Int.natAbs_ne_zero.2 (ha 1), fun v => ⟨?_, ?_⟩⟩
  · intro hv
    have hrep := ab'.sum_repr ⟨v, hv⟩
    rw [Fin.sum_univ_two] at hrep
    have hv' : v = (ab'.repr ⟨v, hv⟩ 0 * a 0) • b' 0 + (ab'.repr ⟨v, hv⟩ 1 * a 1) • b' 1 := by
      have := congrArg Subtype.val hrep
      simp only [Submodule.coe_add, Submodule.coe_smul, hab, smul_smul] at this
      exact this.symm
    refine ⟨(a 0).sign * ab'.repr ⟨v, hv⟩ 0, (a 1).sign * ab'.repr ⟨v, hv⟩ 1, ?_⟩
    change v = ψ _
    rw [hψ]
    refine hv'.trans ?_
    congr 2
    · linear_combination (-(ab'.repr ⟨v, hv⟩ 0)) * Int.sign_mul_natAbs (a 0)
    · linear_combination (-(ab'.repr ⟨v, hv⟩ 1)) * Int.sign_mul_natAbs (a 1)
  · rintro ⟨x, y, rfl⟩
    change ψ _ ∈ Λ
    rw [hψ]
    have key : ∀ i (c : ℤ), (((a i).natAbs : ℤ) * c) • b' i = ((a i).sign * c) • (ab' i : ℤ × ℤ) := by
      intro i c
      rw [hab, smul_smul]
      congr 1
      linear_combination (-c) * Int.mul_sign_self (a i)
    rw [key 0, key 1]
    exact Λ.add_mem (Λ.smul_mem _ (ab' 0).2) (Λ.smul_mem _ (ab' 1).2)

/-- Byte av koordinaterna `X ↔ Z`. -/
def swapZ : ℤ × ℤ ≃+ ℤ × ℤ := AddEquiv.prodComm

/-- Lyft i `Z`-riktningen. -/
def Net.liftZ (d : ℕ) [NeZero d] (G : Net ℝ) : Net ℝ :=
  ((G.transform swapZ.toAddMonoidHom).liftX d).transform swapZ.toAddMonoidHom

/-- Nätet på övertorusen `T_Λ` med `Λ = φ(d₁ℤ × d₂ℤ)`. -/
def Net.coverSmith (φ : ℤ × ℤ ≃+ ℤ × ℤ) (d₁ d₂ : ℕ) [NeZero d₁] [NeZero d₂] (G : Net ℝ) : Net ℝ :=
  (((G.transform φ.symm.toAddMonoidHom).liftX d₁).liftZ d₂).transform φ.toAddMonoidHom

/-- **Varje övertorus nås med `CoverStep`.** -/
theorem cover_reachable (φ : ℤ × ℤ ≃+ ℤ × ℤ) (d₁ d₂ : ℕ) [NeZero d₁] [NeZero d₂] (G : Net ℝ) :
    Relation.ReflTransGen CoverStep G (G.coverSmith φ d₁ d₂) := by
  unfold Net.coverSmith Net.liftZ
  open Relation.ReflTransGen in
  exact tail (tail (tail (tail (single (CoverStep.transform φ.symm G)) (CoverStep.lift d₁ _))
    (CoverStep.transform swapZ _)) (CoverStep.lift d₂ _)) (CoverStep.transform swapZ _) |>.tail
    (CoverStep.transform φ _)

/-- **Sats 10.1 för alla övertorusar.** Om `G` nås från snub square med lokala drag och övertorusbyten
(i synnerhet om `G` är nätet på någon `T_Λ` över ett sådant nät, `cover_reachable`), så är `G` inte minimalt. -/
theorem sats_10_1_smith (F : Subfield ℝ) (l κ : ℝ) (hl0 : 0 < l) (hκ0 : 0 < κ)
    (hκ2 : κ ^ 2 = l * (l + 2)) (hlF : l ∈ F) (hκF : κ ∉ F)
    (IsMinimal IsGeodesic : Net ℝ → Prop)
    (Schrijver : ∀ G, IsMinimal G → ∃ G', Relation.ReflTransGen (LocalMove F) G G' ∧ IsGeodesic G')
    (Geo : ∀ G, IsGeodesic G → HasZigzags G)
    (G : Net ℝ) (hG : Relation.ReflTransGen (fun G G' => LocalMove F G G' ∨ CoverStep G G') (snubNet l) G)
    (Λ : Submodule ℤ (ℤ × ℤ)) (hΛ : finrank ℤ Λ = 2) :
    ∃ φ : ℤ × ℤ ≃+ ℤ × ℤ, ∃ d₁ d₂ : ℕ, ∃ _ : NeZero d₁, ∃ _ : NeZero d₂,
      (∀ v, v ∈ Λ ↔ ∃ x y : ℤ, v = φ (d₁ * x, d₂ * y)) ∧ ¬ IsMinimal (G.coverSmith φ d₁ d₂) := by
  obtain ⟨φ, d₁, d₂, h1, h2, hv⟩ := lattice_smith Λ hΛ
  have : NeZero d₁ := ⟨h1⟩
  have : NeZero d₂ := ⟨h2⟩
  refine ⟨φ, d₁, d₂, inferInstance, inferInstance, hv, ?_⟩
  apply sats_10_1_geo F l κ hl0 hκ0 hκ2 hlF hκF IsMinimal IsGeodesic Schrijver Geo
  exact hG.trans (Relation.ReflTransGen.mono (fun _ _ h => Or.inr h) _ _ (cover_reachable φ d₁ d₂ G))

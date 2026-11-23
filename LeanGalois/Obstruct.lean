import LeanGalois.Cover
import LeanGalois.Local
import LeanGalois.Concrete
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Galois-hindret som invariant, och Sats 10.1 på alla övertorusar

`Obstructed F P`: det finns en sida (normal `n ≠ 0`, nivå `k`) av Newtonpolygonen till `P`
med nollskilt sidpolynom `f` och en punkt `(x, z) ∈ (ℝˣ)²` med `f(x, z) = 0`, så att
`x^{s₁} z^{s₂} ∉ F` för varje `s ≠ 0` längs sidan. (För snub: `(x, z) = (1, t²)`.)

Invarianten bevaras av
* multiplikation med en konstant `c ≠ 0` (alla lokala drag),
* koordinatbyte `φ ∈ GL₂(ℤ)` (`Net.transform`),
* lyft `X ↦ X^d` till övertorusen (`Net.liftX`), via produktformeln över `ℂ`.

Och ett hindrat nät med konduktanser i `F` är aldrig minimalt (givet Lemma 4).
Med Smiths normalform fås varje övertorus `T_Λ` ur koordinatbyten och lyft `liftX`
(lyft i `Z`-led = byt koordinater, lyft, byt tillbaka); det steget är inte formaliserat.
-/

noncomputable section

open LP2 AddMonoidAlgebra

namespace LP2

section general
variable {K L : Type*} [CommRing K] [CommRing L]

lemma exists_coeff_ne_zero {p : LP2 K} (hp : p ≠ 0) : ∃ v, p.coeff v ≠ 0 := by
  have : p.coeff ≠ 0 := by simpa using hp
  obtain ⟨v, hv⟩ := Finsupp.ne_iff.1 this
  exact ⟨v, by simpa using hv⟩

lemma mapD_mapC (φ : ℤ × ℤ →+ ℤ × ℤ) (f : K →+* L) (p : LP2 K) :
    mapD φ (mapC f p) = mapC f (mapD φ p) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | single v a => simp [mapD_single, mapC_single]

lemma twist_one (p : LP2 K) : twist 1 p = p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => rw [map_add, hp, hq]
  | single v a => simp

lemma twist_ne_zero (ω : Kˣ) {p : LP2 K} (hp : p ≠ 0) : twist ω p ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_coeff_ne_zero hp
  intro h
  have := congrArg (fun q : LP2 K => q.coeff v) h
  simp only [coeff_twist, coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at this
  exact hv ((Units.mul_left_eq_zero _).1 this)

lemma mapC_ne_zero (f : K →+* L) (hf : Function.Injective f) {p : LP2 K} (hp : p ≠ 0) :
    mapC f p ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_coeff_ne_zero hp
  intro h
  have := congrArg (fun q : LP2 L => q.coeff v) h
  simp only [coeff_mapC, coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at this
  exact hv (hf (by rw [this, map_zero]))

lemma mapD_ne_zero (φ : ℤ × ℤ →+ ℤ × ℤ) (hφ : Function.Injective φ) {p : LP2 K} (hp : p ≠ 0) :
    mapD φ p ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_coeff_ne_zero hp
  intro h
  apply hv
  rw [← coeff_mapD_of_inj φ hφ p v, h]
  rfl

lemma isTop_of_mapC (f : K →+* L) (hf : Function.Injective f) {n : ℤ × ℤ} {k : ℤ} {p : LP2 K}
    (h : IsTop n k (mapC f p)) : IsTop n k p := by
  rw [isTop_iff] at *
  intro v hv
  apply hf
  rw [← coeff_mapC, h v hv, map_zero]

lemma evP_C (x z : Kˣ) (a : K) : evP x z (C a) = a := by
  simp [C_apply]

lemma evP_mono (x z : Kˣ) (v : ℤ × ℤ) : evP x z (mono v) = ((x ^ v.1 * z ^ v.2 : Kˣ) : K) := by
  simp [mono]

lemma evP_mapC (f : K →+* L) (x z : Kˣ) (p : LP2 K) :
    evP (Units.map f.toMonoidHom x) (Units.map f.toMonoidHom z) (mapC f p) = f (evP x z p) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | single v a =>
    rw [mapC_single, evP_single, evP_single, map_mul, ← map_zpow, ← map_zpow, ← map_mul,
      Units.coe_map]
    rfl

lemma evP_mapD (φ : ℤ × ℤ →+ ℤ × ℤ) (x z x' z' : Kˣ)
    (h : ∀ v, x' ^ (φ v).1 * z' ^ (φ v).2 = x ^ v.1 * z ^ v.2) (p : LP2 K) :
    evP x' z' (mapD φ p) = evP x z p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | single v a => rw [mapD_single, evP_single, evP_single, h]

/-- Toppsidan av en ändlig produkt. -/
lemma face_prod (n : ℤ × ℤ) {ι : Type*} (s : Finset ι) (p : ι → LP2 K) (k : ℤ)
    (h : ∀ i ∈ s, IsTop n k (p i)) :
    IsTop n (s.card * k) (∏ i ∈ s, p i) ∧
      faceAt n (s.card * k) (∏ i ∈ s, p i) = ∏ i ∈ s, faceAt n k (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul, Finset.prod_empty]
    have h1 : (1 : LP2 K) = single 0 1 := rfl
    rw [h1]
    exact ⟨isTop_single n 0 1 (by simp [dot]), faceAt_single_pos n 0 0 1 (by simp [dot])⟩
  | insert i s hi ih =>
    obtain ⟨ih1, ih2⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hk : ((Finset.card (insert i s) : ℕ) : ℤ) * k = k + (s.card : ℤ) * k := by
      rw [Finset.card_insert_of_notMem hi]; push_cast; ring
    rw [hk, Finset.prod_insert hi, Finset.prod_insert hi]
    obtain ⟨h1, h2⟩ := face_mul n (h i (Finset.mem_insert_self i s)) ih1
    exact ⟨h1, by rw [h2, ih2]⟩

end general

end LP2

/-! ## Invarianten -/

/-- Värdet av tecknet `v ↦ x^{v₁} z^{v₂}`. -/
abbrev chi (x z : ℝˣ) (v : ℤ × ℤ) : ℝ := ((x ^ v.1 * z ^ v.2 : ℝˣ) : ℝ)

/-- Galois-hindret för ett Laurentpolynom. -/
def Obstructed (F : Subfield ℝ) (P : LP2 ℝ) : Prop :=
  ∃ n : ℤ × ℤ, n ≠ 0 ∧ ∃ k : ℤ, IsTop n k P ∧ faceAt n k P ≠ 0 ∧
    ∃ x z : ℝˣ, evP x z (faceAt n k P) = 0 ∧
      ∀ s : ℤ × ℤ, s ≠ 0 → dot n s = 0 → chi x z s ∉ F

namespace Obstructed

variable {F : Subfield ℝ}

lemma C_mul {P : LP2 ℝ} (h : Obstructed F P) {c : ℝ} (hc : c ≠ 0) : Obstructed F (C c * P) := by
  obtain ⟨n, hn, k, htop, hf, x, z, hev, hs⟩ := h
  refine ⟨n, hn, k, isTop_C_mul n k c htop, ?_, x, z, ?_, hs⟩
  · rw [faceAt_C_mul]
    refine mul_ne_zero ?_ hf
    rw [C_apply]; simpa using hc
  · rw [faceAt_C_mul, map_mul, hev, mul_zero]

/-- Koordinatbyte med `φ ∈ GL₂(ℤ)`. -/
lemma mapD_equiv {P : LP2 ℝ} (h : Obstructed F P) (φ : ℤ × ℤ ≃+ ℤ × ℤ) :
    Obstructed F (mapD φ.toAddMonoidHom P) := by
  obtain ⟨n, hn, k, htop, hf, x, z, hev, hs⟩ := h
  -- `ψ = (φ⁻¹)ᵀ`: `⟨ψ n, φ v⟩ = ⟨n, v⟩`
  set ψn : ℤ × ℤ := (dot n (φ.symm (1, 0)), dot n (φ.symm (0, 1))) with hψn
  have hdot_lin : ∀ a b : ℤ × ℤ, dot n (a + b) = dot n a + dot n b := by
    intro a b; simp only [dot, Prod.fst_add, Prod.snd_add]; ring
  have hdot_smul : ∀ (m : ℤ) (a : ℤ × ℤ), dot n (m • a) = m * dot n a := by
    intro m a; simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hdecomp : ∀ w : ℤ × ℤ, w = w.1 • ((1 : ℤ), (0 : ℤ)) + w.2 • ((0 : ℤ), (1 : ℤ)) := by
    intro w; ext <;> simp
  have hψ : ∀ w : ℤ × ℤ, dot ψn w = dot n (φ.symm w) := by
    intro w
    conv_rhs => rw [hdecomp w]
    rw [map_add, map_zsmul, map_zsmul, hdot_lin, hdot_smul, hdot_smul, hψn]
    simp only [dot]; ring
  have hφ : ∀ v, dot ψn (φ.toAddMonoidHom v) = dot n v := by
    intro v; rw [hψ]; simp
  have hψ0 : ψn ≠ 0 := by
    intro h0
    apply hn
    have h1 := hφ (1, 0)
    have h2 := hφ (0, 1)
    rw [h0] at h1 h2
    simp only [dot, zero_mul, add_zero, Prod.fst_zero, Prod.snd_zero] at h1 h2
    exact Prod.ext (by simpa [dot] using h1.symm) (by simpa [dot] using h2.symm)
  -- ny punkt: `x' = χ(φ⁻¹ e₁)`, `z' = χ(φ⁻¹ e₂)`
  set χ : Multiplicative (ℤ × ℤ) →* ℝˣ :=
    { toFun := fun v => x ^ (Multiplicative.toAdd v).1 * z ^ (Multiplicative.toAdd v).2
      map_one' := by simp
      map_mul' := by
        intro a b
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, zpow_add]
        rw [mul_mul_mul_comm] } with hχ
  have hχv : ∀ v : ℤ × ℤ, χ (Multiplicative.ofAdd v) = x ^ v.1 * z ^ v.2 := fun v => rfl
  set x' := χ (Multiplicative.ofAdd (φ.symm (1, 0)))
  set z' := χ (Multiplicative.ofAdd (φ.symm (0, 1)))
  have hpt : ∀ w : ℤ × ℤ, x' ^ w.1 * z' ^ w.2 = χ (Multiplicative.ofAdd (φ.symm w)) := by
    intro w
    conv_rhs => rw [hdecomp w]
    rw [map_add, map_zsmul, map_zsmul, ofAdd_add, ofAdd_zsmul, ofAdd_zsmul, map_mul, map_zpow,
      map_zpow]
  have hev' : ∀ p : LP2 ℝ, evP x' z' (mapD φ.toAddMonoidHom p) = evP x z p := by
    apply evP_mapD
    intro v
    rw [hpt, ← hχv]
    simp
  refine ⟨ψn, hψ0, k, (isTop_mapD_iff ψn k _ φ.injective n hφ P).2 htop, ?_, x', z', ?_, ?_⟩
  · rw [faceAt_mapD ψn k _ n hφ]
    exact mapD_ne_zero _ φ.injective hf
  · rw [faceAt_mapD ψn k _ n hφ, hev', hev]
  · intro s hs0 hsn
    have : chi x' z' s = chi x z (φ.symm s) := by
      simp only [chi]; rw [hpt, hχv]
    rw [this]
    apply hs _ (by simpa using hs0)
    rw [← hψ]; exact hsn

end Obstructed

/-! ## Lyftet till övertorusen -/

lemma Net.liftX_mapCond {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) (d : ℕ) [NeZero d]
    (G : Net K) : ((G.liftX d).mapCond f).specPoly = ((G.mapCond f).liftX d).specPoly := by
  obtain ⟨n, E⟩ := G
  simp only [Net.liftX, Net.mapCond, List.map_flatMap, List.flatMap_map, List.map_ofFn]
  rfl

namespace Obstructed

variable {F : Subfield ℝ}

lemma scaleX_injective (d : ℕ) [NeZero d] : Function.Injective (Lift.scaleX d) := by
  intro v w h
  simp only [Lift.scaleX_apply, Prod.mk.injEq] at h
  have hd : (d : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne d
  exact Prod.ext (mul_left_cancel₀ hd h.1) h.2

/-- **Lyft `X ↦ X^d`** bevarar hindret (via produktformeln över `ℂ`). -/
lemma liftX {G : Net ℝ} (h : Obstructed F G.specPoly) (d : ℕ) [NeZero d] :
    Obstructed F (G.liftX d).specPoly := by
  obtain ⟨n, hn, k, htop, hf, x, z, hev, hs⟩ := h
  set ι : ℝ →+* ℂ := Complex.ofRealHom
  have hι : Function.Injective ι := Complex.ofReal_injective
  have hprim := Complex.isPrimitiveRoot_exp d (NeZero.ne d)
  set ζ : ℂˣ := (hprim.isUnit (NeZero.ne d)).unit
  have hζ : IsPrimitiveRoot (ζ : ℂ) d := by
    simpa [ζ, IsUnit.unit_spec] using hprim
  set P := G.specPoly
  set P' := (G.liftX d).specPoly
  set Q := mapD (Lift.scaleX d) P'
  have hQ : mapC ι Q = ∏ j : Fin d, twist (ζ ^ ((j : ℕ) : ℤ)) (mapC ι P) := by
    rw [← mapD_mapC, ← Net.specPoly_mapCond, Net.liftX_mapCond, specPoly_liftX d ζ hζ,
      Net.specPoly_mapCond]
  have hfp := face_prod n (Finset.univ : Finset (Fin d))
    (fun j => twist (ζ ^ ((j : ℕ) : ℤ)) (mapC ι P)) k
    (fun j _ => isTop_twist n k _ (isTop_mapC n k ι htop))
  rw [Finset.card_univ, Fintype.card_fin, ← hQ] at hfp
  obtain ⟨htopQ, hfaceQ⟩ := hfp
  set n' : ℤ × ℤ := ((d : ℤ) * n.1, n.2)
  have hφ : ∀ v, dot n (Lift.scaleX d v) = dot n' v := by
    intro v; simp only [dot, Lift.scaleX_apply, n']; ring
  have hn' : n' ≠ 0 := by
    intro h0
    apply hn
    have hd : (d : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne d
    have h1 : (d : ℤ) * n.1 = 0 := congrArg Prod.fst h0
    have h2 : n.2 = 0 := congrArg Prod.snd h0
    exact Prod.ext ((mul_eq_zero.1 h1).resolve_left hd) h2
  have htop' : IsTop n' ((d : ℤ) * k) P' :=
    (isTop_mapD_iff n _ _ (scaleX_injective d) n' hφ P').1 (isTop_of_mapC ι hι htopQ)
  have hface' : faceAt n ((d : ℤ) * k) Q = mapD (Lift.scaleX d) (faceAt n' ((d : ℤ) * k) P') :=
    faceAt_mapD n _ _ n' hφ P'
  have hmapface : mapC ι (faceAt n ((d : ℤ) * k) Q) =
      ∏ j : Fin d, twist (ζ ^ ((j : ℕ) : ℤ)) (mapC ι (faceAt n k P)) := by
    rw [← faceAt_mapC, hfaceQ]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [faceAt_twist, faceAt_mapC]
  refine ⟨n', hn', (d : ℤ) * k, htop', ?_, x ^ (d : ℤ), z, ?_, ?_⟩
  · intro h0
    have : mapC ι (faceAt n ((d : ℤ) * k) Q) = 0 := by rw [hface', h0, map_zero, map_zero]
    rw [hmapface] at this
    exact (Finset.prod_ne_zero_iff.2 fun j _ => twist_ne_zero _ (mapC_ne_zero ι hι hf)) this
  · have hpt : ∀ p, evP x z (mapD (Lift.scaleX d) p) = evP (x ^ (d : ℤ)) z p := by
      apply evP_mapD
      intro v
      simp only [Lift.scaleX_apply, zpow_mul]
    rw [← hpt, ← hface']
    apply hι
    rw [← evP_mapC, hmapface, map_prod, map_zero]
    apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin d))
    simp only [Fin.val_zero, Nat.cast_zero, zpow_zero, twist_one, evP_mapC, hev, map_zero]
  · intro s hs0 hsn
    have : chi (x ^ (d : ℤ)) z s = chi x z (Lift.scaleX d s) := by
      simp only [chi, Lift.scaleX_apply, zpow_mul]
    rw [this]
    apply hs
    · intro h0; exact hs0 (scaleX_injective d (by rw [h0, map_zero]))
    · rw [hφ]; exact hsn

/-! ## Hindrat ⇒ inte minimalt (givet Lemma 4) -/

theorem not_minimal (IsMinimal TwoDirections : Net ℝ → Prop)
    (H4 : ∀ G, IsMinimal G → TwoDirections G → SideSplits G)
    (H4deg : ∀ G, IsMinimal G → ¬ TwoDirections G → G.edges = [])
    (G : Net ℝ) (hGF : ∀ e ∈ G.edges, e.cond ∈ F) (h : Obstructed F G.specPoly) :
    ¬ IsMinimal G := by
  intro hmin
  obtain ⟨n, hn, k, htop, hf, x, z, hev, hs⟩ := h
  by_cases h2 : TwoDirections G
  · obtain ⟨s, hs0, hsn, c, hc, m, ε, hε, Ls, hLs, hsplit⟩ :=
      H4 G hmin h2 n k hn htop (two_monomials hf x z hev)
    rw [hsplit] at hev hf
    simp only [map_mul, map_list_prod, List.map_map, evP_C, evP_mono] at hev
    rcases mul_eq_zero.1 hev with h | hprod
    · rcases mul_eq_zero.1 h with h | h
      · exact hc h
      · exact Units.ne_zero _ h
    obtain ⟨⟨α, β⟩, hab, hy0⟩ := List.mem_map.1 (List.prod_eq_zero_iff.1 hprod)
    simp only [Function.comp, map_add, map_mul, evP_C, evP_mono] at hy0
    have hαF : α ∈ F := Galois.condProds_mem F G hGF α (hLs _ hab).1
    have hβF : β ∈ F := Galois.condProds_mem F G hGF β (hLs _ hab).2
    have hεF : ε ∈ F := by
      rcases hε with rfl | rfl
      · exact F.one_mem
      · exact F.neg_mem F.one_mem
    have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
    by_cases hβ : β = 0
    · subst hβ
      have hα : α = 0 := by simpa using hy0
      subst hα
      apply hf
      apply mul_eq_zero_of_right
      apply List.prod_eq_zero
      exact List.mem_map.2 ⟨(0, 0), hab, by simp⟩
    · apply hs s hs0 hsn
      have hchi : chi x z s = -α / (ε * β) := by
        field_simp
        linear_combination hy0
      rw [hchi]
      exact F.div_mem (F.neg_mem hαF) (F.mul_mem hεF hβF)
  · have hE := H4deg G hmin h2
    have hL : G.laplacian = 0 := by
      ext i j
      simp [Net.laplacian, hE]
    rw [Net.specPoly, hL] at hf hev
    rcases Nat.eq_zero_or_pos G.n with h | h
    · haveI : IsEmpty (Fin G.n) := by rw [h]; infer_instance
      rw [Matrix.det_isEmpty] at hf hev
      have h1 : (1 : LP2 ℝ) = single 0 1 := rfl
      rw [h1] at hf hev
      by_cases hk : dot n 0 = k
      · rw [faceAt_single_pos n k 0 1 hk, evP_single] at hev
        simp at hev
      · exact hf (faceAt_single_neg n k 0 1 hk)
    · haveI : Nonempty (Fin G.n) := ⟨⟨0, h⟩⟩
      rw [Matrix.det_zero] at hf
      exact hf (faceAt_zero n k)

end Obstructed

/-! ## Snub square är hindrat -/

open Galois in
theorem snub_obstructed (F : Subfield ℝ) (l κ : ℝ) (hl0 : 0 < l) (hκ0 : 0 < κ)
    (hκ2 : κ ^ 2 = l * (l + 2)) (hlF : l ∈ F) (hκF : κ ∉ F) :
    Obstructed F (snubNet l).specPoly := by
  set q : ℝ := 2 * (2 * l ^ 2 + 4 * l + 1) with hq
  set w : ℝ := (1 + l + κ) ^ 2 with hw_def
  have hw : w ≠ 0 := by positivity
  have hroot : 1 - q * w + w ^ 2 = 0 := by
    have htt : (1 + l + κ) * (1 + l - κ) = 1 := by linear_combination (-1 : ℝ) * hκ2
    have hsum : (1 + l + κ) ^ 2 + (1 + l - κ) ^ 2 = q := by
      rw [hq]; linear_combination (2 : ℝ) * hκ2
    have : w * (1 + l - κ) ^ 2 = 1 := by rw [hw_def, ← mul_pow, htt, one_pow]
    linear_combination w * hsum - this
  refine ⟨(1, 1), by decide, 2, snub_isTop l, ?_, 1, Units.mk0 w hw, ?_, ?_⟩
  · intro h0
    have := congrArg (fun p : LP2 ℝ => p.coeff (2, 0)) h0
    simp only [snub_face] at this
    rw [C_mul_mono] at this
    simp [mono, coeff_add, coeff_sub, coeff_single, Finsupp.single_apply] at this
  · rw [snub_face]
    simp only [map_add, map_sub, map_mul, evP_C, evP_mono]
    simp
    linear_combination hroot
  · intro s hs0 hsn
    have hs2 : s.2 ≠ 0 := by
      intro h
      apply hs0
      have : s.1 + s.2 = 0 := by simpa [dot] using hsn
      ext <;> simp_all
    simp only [chi, one_zpow, one_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    exact w_zpow_not_mem F l κ hl0 hκ0 hκ2 hlF hκF s.2 hs2

/-! ## Sats 10.1 med övertorusar -/

/-- Byte av torus: lyft `X ↦ X^d` eller koordinatbyte med `φ ∈ GL₂(ℤ)`. -/
inductive CoverStep : Net ℝ → Net ℝ → Prop
  | lift (d : ℕ) [NeZero d] (G : Net ℝ) : CoverStep G (G.liftX d)
  | transform (φ : ℤ × ℤ ≃+ ℤ × ℤ) (G : Net ℝ) : CoverStep G (G.transform φ.toAddMonoidHom)

lemma CoverStep.field_hyp (F : Subfield ℝ) {G G' : Net ℝ} (h : CoverStep G G') :
    (∀ e ∈ G.edges, e.cond ∈ F) → ∀ e ∈ G'.edges, e.cond ∈ F := by
  intro hG e he
  cases h with
  | lift d G =>
    obtain ⟨e₀, he₀, he'⟩ := List.mem_flatMap.1 he
    obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ _).1 he'
    exact hG e₀ he₀
  | transform φ G =>
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 he
    exact hG e₀ he₀

lemma CoverStep.obstructed {F : Subfield ℝ} {G G' : Net ℝ} (h : CoverStep G G')
    (hG : Obstructed F G.specPoly) : Obstructed F G'.specPoly := by
  cases h with
  | lift d G => exact hG.liftX d
  | transform φ G => rw [Net.specPoly_transform]; exact hG.mapD_equiv φ

/-- **Sats 10.1 på övertorusar.** Varje följd av lokala drag och torusbyten (lyft `X ↦ X^d`,
koordinatbyten i `GL₂(ℤ)`, i valfri ordning) från snub square slutar i ett icke-minimalt nät,
givet Lemma 4 (`H4`, `H4deg`). -/
theorem sats_10_1_cover (F : Subfield ℝ) (l κ : ℝ) (hl0 : 0 < l) (hκ0 : 0 < κ)
    (hκ2 : κ ^ 2 = l * (l + 2)) (hlF : l ∈ F) (hκF : κ ∉ F)
    (IsMinimal TwoDirections : Net ℝ → Prop)
    (H4 : ∀ G, IsMinimal G → TwoDirections G → SideSplits G)
    (H4deg : ∀ G, IsMinimal G → ¬ TwoDirections G → G.edges = [])
    (G : Net ℝ)
    (hreach : Relation.ReflTransGen (fun G G' => LocalMove F G G' ∨ CoverStep G G') (snubNet l) G) :
    ¬ IsMinimal G := by
  have key : (∀ e ∈ G.edges, e.cond ∈ F) ∧ Obstructed F G.specPoly := by
    induction hreach with
    | refl =>
      refine ⟨?_, snub_obstructed F l κ hl0 hκ0 hκ2 hlF hκF⟩
      change ∀ e ∈ snubEdges l, e.cond ∈ F
      simp [snubEdges, hlF]
    | tail _ hmove ih =>
      obtain ⟨hF', hO⟩ := ih
      rcases hmove with hm | hm
      · obtain ⟨c, hc, hP⟩ := hm.det_hyp
        exact ⟨hm.field_hyp F hF', hP ▸ hO.C_mul hc⟩
      · exact ⟨hm.field_hyp F hF', hm.obstructed hO⟩
  exact Obstructed.not_minimal IsMinimal TwoDirections H4 H4deg G key.1 key.2

/-- **Konkret**: snub square med alla konduktanser 1, rationella drag, alla övertorusar. -/
theorem sats_10_1_cover_snub_rat
    (IsMinimal TwoDirections : Net ℝ → Prop)
    (H4 : ∀ G, IsMinimal G → TwoDirections G → SideSplits G)
    (H4deg : ∀ G, IsMinimal G → ¬ TwoDirections G → G.edges = [])
    (G : Net ℝ)
    (hreach : Relation.ReflTransGen (fun G G' => LocalMove Qsub G G' ∨ CoverStep G G')
      (snubNet 1) G) :
    ¬ IsMinimal G := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  refine sats_10_1_cover Qsub 1 (Real.sqrt 3) one_pos (Real.sqrt_pos.2 (by norm_num)) ?_
    (Subfield.one_mem _) sqrt3_not_mem_Q IsMinimal TwoDirections H4 H4deg G hreach
  rw [Real.sq_sqrt h3]; norm_num

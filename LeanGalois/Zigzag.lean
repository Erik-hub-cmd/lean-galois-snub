import LeanGalois.TopDet
import LeanGalois.Block

/-!
# Lemma 4 steg 1(iv): toppsidan delas i binom

**Sicksackdata** (`ZigzagData`) för den täta matrisen `Δ^top`: raderna (utgångar) och kolonnerna
(ingångar) delas i block `a`, numrerade cykliskt `t = 0, …, m_a`. I block `a` har `Δ^top`
posten `-c·z^d` på platsen (utgång `t`, ingång `t`) ("jämna" kanter) och `-c'·z^{d'}` på
(utgång `t+1`, ingång `t`) ("udda" kanter); utanför blocken är `Δ^top` noll. Ett block med
`c' = 0` är en tvingad kant. Det är sicksackvägen `A₁B₁A₂B₂…` längs ett spår i steg 1(iv).

**Sats (`face_splits`)**: då är toppsidan `C c · z^M · ∏_a (α_a + ε_a β_a z^{s_a})` med
`α_a = ∏ c` (jämna), `β_a = ∏ c'` (udda), `ε_a = (-1)^{m_a}`, `s_a = Σ d' - Σ d`.
-/

noncomputable section

open LP2 Matrix AddMonoidAlgebra

variable {K : Type*} [Field K] {n : ℕ}

/-- Ringen som genereras av konduktanserna (innehåller `0` och alla produkter). -/
def Net.condRing (G : Net K) : Subring K := Subring.closure {c | ∃ e ∈ G.edges, e.cond = c}

/-- Sicksackdata för `Δ^top`. -/
structure ZigzagData {E : List (Edge n K)} {nv : ℤ × ℤ} (H : Heights E nv) where
  r : ℕ
  m : Fin r → ℕ
  eR : (Σ a : Fin r, Fin (m a + 1)) ≃ Fin n
  eC : (Σ a : Fin r, Fin (m a + 1)) ≃ Fin n
  cA : (a : Fin r) → Fin (m a + 1) → K
  dA : (a : Fin r) → Fin (m a + 1) → ℤ × ℤ
  cB : (a : Fin r) → Fin (m a + 1) → K
  dB : (a : Fin r) → Fin (m a + 1) → ℤ × ℤ
  cA_ne : ∀ a t, cA a t ≠ 0
  cA_mem : ∀ a t, cA a t ∈ (Net.mk n E).condRing
  cB_mem : ∀ a t, cB a t ∈ (Net.mk n E).condRing
  hout : ∀ x y, x.1 ≠ y.1 → H.lapTop (eR x) (eC y) = 0
  hin : ∀ a t t', H.lapTop (eR ⟨a, t⟩) (eC ⟨a, t'⟩) =
    cycMat (fun t => -(C (cA a t) * mono (dA a t))) (fun t => -(C (cB a t) * mono (dB a t))) t t'

namespace LP2

lemma isUnit_C_mono {c : K} (hc : c ≠ 0) (d : ℤ × ℤ) : IsUnit (-(C c * mono d) : LP2 K) := by
  refine IsUnit.neg ?_
  refine IsUnit.mul ((Units.map (C : K →+* LP2 K).toMonoidHom (Units.mk0 c hc)).isUnit) ?_
  refine ⟨⟨mono d, mono (-d), ?_, ?_⟩, rfl⟩
  · rw [← mono_add, add_neg_cancel, mono_zero]
  · rw [← mono_add, neg_add_cancel, mono_zero]

lemma prod_C_mono {ι : Type*} (s : Finset ι) (c : ι → K) (d : ι → ℤ × ℤ) :
    ∏ t ∈ s, (C (c t) * mono (d t) : LP2 K) = C (∏ t ∈ s, c t) * mono (∑ t ∈ s, d t) := by
  rw [Finset.prod_mul_distrib, map_prod, mono_sum]

end LP2

/-- **Toppsidan delas i binom.** -/
theorem face_splits (E : List (Edge n K)) (nv : ℤ × ℤ) (H : Heights E nv)
    (hpos : ∀ i, H.lo i < H.hi i) (Z : ZigzagData H) :
    ∃ c : K, ∃ M : ℤ × ℤ,
      faceR nv (∑ i, H.w i) (Net.mk n E).specPoly =
        C c * mono M * ∏ a, (C (∏ t, Z.cA a t) +
          C ((-1) ^ (Z.m a) * ∏ t, Z.cB a t) * mono (∑ t, Z.dB a t - ∑ t, Z.dA a t)) := by
  rw [top_det E nv H hpos]
  set Au : (a : Fin Z.r) → Fin (Z.m a + 1) → (LP2 K)ˣ :=
    fun a t => (isUnit_C_mono (Z.cA_ne a t) (Z.dA a t)).unit
  have hAu : ∀ a t, ((Au a t : (LP2 K)ˣ) : LP2 K) = -(C (Z.cA a t) * mono (Z.dA a t)) :=
    fun a t => IsUnit.unit_spec _
  obtain ⟨σ, hσ⟩ := det_blocks H.lapTop Z.eR Z.eC Au
    (fun a t => -(C (Z.cB a t) * mono (Z.dB a t))) Z.hout
    (fun a t t' => by rw [Z.hin]; simp only [hAu])
  rw [hσ]
  simp only [hAu]
  -- varje blockfaktor
  have hfac : ∀ a, (∏ t, -(C (Z.cA a t) * mono (Z.dA a t)) -
      (-1) ^ (Z.m a + 1) * ∏ t, -(C (Z.cB a t) * mono (Z.dB a t)) : LP2 K) =
      C ((-1) ^ (Z.m a + 1)) * mono (∑ t, Z.dA a t) *
        (C (∏ t, Z.cA a t) + C ((-1) ^ (Z.m a) * ∏ t, Z.cB a t) *
          mono (∑ t, Z.dB a t - ∑ t, Z.dA a t)) := by
    intro a
    simp only [Finset.prod_neg, Finset.card_univ, Fintype.card_fin, prod_C_mono]
    set u : LP2 K := (-1) ^ (Z.m a)
    have hm : (mono (∑ t, Z.dA a t) * mono (∑ t, Z.dB a t - ∑ t, Z.dA a t) : LP2 K) =
        mono (∑ t, Z.dB a t) := by rw [← mono_add]; congr 1; abel
    have e1 : ((-1 : LP2 K)) ^ (Z.m a + 1) = -u := by rw [pow_succ]; ring
    have e2 : (C ((-1 : K) ^ (Z.m a + 1)) : LP2 K) = -u := by
      rw [map_pow, map_neg, map_one, e1]
    have e3 : (C ((-1 : K) ^ (Z.m a) * ∏ t, Z.cB a t) : LP2 K) = u * C (∏ t, Z.cB a t) := by
      rw [map_mul, map_pow, map_neg, map_one]
    rw [e1, e2, e3]
    linear_combination (u ^ 2 * C (∏ t, Z.cB a t)) * hm
  rw [Finset.prod_congr rfl fun a _ => hfac a, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    ← map_prod, ← mono_sum]
  refine ⟨(σ : ℤ) * ∏ a, (-1 : K) ^ (Z.m a + 1), ∑ a, ∑ t, Z.dA a t, ?_⟩
  rw [map_mul, map_intCast]
  ring

namespace Heights

variable {E : List (Edge n K)} {nv : ℤ × ℤ} (H : Heights E nv)

lemma lapTop_apply_eq (hpos : ∀ i, H.lo i < H.hi i) (i j : Fin n) :
    H.lapTop i j = faceR nv (H.hi i + -H.lo j) ((Net.mk n E).laplacian i j) := by
  rw [Net.laplacian_apply, lap_sum_eq, faceR_sum, lapTop, of_apply, ← Finset.sum_neg_distrib]
  exact (Finset.sum_congr rfl fun k _ => H.faceR_lap hpos k i j).symm

lemma dot_of_coeff (hpos : ∀ i, H.lo i < H.hi i) {i j : Fin n} {v : ℤ × ℤ}
    (h : (H.lapTop i j).coeff v ≠ 0) : (dot nv v : ℝ) = H.hi i + -H.lo j := by
  rw [H.lapTop_apply_eq hpos, coeff_faceR] at h
  by_contra hne
  exact h (if_neg hne)

end Heights

lemma coeff_neg_C_mono (c : K) (d v : ℤ × ℤ) :
    (-(C c * mono d) : LP2 K).coeff v = if d = v then -c else 0 := by
  rw [C_mul_mono, coeff_neg, coeff_single, Finsupp.neg_apply, Finsupp.single_apply]
  split_ifs <;> simp

/-- Varje binoms exponent ligger längs sidan: `⟨nv, s_a⟩ = 0` (om `β_a ≠ 0`). -/
theorem ZigzagData.dot_s {E : List (Edge n K)} {nv : ℤ × ℤ} {H : Heights E nv}
    (hpos : ∀ i, H.lo i < H.hi i) (Z : ZigzagData H) (a : Fin Z.r) (hB : ∀ t, Z.cB a t ≠ 0) :
    dot nv (∑ t, Z.dB a t - ∑ t, Z.dA a t) = 0 := by
  have hlin : ∀ u w : ℤ × ℤ, dot nv (u - w) = dot nv u - dot nv w := by
    intro u w; simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring
  have hcoef : ∀ (i j : Fin n) (v : ℤ × ℤ), (H.lapTop i j).coeff v ≠ 0 →
      (dot nv v : ℝ) = H.hi i + -H.lo j := fun i j v h => H.dot_of_coeff hpos h
  rcases Nat.eq_zero_or_pos (Z.m a) with h0 | hm
  · -- block av storlek 1
    have hall : ∀ t : Fin (Z.m a + 1), t = 0 := fun t => Fin.ext (by have := t.isLt; simp; omega)
    have hsum : ∀ F : Fin (Z.m a + 1) → ℤ × ℤ, ∑ t, F t = F 0 := fun F =>
      Finset.sum_eq_single 0 (fun b _ hb => absurd (hall b) hb) (by simp)
    rw [hsum, hsum, hlin]
    by_cases hd : Z.dA a 0 = Z.dB a 0
    · rw [hd, sub_self]
    have hentry : H.lapTop (Z.eR ⟨a, 0⟩) (Z.eC ⟨a, 0⟩) =
        -(C (Z.cA a 0) * mono (Z.dA a 0)) + -(C (Z.cB a 0) * mono (Z.dB a 0)) := by
      rw [Z.hin, cycMat, Matrix.of_apply, if_pos rfl, if_pos (hall (0 + 1)).symm]
    have h1 := hcoef _ _ (Z.dA a 0) (by
      rw [hentry, coeff_add, Finsupp.add_apply, coeff_neg_C_mono, coeff_neg_C_mono, if_pos rfl,
        if_neg (Ne.symm hd), add_zero]
      exact neg_ne_zero.2 (Z.cA_ne a 0))
    have h2 := hcoef _ _ (Z.dB a 0) (by
      rw [hentry, coeff_add, Finsupp.add_apply, coeff_neg_C_mono, coeff_neg_C_mono, if_neg hd,
        if_pos rfl, zero_add]
      exact neg_ne_zero.2 (hB 0))
    have : (dot nv (Z.dB a 0) : ℝ) = dot nv (Z.dA a 0) := by rw [h1, h2]
    have := Int.cast_injective this
    omega
  · -- block av storlek ≥ 2
    have hne : ∀ t : Fin (Z.m a + 1), t ≠ t + 1 := by
      intro t h
      have h1 : (1 : Fin (Z.m a + 1)) = 0 := by
        have := congrArg (· - t) h
        simpa using this.symm
      rw [Fin.one_eq_zero_iff] at h1
      omega
    have hA : ∀ t, (dot nv (Z.dA a t) : ℝ) = H.hi (Z.eR ⟨a, t⟩) + -H.lo (Z.eC ⟨a, t⟩) := by
      intro t
      apply hcoef
      rw [Z.hin, cycMat, Matrix.of_apply, if_pos rfl, if_neg (hne t), add_zero, coeff_neg_C_mono, if_pos rfl]
      exact neg_ne_zero.2 (Z.cA_ne a t)
    have hBd : ∀ t, (dot nv (Z.dB a t) : ℝ) = H.hi (Z.eR ⟨a, t + 1⟩) + -H.lo (Z.eC ⟨a, t⟩) := by
      intro t
      apply hcoef
      rw [Z.hin, cycMat, Matrix.of_apply, if_neg (Ne.symm (hne t)), if_pos rfl, zero_add,
        coeff_neg_C_mono, if_pos rfl]
      exact neg_ne_zero.2 (hB t)
    apply Int.cast_injective (α := ℝ)
    rw [hlin, dot_sum, dot_sum]
    push_cast
    simp only [hA, hBd, Finset.sum_add_distrib]
    have hshift := Equiv.sum_comp (Equiv.addRight (1 : Fin (Z.m a + 1)))
      (fun t => H.hi (Z.eR ⟨a, t⟩))
    simp only [Equiv.coe_addRight] at hshift
    rw [hshift]
    ring

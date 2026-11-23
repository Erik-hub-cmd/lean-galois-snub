import LeanGalois.Examples

/-!
# Galois-hindret (Sats 10.1′ och 10.1)

Snub square med diagonalkonduktans `l`, `κ = √(l(l+2))`, `t = 1 + l + κ`.
Sidpolynomet längs sidan `(2,0)–(0,2)` är `1 - q·u + u²` med `q = 2(2l²+4l+1)`, `u = X⁻¹Z`,
och dess rötter är `t^{±2}`. Om konduktanserna ligger i en kropp `F ∋ l` med `κ ∉ F` kan
inget minimalt nät med konduktanser i `F` ha samma spektralpolynom (upp till konstant).

Den kombinatoriska delen (Lemma 4: tågspår, minimalitet) är **inte** formaliserad. Den
kommer in som två explicita hypoteser om ett abstrakt predikat `IsMinimal`:
* `H4`   : minimalt nät med minst två spårriktningar ⇒ `SideSplits` (Lemma 4(b)),
* `H4deg`: minimalt nät med högst en spårriktning ⇒ inga kanter (spår i samma klass är
  disjunkta, så det finns inga korsningar = kanter; Lemma 4a i version 1).
-/

noncomputable section

open LP2 AddMonoidAlgebra

namespace Galois

variable (F : Subfield ℝ)

/-- `t^m = A + Bκ` och `t'^m = A - Bκ` med `A, B ∈ F`, där `t' = 1 + l - κ`. -/
lemma pow_conj (l κ : ℝ) (hl : l ∈ F) (hκ2 : κ ^ 2 = l * (l + 2)) (m : ℕ) :
    ∃ A ∈ F, ∃ B ∈ F, (1 + l + κ) ^ m = A + B * κ ∧ (1 + l - κ) ^ m = A - B * κ := by
  induction m with
  | zero => exact ⟨1, F.one_mem, 0, F.zero_mem, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨A, hA, B, hB, h1, h2⟩ := ih
    have h2F : (2 : ℝ) ∈ F := by
      have h := F.add_mem F.one_mem F.one_mem
      rwa [one_add_one_eq_two] at h
    refine ⟨A * (1 + l) + B * (l * (l + 2)), ?_, A + B * (1 + l), ?_, ?_, ?_⟩
    · exact F.add_mem (F.mul_mem hA (F.add_mem F.one_mem hl))
        (F.mul_mem hB (F.mul_mem hl (F.add_mem hl h2F)))
    · exact F.add_mem hA (F.mul_mem hB (F.add_mem F.one_mem hl))
    · rw [pow_succ, h1]; linear_combination B * hκ2
    · rw [pow_succ, h2]; linear_combination B * hκ2

/-- **Lemma 3**: `t^m ∉ F` för `m ≥ 1`. -/
lemma t_pow_not_mem (l κ : ℝ) (hl0 : 0 < l) (hκ0 : 0 < κ) (hκ2 : κ ^ 2 = l * (l + 2))
    (hl : l ∈ F) (hκ : κ ∉ F) (m : ℕ) (hm : m ≠ 0) : (1 + l + κ) ^ m ∉ F := by
  intro hmem
  obtain ⟨A, hA, B, hB, h1, h2⟩ := pow_conj F l κ hl hκ2 m
  by_cases hB0 : B = 0
  · subst hB0
    have htt : (1 + l + κ) * (1 + l - κ) = 1 := by linear_combination (-1 : ℝ) * hκ2
    have heq : (1 + l + κ) ^ m = (1 + l - κ) ^ m := by rw [h1, h2]; ring
    have hprod : ((1 + l + κ) * (1 + l - κ)) ^ m = 1 := by rw [htt, one_pow]
    rw [mul_pow, ← heq] at hprod
    have ht1 : 1 < 1 + l + κ := by linarith
    have : 1 < (1 + l + κ) ^ m := one_lt_pow₀ ht1 hm
    nlinarith
  · apply hκ
    have hk : κ = ((1 + l + κ) ^ m - A) / B := by
      rw [h1]; field_simp; ring
    rw [hk]
    exact F.div_mem (F.sub_mem hmem hA) hB

/-- `(t²)^j ∉ F` för heltal `j ≠ 0` (rötterna `t^{±2}` och deras potenser). -/
lemma w_zpow_not_mem (l κ : ℝ) (hl0 : 0 < l) (hκ0 : 0 < κ) (hκ2 : κ ^ 2 = l * (l + 2))
    (hl : l ∈ F) (hκ : κ ∉ F) (j : ℤ) (hj : j ≠ 0) : ((1 + l + κ) ^ 2) ^ j ∉ F := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · have hm : m ≠ 0 := by rintro rfl; exact hj rfl
    rw [zpow_natCast, ← pow_mul]
    exact t_pow_not_mem F l κ hl0 hκ0 hκ2 hl hκ (2 * m) (by omega)
  · have hm : m ≠ 0 := by rintro rfl; exact hj (by simp)
    rw [zpow_neg, zpow_natCast, ← pow_mul]
    intro h
    have h' := F.inv_mem h
    rw [inv_inv] at h'
    exact t_pow_not_mem F l κ hl0 hκ0 hκ2 hl hκ (2 * m) (by omega) h'

lemma condProds_mem (G : Net ℝ) (hGF : ∀ e ∈ G.edges, e.cond ∈ F) :
    ∀ x ∈ G.condProds, x ∈ F := by
  intro x hx
  induction hx using Submonoid.closure_induction with
  | mem x hx => obtain ⟨e, he, rfl⟩ := hx; exact hGF e he
  | one => exact F.one_mem
  | mul x y _ _ hx hy => exact F.mul_mem hx hy

end Galois

namespace LP2

lemma isTop_mono {n : ℤ × ℤ} {k : ℤ} {K : Type*} [CommRing K] {v : ℤ × ℤ} (h : dot n v ≤ k) :
    IsTop n k (mono v : LP2 K) := isTop_single n k 1 h

lemma isTop_C {n : ℤ × ℤ} {k : ℤ} {K : Type*} [CommRing K] (a : K) (h : dot n 0 ≤ k) :
    IsTop n k (C a) := isTop_single n k a h

end LP2

/-- Snub squares spektralpolynom som summa av termer `single v a`. -/
theorem snub_single (l : ℝ) :
    (snubNet l).specPoly =
      single (2, 0) 1 + single (-2, 0) 1 + single (0, 2) 1 + single (0, -2) 1
      - (single (1, 1) (2 * (2 * l ^ 2 + 4 * l + 1)) + single (1, -1) (2 * (2 * l ^ 2 + 4 * l + 1))
        + single (-1, 1) (2 * (2 * l ^ 2 + 4 * l + 1)) + single (-1, -1) (2 * (2 * l ^ 2 + 4 * l + 1)))
      - (single (1, 0) (8 * (l + 2) ^ 2) + single (-1, 0) (8 * (l + 2) ^ 2)
        + single (0, 1) (8 * (l + 2) ^ 2) + single (0, -1) (8 * (l + 2) ^ 2))
      + single (0, 0) (4 * (2 * l + 3) * (6 * l + 11)) := by
  rw [snubNet_specPoly]
  simp only [mul_add, C_mul_mono]
  rw [C_apply]
  rfl

/-- Sidan `(2,0)–(0,2)` av snub squares Newtonpolygon: `X² - q·XZ + Z²`. -/
theorem snub_face (l : ℝ) :
    faceAt (1, 1) 2 (snubNet l).specPoly =
      mono (2, 0) - C (2 * (2 * l ^ 2 + 4 * l + 1)) * mono (1, 1) + mono (0, 2) := by
  rw [snub_single, C_mul_mono]
  simp only [mono, faceAt_add, faceAt_sub]
  rw [faceAt_single_pos _ _ (2, 0) _ (by simp [dot]), faceAt_single_pos _ _ (1, 1) _ (by simp [dot]),
    faceAt_single_pos _ _ (0, 2) _ (by simp [dot])]
  repeat rw [faceAt_single_neg _ _ _ _ (by simp [dot])]
  abel

theorem snub_isTop (l : ℝ) : IsTop (1, 1) 2 (snubNet l).specPoly := by
  intro v hv
  by_contra hlt
  push_neg at hlt
  have hne : ∀ w : ℤ × ℤ, dot (1, 1) w ≤ 2 → ∀ a : ℝ, (Finsupp.single w a) v = 0 := by
    intro w hw a
    rw [Finsupp.single_apply, if_neg]
    rintro rfl
    omega
  apply Finsupp.mem_support_iff.1 hv
  rw [snub_single]
  simp only [coeff_add, coeff_sub, coeff_single, Finsupp.add_apply, Finsupp.sub_apply]
  simp [hne, dot]

open Galois

/-- **Sats 10.1′.** Låt `F ⊆ ℝ` vara en kropp med `l ∈ F`, `l > 0`, och `κ = √(l(l+2)) ∉ F`
(t.ex. `F = ℚ`, `l = 1`, `κ = √3`). Om `IsMinimal` uppfyller hypoteserna `H4` och `H4deg`
(Lemma 4), så är inget nät `G` med konduktanser i `F` och `det Δ_G = c · det M_snub`
(`c ≠ 0`) minimalt. -/
theorem sats_10_1' (F : Subfield ℝ) (l κ : ℝ) (hl0 : 0 < l) (hκ0 : 0 < κ) (hκ2 : κ ^ 2 = l * (l + 2))
    (hlF : l ∈ F) (hκF : κ ∉ F)
    (IsMinimal TwoDirections : Net ℝ → Prop)
    (H4 : ∀ G, IsMinimal G → TwoDirections G → SideSplits G)
    (H4deg : ∀ G, IsMinimal G → ¬ TwoDirections G → G.edges = [])
    (G : Net ℝ) (hGF : ∀ e ∈ G.edges, e.cond ∈ F) (c : ℝ) (hc : c ≠ 0)
    (hP : G.specPoly = C c * (snubNet l).specPoly) : ¬ IsMinimal G := by
  intro hmin
  set q : ℝ := 2 * (2 * l ^ 2 + 4 * l + 1) with hq
  have hface : faceAt (1, 1) 2 G.specPoly = C c * (mono (2, 0) - C q * mono (1, 1) + mono (0, 2)) := by
    rw [hP, faceAt_C_mul, snub_face]
  have hface' : faceAt (1, 1) 2 G.specPoly =
      single (2, 0) c - single (1, 1) (c * q) + single (0, 2) c := by
    rw [hface, mul_add, mul_sub, ← mul_assoc, ← map_mul, C_mul_mono, C_mul_mono, C_mul_mono]
  have hcoef20 : (faceAt (1, 1) 2 G.specPoly).coeff (2, 0) = c := by
    rw [hface']; simp [coeff_add, coeff_sub, coeff_single, Finsupp.single_apply]
  have hcoef02 : (faceAt (1, 1) 2 G.specPoly).coeff (0, 2) = c := by
    rw [hface']; simp [coeff_add, coeff_sub, coeff_single, Finsupp.single_apply]
  by_cases h2 : TwoDirections G
  · have htop : IsTop (1, 1) 2 G.specPoly := by
      rw [hP]; exact isTop_C_mul _ _ c (snub_isTop l)
    have hsupp : ∃ v ∈ (faceAt (1, 1) 2 G.specPoly).coeff.support,
        ∃ w ∈ (faceAt (1, 1) 2 G.specPoly).coeff.support, v ≠ w :=
      ⟨(2, 0), by simp [Finsupp.mem_support_iff, hcoef20, hc],
       (0, 2), by simp [Finsupp.mem_support_iff, hcoef02, hc], by decide⟩
    obtain ⟨s, hs0, hsn, c', hc', m, ε, hε, Ls, hLs, hsplit⟩ :=
      H4 G hmin h2 (1, 1) 2 (by decide) htop hsupp
    set w : ℝ := (1 + l + κ) ^ 2 with hw_def
    have hw : w ≠ 0 := by positivity
    -- `w = t²` är en rot till `1 - q u + u²`
    have hroot : 1 - q * w + w ^ 2 = 0 := by
      have htt : (1 + l + κ) * (1 + l - κ) = 1 := by linear_combination (-1 : ℝ) * hκ2
      have hsum : (1 + l + κ) ^ 2 + (1 + l - κ) ^ 2 = q := by
        rw [hq]; linear_combination (2 : ℝ) * hκ2
      have : w * (1 + l - κ) ^ 2 = 1 := by rw [hw_def, ← mul_pow, htt, one_pow]
      linear_combination w * hsum - this
    have hev0 : evZ w hw (faceAt (1, 1) 2 G.specPoly) = 0 := by
      rw [hface]
      simp [evZ_C, evZ_mono]
      right
      linear_combination hroot
    rw [hsplit] at hev0
    simp only [map_mul, map_list_prod, List.map_map, evZ_C, evZ_mono] at hev0
    rcases mul_eq_zero.1 hev0 with h | hprod
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hc'
      · exact absurd h (zpow_ne_zero _ hw)
    obtain ⟨⟨α, β⟩, hab, hy0⟩ := List.mem_map.1 (List.prod_eq_zero_iff.1 hprod)
    have hαF : α ∈ F := condProds_mem F G hGF α (hLs _ hab).1
    have hβF : β ∈ F := condProds_mem F G hGF β (hLs _ hab).2
    simp only [Function.comp, map_add, map_mul, evZ_C, evZ_mono] at hy0
    -- hy0 : α + ε * β * w ^ s.2 = 0
    have hs2 : s.2 ≠ 0 := by
      intro h
      apply hs0
      have : s.1 + s.2 = 0 := by simpa [dot] using hsn
      ext <;> simp_all
    have hεF : ε ∈ F := by
      rcases hε with rfl | rfl
      · exact F.one_mem
      · exact F.neg_mem F.one_mem
    have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
    by_cases hβ : β = 0
    · -- då är α = 0, faktorn är noll och hela sidpolynomet noll: motsägelse med koefficienten c
      subst hβ
      have hα : α = 0 := by simpa using hy0
      subst hα
      have hzero : faceAt (1, 1) 2 G.specPoly = 0 := by
        rw [hsplit]
        apply mul_eq_zero_of_right
        apply List.prod_eq_zero
        exact List.mem_map.2 ⟨(0, 0), hab, by simp⟩
      rw [hzero] at hcoef20
      exact hc (by simpa using hcoef20.symm)
    · apply w_zpow_not_mem F l κ hl0 hκ0 hκ2 hlF hκF s.2 hs2
      have hwj : w ^ s.2 = -α / (ε * β) := by
        field_simp
        linear_combination hy0
      rw [← hw_def, hwj]
      exact F.div_mem (F.neg_mem hαF) (F.mul_mem hεF hβF)
  · have hE := H4deg G hmin h2
    have hL : G.laplacian = 0 := by
      ext i j
      simp [Net.laplacian, hE]
    have h0 : (faceAt (1, 1) 2 G.specPoly).coeff (2, 0) = 0 := by
      rw [faceAt_coeff_of _ _ _ _ (by simp [dot]), Net.specPoly, hL]
      rcases Nat.eq_zero_or_pos G.n with h | h
      · haveI : IsEmpty (Fin G.n) := by rw [h]; infer_instance
        rw [Matrix.det_isEmpty]
        simp [AddMonoidAlgebra.one_def, coeff_single, Finsupp.single_apply]
      · haveI : Nonempty (Fin G.n) := ⟨⟨0, h⟩⟩
        rw [Matrix.det_zero]
        rfl
    exact hc (hcoef20 ▸ h0)

/-- **Sats 10.1** (egen torus). `Move` är en godtycklig relation ("ett drag") som
(i) bevarar att alla konduktanser ligger i `F` och (ii) multiplicerar `det Δ` med en nollskild
konstant. Då når ingen ändlig följd av drag från snub square ett minimalt nät. -/
theorem sats_10_1 (F : Subfield ℝ) (l κ : ℝ) (hl0 : 0 < l) (hκ0 : 0 < κ) (hκ2 : κ ^ 2 = l * (l + 2))
    (hlF : l ∈ F) (hκF : κ ∉ F)
    (IsMinimal TwoDirections : Net ℝ → Prop)
    (H4 : ∀ G, IsMinimal G → TwoDirections G → SideSplits G)
    (H4deg : ∀ G, IsMinimal G → ¬ TwoDirections G → G.edges = [])
    (Move : Net ℝ → Net ℝ → Prop)
    (hMoveF : ∀ G G', Move G G' → (∀ e ∈ G.edges, e.cond ∈ F) → ∀ e ∈ G'.edges, e.cond ∈ F)
    (hMoveDet : ∀ G G', Move G G' → ∃ c : ℝ, c ≠ 0 ∧ G'.specPoly = C c * G.specPoly)
    (G : Net ℝ) (hreach : Relation.ReflTransGen Move (snubNet l) G) : ¬ IsMinimal G := by
  have key : (∀ e ∈ G.edges, e.cond ∈ F) ∧
      ∃ c : ℝ, c ≠ 0 ∧ G.specPoly = C c * (snubNet l).specPoly := by
    induction hreach with
    | refl =>
      refine ⟨?_, 1, one_ne_zero, by simp⟩
      change ∀ e ∈ snubEdges l, e.cond ∈ F
      simp [snubEdges, hlF]
    | tail _ hmove ih =>
      obtain ⟨hF', c, hc, hP⟩ := ih
      obtain ⟨c', hc', hP'⟩ := hMoveDet _ _ hmove
      refine ⟨hMoveF _ _ hmove hF', c' * c, mul_ne_zero hc' hc, ?_⟩
      rw [hP', hP, ← mul_assoc, ← map_mul]
  obtain ⟨hF', c, hc, hP⟩ := key
  exact sats_10_1' F l κ hl0 hκ0 hκ2 hlF hκF IsMinimal TwoDirections H4 H4deg G hF' c hc hP

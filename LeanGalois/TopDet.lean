import LeanGalois.Sweep

/-!
# Toppsidan som determinant (Lemma 4, steg 1(iii)–(iv))

**Initialformen av en determinant** (`faceR_det`): om posten `M i j` ligger under nivån
`u i + v j`, så ligger `det M` under `Σ u + Σ v`, och toppdelen är `det` av posternas toppdelar.

Med höjddata (`u i = hi i`, `v j = -lo j`) ger det: toppsidan av `det Δ` är `det Δ^top`, där
`Δ^top i j` bara innehåller de **täta** kanterna (ut ur `i` vid `hi i`, in i `j` vid `lo j`).
-/

noncomputable section

open LP2 Matrix AddMonoidAlgebra

namespace LP2

variable {K : Type*} [CommRing K] {n : ℤ × ℤ}

lemma faceR_zsmul (W : ℝ) (z : ℤ) (p : LP2 K) : faceR n W (z • p) = z • faceR n W p := by
  ext v
  simp only [coeff_faceR, coeff_smul, Finsupp.smul_apply]
  split_ifs <;> simp

lemma isTopR_zsmul {W : ℝ} (z : ℤ) {p : LP2 K} (h : IsTopR n W p) : IsTopR n W (z • p) := by
  intro v hv
  apply h v
  rw [coeff_smul] at hv
  exact Finsupp.support_smul hv

/-- **Initialformen av en determinant.** -/
theorem faceR_det {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (LP2 K)) (u v : ι → ℝ)
    (h : ∀ i j, IsTopR n (u i + v j) (M i j)) :
    IsTopR n (∑ i, u i + ∑ j, v j) M.det ∧
      faceR n (∑ i, u i + ∑ j, v j) M.det = (Matrix.of fun i j => faceR n (u i + v j) (M i j)).det := by
  have hlev : ∀ σ : Equiv.Perm ι, ∑ i, (u (σ i) + v i) = ∑ i, u i + ∑ j, v j := by
    intro σ
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ u]
  have htop : ∀ σ : Equiv.Perm ι, IsTopR n (∑ i, u i + ∑ j, v j) (∏ i, M (σ i) i) := by
    intro σ
    rw [← hlev σ]
    exact isTopR_prod _ _ _ fun i _ => h (σ i) i
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_apply]
    apply isTopR_sum
    intro σ _
    rw [Units.smul_def]
    exact isTopR_zsmul _ (htop σ)
  · rw [Matrix.det_apply, Matrix.det_apply, faceR_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, Units.smul_def, faceR_zsmul, ← hlev σ,
      faceR_prod _ _ _ fun i _ => h (σ i) i]
    rfl

end LP2

variable {K : Type*} [CommRing K] {n : ℕ}

namespace Heights

variable {E : List (Edge n K)} {nv : ℤ × ℤ} (H : Heights E nv)

/-- Kantens täta bidrag till posten `(i, j)`: `c·z^{s}` om kanten går tätt `i → j` framåt,
`c·z^{-s}` om den går tätt `i → j` bakåt. -/
def tightTerm (k : Fin E.length) (i j : Fin n) : LP2 K :=
  C (E.get k).cond * (if (i = (E.get k).src ∧ j = (E.get k).tgt) ∧
      (dot nv (E.get k).shift : ℝ) = H.hi i + -H.lo j then mono (E.get k).shift else 0) +
  C (E.get k).cond * (if (i = (E.get k).tgt ∧ j = (E.get k).src) ∧
      (dot nv (-(E.get k).shift) : ℝ) = H.hi i + -H.lo j then mono (-(E.get k).shift) else 0)

/-- Den täta delen av Laplacematrisen. -/
def lapTop : Matrix (Fin n) (Fin n) (LP2 K) :=
  Matrix.of fun i j => -∑ k : Fin E.length, H.tightTerm k i j

lemma faceR_one_pos {W : ℝ} (hW : W ≠ 0) : faceR nv W (1 : LP2 K) = 0 := by
  have h1 : (1 : LP2 K) = single 0 1 := rfl
  rw [h1, faceR_single, if_neg]
  simpa [dot] using hW.symm

lemma faceR_mono (W : ℝ) (s : ℤ × ℤ) :
    faceR nv W (mono s : LP2 K) = if (dot nv s : ℝ) = W then mono s else 0 := faceR_single W s 1

lemma isTopR_C_mul' {W : ℝ} {c : K} {p : LP2 K} (h : IsTopR nv W p) : IsTopR nv W (C c * p) := by
  have := isTopR_mul (isTopR_C (n := nv) c (le_refl (0 : ℝ))) h
  rwa [zero_add] at this

lemma lap_isTopR (k : Fin E.length) (i j : Fin n) :
    IsTopR nv (H.hi i + -H.lo j) ((E.get k).lap i j) := by
  have h1 := H.src_lo k; have h2 := H.src_hi k; have h3 := H.tgt_lo k; have h4 := H.tgt_hi k
  have hneg : (dot nv (-(E.get k).shift) : ℝ) = -dot nv (E.get k).shift := by
    simp only [dot, Prod.fst_neg, Prod.snd_neg]; push_cast; ring
  unfold Edge.lap
  apply isTopR_C_mul'
  refine isTopR_sub (isTopR_sub (isTopR_add ?_ ?_) ?_) ?_
  · split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact isTopR_one (by linarith [H.lo_le_hi (E.get k).src])
    · exact isTopR_zero
  · split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact isTopR_one (by linarith [H.lo_le_hi (E.get k).tgt])
    · exact isTopR_zero
  · split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact isTopR_mono' _ (by linarith)
    · exact isTopR_zero
  · split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact isTopR_mono' _ (by rw [hneg]; linarith)
    · exact isTopR_zero

lemma faceR_ite_mono (W : ℝ) (P : Prop) [Decidable P] (w : ℤ × ℤ) :
    faceR nv W (if P then (mono w : LP2 K) else 0) = if P ∧ (dot nv w : ℝ) = W then mono w else 0 := by
  by_cases hP : P
  · rw [if_pos hP, faceR_mono]; simp [hP]
  · rw [if_neg hP, faceR_zero, if_neg (fun h => hP h.1)]

lemma faceR_lap (hpos : ∀ i, H.lo i < H.hi i) (k : Fin E.length) (i j : Fin n) :
    faceR nv (H.hi i + -H.lo j) ((E.get k).lap i j) = -H.tightTerm k i j := by
  have hlap : (E.get k).lap i j = C (E.get k).cond *
      ((if i = (E.get k).src ∧ j = (E.get k).src then mono 0 else 0) +
        (if i = (E.get k).tgt ∧ j = (E.get k).tgt then mono 0 else 0) -
        (if i = (E.get k).src ∧ j = (E.get k).tgt then mono (E.get k).shift else 0) -
        (if i = (E.get k).tgt ∧ j = (E.get k).src then mono (-(E.get k).shift) else 0)) := by
    rw [mono_zero]; rfl
  rw [hlap, faceR_C_mul_eq, faceR_sub, faceR_sub, faceR_add, faceR_ite_mono, faceR_ite_mono,
    faceR_ite_mono, faceR_ite_mono]
  have h0 : ∀ x : Fin n, ¬ ((i = x ∧ j = x) ∧ (dot nv (0 : ℤ × ℤ) : ℝ) = H.hi i + -H.lo j) := by
    rintro x ⟨⟨hix, hjx⟩, h⟩
    rw [hix, hjx] at h
    simp only [dot, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero, Int.cast_zero] at h
    linarith [hpos x]
  rw [if_neg (h0 _), if_neg (h0 _)]
  unfold tightTerm
  ring

lemma lap_sum_eq (E : List (Edge n K)) (i j : Fin n) :
    (E.map fun e => e.lap i j).sum = ∑ k : Fin E.length, (E.get k).lap i j := by
  rw [← List.sum_ofFn,
    show (List.ofFn fun k => (E.get k).lap i j) = (List.ofFn E.get).map (fun e => e.lap i j) from
      by rw [List.map_ofFn]; rfl, List.ofFn_get]

end Heights

/-- **Toppsidan är determinanten av den täta delen**: med höjddata och positiva bredder är
`faceR (Σ bredder) (det Δ) = det Δ^top`. -/
theorem top_det (E : List (Edge n K)) (nv : ℤ × ℤ) (H : Heights E nv)
    (hpos : ∀ i, H.lo i < H.hi i) :
    faceR nv (∑ i, H.w i) (Net.mk n E).specPoly = H.lapTop.det := by
  rw [Net.specPoly_mk]
  have hent : ∀ i j, IsTopR nv (H.hi i + -H.lo j)
      ((Matrix.of fun i j => (E.map fun e => e.lap i j).sum) i j) := by
    intro i j
    rw [of_apply, Heights.lap_sum_eq]
    exact isTopR_sum _ _ fun k _ => H.lap_isTopR k i j
  have hW : ∑ i, H.w i = ∑ i, H.hi i + ∑ j, -H.lo j := by
    simp only [Heights.w, sub_eq_add_neg, Finset.sum_add_distrib]
  rw [hW, (faceR_det _ H.hi (fun j => -H.lo j) hent).2]
  congr 1
  refine Matrix.ext fun i j => ?_
  rw [of_apply, of_apply, Heights.lap_sum_eq, faceR_sum, Heights.lapTop, of_apply,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => H.faceR_lap hpos k i j

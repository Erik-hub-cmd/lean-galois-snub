import LeanGalois.Zigzag
import LeanGalois.Obstruct

/-!
# Sats 10.1 med Lemma 4 ersatt av mindre hypoteser

I stället för `H4` (Lemma 4(b) som svart låda) används:

* **Schrijver** (citerat, steg 2): ett minimalt nät förs med lokala drag (Y–Δ åt båda hållen)
  till ett geodetiskt nät.
* **Geometri** (steg 1, elementärt): ett geodetiskt nät har för varje toppsida höjddata med
  positiva bredder och sicksackdata (`HasZigzags`).

Allt annat i Lemma 4 (CRSF, svepet, toppsidan som determinant, blockfaktoriseringen) är bevisat.
-/

noncomputable section

open LP2 AddMonoidAlgebra

/-- Varje nollskild toppsida har höjddata med positiva bredder på rätt nivå och sicksackdata. -/
def HasZigzags (G : Net ℝ) : Prop :=
  ∀ nv : ℤ × ℤ, ∀ k : ℤ, nv ≠ 0 → IsTop nv k G.specPoly → faceAt nv k G.specPoly ≠ 0 →
    ∃ H : Heights G.edges nv, (∀ i, H.lo i < H.hi i) ∧ ∑ i, H.w i = k ∧ Nonempty (ZigzagData H)

lemma faceAt_eq_faceR {K : Type*} [CommRing K] (nv : ℤ × ℤ) (k : ℤ) (p : LP2 K) :
    faceAt nv k p = faceR nv k p := by
  ext v
  rw [coeff_faceR, faceAt]
  simp only [coeff_ofCoeff, Finsupp.filter_apply]
  congr 1
  exact propext ⟨fun h => by rw [h], fun h => by exact_mod_cast h⟩

lemma condRing_le (F : Subfield ℝ) (G : Net ℝ) (hGF : ∀ e ∈ G.edges, e.cond ∈ F) :
    ∀ x ∈ G.condRing, x ∈ F := by
  intro x hx
  have : G.condRing ≤ F.toSubring := by
    apply Subring.closure_le.2
    rintro c ⟨e, he, rfl⟩
    exact hGF e he
  exact this hx

/-- **Ett hindrat nät har inga sicksackdata.** -/
theorem Obstructed.not_hasZigzags {F : Subfield ℝ} (G : Net ℝ) (hGF : ∀ e ∈ G.edges, e.cond ∈ F)
    (hO : Obstructed F G.specPoly) : ¬ HasZigzags G := by
  intro hZ
  obtain ⟨nv, hn, k, htop, hf, x, z, hev, hs⟩ := hO
  obtain ⟨H, hpos, hW, ⟨Z⟩⟩ := hZ nv k hn htop hf
  obtain ⟨c, M, hsplit⟩ := face_splits G.edges nv H hpos Z
  have hface : faceAt nv k G.specPoly = C c * mono M * ∏ a, (C (∏ t, Z.cA a t) +
      C ((-1) ^ (Z.m a) * ∏ t, Z.cB a t) * mono (∑ t, Z.dB a t - ∑ t, Z.dA a t)) := by
    rw [faceAt_eq_faceR, ← hW]; exact hsplit
  rw [hface] at hev hf
  simp only [map_mul, map_prod, map_add, evP_C, evP_mono] at hev
  rcases mul_eq_zero.1 hev with h | hprod
  · rcases mul_eq_zero.1 h with h | h
    · apply hf; rw [h, map_zero, zero_mul, zero_mul]
    · exact Units.ne_zero _ h
  obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 hprod
  set α := ∏ t, Z.cA a t
  set β := ∏ t, Z.cB a t
  set s := ∑ t, Z.dB a t - ∑ t, Z.dA a t
  have hα0 : α ≠ 0 := Finset.prod_ne_zero_iff.2 fun t _ => Z.cA_ne a t
  have hαF : α ∈ F := condRing_le F G hGF α (Subring.prod_mem _ fun t _ => Z.cA_mem a t)
  have hβF : β ∈ F := condRing_le F G hGF β (Subring.prod_mem _ fun t _ => Z.cB_mem a t)
  have hεF : ((-1 : ℝ) ^ (Z.m a)) ∈ F := F.pow_mem (F.neg_mem F.one_mem) _
  have hε0 : ((-1 : ℝ) ^ (Z.m a)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hβ0 : β ≠ 0 := by
    intro hβ
    rw [hβ, mul_zero, zero_mul, add_zero] at ha
    exact hα0 ha
  have hB : ∀ t, Z.cB a t ≠ 0 := fun t => (Finset.prod_ne_zero_iff.1 hβ0) t (Finset.mem_univ t)
  have hsn : dot nv s = 0 := Z.dot_s hpos a hB
  by_cases hs0 : s = 0
  · -- faktorn är en konstant, alltså noll, och sidan är noll
    apply hf
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    have h0 : α + (-1) ^ (Z.m a) * β = 0 := by
      have := ha
      simp only [chi, hs0] at this ⊢
      simpa using this
    rw [show (∑ t, Z.dB a t - ∑ t, Z.dA a t) = s from rfl, hs0, mono_zero, mul_one, ← map_add, h0,
      map_zero]
  · apply hs s hs0 hsn
    have hchi : chi x z s = -α / ((-1) ^ (Z.m a) * β) := by
      field_simp
      linear_combination ha
    rw [hchi]
    exact F.div_mem (F.neg_mem hαF) (F.mul_mem hεF hβF)

/-- **Sats 10.1 med Lemma 4 reducerat** till Schrijvers sats och geometrin för geodetiska
nät: ingen följd av lokala drag och torusbyten från snub square når ett minimalt nät. -/
theorem sats_10_1_geo (F : Subfield ℝ) (l κ : ℝ) (hl0 : 0 < l) (hκ0 : 0 < κ)
    (hκ2 : κ ^ 2 = l * (l + 2)) (hlF : l ∈ F) (hκF : κ ∉ F)
    (IsMinimal IsGeodesic : Net ℝ → Prop)
    (Schrijver : ∀ G, IsMinimal G → ∃ G', Relation.ReflTransGen (LocalMove F) G G' ∧ IsGeodesic G')
    (Geo : ∀ G, IsGeodesic G → HasZigzags G)
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
  intro hmin
  obtain ⟨G', hpath, hgeo⟩ := Schrijver G hmin
  have key' : (∀ e ∈ G'.edges, e.cond ∈ F) ∧ Obstructed F G'.specPoly := by
    clear hgeo
    induction hpath with
    | refl => exact key
    | tail _ hm ih =>
      obtain ⟨hF', hO⟩ := ih
      obtain ⟨c, hc, hP⟩ := hm.det_hyp
      exact ⟨hm.field_hyp F hF', hP ▸ hO.C_mul hc⟩
  exact Obstructed.not_hasZigzags G' key'.1 key'.2 (Geo G' hgeo)

/-- **Konkret** (`F = ℚ`, `l = 1`). -/
theorem sats_10_1_geo_snub_rat (IsMinimal IsGeodesic : Net ℝ → Prop)
    (Schrijver : ∀ G, IsMinimal G →
      ∃ G', Relation.ReflTransGen (LocalMove Qsub) G G' ∧ IsGeodesic G')
    (Geo : ∀ G, IsGeodesic G → HasZigzags G) (G : Net ℝ)
    (hreach : Relation.ReflTransGen (fun G G' => LocalMove Qsub G G' ∨ CoverStep G G')
      (snubNet 1) G) :
    ¬ IsMinimal G := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  refine sats_10_1_geo Qsub 1 (Real.sqrt 3) one_pos (Real.sqrt_pos.2 (by norm_num)) ?_
    (Subfield.one_mem _) sqrt3_not_mem_Q IsMinimal IsGeodesic Schrijver Geo G hreach
  rw [Real.sq_sqrt h3]; norm_num

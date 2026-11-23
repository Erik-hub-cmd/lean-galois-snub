import LeanGalois.Basic
import LeanGalois.FunMat

/-!
# CRSF-utvecklingen av `det Δ` (Lemma 4, steg 0), orienterad form

Ett **val** `f` låter varje nod `i` välja en kant `f(i)` (ett index i kantlistan) som går
genom `i`. Det ger en funktionsgraf `g_f(i)` = andra änden av `f(i)`, med fasen
`φ_f(i) = z^{±shift}` (riktningen från `i`). För en ögla är `g_f(i) = i` och
`φ_f(i) = z^ℓ + z^{-ℓ} - 1`, så att `1 - φ = 2 - z^ℓ - z^{-ℓ}`. Satsen (`specPoly_crsf`):

  `det Δ = Σ_f ∏_i c_{f(i)} · ∏_{γ cykel i g_f} (1 - ∏_{i ∈ γ} φ_f(i))`.

Komponenterna i ett val är precis de orienterade cykelrotade spännskogarna (varje nod pekar ut
längs sin kant, varje komponent har exakt en cykel). En cykel som använder samma kant fram och
tillbaka, eller som är kontraktibel, har `∏ φ = 1` och ger bidraget 0. Över de två
orienteringarna av en cykel blir `(1 - w) + (1 - w⁻¹) = 2 - w - w⁻¹`, Kenyons/Formans form.
-/

noncomputable section

open LP2 Matrix FunMat

variable {K : Type*} [CommRing K] {n : ℕ}

namespace Edge

/-- `e` går genom `i`. -/
def Incident (e : Edge n K) (i : Fin n) : Prop := i = e.src ∨ i = e.tgt

instance (e : Edge n K) (i : Fin n) : Decidable (e.Incident i) := by
  unfold Incident; infer_instance

/-- Andra änden av `e` sett från `i`. -/
def other (e : Edge n K) (i : Fin n) : Fin n := if i = e.src then e.tgt else e.src

/-- Fasen när man går längs `e` från `i`. -/
def phase (e : Edge n K) (i : Fin n) : LP2 K :=
  if e.src = e.tgt then mono e.shift + mono (-e.shift) - 1
  else if i = e.src then mono e.shift else mono (-e.shift)

lemma lap_of_incident (e : Edge n K) (i j : Fin n) (h : e.Incident i) :
    e.lap i j = C e.cond * ((if j = i then 1 else 0) - (if j = e.other i then e.phase i else 0)) := by
  unfold Edge.lap other phase
  congr 1
  rcases h with rfl | rfl
  · by_cases hst : e.src = e.tgt
    · rw [if_pos hst, if_pos rfl]
      by_cases hj : j = e.src
      · subst hj; simp [← hst]; ring
      · simp [hj, ← hst]
    · rw [if_neg hst, if_pos rfl, if_pos rfl]
      by_cases hj : j = e.src
      · subst hj; simp [hst, Ne.symm hst]
      · by_cases hj2 : j = e.tgt
        · subst hj2; simp [hst, Ne.symm hst]
        · simp [hj, hj2]
  · by_cases hst : e.src = e.tgt
    · rw [if_pos hst, ← hst, if_pos rfl]
      by_cases hj : j = e.src
      · subst hj; simp; ring
      · simp [hj]
    · rw [if_neg hst, if_neg (Ne.symm hst), if_neg (Ne.symm hst)]
      by_cases hj : j = e.tgt
      · subst hj; simp [hst, Ne.symm hst]
      · by_cases hj2 : j = e.src
        · subst hj2; simp [hst, Ne.symm hst]
        · simp [hj, hj2]

lemma lap_of_not_incident (e : Edge n K) (i j : Fin n) (h : ¬ e.Incident i) : e.lap i j = 0 := by
  unfold Incident at h
  push Not at h
  simp [Edge.lap, h.1, h.2]

/-- För en kant som inte är en ögla är fasen ett monom. -/
lemma phase_of_ne (e : Edge n K) (i : Fin n) (h : e.src ≠ e.tgt) :
    e.phase i = mono (if i = e.src then e.shift else -e.shift) := by
  unfold phase; rw [if_neg h]; split_ifs <;> rfl

end Edge

section expansion
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Multilinearitet i raderna: `det (Σ_k A_k)` radvis. -/
lemma det_sum_rows {m : ℕ} (A : Fin m → Matrix ι ι R) :
    (Matrix.of fun i j => ∑ k, A k i j).det = ∑ f : ι → Fin m, (Matrix.of fun i j => A (f i) i j).det := by
  have h := (detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R).toMultilinearMap.map_sum (fun i k => A k i)
  have e1 : (fun i => ∑ k, A k i) = (Matrix.of fun i j => ∑ k, A k i j) := by
    funext i j; simp [Finset.sum_apply]
  rw [e1] at h
  exact h

end expansion

/-- Valets funktionsgraf och faser. -/
def choiceMap (E : List (Edge n K)) (f : Fin n → Fin E.length) (i : Fin n) : Fin n :=
  (E.get (f i)).other i

def choicePhase (E : List (Edge n K)) (f : Fin n → Fin E.length) (i : Fin n) : LP2 K :=
  (E.get (f i)).phase i

/-- Valets bidrag. -/
def choiceTerm (E : List (Edge n K)) (f : Fin n → Fin E.length) : LP2 K :=
  if ∀ i, (E.get (f i)).Incident i then
    (∏ i, C (E.get (f i)).cond) *
      ∏ γ ∈ cycles (choiceMap E f), (1 - ∏ i ∈ γ, choicePhase E f i)
  else 0

/-- **CRSF-utvecklingen** (orienterad): `det Δ = Σ_f choiceTerm f`. -/
theorem specPoly_crsf (E : List (Edge n K)) :
    (Net.mk n E).specPoly = ∑ f : Fin n → Fin E.length, choiceTerm E f := by
  rw [Net.specPoly_mk]
  have hsum : (Matrix.of fun i j => (E.map fun e => e.lap i j).sum) =
      Matrix.of fun i j => ∑ k : Fin E.length, (Matrix.of fun i j => (E.get k).lap i j) i j := by
    refine Matrix.ext fun i j => ?_
    simp only [of_apply]
    rw [← List.sum_ofFn,
      show (List.ofFn fun k => (E.get k).lap i j) = (List.ofFn E.get).map (fun e => e.lap i j) from
        by rw [List.map_ofFn]; rfl, List.ofFn_get]
  rw [hsum, det_sum_rows]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [of_apply]
  unfold choiceTerm
  split_ifs with hinc
  · have hM : (Matrix.of fun i j => (E.get (f i)).lap i j) =
        Matrix.diagonal (fun i => C (E.get (f i)).cond) * funMat (choiceMap E f) (choicePhase E f) := by
      refine Matrix.ext fun i j => ?_
      rw [Matrix.diagonal_mul, of_apply, Edge.lap_of_incident _ _ _ (hinc i)]
      simp only [funMat, of_apply, choiceMap, choicePhase]
      rfl
    rw [hM, det_mul, det_diagonal, det_funMat]
  · push Not at hinc
    obtain ⟨i, hi⟩ := hinc
    apply det_eq_zero_of_row_eq_zero i
    intro j
    rw [of_apply]
    exact Edge.lap_of_not_incident _ _ _ hi

end

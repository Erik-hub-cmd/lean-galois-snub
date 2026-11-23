import LeanGalois.Imports
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Determinanten av `I - W` för en viktad funktionsgraf

`g : ι → ι` är en funktion (varje nod pekar på en nod), `ω : ι → R` vikter, och
`funMat g ω = I - W` med `W i (g i) = ω i`. Satsen:

  `det (I - W) = ∏_{γ cykel i g} (1 - ∏_{i ∈ γ} ω i)`.

Cyklerna är banorna av de periodiska punkterna. Beviset: radoperationer längs en cykel ger
faktorn `1 - w_γ` och nollställer en vikt; en vikt vars nod inte är periodisk och som inga
nollskilda vikter pekar på kan nollställas utan att `det` ändras.
-/

noncomputable section

open Function Matrix

namespace FunMat

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- `I - W`. -/
def funMat (g : ι → ι) (ω : ι → R) : Matrix ι ι R :=
  Matrix.of fun i j => (if j = i then 1 else 0) - (if j = g i then ω i else 0)

/-- Cykeln genom en (periodisk) punkt. -/
def cyc (g : ι → ι) (i : ι) : Finset ι :=
  (Finset.range (minimalPeriod g i)).image fun k => g^[k] i

instance decPer (g : ι → ι) : DecidablePred (· ∈ periodicPts g) := Classical.decPred _

/-- Alla cykler i funktionsgrafen. -/
def cycles (g : ι → ι) : Finset (Finset ι) :=
  (Finset.univ.filter fun i => i ∈ periodicPts g).image (cyc g)

section cyc
variable (g : ι → ι)

lemma iterate_mem_periodicPts {x : ι} (hx : x ∈ periodicPts g) (n : ℕ) :
    g^[n] x ∈ periodicPts g :=
  mk_mem_periodicPts (minimalPeriod_pos_of_mem_periodicPts hx)
    ((isPeriodicPt_minimalPeriod g x).apply_iterate n)

lemma mem_cyc {i : ι} (hi : i ∈ periodicPts g) (x : ι) : x ∈ cyc g i ↔ ∃ k, g^[k] i = x := by
  constructor
  · intro h
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 h
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    refine Finset.mem_image.2 ⟨k % minimalPeriod g i, ?_, iterate_mod_minimalPeriod_eq⟩
    exact Finset.mem_range.2 (Nat.mod_lt _ (minimalPeriod_pos_of_mem_periodicPts hi))

lemma self_mem_cyc {i : ι} (hi : i ∈ periodicPts g) : i ∈ cyc g i :=
  (mem_cyc g hi i).2 ⟨0, rfl⟩

lemma cyc_eq_of_mem {i j : ι} (hi : i ∈ periodicPts g) (hj : j ∈ cyc g i) : cyc g j = cyc g i := by
  obtain ⟨a, rfl⟩ := (mem_cyc g hi j).1 hj
  have hj' := iterate_mem_periodicPts g hi a
  ext x
  rw [mem_cyc g hj', mem_cyc g hi]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k + a, by rw [iterate_add_apply]⟩
  · rintro ⟨k, rfl⟩
    -- `i = g^[b] (g^[a] i)` med `a + b ≡ 0`
    have hL := minimalPeriod_pos_of_mem_periodicPts hi
    refine ⟨k + (minimalPeriod g i - a % minimalPeriod g i), ?_⟩
    rw [iterate_add_apply, ← iterate_add_apply g (minimalPeriod g i - a % minimalPeriod g i) a]
    congr 1
    rw [← iterate_mod_minimalPeriod_eq]
    have : (minimalPeriod g i - a % minimalPeriod g i + a) % minimalPeriod g i = 0 := by
      have h1 := Nat.mod_lt a hL
      have h2 : minimalPeriod g i - a % minimalPeriod g i + a =
          minimalPeriod g i * (a / minimalPeriod g i + 1) := by
        have h3 := Nat.div_add_mod a (minimalPeriod g i)
        rw [mul_add, mul_one]
        generalize minimalPeriod g i * (a / minimalPeriod g i) = M at *
        omega
      rw [h2, Nat.mul_mod_right]
    rw [this]
    rfl

/-- `∏_{i ∈ cyc} ω i` är produkten längs cykeln. -/
lemma prod_cyc {i : ι} (ω : ι → R) :
    ∏ x ∈ cyc g i, ω x = ∏ k ∈ Finset.range (minimalPeriod g i), ω (g^[k] i) := by
  rw [cyc, Finset.prod_image]
  intro a ha b hb hab
  exact iterate_injOn_Iio_minimalPeriod (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) hab

lemma not_mem_of_not_periodic {j : ι} (hj : j ∉ periodicPts g) :
    ∀ γ ∈ cycles g, j ∉ γ := by
  intro γ hγ hjγ
  unfold cycles at hγ
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hγ
  have hi' := (Finset.mem_filter.1 hi).2
  obtain ⟨k, rfl⟩ := (mem_cyc g hi' j).1 hjγ
  exact hj (iterate_mem_periodicPts g hi' k)

end cyc

section ops
variable (g : ι → ι)

/-- Raden `e_i`. -/
def e (i : ι) : ι → R := fun j => if j = i then 1 else 0

lemma updateRow_e (ω : ι → R) (j : ι) :
    updateRow (funMat g ω) j (e j) = funMat g (Function.update ω j 0) := by
  refine Matrix.ext fun i k => ?_
  by_cases hij : i = j
  · subst hij
    simp [funMat, e, updateRow_self]
  · rw [updateRow_ne hij]
    simp [funMat, Function.update_of_ne hij]

/-- **Löv**: om inga nollskilda vikter pekar på `j` och `g j ≠ j` kan `ω j` nollställas. -/
lemma det_leaf (ω : ι → R) (j : ι) (hgj : g j ≠ j) (hin : ∀ i, g i = j → ω i = 0) :
    (funMat g ω).det = (funMat g (Function.update ω j 0)).det := by
  have hrow : funMat g ω j = e j + (-ω j) • e (g j) := by
    ext k
    simp only [funMat, of_apply, e, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  conv_lhs => rw [← updateRow_eq_self (funMat g ω) j, hrow]
  rw [det_updateRow_add, det_updateRow_smul, updateRow_e]
  have h0 : (updateRow (funMat g ω) j (e (g j))).det = 0 := by
    apply det_eq_zero_of_column_eq_zero j
    intro i
    by_cases hij : i = j
    · subst hij; simp [e, updateRow_self, Ne.symm hgj]
    · rw [updateRow_ne hij]
      simp only [funMat, of_apply, if_neg (Ne.symm hij)]
      split_ifs with h
      · rw [hin i h.symm]; ring
      · ring
  rw [h0, mul_zero, add_zero]

/-- **Cykel**: för en periodisk punkt `i₀` med cykelvikt `w` är
`det (I - W) = (1 - w) · det (I - W)|_{ω i₀ = 0}`. -/
lemma det_cycle (ω : ι → R) (i₀ : ι) (hi₀ : i₀ ∈ periodicPts g) :
    (funMat g ω).det =
      (1 - ∏ k ∈ Finset.range (minimalPeriod g i₀), ω (g^[k] i₀)) *
        (funMat g (Function.update ω i₀ 0)).det := by
  set L := minimalPeriod g i₀
  have hL := minimalPeriod_pos_of_mem_periodicPts hi₀
  set P : ℕ → R := fun k => ∏ t ∈ Finset.range k, ω (g^[t] i₀)
  set row : ℕ → ι → R := fun k => e i₀ - P k • e (g^[k] i₀)
  have hstep : ∀ k, 1 ≤ k → k ≤ L →
      (updateRow (funMat g ω) i₀ (row k)).det = (funMat g ω).det := by
    intro k hk1 hkL
    induction k, hk1 using Nat.le_induction with
    | base =>
      have h1 : row 1 = funMat g ω i₀ := by
        ext j
        simp only [row, P, funMat, of_apply, e, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          Finset.prod_range_one, iterate_zero, id_eq, iterate_one]
        split_ifs <;> ring
      rw [h1, updateRow_eq_self]
    | succ k hk ih =>
      rw [← ih (by omega)]
      have hne : g^[k] i₀ ≠ i₀ := by
        intro h
        have := (iterate_eq_iterate_iff_of_lt_minimalPeriod (f := g) (x := i₀)
          (show k < L by omega) hL).1 (by rw [h]; rfl)
        omega
      rw [← det_updateRow_add_smul_self (updateRow (funMat g ω) i₀ (row k)) (Ne.symm hne) (P k)]
      rw [updateRow_self, updateRow_idem]
      congr 2
      rw [updateRow_ne hne]
      ext j
      simp only [row, P, funMat, of_apply, e, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Finset.prod_range_succ, iterate_succ_apply']
      split_ifs <;> ring
  have hL' := hstep L hL le_rfl
  have hrowL : row L = (1 - P L) • e i₀ := by
    ext j
    simp only [row, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, iterate_minimalPeriod, L]
    ring
  rw [← hL', hrowL, det_updateRow_smul, updateRow_e]

end ops

/-- **Determinanten av en viktad funktionsgraf.** -/
theorem det_funMat (g : ι → ι) (ω : ι → R) :
    (funMat g ω).det = ∏ γ ∈ cycles g, (1 - ∏ i ∈ γ, ω i) := by
  classical
  -- stark induktion på antalet nollskilda vikter
  suffices H : ∀ N : ℕ, ∀ ω : ι → R, (Finset.univ.filter fun i => ω i ≠ 0).card = N →
      (funMat g ω).det = ∏ γ ∈ cycles g, (1 - ∏ i ∈ γ, ω i) from H _ ω rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro ω hN
  set S := Finset.univ.filter fun i => ω i ≠ 0
  have hdec : ∀ j, ω j ≠ 0 →
      (Finset.univ.filter fun i => Function.update ω j 0 i ≠ 0).card < N := by
    intro j hj
    rw [← hN]
    apply Finset.card_lt_card
    refine ⟨fun i hi => ?_, fun h => ?_⟩
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      by_cases hij : i = j
      · subst hij; simp at hi
      · rwa [Function.update_of_ne hij] at hi
    · have := h (Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩)
      simp at this
  by_cases hS : S = ∅
  · -- alla vikter noll
    have hω : ω = 0 := by
      ext i
      by_contra h
      have : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩
      rw [hS] at this; simp at this
    subst hω
    have h1 : funMat g (0 : ι → R) = 1 := by
      refine Matrix.ext fun i j => ?_
      simp [funMat, Matrix.one_apply, eq_comm]
    rw [h1, det_one]
    symm
    apply Finset.prod_eq_one
    intro γ hγ
    unfold cycles at hγ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hγ
    rw [Finset.prod_eq_zero (self_mem_cyc g (Finset.mem_filter.1 hi).2) rfl, sub_zero]
  obtain ⟨j, hj⟩ := Finset.nonempty_of_ne_empty hS
  have hj0 : ω j ≠ 0 := (Finset.mem_filter.1 hj).2
  by_cases hper : ∃ i ∈ S, i ∈ periodicPts g
  · -- en cykel med en nollskild vikt
    obtain ⟨i₀, hi₀S, hi₀⟩ := hper
    have hi₀0 : ω i₀ ≠ 0 := (Finset.mem_filter.1 hi₀S).2
    rw [det_cycle g ω i₀ hi₀, ih _ (hdec i₀ hi₀0) _ rfl]
    have hγ₀ : cyc g i₀ ∈ cycles g := by
      unfold cycles
      exact Finset.mem_image.2 ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi₀⟩, rfl⟩
    rw [← Finset.mul_prod_erase _ _ hγ₀, ← Finset.mul_prod_erase _ _ hγ₀]
    rw [Finset.prod_eq_zero (self_mem_cyc g hi₀) (by simp), sub_zero, one_mul, prod_cyc]
    congr 1
    refine Finset.prod_congr rfl fun γ hγ => ?_
    obtain ⟨hne, hγ'⟩ := Finset.mem_erase.1 hγ
    have hnot : i₀ ∉ γ := by
      intro hmem
      unfold cycles at hγ'
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hγ'
      exact hne (cyc_eq_of_mem g (Finset.mem_filter.1 hi).2 hmem).symm
    congr 1
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [Function.update_of_ne (fun h => hnot (by rw [← h]; exact hx))]
  · -- ingen nollskild vikt på en cykel: hitta ett löv
    push Not at hper
    have hleaf : ∃ j ∈ S, ∀ i ∈ S, g i ≠ j := by
      by_contra hno
      push Not at hno
      -- varje nod i `S` har en föregångare i `S`
      choose! p hpS hp using hno
      obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => p^[k] j)
      have hpS' : ∀ k, p^[k] j ∈ S := by
        intro k
        induction k with
        | zero => exact hj
        | succ k ihk => rw [iterate_succ_apply']; exact hpS _ ihk
      have hgp : ∀ k x, x ∈ S → g^[k] (p^[k] x) = x := by
        intro k
        induction k with
        | zero => intro x _; rfl
        | succ k ihk =>
          intro x hx
          rw [iterate_succ_apply, iterate_succ_apply', hp _ (by
            have : ∀ k, p^[k] x ∈ S := by
              intro k
              induction k with
              | zero => exact hx
              | succ k ihk' => rw [iterate_succ_apply']; exact hpS _ ihk'
            exact this k), ihk x hx]
      wlog hlt : a < b generalizing a b
      · exact this b a hab.symm heq.symm (lt_of_le_of_ne (not_lt.1 hlt) hab.symm)
      set y := p^[b] j
      have hy : g^[b - a] y = y := by
        have h1 : y = p^[b - a] (p^[a] j) := by
          show p^[b] j = _
          rw [← iterate_add_apply, Nat.sub_add_cancel hlt.le]
        calc g^[b - a] y = g^[b - a] (p^[b - a] (p^[a] j)) := by rw [h1]
          _ = p^[a] j := hgp _ _ (hpS' a)
          _ = y := heq
      exact hper y (hpS' b) (mk_mem_periodicPts (by omega) hy)
    obtain ⟨j, hjS, hjin⟩ := hleaf
    have hj0 : ω j ≠ 0 := (Finset.mem_filter.1 hjS).2
    have hjper : j ∉ periodicPts g := hper j hjS
    have hgj : g j ≠ j := fun h => hjper (mk_mem_periodicPts one_pos (by simp [IsPeriodicPt, IsFixedPt, h]))
    have hin : ∀ i, g i = j → ω i = 0 := by
      intro i hi
      by_contra h
      exact hjin i (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩) hi
    rw [det_leaf g ω j hgj hin, ih _ (hdec j hj0) _ rfl]
    refine Finset.prod_congr rfl fun γ hγ => ?_
    congr 1
    refine Finset.prod_congr rfl fun x hx => ?_
    have : x ≠ j := fun h => not_mem_of_not_periodic g hjper γ hγ (by rw [← h]; exact hx)
    rw [Function.update_of_ne this]

end FunMat

import LeanGalois.Local
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.MonoidAlgebra.Support

/-!
# Avbildningar av Laurentpolynom och hur sidpolynom beter sig under dem

* `mapC f`: koefficienterna avbildas med en ringhomomorfi `f` (t.ex. `ℝ → ℂ`).
* `mapD φ`: monomavbildning `z^v ↦ z^{φ v}` för en additiv homomorfi `φ : ℤ² → ℤ²`.
* `twist ω`: `X ↦ ωX` (dvs. `z^v ↦ ω^{v.1} z^v`).
* `evP x z`: evaluering i en punkt `(x, z)` med `x, z` inverterbara.
-/

noncomputable section

open AddMonoidAlgebra

namespace LP2

variable {K L : Type*} [CommRing K] [CommRing L]

def mapC (f : K →+* L) : LP2 K →+* LP2 L := AddMonoidAlgebra.mapRingHom (ℤ × ℤ) f

@[simp] lemma mapC_single (f : K →+* L) (v : ℤ × ℤ) (a : K) :
    mapC f (single v a) = single v (f a) := by simp [mapC]

lemma coeff_mapC (f : K →+* L) (p : LP2 K) (v : ℤ × ℤ) : (mapC f p).coeff v = f (p.coeff v) := by
  simp [mapC]

def mapD (φ : ℤ × ℤ →+ ℤ × ℤ) : LP2 K →+* LP2 K := AddMonoidAlgebra.mapDomainRingHom K φ

@[simp] lemma mapD_single (φ : ℤ × ℤ →+ ℤ × ℤ) (v : ℤ × ℤ) (a : K) :
    mapD φ (single v a) = single (φ v) a := by simp [mapD]

/-- `X ↦ ω X`. -/
def twist (ω : Kˣ) : LP2 K →+* LP2 K :=
  (AddMonoidAlgebra.lift K (LP2 K) (ℤ × ℤ)
    { toFun := fun v => single (Multiplicative.toAdd v) ((ω ^ (Multiplicative.toAdd v).1 : Kˣ) : K)
      map_one' := by simp; rfl
      map_mul' := by
        intro a b
        simp [single_mul_single, zpow_add] }).toRingHom

@[simp] lemma twist_single (ω : Kˣ) (v : ℤ × ℤ) (a : K) :
    twist ω (single v a) = single v (a * ((ω ^ v.1 : Kˣ) : K)) := by
  simp [twist, AddMonoidAlgebra.lift_single, smul_single]

/-- Evaluering i `(x, z)`. -/
def evP (x z : Lˣ) : LP2 L →+* L :=
  (AddMonoidAlgebra.lift L L (ℤ × ℤ)
    { toFun := fun v => ((x ^ (Multiplicative.toAdd v).1 * z ^ (Multiplicative.toAdd v).2 : Lˣ) : L)
      map_one' := by simp
      map_mul' := by
        intro a b
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, zpow_add, Units.val_mul]
        ring }).toRingHom

@[simp] lemma evP_single (x z : Lˣ) (v : ℤ × ℤ) (a : L) :
    evP x z (single v a) = a * ((x ^ v.1 * z ^ v.2 : Lˣ) : L) := by
  simp [evP, AddMonoidAlgebra.lift_single]

/-! ## Sidor under avbildningarna -/

section faces

variable (n : ℤ × ℤ) (k : ℤ)

lemma faceAt_zero : faceAt n k (0 : LP2 K) = 0 := by
  simp only [faceAt, coeff_zero, Finsupp.filter_zero]; rfl

lemma faceAt_single (v : ℤ × ℤ) (a : K) :
    faceAt n k (single v a) = if dot n v = k then single v a else 0 := by
  split_ifs with h
  · exact faceAt_single_pos n k v a h
  · exact faceAt_single_neg n k v a h

lemma faceAt_mapD (φ : ℤ × ℤ →+ ℤ × ℤ) (n' : ℤ × ℤ) (hφ : ∀ v, dot n (φ v) = dot n' v)
    (p : LP2 K) : faceAt n k (mapD φ p) = mapD φ (faceAt n' k p) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp [faceAt_zero]
  | add p q hp hq => rw [map_add, faceAt_add, faceAt_add, hp, hq, map_add]
  | single v a =>
    rw [mapD_single, faceAt_single, faceAt_single, hφ]
    split_ifs <;> simp

lemma faceAt_twist (ω : Kˣ) (p : LP2 K) : faceAt n k (twist ω p) = twist ω (faceAt n k p) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp [faceAt_zero]
  | add p q hp hq => rw [map_add, faceAt_add, faceAt_add, hp, hq, map_add]
  | single v a =>
    rw [twist_single, faceAt_single, faceAt_single]
    split_ifs <;> simp

lemma faceAt_mapC (f : K →+* L) (p : LP2 K) : faceAt n k (mapC f p) = mapC f (faceAt n k p) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp [faceAt_zero]
  | add p q hp hq => rw [map_add, faceAt_add, faceAt_add, hp, hq, map_add]
  | single v a =>
    rw [mapC_single, faceAt_single, faceAt_single]
    split_ifs <;> simp

lemma isTop_iff (p : LP2 K) : IsTop n k p ↔ ∀ v, k < dot n v → p.coeff v = 0 := by
  constructor
  · intro h v hv
    by_contra h0
    exact absurd (h v (Finsupp.mem_support_iff.2 h0)) (not_le.2 hv)
  · intro h v hv
    by_contra h0
    exact Finsupp.mem_support_iff.1 hv (h v (not_le.1 h0))

lemma coeff_twist (ω : Kˣ) (p : LP2 K) (v : ℤ × ℤ) :
    (twist ω p).coeff v = p.coeff v * ((ω ^ v.1 : Kˣ) : K) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, Finsupp.add_apply, Finsupp.add_apply, hp, hq,
      add_mul]
  | single w a =>
    rw [twist_single, coeff_single, coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; rfl
    · simp

lemma isTop_twist (ω : Kˣ) {p : LP2 K} (h : IsTop n k p) : IsTop n k (twist ω p) := by
  rw [isTop_iff] at *
  intro v hv
  rw [coeff_twist, h v hv, zero_mul]

lemma isTop_mapC (f : K →+* L) {p : LP2 K} (h : IsTop n k p) : IsTop n k (mapC f p) := by
  rw [isTop_iff] at *
  intro v hv
  rw [coeff_mapC, h v hv, map_zero]

lemma coeff_mapD_of_inj (φ : ℤ × ℤ →+ ℤ × ℤ) (hinj : Function.Injective φ) (p : LP2 K) (v : ℤ × ℤ) :
    (mapD φ p).coeff (φ v) = p.coeff v := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, Finsupp.add_apply, Finsupp.add_apply, hp, hq]
  | single w a =>
    rw [mapD_single, coeff_single, coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    simp [hinj.eq_iff]

lemma coeff_mapD_of_not_mem (φ : ℤ × ℤ →+ ℤ × ℤ) (p : LP2 K) (w : ℤ × ℤ) (hw : w ∉ Set.range φ) :
    (mapD φ p).coeff w = 0 := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => rw [map_add, coeff_add, Finsupp.add_apply, hp, hq, add_zero]
  | single u a =>
    rw [mapD_single, coeff_single, Finsupp.single_apply, if_neg]
    rintro rfl; exact hw ⟨u, rfl⟩

lemma isTop_mapD_iff (φ : ℤ × ℤ →+ ℤ × ℤ) (hinj : Function.Injective φ) (n' : ℤ × ℤ)
    (hφ : ∀ v, dot n (φ v) = dot n' v) (p : LP2 K) :
    IsTop n k (mapD φ p) ↔ IsTop n' k p := by
  have hc := coeff_mapD_of_inj φ hinj p
  have hc' := coeff_mapD_of_not_mem φ p
  rw [isTop_iff, isTop_iff]
  constructor
  · intro h v hv
    rw [← hc]; exact h _ (by rw [hφ]; exact hv)
  · intro h w hw
    by_cases hr : w ∈ Set.range φ
    · obtain ⟨v, rfl⟩ := hr
      rw [hc]; exact h v (by rw [← hφ]; exact hw)
    · exact hc' w hr

/-- Toppsidan av en produkt är produkten av toppsidorna. -/
lemma face_mul {p q : LP2 K} {k₁ k₂ : ℤ} (hp : IsTop n k₁ p) (hq : IsTop n k₂ q) :
    IsTop n (k₁ + k₂) (p * q) ∧ faceAt n (k₁ + k₂) (p * q) = faceAt n k₁ p * faceAt n k₂ q := by
  classical
  -- p = fp + rp, där rp ligger strikt under nivån
  set fp := faceAt n k₁ p
  set fq := faceAt n k₂ q
  set rp := p - fp
  set rq := q - fq
  have hsupp : ∀ (a b : LP2 K) (A B : ℤ → Prop),
      (∀ v ∈ a.coeff.support, A (dot n v)) → (∀ v ∈ b.coeff.support, B (dot n v)) →
      ∀ v ∈ (a * b).coeff.support, ∃ i j, A i ∧ B j ∧ dot n v = i + j := by
    intro a b A B ha hb v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset a b hv)
    exact ⟨_, _, ha x hx, hb y hy, by simp [dot]; ring⟩
  have hfp : ∀ v ∈ fp.coeff.support, dot n v = k₁ := by
    intro v hv
    simp only [fp, faceAt, coeff_ofCoeff, Finsupp.mem_support_iff, Finsupp.filter_apply] at hv
    by_contra h; exact hv (if_neg h)
  have hfq : ∀ v ∈ fq.coeff.support, dot n v = k₂ := by
    intro v hv
    simp only [fq, faceAt, coeff_ofCoeff, Finsupp.mem_support_iff, Finsupp.filter_apply] at hv
    by_contra h; exact hv (if_neg h)
  have hrp : ∀ v ∈ rp.coeff.support, dot n v < k₁ := by
    intro v hv
    have hv' : p.coeff v - fp.coeff v ≠ 0 := by simpa [rp, coeff_sub] using hv
    by_contra h
    rcases (not_lt.1 h).lt_or_eq with h | h
    · exact hv' (by rw [(isTop_iff n k₁ p).1 hp v h]; simp [fp, faceAt, Finsupp.filter_apply, h.ne'])
    · exact hv' (by rw [faceAt_coeff_of n k₁ p v h.symm, sub_self])
  have hrq : ∀ v ∈ rq.coeff.support, dot n v < k₂ := by
    intro v hv
    have hv' : q.coeff v - fq.coeff v ≠ 0 := by simpa [rq, coeff_sub] using hv
    by_contra h
    rcases (not_lt.1 h).lt_or_eq with h | h
    · exact hv' (by rw [(isTop_iff n k₂ q).1 hq v h]; simp [fq, faceAt, Finsupp.filter_apply, h.ne'])
    · exact hv' (by rw [faceAt_coeff_of n k₂ q v h.symm, sub_self])
  have hdec : p * q = fp * fq + (fp * rq + rp * fq + rp * rq) := by
    simp only [rp, rq]; ring
  -- nivåerna i de fyra produkterna
  have h1 : ∀ v ∈ (fp * fq).coeff.support, dot n v = k₁ + k₂ := by
    intro v hv
    obtain ⟨i, j, hi, hj, h⟩ := hsupp fp fq (· = k₁) (· = k₂) hfp hfq v hv
    rw [h, hi, hj]
  have hlow : ∀ v ∈ (fp * rq + rp * fq + rp * rq).coeff.support, dot n v < k₁ + k₂ := by
    intro v hv
    simp only [coeff_add] at hv
    rcases Finset.mem_union.1 (Finsupp.support_add hv) with hv | hv
    · rcases Finset.mem_union.1 (Finsupp.support_add hv) with hv | hv
      · obtain ⟨i, j, hi, hj, h⟩ := hsupp fp rq (· = k₁) (· < k₂) hfp hrq v hv
        omega
      · obtain ⟨i, j, hi, hj, h⟩ := hsupp rp fq (· < k₁) (· = k₂) hrp hfq v hv
        omega
    · obtain ⟨i, j, hi, hj, h⟩ := hsupp rp rq (· < k₁) (· < k₂) hrp hrq v hv
      omega
  have hface_low : faceAt n (k₁ + k₂) (fp * rq + rp * fq + rp * rq) = 0 := by
    ext v
    simp only [faceAt, coeff_ofCoeff, Finsupp.filter_apply, coeff_zero, Finsupp.coe_zero,
      Pi.zero_apply]
    split_ifs with h
    · by_contra h0
      exact absurd (hlow v (Finsupp.mem_support_iff.2 h0)) (by omega)
    · rfl
  have hface_top : faceAt n (k₁ + k₂) (fp * fq) = fp * fq := by
    ext v
    simp only [faceAt, coeff_ofCoeff, Finsupp.filter_apply]
    split_ifs with h
    · rfl
    · by_contra h0
      exact h (h1 v (Finsupp.mem_support_iff.2 (Ne.symm h0)))
  refine ⟨?_, ?_⟩
  · intro v hv
    rw [hdec, coeff_add] at hv
    rcases Finset.mem_union.1 (Finsupp.support_add hv) with hv | hv
    · exact (h1 v hv).le
    · exact (hlow v hv).le
  · rw [hdec, faceAt_add, hface_low, add_zero, hface_top]

/-- Ett nollskilt polynom som är noll i en punkt med inverterbara koordinater har minst två monom. -/
lemma two_monomials [IsDomain L] {p : LP2 L} (hp : p ≠ 0) (x z : Lˣ) (h0 : evP x z p = 0) :
    ∃ v ∈ p.coeff.support, ∃ w ∈ p.coeff.support, v ≠ w := by
  classical
  by_contra hne
  push_neg at hne
  obtain ⟨v, hv⟩ : ∃ v, v ∈ p.coeff.support := by
    by_contra h; push_neg at h
    exact hp (by ext w; by_contra hw; exact h w (Finsupp.mem_support_iff.2 hw))
  have hp' : p = single v (p.coeff v) := by
    ext w
    rw [coeff_single, Finsupp.single_apply]
    split_ifs with h
    · rw [h]
    · by_contra hw
      exact h (hne v hv w (Finsupp.mem_support_iff.2 hw))
  rw [hp', evP_single] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · exact Finsupp.mem_support_iff.1 hv h
  · exact Units.ne_zero _ h

end faces

end LP2

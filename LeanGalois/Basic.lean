import LeanGalois.Imports

/-!
# Periodiska resistornät och deras spektralpolynom

Allt byggs tunt ovanpå Mathlib.

* `LP2 K = K[ℤ × ℤ]`: Laurentpolynom i två variabler `X, Z` (Bloch-variablerna för
  torusens två periodvektorer). Monomet `X^a Z^b` är `mono (a, b)`.
* Ett nät på torusen är en lista kanter `(src, tgt, shift, cond)`: kanten går från noden
  `src` i grundcellen till noden `tgt` i cellen förskjuten med `shift`, med konduktans `cond`.
  Öglor (`src = tgt`) och parallella kanter är tillåtna.
* `Net.laplacian`: den magnetiska Laplacematrisen Δ(X, Z); kanten bidrar med
  `c` på diagonalen i båda ändar och `-c·z^shift`, `-c·z^{-shift}` utanför.
  (En ögla av klass ℓ ger alltså `c(2 - z^ℓ - z^{-ℓ})`, som i avsnitt 10.1.)
* `Net.specPoly = det Δ`: spektralpolynomet. Spektralkurvan är dess nollställemängd.
* `faceAt n k p`: delen av `p` på linjen `⟨n, v⟩ = k`. Om alla exponenter har `⟨n,v⟩ ≤ k`
  (`IsTop n k p`) är det sidpolynomet till Newtonpolygonens sida med yttre normal `n`.
-/

noncomputable section

open AddMonoidAlgebra

/-- Laurentpolynom i två variabler med koefficienter i `K`. -/
abbrev LP2 (K : Type*) [CommRing K] := AddMonoidAlgebra K (ℤ × ℤ)

namespace LP2

variable {K : Type*} [CommRing K]

/-- Monomet `X^{v.1} Z^{v.2}`. -/
def mono (v : ℤ × ℤ) : LP2 K := single v 1

/-- Konstanta Laurentpolynom. -/
def C : K →+* LP2 K := algebraMap K (LP2 K)

lemma C_apply (c : K) : C c = single 0 c := rfl

lemma C_mul_mono (c : K) (v : ℤ × ℤ) : C c * mono v = single v c := by
  simp [C_apply, mono, single_mul_single]

lemma mono_add (v w : ℤ × ℤ) : (mono (v + w) : LP2 K) = mono v * mono w := by
  simp [mono, single_mul_single]

lemma mono_zero : (mono 0 : LP2 K) = 1 := rfl

lemma C_mul_eq_smul (c : K) (p : LP2 K) : C c * p = c • p := by
  rw [C, Algebra.smul_def]

/-- Skalärprodukt `⟨n, v⟩`. -/
def dot (n v : ℤ × ℤ) : ℤ := n.1 * v.1 + n.2 * v.2

/-- Delen av `p` på linjen `⟨n, v⟩ = k`. -/
def faceAt (n : ℤ × ℤ) (k : ℤ) (p : LP2 K) : LP2 K :=
  ofCoeff (p.coeff.filter fun v => dot n v = k)

/-- Alla exponenter i `p` uppfyller `⟨n, v⟩ ≤ k`. -/
def IsTop (n : ℤ × ℤ) (k : ℤ) (p : LP2 K) : Prop :=
  ∀ v ∈ p.coeff.support, dot n v ≤ k

section face

variable (n : ℤ × ℤ) (k : ℤ)

@[simp] lemma faceAt_add (p q : LP2 K) : faceAt n k (p + q) = faceAt n k p + faceAt n k q := by
  simp [faceAt, coeff_add, Finsupp.filter_add, ofCoeff_add]

@[simp] lemma faceAt_neg (p : LP2 K) : faceAt n k (-p) = -faceAt n k p := by
  have h := faceAt_add n k p (-p)
  rw [add_neg_cancel] at h
  have h0 : faceAt n k (0 : LP2 K) = 0 := by
    simp only [faceAt, coeff_zero, Finsupp.filter_zero]; rfl
  rw [h0] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

@[simp] lemma faceAt_sub (p q : LP2 K) : faceAt n k (p - q) = faceAt n k p - faceAt n k q := by
  rw [sub_eq_add_neg, faceAt_add, faceAt_neg, ← sub_eq_add_neg]

lemma faceAt_single_pos (v : ℤ × ℤ) (a : K) (h : dot n v = k) :
    faceAt n k (single v a) = single v a := by
  simp only [faceAt, coeff_single]
  rw [Finsupp.filter_single_of_pos (fun v => dot n v = k) h, ofCoeff_single]

lemma faceAt_single_neg (v : ℤ × ℤ) (a : K) (h : ¬ dot n v = k) :
    faceAt n k (single v a) = 0 := by
  simp only [faceAt, coeff_single]
  rw [Finsupp.filter_single_of_neg (fun v => dot n v = k) h]
  rfl

lemma faceAt_C_mul (c : K) (p : LP2 K) : faceAt n k (C c * p) = C c * faceAt n k p := by
  rw [C_mul_eq_smul, C_mul_eq_smul]
  simp only [faceAt]
  congr 1
  ext v
  simp [Finsupp.filter_apply, coeff_smul]

lemma faceAt_coeff_of (p : LP2 K) (v : ℤ × ℤ) (h : dot n v = k) :
    (faceAt n k p).coeff v = p.coeff v := by
  simp [faceAt, coeff_ofCoeff, Finsupp.filter_apply, h]

lemma isTop_add {p q : LP2 K} (hp : IsTop n k p) (hq : IsTop n k q) : IsTop n k (p + q) := by
  intro v hv
  rw [coeff_add] at hv
  rcases Finset.mem_union.1 (Finsupp.support_add hv) with h | h
  exacts [hp v h, hq v h]

lemma isTop_neg {p : LP2 K} (hp : IsTop n k p) : IsTop n k (-p) := by
  intro v hv
  apply hp v
  simpa [coeff_neg] using hv

lemma isTop_sub {p q : LP2 K} (hp : IsTop n k p) (hq : IsTop n k q) : IsTop n k (p - q) := by
  rw [sub_eq_add_neg]; exact isTop_add n k hp (isTop_neg n k hq)

lemma isTop_single {v : ℤ × ℤ} (a : K) (h : dot n v ≤ k) : IsTop n k (single v a) := by
  intro w hw
  rw [coeff_single] at hw
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hw)]
  exact h

lemma isTop_C_mul (c : K) {p : LP2 K} (hp : IsTop n k p) : IsTop n k (C c * p) := by
  intro v hv
  rw [C_mul_eq_smul, coeff_smul] at hv
  exact hp v (Finsupp.support_smul hv)

end face

/-- Evaluering `X ↦ 1, Z ↦ w` (för `w ≠ 0`) som ringhomomorfi `ℝ[ℤ²] → ℝ`. -/
def evZ (w : ℝ) (hw : w ≠ 0) : LP2 ℝ →+* ℝ :=
  (AddMonoidAlgebra.lift ℝ ℝ (ℤ × ℤ)
    { toFun := fun v => w ^ (Multiplicative.toAdd v).2
      map_one' := by simp
      map_mul' := by
        intro a b
        simp [zpow_add₀ hw] }).toRingHom

lemma evZ_single (w : ℝ) (hw : w ≠ 0) (v : ℤ × ℤ) (a : ℝ) :
    evZ w hw (single v a) = a * w ^ v.2 := by
  simp [evZ, AddMonoidAlgebra.lift_single]

lemma evZ_mono (w : ℝ) (hw : w ≠ 0) (v : ℤ × ℤ) : evZ w hw (mono v) = w ^ v.2 := by
  simp [mono, evZ_single]

lemma evZ_C (w : ℝ) (hw : w ≠ 0) (c : ℝ) : evZ w hw (C c) = c := by
  simp [C_apply, evZ_single]

end LP2

open LP2

/-- En kant i ett periodiskt nät med `n` noder per cell. -/
structure Edge (n : ℕ) (K : Type*) where
  src : Fin n
  tgt : Fin n
  shift : ℤ × ℤ
  cond : K

/-- Ett periodiskt nät på torusen: `n` noder i grundcellen och en lista kanter. -/
structure Net (K : Type*) where
  n : ℕ
  edges : List (Edge n K)

variable {K : Type*} [CommRing K]

/-- Kantens bidrag till Laplacematrisens post `(i, j)`. -/
def Edge.lap {n : ℕ} (e : Edge n K) (i j : Fin n) : LP2 K :=
  C e.cond * ((if i = e.src ∧ j = e.src then 1 else 0) + (if i = e.tgt ∧ j = e.tgt then 1 else 0)
    - (if i = e.src ∧ j = e.tgt then mono e.shift else 0)
    - (if i = e.tgt ∧ j = e.src then mono (-e.shift) else 0))

/-- Laplacematrisen Δ(X, Z) (med Bloch-faser). -/
def Net.laplacian (G : Net K) : Matrix (Fin G.n) (Fin G.n) (LP2 K) :=
  Matrix.of fun i j => (G.edges.map fun e => e.lap i j).sum

/-- Spektralpolynomet `det Δ(X, Z)`. -/
def Net.specPoly (G : Net K) : LP2 K := G.laplacian.det

/-- Alla produkter av (ändligt många) konduktanser i `G`. -/
def Net.condProds (G : Net K) : Submonoid K :=
  Submonoid.closure {c | ∃ e ∈ G.edges, e.cond = c}

/-- **Slutsatsen i Lemma 4(b)**, som påstående om ett nät `G`: för varje sida av
Newtonpolygonen (yttre normal `n`, nivå `k`, minst två monom på sidan) finns en riktning
`s ≠ 0` längs sidan så att sidpolynomet är
`c · z^m · ∏ (α_T + ε β_T z^s)` med `α_T, β_T` produkter av konduktanser i `G`. -/
def SideSplits (G : Net K) : Prop :=
  ∀ n : ℤ × ℤ, ∀ k : ℤ, n ≠ 0 → IsTop n k G.specPoly →
    (∃ v ∈ (faceAt n k G.specPoly).coeff.support, ∃ w ∈ (faceAt n k G.specPoly).coeff.support, v ≠ w) →
    ∃ s : ℤ × ℤ, s ≠ 0 ∧ dot n s = 0 ∧
    ∃ c : K, c ≠ 0 ∧ ∃ m : ℤ × ℤ, ∃ ε : K, (ε = 1 ∨ ε = -1) ∧
    ∃ L : List (K × K), (∀ ab ∈ L, ab.1 ∈ G.condProds ∧ ab.2 ∈ G.condProds) ∧
      faceAt n k G.specPoly = C c * mono m * (L.map fun ab => C ab.1 + C (ε * ab.2) * mono s).prod

@[simp] lemma Net.laplacian_apply (G : Net K) (i j : Fin G.n) :
    G.laplacian i j = (G.edges.map fun e => e.lap i j).sum := rfl

lemma Net.specPoly_mk (n : ℕ) (E : List (Edge n K)) :
    (Net.mk n E).specPoly = (Matrix.of fun i j => (E.map fun e => e.lap i j).sum).det := rfl

import LeanGalois.Maps
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Övertorusar: lyft av nät och produktformeln (Lemma 2)

* `Net.mapCond f`: konduktanserna avbildas med `f` (t.ex. `ℝ → ℂ`).
* `Net.transform φ`: förskjutningarna avbildas med `φ : ℤ² →+ ℤ²` (koordinatbyte med GL₂(ℤ)).
* `Net.liftX d G`: `G` lyft till övertorusen med `d` gånger så lång period i `X`-led.

Huvudresultat (`specPoly_liftX`): om `ζ` är en primitiv `d`:te enhetsrot i en kropp `K` så är
`det Δ_lyft (X^d, Z) = ∏_{k<d} det Δ_G (ζ^k X, Z)`.
-/

noncomputable section

open LP2 AddMonoidAlgebra Matrix

variable {K L : Type*}

namespace Net

section maps
variable [CommRing K] [CommRing L]

def mapCond (f : K →+* L) (G : Net K) : Net L :=
  ⟨G.n, G.edges.map fun e => ⟨e.src, e.tgt, e.shift, f e.cond⟩⟩

def transform (φ : ℤ × ℤ →+ ℤ × ℤ) (G : Net K) : Net K :=
  ⟨G.n, G.edges.map fun e => ⟨e.src, e.tgt, φ e.shift, e.cond⟩⟩

lemma lap_mapC (f : K →+* L) {n : ℕ} (e : Edge n K) (i j : Fin n) :
    mapC f (e.lap i j) = (⟨e.src, e.tgt, e.shift, f e.cond⟩ : Edge n L).lap i j := by
  simp only [Edge.lap, map_mul, map_sub, map_add, apply_ite (mapC f), map_one, map_zero, C_apply,
    mono, mapC_single]

lemma lap_mapD (φ : ℤ × ℤ →+ ℤ × ℤ) {n : ℕ} (e : Edge n K) (i j : Fin n) :
    mapD φ (e.lap i j) = (⟨e.src, e.tgt, φ e.shift, e.cond⟩ : Edge n K).lap i j := by
  simp only [Edge.lap, map_mul, map_sub, map_add, apply_ite (mapD φ), map_one, map_zero, C_apply,
    mono, mapD_single, map_neg]

theorem specPoly_mapCond (f : K →+* L) (G : Net K) :
    (G.mapCond f).specPoly = mapC f G.specPoly := by
  obtain ⟨n, E⟩ := G
  rw [mapCond, Net.specPoly_mk, Net.specPoly_mk, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, of_apply, map_list_sum, List.map_map,
    Function.comp_def, lap_mapC]

theorem specPoly_transform (φ : ℤ × ℤ →+ ℤ × ℤ) (G : Net K) :
    (G.transform φ).specPoly = mapD φ G.specPoly := by
  obtain ⟨n, E⟩ := G
  rw [transform, Net.specPoly_mk, Net.specPoly_mk, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, of_apply, map_list_sum, List.map_map,
    Function.comp_def, lap_mapD]

end maps

end Net

/-! ## Lyftet i `X`-led -/

namespace Lift

variable (d : ℕ) [NeZero d]

lemma d_pos : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)

/-- `(a + s) mod d`. -/
def idx (s : ℤ) (a : Fin d) : Fin d :=
  ⟨(((a : ℤ) + s) % d).toNat, by
    have h0 : (0 : ℤ) ≤ ((a : ℤ) + s) % d := Int.emod_nonneg _ (d_pos d).ne'
    have h1 : ((a : ℤ) + s) % d < d := Int.emod_lt_of_pos _ (d_pos d)
    generalize ((a : ℤ) + s) % d = r at *
    omega⟩

lemma idx_val (s : ℤ) (a : Fin d) : ((idx d s a : ℕ) : ℤ) = ((a : ℤ) + s) % d := by
  simp only [idx]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (d_pos d).ne')

/-- `⌊(a + s)/d⌋`. -/
def quot (s : ℤ) (a : Fin d) : ℤ := ((a : ℤ) + s) / d

lemma quot_spec (s : ℤ) (a : Fin d) : (d : ℤ) * quot d s a + (idx d s a : ℤ) = a + s := by
  rw [idx_val, quot]; exact Int.mul_ediv_add_emod _ _

lemma idx_inj (s : ℤ) : Function.Injective (idx d s) := by
  intro a b h
  have h' := congrArg (fun x : Fin d => ((x : ℕ) : ℤ)) h
  simp only [idx_val] at h'
  have hm : Int.ModEq d ((a : ℤ) + s) ((b : ℤ) + s) := h'
  have hab := Int.ModEq.add_right_cancel' s hm
  unfold Int.ModEq at hab
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast a.isLt),
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast b.isLt)] at hab
  exact Fin.ext (by exact_mod_cast hab)

/-- `a ↦ (a + s) mod d` som permutation. -/
def perm (s : ℤ) : Equiv.Perm (Fin d) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (idx_inj d s))

@[simp] lemma perm_apply (s : ℤ) (a : Fin d) : perm d s a = idx d s a := rfl

variable {K : Type*} [CommRing K] {n : ℕ}

def liftEdge (e : Edge n K) (a : Fin d) : Edge (n * d) K :=
  ⟨finProdFinEquiv (e.src, a), finProdFinEquiv (e.tgt, perm d e.shift.1 a),
    (quot d e.shift.1 a, e.shift.2), e.cond⟩

/-- `(a, b) ↦ (d a, b)`, dvs. `X ↦ X^d`. -/
def scaleX : ℤ × ℤ →+ ℤ × ℤ where
  toFun v := ((d : ℤ) * v.1, v.2)
  map_zero' := by simp
  map_add' a b := by simp [mul_add]

@[simp] lemma scaleX_apply (v : ℤ × ℤ) : scaleX d v = ((d : ℤ) * v.1, v.2) := rfl

/-- Fouriermatrisens poster (med faktorn `X^b`). -/
def Mv (ζ : Kˣ) (b k : Fin d) : LP2 K :=
  C ((ζ ^ (((b : ℕ) : ℤ) * ((k : ℕ) : ℤ)) : Kˣ) : K) * mono (((b : ℕ) : ℤ), 0)

end Lift

/-- `G` lyft till övertorusen med period `d` gånger längre i `X`-led. Noden `(u, a)`
(`u` i `G`, `a < d`) är `finProdFinEquiv (u, a)`. -/
def Net.liftX (d : ℕ) [NeZero d] [CommRing K] (G : Net K) : Net K :=
  ⟨G.n * d, G.edges.flatMap fun e => List.ofFn (Lift.liftEdge d e)⟩

namespace Lift
variable (d : ℕ) [NeZero d] {K : Type*} [CommRing K] {n : ℕ}

section sums
variable {R : Type*} [CommRing R] {m : ℕ}

lemma sum1 (A B : Prop) [Decidable A] [Decidable B] (b : Fin d) (F : Fin d → R) :
    ∑ x : Fin d, ∑ x₁ : Fin d, (if A then if b = x then if B then if x₁ = x then F x₁ else 0
      else 0 else 0 else 0) = if A then if B then F b else 0 else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

lemma sum2 (σ : Equiv.Perm (Fin d)) (A B : Prop) [Decidable A] [Decidable B] (b : Fin d)
    (F : Fin d → R) :
    ∑ x : Fin d, ∑ x₁ : Fin d, (if A then if b = σ x then if B then if x₁ = σ x then F x₁ else 0
      else 0 else 0 else 0) = if A then if B then F b else 0 else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> simp only [hA, hB, ite_true, ite_false, Finset.sum_const_zero]
  all_goals first | rfl | (rw [← Equiv.sum_comp σ.symm]; simp)

lemma sum3 (σ : Equiv.Perm (Fin d)) (A B : Prop) [Decidable A] [Decidable B] (b : Fin d)
    (G : Fin d → Fin d → R) :
    ∑ x : Fin d, ∑ x₁ : Fin d, (if A then if b = x then if B then if x₁ = σ x then G x x₁ else 0
      else 0 else 0 else 0) = if A then if B then G b (σ b) else 0 else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

lemma sum4 (σ : Equiv.Perm (Fin d)) (A B : Prop) [Decidable A] [Decidable B] (b : Fin d)
    (G : Fin d → Fin d → R) :
    ∑ x : Fin d, ∑ x₁ : Fin d, (if A then if b = σ x then if B then if x₁ = x then G x x₁ else 0
      else 0 else 0 else 0) = if A then if B then G (σ.symm b) (σ.symm b) else 0 else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> simp only [hA, hB, ite_true, ite_false, Finset.sum_const_zero]
  all_goals first | rfl | (rw [← Equiv.sum_comp σ.symm]; simp)

end sums

lemma zeta_periodic (ζ : Kˣ) (hζ : ζ ^ (d : ℤ) = 1) (m t : ℤ) : ζ ^ (m + d * t) = ζ ^ m := by
  rw [zpow_add, zpow_mul, hζ, one_zpow, mul_one]

lemma alg3 (ζ : Kˣ) (hζ : ζ ^ (d : ℤ) = 1) (s1 s2 : ℤ) (b k : Fin d) :
    single ((d : ℤ) * quot d s1 b, s2) (1 : K) * Mv d ζ (perm d s1 b) k =
      Mv d ζ b k * single (s1, s2) (((ζ ^ ((k : ℕ) : ℤ)) ^ s1 : Kˣ) : K) := by
  simp only [Mv, C_mul_mono, single_mul_single, one_mul, perm_apply]
  have hq := quot_spec d s1 b
  congr 1
  · ext <;> simp <;> linarith
  · rw [← Units.val_mul, ← zpow_mul, ← zpow_add]
    congr 1
    have : ((idx d s1 b : ℕ) : ℤ) * (k : ℕ) = (((b : ℕ) : ℤ) * (k : ℕ) + (k : ℕ) * s1) +
        d * (-(quot d s1 b) * (k : ℕ)) := by linear_combination (k : ℕ) * hq
    rw [this, zeta_periodic d ζ hζ]

lemma alg4 (ζ : Kˣ) (hζ : ζ ^ (d : ℤ) = 1) (s1 s2 : ℤ) (a k : Fin d) :
    single (-((d : ℤ) * quot d s1 a, s2)) (1 : K) * Mv d ζ a k =
      Mv d ζ (perm d s1 a) k * single (-(s1, s2)) (((ζ ^ ((k : ℕ) : ℤ)) ^ (-(s1, s2)).1 : Kˣ) : K) := by
  simp only [Mv, C_mul_mono, single_mul_single, one_mul, perm_apply, Prod.fst_neg]
  have hq := quot_spec d s1 a
  congr 1
  · ext <;> simp <;> linarith
  · rw [← Units.val_mul, ← zpow_mul, ← zpow_add]
    congr 1
    have : ((a : ℕ) : ℤ) * (k : ℕ) = ((((idx d s1 a : ℕ) : ℤ)) * (k : ℕ) + (k : ℕ) * -s1) +
        d * (quot d s1 a * (k : ℕ)) := by linear_combination (-(k : ℕ) : ℤ) * hq
    rw [this, zeta_periodic d ζ hζ]

/-- Bidraget från en kant till `(L'' W)((u,b),(v,k))`. -/
lemma edge_sum (ζ : Kˣ) (hζ : ζ ^ (d : ℤ) = 1) (e : Edge n K) (u v : Fin n) (b k : Fin d) :
    ∑ a, ∑ b', mapD (scaleX d) ((liftEdge d e a).lap (finProdFinEquiv (u, b))
      (finProdFinEquiv (v, b'))) * Mv d ζ b' k =
      Mv d ζ b k * twist (ζ ^ ((k : ℕ) : ℤ)) (e.lap u v) := by
  obtain ⟨p, q, ⟨s1, s2⟩, c⟩ := e
  simp only [liftEdge, Edge.lap, Equiv.apply_eq_iff_eq, Prod.mk.injEq, map_mul, map_add, map_sub,
    apply_ite (mapD _), apply_ite (twist _), map_one, map_zero, mono, C_apply, mapD_single, twist_single,
    map_neg, scaleX_apply]
  simp only [add_mul, sub_mul, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ite_and, ite_mul, mul_ite, zero_mul, mul_zero]
  rw [sum1, sum2, sum3, sum4]
  simp only [Prod.fst_zero, zpow_zero, Units.val_one, mul_one, mul_assoc]
  rw [alg3 d ζ hζ, alg4 d ζ hζ, Equiv.apply_symm_apply]
  split_ifs <;> ring

lemma flat_sum {M : Type*} [AddCommMonoid M] (E : List (Edge n K)) (g : Edge (n * d) K → M) :
    ((E.flatMap fun e => List.ofFn (liftEdge d e)).map g).sum =
      (E.map fun e => ∑ a, g (liftEdge d e a)).sum := by
  induction E with
  | nil => simp
  | cons e E ih => simp [List.flatMap_cons, List.sum_append, List.sum_ofFn, ih]

lemma entry_sum (ζ : Kˣ) (hζ : ζ ^ (d : ℤ) = 1) (E : List (Edge n K)) (u v : Fin n) (b k : Fin d) :
    ∑ b', mapD (scaleX d) (((E.flatMap fun e => List.ofFn (liftEdge d e)).map fun e =>
      e.lap (finProdFinEquiv (u, b)) (finProdFinEquiv (v, b'))).sum) * Mv d ζ b' k =
      Mv d ζ b k * twist (ζ ^ ((k : ℕ) : ℤ)) ((E.map fun e => e.lap u v).sum) := by
  induction E with
  | nil => simp
  | cons e E ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, map_add, add_mul,
      Finset.sum_add_distrib, List.map_cons, List.sum_cons, mul_add]
    rw [ih, ← edge_sum d ζ hζ e u v b k]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [List.map_ofFn, List.sum_ofFn, map_sum, Finset.sum_mul]
    rfl

end Lift

namespace Lift
section field
variable (d : ℕ) [NeZero d] {K : Type*} [Field K]

/-- `det` av Fouriermatrisen är nollskild. -/
lemma det_Mv_ne_zero (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) d) :
    (Matrix.of (Mv d ζ)).det ≠ 0 := by
  have hM : Matrix.of (Mv d ζ) = Matrix.diagonal (fun b : Fin d => (mono (((b : ℕ) : ℤ), 0) : LP2 K)) *
      Matrix.vandermonde (fun b : Fin d => C ((ζ : K) ^ (b : ℕ))) := by
    refine Matrix.ext fun b k => ?_
    rw [Matrix.diagonal_mul, Matrix.vandermonde_apply, of_apply, Mv, ← map_pow, ← pow_mul,
      mul_comm (mono _)]
    congr 2
  rw [hM, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_vandermonde]
  apply mul_ne_zero
  · rw [Finset.prod_ne_zero_iff]
    intro b _
    simp [mono]
  · rw [Finset.prod_ne_zero_iff]
    intro i _
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    rw [← map_sub, C_apply]
    simp only [ne_eq, single_eq_zero, sub_eq_zero]
    intro h
    have := hζ.pow_inj j.isLt i.isLt h
    exact (Finset.mem_Ioi.1 hj).ne' (Fin.ext this)

end field
end Lift

open scoped Kronecker

open Lift in
/-- **Produktformeln (Lemma 2)**: `det Δ_lyft(X^d, Z) = ∏_{k<d} det Δ(ζ^k X, Z)`. -/
theorem specPoly_liftX [Field K] (d : ℕ) [NeZero d] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) d)
    (G : Net K) :
    mapD (scaleX d) (G.liftX d).specPoly = ∏ k : Fin d, twist (ζ ^ ((k : ℕ) : ℤ)) G.specPoly := by
  have hζd : ζ ^ (d : ℤ) = 1 := by
    rw [zpow_natCast]; ext; simp [hζ.pow_eq_one]
  obtain ⟨n, E⟩ := G
  rw [Net.liftX, Net.specPoly_mk, Net.specPoly_mk, RingHom.map_det,
    ← det_submatrix_equiv_self finProdFinEquiv]
  set A := ((mapD (scaleX d)).mapMatrix (Matrix.of fun i j =>
    ((E.flatMap fun e => List.ofFn (liftEdge d e)).map fun e => e.lap i j).sum)).submatrix
      finProdFinEquiv finProdFinEquiv
  set Δ : Matrix (Fin n) (Fin n) (LP2 K) := Matrix.of fun i j => (E.map fun e => e.lap i j).sum
  set W := (1 : Matrix (Fin n) (Fin n) (LP2 K)) ⊗ₖ Matrix.of (Mv d ζ)
  set B := Matrix.blockDiagonal fun k : Fin d => (twist (ζ ^ ((k : ℕ) : ℤ))).mapMatrix Δ
  have key : A * W = W * B := by
    refine Matrix.ext fun x y => ?_
    obtain ⟨u, b⟩ := x
    obtain ⟨v, k⟩ := y
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, W, B, A, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Matrix.blockDiagonal_apply, Matrix.submatrix_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, of_apply, Δ]
    simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [entry_sum d ζ hζd E u v b k]
  have hW : W.det ≠ 0 := by
    simp only [W, Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul]
    exact pow_ne_zero _ (det_Mv_ne_zero d ζ hζ)
  have h := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm] at h
  have h' := mul_left_cancel₀ hW h
  rw [h', Matrix.det_blockDiagonal]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← RingHom.map_det]

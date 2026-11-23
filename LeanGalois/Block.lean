import LeanGalois.FunMat
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Sicksackblock: determinanten av en blockcyklisk matris

`cycMat A B` är `m×m`-matrisen (`m = k+1`) med `A t` på diagonalen och `B t` på platsen
`(t+1, t)` (cykliskt). För `m = 1` är posten `A 0 + B 0`. Om alla `A t` är enheter är

  `det (cycMat A B) = ∏ A - (-1)^m ∏ B`   (`det_cycMat`).

`det_blocks`: om raderna och kolonnerna i `T` delas upp i block (två uppräkningar
`eR, eC : (Σ a, Fin (m a + 1)) ≃ ι`) och `T` är noll utanför blocken och cyklisk i varje block, så är
`det T = ± ∏_a (∏ A_a - (-1)^{m_a+1} ∏ B_a)`, med ett tecken som bara beror på `eR, eC`.
-/

noncomputable section

open Matrix Function FunMat
open Fin.NatCast

variable {R : Type*} [CommRing R]

/-- Den cykliska blockmatrisen. -/
def cycMat {k : ℕ} (A B : Fin (k + 1) → R) : Matrix (Fin (k + 1)) (Fin (k + 1)) R :=
  Matrix.of fun t t' => (if t = t' then A t' else 0) + (if t = t' + 1 then B t' else 0)

section cyc

variable {k : ℕ}

lemma iterate_add_one (x : Fin (k + 1)) (j : ℕ) :
    (fun t : Fin (k + 1) => t + 1)^[j] x = x + (j : Fin (k + 1)) := by
  induction j with
  | zero => simp
  | succ j ih => rw [iterate_succ_apply', ih, Nat.cast_succ, add_assoc]

lemma cycles_add_one : cycles (fun t : Fin (k + 1) => t + 1) = {Finset.univ} := by
  set g := fun t : Fin (k + 1) => t + 1
  have hper : ∀ x, x ∈ periodicPts g := by
    intro x
    refine mk_mem_periodicPts (Nat.succ_pos k) ?_
    show g^[k + 1] x = x
    rw [show g = fun t : Fin (k + 1) => t + 1 from rfl, iterate_add_one]
    simp
  have hcyc : ∀ x, cyc g x = Finset.univ := by
    intro x
    ext y
    simp only [Finset.mem_univ, iff_true]
    rw [mem_cyc g (hper x)]
    refine ⟨(y - x).val, ?_⟩
    rw [show g = fun t : Fin (k + 1) => t + 1 from rfl, iterate_add_one, Fin.cast_val_eq_self]
    abel
  unfold cycles
  rw [Finset.filter_true_of_mem (fun x _ => hper x)]
  ext γ
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton, hcyc]
  exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨0, h.symm⟩⟩

/-- **Determinanten av ett sicksackblock.** -/
theorem det_cycMat (A : Fin (k + 1) → Rˣ) (B : Fin (k + 1) → R) :
    (cycMat (fun t => (A t : R)) B).det = ∏ t, (A t : R) - (-1) ^ (k + 1) * ∏ t, B t := by
  set g := fun t : Fin (k + 1) => t + 1
  set ω : Fin (k + 1) → R := fun t => -B t * ((A t)⁻¹ : Rˣ)
  have hM : (cycMat (fun t => (A t : R)) B).transpose =
      Matrix.diagonal (fun t => (A t : R)) * funMat g ω := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.diagonal_mul, transpose_apply]
    simp only [cycMat, funMat, of_apply, ω, g]
    have hu : (A i : R) * ((A i)⁻¹ : Rˣ) = 1 := Units.mul_inv (A i)
    by_cases h1 : j = i <;> by_cases h2 : j = i + 1
    · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2]
      linear_combination (-B i) * hu
    · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]; ring
    · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
      linear_combination (-B i) * hu
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]; ring
  rw [← det_transpose, hM, det_mul, det_diagonal, det_funMat, cycles_add_one, Finset.prod_singleton]
  have hp : (∏ t, (A t : R)) * ∏ t, (((A t)⁻¹ : Rˣ) : R) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun t _ => Units.mul_inv (A t)
  simp only [ω, Finset.prod_mul_distrib, Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
  linear_combination (-(-1) ^ (k + 1) * ∏ t, B t) * hp

end cyc

section blocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} {m : Fin r → ℕ}

/-- **Blockdeterminanten.** -/
theorem det_blocks (T : Matrix ι ι R) (eR eC : (Σ a : Fin r, Fin (m a + 1)) ≃ ι)
    (A : (a : Fin r) → Fin (m a + 1) → Rˣ) (B : (a : Fin r) → Fin (m a + 1) → R)
    (hout : ∀ x y, x.1 ≠ y.1 → T (eR x) (eC y) = 0)
    (hin : ∀ a t t', T (eR ⟨a, t⟩) (eC ⟨a, t'⟩) = cycMat (fun t => (A a t : R)) (B a) t t') :
    ∃ σ : ℤˣ, T.det = σ * ∏ a, (∏ t, (A a t : R) - (-1) ^ (m a + 1) * ∏ t, B a t) := by
  let T' : Matrix (Σ a : Fin r, Fin (m a + 1)) (Σ a : Fin r, Fin (m a + 1)) R := T.submatrix eR eC
  let π : Equiv.Perm ι := eC.symm.trans eR
  have hT' : T'.det = Equiv.Perm.sign π * T.det := by
    have : T' = (T.submatrix π id).submatrix eC eC := by
      refine Matrix.ext fun x y => ?_
      simp [T', π]
    rw [this, det_submatrix_equiv_self, det_permute]
  have hbt : T'.BlockTriangular Sigma.fst := by
    intro x y hxy
    exact hout x y (ne_of_gt hxy)
  have hblk : ∀ a, (T'.toSquareBlock Sigma.fst a).det =
      ∏ t, (A a t : R) - (-1) ^ (m a + 1) * ∏ t, B a t := by
    intro a
    rw [← det_cycMat, ← det_submatrix_equiv_self (Equiv.sigmaSubtype a).symm]
    congr 1
    refine Matrix.ext fun t t' => ?_
    exact hin a t t'
  refine ⟨Equiv.Perm.sign π, ?_⟩
  have hdet := hbt.det_fintype
  simp only [hblk] at hdet
  rw [← hdet]
  have hs : ((Equiv.Perm.sign π : ℤˣ) : R) * (Equiv.Perm.sign π : ℤˣ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  rw [hT', ← mul_assoc, hs, one_mul]

end blocks

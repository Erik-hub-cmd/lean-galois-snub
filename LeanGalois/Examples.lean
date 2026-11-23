import LeanGalois.Basic

/-!
# Validering: spektralpolynom för tre gitter

Vi räknar ut `det Δ` exakt för kvadratgittret, det hexagonala gittret och snub square
(med konduktans 1 på kvadratkanterna och `l` på diagonalerna) och jämför med kända värden.
-/

noncomputable section

open LP2 AddMonoidAlgebra

namespace LP2
variable {K : Type*} [CommRing K]

@[simp] lemma mono_zero_zero : (mono (0, 0) : LP2 K) = 1 := rfl

lemma mono_X_Xi : (mono (1, 0) : LP2 K) * mono (-1, 0) = 1 := by
  rw [← mono_add]; rfl
lemma mono_Z_Zi : (mono (0, 1) : LP2 K) * mono (0, -1) = 1 := by
  rw [← mono_add]; rfl
lemma mono_2_0 : (mono (2, 0) : LP2 K) = mono (1, 0) * mono (1, 0) := by
  rw [← mono_add]; rfl
lemma mono_m2_0 : (mono (-2, 0) : LP2 K) = mono (-1, 0) * mono (-1, 0) := by
  rw [← mono_add]; rfl
lemma mono_0_2 : (mono (0, 2) : LP2 K) = mono (0, 1) * mono (0, 1) := by
  rw [← mono_add]; rfl
lemma mono_0_m2 : (mono (0, -2) : LP2 K) = mono (0, -1) * mono (0, -1) := by
  rw [← mono_add]; rfl
lemma mono_1_1 : (mono (1, 1) : LP2 K) = mono (1, 0) * mono (0, 1) := by
  rw [← mono_add]; rfl
lemma mono_1_m1 : (mono (1, -1) : LP2 K) = mono (1, 0) * mono (0, -1) := by
  rw [← mono_add]; rfl
lemma mono_m1_1 : (mono (-1, 1) : LP2 K) = mono (-1, 0) * mono (0, 1) := by
  rw [← mono_add]; rfl
lemma mono_m1_m1 : (mono (-1, -1) : LP2 K) = mono (-1, 0) * mono (0, -1) := by
  rw [← mono_add]; rfl

end LP2

variable {K : Type*} [CommRing K]

/-! ## Kvadratgittret: en nod, kanter i riktning (1,0) och (0,1). -/

def squareNet (a b : K) : Net K := ⟨1, [⟨0, 0, (1, 0), a⟩, ⟨0, 0, (0, 1), b⟩]⟩

/-- `det Δ = 2a + 2b - a(X + X⁻¹) - b(Z + Z⁻¹)`. -/
theorem squareNet_specPoly (a b : K) :
    (squareNet a b).specPoly =
      C (2 * a + 2 * b) - C a * (mono (1, 0) + mono (-1, 0)) - C b * (mono (0, 1) + mono (0, -1)) := by
  simp only [squareNet, Net.specPoly_mk]
  simp [Edge.lap, Matrix.det_unique, Matrix.of_apply, map_ofNat]
  ring

/-! ## Hexagonala gittret: två noder, tre kanter. -/

def hexNet : Net K := ⟨2, [⟨0, 1, (0, 0), 1⟩, ⟨0, 1, (-1, 0), 1⟩, ⟨0, 1, (0, -1), 1⟩]⟩

/-- `det Δ = 9 - (1 + X + Z)(1 + X⁻¹ + Z⁻¹) = 6 - X - X⁻¹ - Z - Z⁻¹ - X Z⁻¹ - X⁻¹ Z`. -/
theorem hexNet_specPoly :
    (hexNet : Net K).specPoly =
      6 - mono (1, 0) - mono (-1, 0) - mono (0, 1) - mono (0, -1) - mono (1, -1) - mono (-1, 1) := by
  simp only [hexNet, Net.specPoly_mk]
  simp [Edge.lap, Matrix.det_fin_two, Matrix.of_apply]
  rw [mono_1_m1, mono_m1_1]
  linear_combination (-1 : LP2 K) * mono_X_Xi (K := K) + (-1 : LP2 K) * mono_Z_Zi (K := K)

/-! ## Snub square: cellen 2×2 i Z², noder 0=(0,0), 1=(1,0), 2=(0,1), 3=(1,1);
kvadratkanter med konduktans 1, diagonalerna (0,0)–(1,1) och (1,2)–(2,1) med konduktans `l`. -/

def snubEdges (l : K) : List (Edge 4 K) :=
  [⟨0, 1, (0, 0), 1⟩, ⟨1, 0, (1, 0), 1⟩, ⟨2, 3, (0, 0), 1⟩, ⟨3, 2, (1, 0), 1⟩,
   ⟨0, 2, (0, 0), 1⟩, ⟨2, 0, (0, 1), 1⟩, ⟨1, 3, (0, 0), 1⟩, ⟨3, 1, (0, 1), 1⟩,
   ⟨0, 3, (0, 0), l⟩, ⟨1, 2, (1, -1), l⟩]

def snubNet (l : K) : Net K := ⟨4, snubEdges l⟩

section snub
variable (l : K)
local notation "X" => (mono (1, 0) : LP2 K)
local notation "Xi" => (mono (-1, 0) : LP2 K)
local notation "Z" => (mono (0, 1) : LP2 K)
local notation "Zi" => (mono (0, -1) : LP2 K)
local notation "L" => (C l : LP2 K)

/-- Snub squares Laplacematris, uträknad. -/
theorem snubNet_laplacian :
    (Matrix.of fun (i j : Fin 4) => ((snubNet l).edges.map fun e => e.lap i j).sum) =
      !![L + 4, -Xi - 1, -Zi - 1, -L;
         -X - 1, L + 4, -L*X*Zi, -Zi - 1;
         -Z - 1, -L*Xi*Z, L + 4, -Xi - 1;
         -L, -Z - 1, -X - 1, L + 4] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.of_apply, snubNet, snubEdges, Edge.lap, mono_1_m1, mono_m1_1] <;> ring

set_option maxHeartbeats 2000000 in
/-- **Lemma 1** (snub squares spektralpolynom), exakt som i avsnitt 10 / Fable-granskningen:
hörn `(±2,0), (0,±2)` med koefficient 1, `-2(2l²+4l+1)` i `(±1,±1)`, `-8(l+2)²` i
`(±1,0), (0,±1)` och `4(2l+3)(6l+11)` i origo. -/
theorem snubNet_specPoly :
    (snubNet l).specPoly =
      mono (2, 0) + mono (-2, 0) + mono (0, 2) + mono (0, -2)
      - C (2 * (2 * l ^ 2 + 4 * l + 1)) * (mono (1, 1) + mono (1, -1) + mono (-1, 1) + mono (-1, -1))
      - C (8 * (l + 2) ^ 2) * (mono (1, 0) + mono (-1, 0) + mono (0, 1) + mono (0, -1))
      + C (4 * (2 * l + 3) * (6 * l + 11)) := by
  show (Matrix.of fun (i j : Fin 4) => ((snubNet l).edges.map fun e => e.lap i j).sum).det = _
  rw [snubNet_laplacian]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  rw [mono_1_m1, mono_m1_1, mono_2_0, mono_m2_0, mono_0_2, mono_0_m2, mono_1_1, mono_m1_m1]
  simp only [map_mul, map_add, map_pow, map_ofNat]
  linear_combination
    (-8*L^3*Z*Zi - L^2*X*Z - L^2*Xi*Zi - 20*L^2*Z*Zi - 4*L^2*Z - 4*L^2*Zi - 2*L^2 - 16*L*Z*Zi
      - 8*L*Z - 8*L*Zi - 16*L + X*Xi + 2*X + 2*Xi - 2*Z*Zi - 2*Z - 2*Zi - 29) * mono_X_Xi (K := K)
    + (-8*L^3 - L^2*X*Z - 4*L^2*X - L^2*Xi*Zi - 4*L^2*Xi - 22*L^2 - 8*L*X - 8*L*Xi - 32*L - 2*X
      - 2*Xi + Z*Zi + 2*Z + 2*Zi - 31) * mono_Z_Zi (K := K)

end snub

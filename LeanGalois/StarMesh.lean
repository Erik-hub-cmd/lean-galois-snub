import LeanGalois.Moves
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Stjärna–maska-draget (döda grenar, serie, Y–Δ) som Schur-komplement

En nod (den sista, `Fin.last n`) med armar `i = 1..m` till noderna `t_i` (förskjutning `s_i`,
konduktans `c_i`, inga öglor vid noden) tas bort. I maskan får varje *ordnat* par `(i, j)` en kant
`t_i → t_j` med förskjutning `s_j - s_i` och konduktans `c_i c_j / (2S)`, `S = Σ c_i`.
Det är den vanliga maskan (varje oordnat par `{i,j}` ger konduktans `c_i c_j / S`) uppdelad i två
parallella halvor, plus öglor `(i, i)` med förskjutning 0, som inte bidrar till Δ.
`m = 1`: död gren. `m = 2`: seriereduktion. `m = 3`: Y→Δ.

Huvudresultat: `det Δ_stjärna = S · det Δ_maska`.
-/

noncomputable section

open LP2 Matrix

variable {K : Type*} [Field K]

/-- En arm från den borttagna noden. -/
structure StarArm (n : ℕ) (K : Type*) where
  tgt : Fin n
  shift : ℤ × ℤ
  cond : K

namespace StarMesh

variable {n m : ℕ}

def Edge.lift (e : Edge n K) : Edge (n + 1) K := ⟨e.src.castSucc, e.tgt.castSucc, e.shift, e.cond⟩

def armEdge (a : StarArm n K) : Edge (n + 1) K := ⟨Fin.last n, a.tgt.castSucc, a.shift, a.cond⟩

/-- `S = Σ c_i`. -/
def armSum (arms : Fin m → StarArm n K) : K := ∑ i, (arms i).cond

def meshEdge (S : K) (a b : StarArm n K) : Edge n K :=
  ⟨a.tgt, b.tgt, b.shift - a.shift, a.cond * b.cond / (2 * S)⟩

/-- Nätet med stjärnan: övriga kanter `rest` (lyfta) och armarna från sista noden. -/
def starNet (rest : List (Edge n K)) (arms : Fin m → StarArm n K) : Net K :=
  ⟨n + 1, rest.map Edge.lift ++ List.ofFn fun i => armEdge (arms i)⟩

/-- Nätet efter draget. -/
def meshNet (rest : List (Edge n K)) (arms : Fin m → StarArm n K) : Net K :=
  ⟨n, rest ++ List.ofFn fun k : Fin (m * m) =>
    meshEdge (armSum arms) (arms (finProdFinEquiv.symm k).1) (arms (finProdFinEquiv.symm k).2)⟩

/-- Indikator `[t = u]` i `LP2 K`. -/
def ind (t u : Fin n) : LP2 K := if t = u then 1 else 0

lemma ite_and_eq (p q : Prop) [Decidable p] [Decidable q] (x : LP2 K) :
    (if p ∧ q then x else 0) = (if p then 1 else 0) * (if q then 1 else 0) * x := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

lemma lap_lift (e : Edge n K) (u v : Fin n) :
    (Edge.lift e).lap u.castSucc v.castSucc = e.lap u v := by
  simp [Edge.lift, Edge.lap]

lemma lap_lift_last_right (e : Edge n K) (u : Fin (n + 1)) : (Edge.lift e).lap u (Fin.last n) = 0 := by
  simp [Edge.lift, Edge.lap, Fin.castSucc_ne_last, eq_comm (a := Fin.last n)]

lemma lap_lift_last_left (e : Edge n K) (v : Fin (n + 1)) : (Edge.lift e).lap (Fin.last n) v = 0 := by
  simp [Edge.lift, Edge.lap, Fin.castSucc_ne_last, eq_comm (a := Fin.last n)]

lemma last_ne_cs (t : Fin n) : Fin.last n ≠ t.castSucc := (Fin.castSucc_ne_last t).symm

lemma lap_arm_cc (a : StarArm n K) (u v : Fin n) :
    (armEdge a).lap u.castSucc v.castSucc = C a.cond * (ind a.tgt u * ind a.tgt v) := by
  simp only [armEdge, Edge.lap, ind, Fin.castSucc_ne_last, false_and, if_false, Fin.castSucc_inj]
  by_cases hu : u = a.tgt <;> by_cases hv : v = a.tgt <;> simp [hu, hv, eq_comm]

lemma lap_arm_cl (a : StarArm n K) (u : Fin n) :
    (armEdge a).lap u.castSucc (Fin.last n) = -(C a.cond * (ind a.tgt u * mono (-a.shift))) := by
  simp only [armEdge, Edge.lap, ind, Fin.castSucc_ne_last, false_and, and_false, if_false,
    Fin.castSucc_inj, and_true]
  by_cases hu : u = a.tgt <;> simp [hu, eq_comm]

lemma lap_arm_lc (a : StarArm n K) (v : Fin n) :
    (armEdge a).lap (Fin.last n) v.castSucc = -(C a.cond * (ind a.tgt v * mono a.shift)) := by
  simp only [armEdge, Edge.lap, ind, Fin.castSucc_ne_last, last_ne_cs, Ne, not_false_eq_true,
    false_and, and_false, if_false, Fin.castSucc_inj, true_and]
  by_cases hv : v = a.tgt <;> simp [hv, eq_comm]

lemma lap_arm_ll (a : StarArm n K) : (armEdge a).lap (Fin.last n) (Fin.last n) = C a.cond := by
  simp [armEdge, Edge.lap, Fin.castSucc_ne_last, last_ne_cs]

lemma lap_mesh (S : K) (a b : StarArm n K) (u v : Fin n) :
    (meshEdge S a b).lap u v = C (a.cond * b.cond / (2 * S)) *
      (ind a.tgt u * ind a.tgt v + ind b.tgt u * ind b.tgt v
        - ind a.tgt u * ind b.tgt v * mono (b.shift - a.shift)
        - ind b.tgt u * ind a.tgt v * mono (-(b.shift - a.shift))) := by
  simp only [meshEdge, Edge.lap, ind]
  congr 1
  by_cases h1 : u = a.tgt <;> by_cases h2 : v = a.tgt <;> by_cases h3 : u = b.tgt <;>
    by_cases h4 : v = b.tgt <;> simp [h1, h2, h3, h4, eq_comm]
  all_goals (intros; simp_all)

/-- Ren ringidentitet för dubbelsumman över maskan. -/
lemma dsum {R : Type*} [CommRing R] {m : ℕ} (a x y P Q : Fin m → R) (h CS CSi : R)
    (hsum : ∑ j, a j = CS) (hh1 : h * CS * 2 = 1) (hh2 : h * 2 = CSi) :
    ∑ i, ∑ j, a i * a j * h * (x i * y i + x j * y j - x i * y j * (P j * Q i)
      - x j * y i * (P i * Q j)) =
      ∑ i, a i * (x i * y i) - (∑ i, a i * (x i * Q i)) * CSi * ∑ j, a j * (y j * P j) := by
  have e1 : ∑ i, ∑ j, a i * a j * h * (x i * y i) = h * (∑ i, a i * (x i * y i)) * ∑ j, a j := by
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  have e2 : ∑ i, ∑ j, a i * a j * h * (x j * y j) = h * (∑ i, a i) * ∑ j, a j * (x j * y j) := by
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  have e3 : ∑ i, ∑ j, a i * a j * h * (x i * y j * (P j * Q i)) =
      h * (∑ i, a i * (x i * Q i)) * ∑ j, a j * (y j * P j) := by
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  have e4 : ∑ i, ∑ j, a i * a j * h * (x j * y i * (P i * Q j)) =
      h * (∑ i, a i * (x i * Q i)) * ∑ j, a j * (y j * P j) := by
    rw [Finset.sum_comm, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  have split : ∀ i j, a i * a j * h * (x i * y i + x j * y j - x i * y j * (P j * Q i)
      - x j * y i * (P i * Q j)) = a i * a j * h * (x i * y i) + a i * a j * h * (x j * y j)
      - a i * a j * h * (x i * y j * (P j * Q i)) - a i * a j * h * (x j * y i * (P i * Q j)) := by
    intro i j; ring
  simp only [split, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [e1, e2, e3, e4, hsum]
  linear_combination (∑ i, a i * (x i * y i)) * hh1
    - (∑ i, a i * (x i * Q i)) * (∑ j, a j * (y j * P j)) * hh2

/-- Den algebraiska kärnan: summan över maskans kanter. -/
lemma mesh_sum (arms : Fin m → StarArm n K) (u v : Fin n) (hS : armSum arms ≠ 0) (h2 : (2 : K) ≠ 0) :
    ∑ k : Fin (m * m), (meshEdge (armSum arms) (arms (finProdFinEquiv.symm k).1)
        (arms (finProdFinEquiv.symm k).2)).lap u v =
      ∑ i, C (arms i).cond * (ind (arms i).tgt u * ind (arms i).tgt v)
      - (∑ i, C (arms i).cond * (ind (arms i).tgt u * mono (-(arms i).shift))) * C (armSum arms)⁻¹ *
        (∑ j, C (arms j).cond * (ind (arms j).tgt v * mono (arms j).shift)) := by
  set S := armSum arms with hSdef
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, lap_mesh]
  have hmono : ∀ i j, (mono ((arms j).shift - (arms i).shift) : LP2 K) =
      mono (arms j).shift * mono (-(arms i).shift) := by
    intro i j; rw [← mono_add, sub_eq_add_neg]
  have hmono' : ∀ i j, (mono (-((arms j).shift - (arms i).shift)) : LP2 K) =
      mono (arms i).shift * mono (-(arms j).shift) := by
    intro i j; rw [← mono_add, neg_sub, sub_eq_add_neg]
  simp only [hmono, hmono']
  have hC : ∀ i j, C ((arms i).cond * (arms j).cond / (2 * S)) =
      C (arms i).cond * C (arms j).cond * C (1 / (2 * S)) := by
    intro i j; simp only [← map_mul]; congr 1; field_simp
  simp only [hC]
  have hsumS : ∑ j, C (arms j).cond = C S := by simp only [hSdef, armSum, map_sum]
  have hh1 : C (1 / (2 * S)) * C S * 2 = 1 := by
    rw [← map_ofNat C 2, ← map_mul, ← map_mul, ← map_one C]; congr 1; field_simp
  have hh2 : C (1 / (2 * S)) * 2 = C S⁻¹ := by
    rw [← map_ofNat C 2, ← map_mul]; congr 1; field_simp
  exact dsum _ _ _ _ _ _ _ _ hsumS hh1 hh2

/-- **Stjärna–maska**: `det Δ_stjärna = S · det Δ_maska`. -/
theorem specPoly_star (rest : List (Edge n K)) (arms : Fin m → StarArm n K)
    (hS : armSum arms ≠ 0) (h2 : (2 : K) ≠ 0) :
    (starNet rest arms).specPoly = C (armSum arms) * (meshNet rest arms).specPoly := by
  set S := armSum arms with hSdef
  rw [starNet, Net.specPoly_mk, meshNet, Net.specPoly_mk]
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) (LP2 K) :=
    Matrix.of fun i j => ((rest.map Edge.lift ++ List.ofFn fun i => armEdge (arms i)).map
      fun e => e.lap i j).sum with hM
  have entry : ∀ i j, M i j = (rest.map fun e => (Edge.lift e).lap i j).sum +
      ∑ k, (armEdge (arms k)).lap i j := by
    intro i j
    simp [hM, List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  have hll : M (Fin.last n) (Fin.last n) = C S := by
    rw [entry]
    simp [lap_lift_last_right, lap_arm_ll, hSdef, armSum, map_sum]
  set A : Matrix (Fin n) (Fin n) (LP2 K) := Matrix.of fun u v => M u.castSucc v.castSucc
  set B : Matrix (Fin n) (Fin 1) (LP2 K) := Matrix.of fun u _ => M u.castSucc (Fin.last n)
  set Cm : Matrix (Fin 1) (Fin n) (LP2 K) := Matrix.of fun _ v => M (Fin.last n) v.castSucc
  set D : Matrix (Fin 1) (Fin 1) (LP2 K) := Matrix.of fun _ _ => C S
  have hblk : M.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks A B Cm D := by
    refine Matrix.ext fun i j => ?_
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · fin_cases j; rfl
    · fin_cases i; rfl
    · fin_cases i; fin_cases j; exact hll
  rw [← det_submatrix_equiv_self finSumFinEquiv M, hblk]
  letI : Invertible D :=
    { invOf := Matrix.of fun _ _ => C S⁻¹
      invOf_mul_self := by
        refine Matrix.ext fun a b => ?_
        fin_cases a; fin_cases b
        simp [D, Matrix.mul_apply, ← map_mul, inv_mul_cancel₀ hS]
      mul_invOf_self := by
        refine Matrix.ext fun a b => ?_
        fin_cases a; fin_cases b
        simp [D, Matrix.mul_apply, ← map_mul, mul_inv_cancel₀ hS] }
  rw [det_fromBlocks₂₂, det_unique]
  congr 1
  congr 1
  refine Matrix.ext fun u v => ?_
  rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one, Matrix.mul_apply, Fin.sum_univ_one]
  change M u.castSucc v.castSucc - M u.castSucc (Fin.last n) * C S⁻¹ * M (Fin.last n) v.castSucc = _
  rw [entry, entry, entry]
  simp only [lap_lift, lap_lift_last_right, lap_lift_last_left, lap_arm_cc, lap_arm_cl, lap_arm_lc,
    List.map_const', List.sum_replicate, smul_zero, zero_add, List.map_append, List.sum_append,
    List.map_ofFn, List.sum_ofFn, Function.comp_def, of_apply]
  rw [mesh_sum arms u v hS h2]
  simp only [Finset.sum_neg_distrib, neg_mul, mul_neg, neg_neg]
  ring

end StarMesh

import LeanGalois.Local
import Mathlib.NumberTheory.Real.Irrational

/-!
# Konkret fall: `F = ℚ`, `l = 1`, `κ = √3`

Visar att hypoteserna om `F` och `κ` inte är tomma: för snub square med alla konduktanser 1.
-/

open LP2

/-- `ℚ` som delkropp av `ℝ`. -/
noncomputable abbrev Qsub : Subfield ℝ := (Rat.castHom ℝ).fieldRange

/-- `√3 ∉ ℚ`. -/
lemma sqrt3_not_mem_Q : Real.sqrt 3 ∉ Qsub := by
  intro h
  obtain ⟨q, hq⟩ := RingHom.mem_fieldRange.1 h
  have hirr : Irrational (Real.sqrt 3) := by
    simpa using (Nat.prime_three.irrational_sqrt)
  exact hirr ⟨q, by simpa using hq⟩

/-- **Sats 10.1, konkret** (egen torus): ingen följd av drag som bevarar rationaliteten och
multiplicerar `det Δ` med en konstant för snub square (alla konduktanser 1) till ett
minimalt nät, givet Lemma 4 (`H4`, `H4deg`). -/
theorem sats_10_1_snub_rat
    (IsMinimal TwoDirections : Net ℝ → Prop)
    (H4 : ∀ G, IsMinimal G → TwoDirections G → SideSplits G)
    (H4deg : ∀ G, IsMinimal G → ¬ TwoDirections G → G.edges = [])
    (Move : Net ℝ → Net ℝ → Prop)
    (hMoveF : ∀ G G', Move G G' →
      (∀ e ∈ G.edges, e.cond ∈ Qsub) → ∀ e ∈ G'.edges, e.cond ∈ Qsub)
    (hMoveDet : ∀ G G', Move G G' → ∃ c : ℝ, c ≠ 0 ∧ G'.specPoly = C c * G.specPoly)
    (G : Net ℝ) (hreach : Relation.ReflTransGen Move (snubNet 1) G) : ¬ IsMinimal G := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  refine sats_10_1 Qsub 1 (Real.sqrt 3) one_pos (Real.sqrt_pos.2 (by norm_num)) ?_ (Subfield.one_mem _)
    sqrt3_not_mem_Q IsMinimal TwoDirections H4 H4deg Move hMoveF hMoveDet G hreach
  rw [Real.sq_sqrt h3]; norm_num

/-- **Sats 10.1, konkret, för hela draglistan**: inga lokala drag (Y–Δ, Δ–Y, serie, parallell,
döda grenar, kontraktibla öglor, med rationella delningsval) för snub square med alla
konduktanser 1 till ett minimalt nät på dess egen torus, givet Lemma 4 (`H4`, `H4deg`). -/
theorem sats_10_1_local_snub_rat
    (IsMinimal TwoDirections : Net ℝ → Prop)
    (H4 : ∀ G, IsMinimal G → TwoDirections G → SideSplits G)
    (H4deg : ∀ G, IsMinimal G → ¬ TwoDirections G → G.edges = [])
    (G : Net ℝ) (hreach : Relation.ReflTransGen (LocalMove Qsub) (snubNet 1) G) :
    ¬ IsMinimal G := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  refine sats_10_1_local Qsub 1 (Real.sqrt 3) one_pos (Real.sqrt_pos.2 (by norm_num)) ?_
    (Subfield.one_mem _) sqrt3_not_mem_Q IsMinimal TwoDirections H4 H4deg G hreach
  rw [Real.sq_sqrt h3]; norm_num

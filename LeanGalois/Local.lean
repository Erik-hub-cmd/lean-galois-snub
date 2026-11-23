import LeanGalois.StarMesh

/-!
# Hela draglistan i 10.1 och Sats 10.1 för den

`LocalMove F` innehåller:
* `ElemMove` (omordning, parallellreduktion, parallelldelning med val i `F`),
* vändning av en kant `⟨u, v, s, c⟩ ↦ ⟨v, u, -s, c⟩`,
* omnumrering av noderna med en permutation,
* tillägg (med `c ∈ F`) och borttagning av en kontraktibel ögla `⟨u, u, 0, c⟩`,
* stjärna → maska (död gren, serie, Y→Δ) och maska → stjärna (Δ→Y, seriedelning), med `S ≠ 0`.

Varje drag multiplicerar `det Δ` med en nollskild konstant och håller konduktanserna i `F`.
-/

noncomputable section

open LP2 StarMesh

variable {K : Type*} [CommRing K]

def Edge.rev {n : ℕ} (e : Edge n K) : Edge n K := ⟨e.tgt, e.src, -e.shift, e.cond⟩

lemma Edge.lap_rev {n : ℕ} (e : Edge n K) (i j : Fin n) : e.rev.lap i j = e.lap i j := by
  by_cases h1 : i = e.src <;> by_cases h2 : j = e.src <;> by_cases h3 : i = e.tgt <;>
    by_cases h4 : j = e.tgt <;> simp [Edge.rev, Edge.lap, h1, h2, h3, h4] <;> ring

def Edge.relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (e : Edge n K) : Edge n K :=
  ⟨σ e.src, σ e.tgt, e.shift, e.cond⟩

lemma Edge.lap_relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (e : Edge n K) (i j : Fin n) :
    (e.relabel σ).lap (σ i) (σ j) = e.lap i j := by
  simp [Edge.relabel, Edge.lap]

lemma Edge.lap_loop0 {n : ℕ} (u : Fin n) (c : K) (i j : Fin n) :
    (⟨u, u, 0, c⟩ : Edge n K).lap i j = 0 := by
  simp only [Edge.lap, neg_zero, mono_zero]
  split_ifs <;> ring

/-- Alla lokala drag i avsnitt 10.1 (på en fast torus). -/
inductive LocalMove (F : Subfield ℝ) : Net ℝ → Net ℝ → Prop
  | elem {G G'} (h : ElemMove (F : Set ℝ) G G') : LocalMove F G G'
  | rev (n : ℕ) (e : Edge n ℝ) (rest : List (Edge n ℝ)) :
      LocalMove F ⟨n, e :: rest⟩ ⟨n, e.rev :: rest⟩
  | relabel (n : ℕ) (σ : Equiv.Perm (Fin n)) (E : List (Edge n ℝ)) :
      LocalMove F ⟨n, E⟩ ⟨n, E.map (Edge.relabel σ)⟩
  | addLoop (n : ℕ) (u : Fin n) (c : ℝ) (hc : c ∈ F) (E : List (Edge n ℝ)) :
      LocalMove F ⟨n, E⟩ ⟨n, ⟨u, u, 0, c⟩ :: E⟩
  | removeLoop (n : ℕ) (u : Fin n) (c : ℝ) (E : List (Edge n ℝ)) :
      LocalMove F ⟨n, ⟨u, u, 0, c⟩ :: E⟩ ⟨n, E⟩
  | star (n m : ℕ) (rest : List (Edge n ℝ)) (arms : Fin m → StarArm n ℝ) (hS : armSum arms ≠ 0) :
      LocalMove F (starNet rest arms) (meshNet rest arms)
  | unstar (n m : ℕ) (rest : List (Edge n ℝ)) (arms : Fin m → StarArm n ℝ) (hS : armSum arms ≠ 0) :
      LocalMove F (meshNet rest arms) (starNet rest arms)

section
variable {n : ℕ}

lemma laplacian_eq_of_lap {E E' : List (Edge n K)}
    (h : ∀ i j, (E'.map fun e => e.lap i j).sum = (E.map fun e => e.lap i j).sum) :
    (Net.mk n E').specPoly = (Net.mk n E).specPoly := by
  rw [Net.specPoly_mk, Net.specPoly_mk]
  congr 1
  exact Matrix.ext fun i j => h i j

end

set_option maxHeartbeats 1000000 in
theorem LocalMove.det_hyp {F : Subfield ℝ} {G G' : Net ℝ} (h : LocalMove F G G') :
    ∃ c : ℝ, c ≠ 0 ∧ G'.specPoly = C c * G.specPoly := by
  cases h with
  | elem h => exact h.det_hyp
  | rev n e rest =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [map_one, one_mul]
    exact laplacian_eq_of_lap fun i j => by simp [Edge.lap_rev]
  | relabel n σ E =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [map_one, one_mul, Net.specPoly_mk, Net.specPoly_mk,
      ← Matrix.det_submatrix_equiv_self σ]
    refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
    rw [Matrix.submatrix_apply, Matrix.of_apply, Matrix.of_apply, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
    rw [Function.comp_apply, Edge.lap_relabel]
  | addLoop n u c hc E =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [map_one, one_mul]
    exact laplacian_eq_of_lap fun i j => by simp [Edge.lap_loop0]
  | removeLoop n u c E =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [map_one, one_mul]
    exact laplacian_eq_of_lap fun i j => by simp [Edge.lap_loop0]
  | star n m rest arms hS =>
    refine ⟨(armSum arms)⁻¹, inv_ne_zero hS, ?_⟩
    rw [specPoly_star rest arms hS two_ne_zero, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hS,
      map_one, one_mul]
  | unstar n m rest arms hS =>
    exact ⟨armSum arms, hS, specPoly_star rest arms hS two_ne_zero⟩

lemma mem_starNet {F : Subfield ℝ} {n m : ℕ} {rest : List (Edge n ℝ)} {arms : Fin m → StarArm n ℝ} :
    (∀ e ∈ (starNet rest arms).edges, e.cond ∈ F) ↔
      (∀ e ∈ rest, e.cond ∈ F) ∧ ∀ i, (arms i).cond ∈ F := by
  change (∀ e ∈ rest.map Edge.lift ++ List.ofFn fun i => armEdge (arms i), e.cond ∈ F) ↔ _
  simp only [List.mem_append, List.mem_map, List.mem_ofFn]
  constructor
  · intro h
    exact ⟨fun e he => h _ (Or.inl ⟨e, he, rfl⟩), fun i => h _ (Or.inr ⟨i, rfl⟩)⟩
  · rintro ⟨h1, h2⟩ e (⟨a, ha, rfl⟩ | ⟨i, rfl⟩)
    exacts [h1 a ha, h2 i]

lemma mem_meshNet {F : Subfield ℝ} {n m : ℕ} {rest : List (Edge n ℝ)} {arms : Fin m → StarArm n ℝ} :
    (∀ e ∈ (meshNet rest arms).edges, e.cond ∈ F) ↔
      (∀ e ∈ rest, e.cond ∈ F) ∧ ∀ i j, (arms i).cond * (arms j).cond / (2 * armSum arms) ∈ F := by
  change (∀ e ∈ rest ++ List.ofFn fun k : Fin (m * m) => meshEdge (armSum arms)
    (arms (finProdFinEquiv.symm k).1) (arms (finProdFinEquiv.symm k).2), e.cond ∈ F) ↔ _
  simp only [List.mem_append, List.mem_ofFn]
  constructor
  · intro h
    refine ⟨fun e he => h e (Or.inl he), fun i j => ?_⟩
    have := h _ (Or.inr ⟨finProdFinEquiv (i, j), rfl⟩)
    simpa [meshEdge] using this
  · rintro ⟨h1, h2⟩ e (he | ⟨k, rfl⟩)
    exacts [h1 e he, h2 _ _]

theorem LocalMove.field_hyp (F : Subfield ℝ) {G G' : Net ℝ} (h : LocalMove F G G') :
    (∀ e ∈ G.edges, e.cond ∈ F) → ∀ e ∈ G'.edges, e.cond ∈ F := by
  have h2F : (2 : ℝ) ∈ F := by
    have h := F.add_mem F.one_mem F.one_mem
    rwa [one_add_one_eq_two] at h
  cases h with
  | elem h => exact h.field_hyp F
  | rev n e rest =>
    intro hG e' he'
    simp only [List.mem_cons] at he'
    rcases he' with rfl | he'
    · exact hG e (by simp)
    · exact hG e' (by simp [he'])
  | relabel n σ E =>
    intro hG e' he'
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    exact hG e he
  | addLoop n u c hc E =>
    intro hG e' he'
    simp only [List.mem_cons] at he'
    rcases he' with rfl | he'
    · exact hc
    · exact hG e' he'
  | removeLoop n u c E =>
    intro hG e' he'
    exact hG e' (by simp [he'])
  | star n m rest arms hS =>
    intro hG
    obtain ⟨h1, h2⟩ := mem_starNet.1 hG
    have hSF : armSum arms ∈ F := F.sum_mem fun i _ => h2 i
    refine mem_meshNet.2 ⟨h1, fun i j => ?_⟩
    exact F.div_mem (F.mul_mem (h2 i) (h2 j)) (F.mul_mem h2F hSF)
  | unstar n m rest arms hS =>
    intro hG
    obtain ⟨h1, h2⟩ := mem_meshNet.1 hG
    refine mem_starNet.2 ⟨h1, fun i => ?_⟩
    -- c_i = 2 · Σ_j c_i c_j / (2S)
    have key : (arms i).cond = 2 * ∑ j, (arms i).cond * (arms j).cond / (2 * armSum arms) := by
      have hs : ∑ j, (arms i).cond * (arms j).cond / (2 * armSum arms) =
          (arms i).cond * armSum arms / (2 * armSum arms) := by
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        rfl
      rw [hs]
      field_simp
    rw [key]
    exact F.mul_mem h2F (F.sum_mem fun j _ => h2 i j)

open Galois in
/-- **Sats 10.1 för hela draglistan** (egen torus): ingen ändlig följd av lokala drag
(Y–Δ, Δ–Y, serie, parallell, döda grenar, kontraktibla öglor och deras inverser, med alla
delningsval i `F`) för snub square till ett minimalt nät, givet Lemma 4 (`H4`, `H4deg`). -/
theorem sats_10_1_local (F : Subfield ℝ) (l κ : ℝ) (hl0 : 0 < l) (hκ0 : 0 < κ)
    (hκ2 : κ ^ 2 = l * (l + 2)) (hlF : l ∈ F) (hκF : κ ∉ F)
    (IsMinimal TwoDirections : Net ℝ → Prop)
    (H4 : ∀ G, IsMinimal G → TwoDirections G → SideSplits G)
    (H4deg : ∀ G, IsMinimal G → ¬ TwoDirections G → G.edges = [])
    (G : Net ℝ) (hreach : Relation.ReflTransGen (LocalMove F) (snubNet l) G) :
    ¬ IsMinimal G :=
  sats_10_1 F l κ hl0 hκ0 hκ2 hlF hκF IsMinimal TwoDirections H4 H4deg _
    (fun _ _ h => h.field_hyp F) (fun _ _ h => h.det_hyp) G hreach

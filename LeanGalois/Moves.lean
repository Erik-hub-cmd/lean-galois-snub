import LeanGalois.Galois

/-!
# Konkreta drag: omordning och parallellreduktion och parallelldelning

Här visas att två av dragen i 10.1 uppfyller hypoteserna i `sats_10_1` (med konstant 1).
Serie- och Y–Δ-drag (Schur-komplement) är inte formaliserade än.
-/

noncomputable section

open LP2

variable {K : Type*} [CommRing K]

/-- Elementära drag som inte ändrar nodmängden; delningar får bara välja tal i `S`. -/
inductive ElemMove (S : Set K) : Net K → Net K → Prop
  /-- Ordna om kantlistan. -/
  | perm (n : ℕ) (E E' : List (Edge n K)) (h : E.Perm E') : ElemMove S ⟨n, E⟩ ⟨n, E'⟩
  /-- Parallellreduktion: två kanter med samma ändar och förskjutning slås ihop. -/
  | parallel (n : ℕ) (u v : Fin n) (s : ℤ × ℤ) (c₁ c₂ : K) (rest : List (Edge n K)) :
      ElemMove S ⟨n, ⟨u, v, s, c₁⟩ :: ⟨u, v, s, c₂⟩ :: rest⟩ ⟨n, ⟨u, v, s, c₁ + c₂⟩ :: rest⟩
  /-- Parallelldelning (inversen). -/
  | parallelSplit (n : ℕ) (u v : Fin n) (s : ℤ × ℤ) (c₁ c₂ : K) (rest : List (Edge n K))
      (hc : c₁ ∈ S) : ElemMove S ⟨n, ⟨u, v, s, c₁ + c₂⟩ :: rest⟩ ⟨n, ⟨u, v, s, c₁⟩ :: ⟨u, v, s, c₂⟩ :: rest⟩

lemma Edge.lap_add {n : ℕ} (u v : Fin n) (s : ℤ × ℤ) (c₁ c₂ : K) (i j : Fin n) :
    (⟨u, v, s, c₁ + c₂⟩ : Edge n K).lap i j =
      (⟨u, v, s, c₁⟩ : Edge n K).lap i j + (⟨u, v, s, c₂⟩ : Edge n K).lap i j := by
  simp only [Edge.lap, map_add, add_mul]

/-- Varje `ElemMove` lämnar Laplacematrisen, och alltså `det Δ`, oförändrad. -/
theorem ElemMove.specPoly_eq {S : Set K} {G G' : Net K} (h : ElemMove S G G') : G'.specPoly = G.specPoly := by
  cases h with
  | perm n E E' hp =>
    simp only [Net.specPoly, Net.laplacian]
    congr 1
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply]
    exact ((hp.map (fun e => e.lap i j)).sum_eq).symm
  | parallel n u v s c₁ c₂ rest =>
    simp only [Net.specPoly, Net.laplacian]
    congr 1
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, List.map_cons, List.sum_cons, Edge.lap_add, add_assoc]
  | parallelSplit n u v s c₁ c₂ rest _ =>
    simp only [Net.specPoly, Net.laplacian]
    congr 1
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, List.map_cons, List.sum_cons, Edge.lap_add, add_assoc]

/-- Hypotesen (ii) i `sats_10_1` för `ElemMove`. -/
theorem ElemMove.det_hyp {S : Set ℝ} {G G' : Net ℝ} (h : ElemMove S G G') :
    ∃ c : ℝ, c ≠ 0 ∧ G'.specPoly = C c * G.specPoly :=
  ⟨1, one_ne_zero, by rw [h.specPoly_eq, map_one, one_mul]⟩

/-- Hypotesen (i) i `sats_10_1` för `ElemMove`, för val av delningar i `F`. -/
theorem ElemMove.field_hyp (F : Subfield ℝ) {G G' : Net ℝ} (h : ElemMove (F : Set ℝ) G G') :
    (∀ e ∈ G.edges, e.cond ∈ F) → ∀ e ∈ G'.edges, e.cond ∈ F := by
  intro hG
  cases h with
  | perm n E E' hp => intro e he; exact hG e (hp.mem_iff.2 he)
  | parallel n u v s c₁ c₂ rest =>
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact F.add_mem (hG ⟨u, v, s, c₁⟩ (by simp)) (hG ⟨u, v, s, c₂⟩ (by simp))
    · exact hG e (by simp [he])
  | parallelSplit n u v s c₁ c₂ rest h1 =>
    have h12 : c₁ + c₂ ∈ F := hG ⟨u, v, s, c₁ + c₂⟩ (by simp)
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | rfl | he
    · exact h1
    · have := F.sub_mem h12 h1; simpa using this
    · exact hG e (by simp [he])

open Galois in
/-- Sats 10.1 för de konkreta dragen i `ElemMove` (med delningsval i `F`). -/
theorem sats_10_1_elem (F : Subfield ℝ) (l κ : ℝ) (hl0 : 0 < l) (hκ0 : 0 < κ)
    (hκ2 : κ ^ 2 = l * (l + 2)) (hlF : l ∈ F) (hκF : κ ∉ F)
    (IsMinimal TwoDirections : Net ℝ → Prop)
    (H4 : ∀ G, IsMinimal G → TwoDirections G → SideSplits G)
    (H4deg : ∀ G, IsMinimal G → ¬ TwoDirections G → G.edges = [])
    (G : Net ℝ) (hreach : Relation.ReflTransGen (ElemMove (F : Set ℝ)) (snubNet l) G) :
    ¬ IsMinimal G :=
  sats_10_1 F l κ hl0 hκ0 hκ2 hlF hκF IsMinimal TwoDirections H4 H4deg _
    (fun _ _ h => h.field_hyp F) (fun _ _ h => h.det_hyp) G hreach

import LeanGalois.Lemma4

/-!
# Hypoteserna är inte tomma: kvadratgittret, riktning `(1, 0)`

Höjddata `lo = 0`, `hi = 1`, kanthöjder `1`; ett block med den tvingade kanten `a·X`.
-/

noncomputable section

open LP2 Matrix

/-- Höjddata för kvadratgittret i riktningen `(1, 0)`. -/
def squareHeights (a b : ℝ) : Heights (squareNet a b).edges (1, 0) where
  lo := fun _ => 0
  hi := fun _ => 1
  y := fun _ => 1
  lo_le_hi := fun _ => zero_le_one
  src_lo := fun _ => zero_le_one
  src_hi := fun _ => le_refl _
  tgt_lo := by intro k; fin_cases k <;> simp [squareNet, dot]
  tgt_hi := by intro k; fin_cases k <;> simp [squareNet, dot]

lemma squareHeights_lapTop (a b : ℝ) (i j : Fin (squareNet a b).n) :
    (squareHeights a b).lapTop i j = -(C a * mono (1, 0)) := by
  have hS : Subsingleton (Fin (squareNet a b).n) := by show Subsingleton (Fin 1); infer_instance
  have hi : ∀ x : Fin (squareNet a b).n, i = x := fun x => Subsingleton.elim _ _
  have hj : ∀ x : Fin (squareNet a b).n, j = x := fun x => Subsingleton.elim _ _
  show -∑ k : Fin 2, (squareHeights a b).tightTerm k i j = _
  rw [Fin.sum_univ_two]
  have e0s : ((squareNet a b).edges.get (0 : Fin 2)).shift = (1, 0) := rfl
  have e0c : ((squareNet a b).edges.get (0 : Fin 2)).cond = a := rfl
  have e1s : ((squareNet a b).edges.get (1 : Fin 2)).shift = (0, 1) := rfl
  simp only [Heights.tightTerm, e0s, e0c, e1s, squareHeights, dot]
  have hij : ∀ x y : Fin (squareNet a b).n, (i = x ∧ j = y) ↔ True :=
    fun x y => ⟨fun _ => trivial, fun _ => ⟨hi x, hj y⟩⟩
  simp only [hij, true_and]
  norm_num

/-- Uppräkningen av den enda noden. -/
def oneEquiv (a b : ℝ) : (Σ _ : Fin 1, Fin (0 + 1)) ≃ Fin (squareNet a b).n where
  toFun := fun _ => ⟨0, by simp [squareNet]⟩
  invFun := fun _ => ⟨0, 0⟩
  left_inv := by
    rintro ⟨x, y⟩
    have hx : x = 0 := Subsingleton.elim _ _
    have hy : y = 0 := Fin.ext (by have := y.2; omega)
    subst hx hy; rfl
  right_inv := by
    intro y
    apply Fin.ext
    have := y.2
    simp only [squareNet] at this ⊢
    omega

/-- Sicksackdata: ett block (den tvingade kanten `a·X`). -/
def squareZigzag (a b : ℝ) (ha : a ≠ 0) : ZigzagData (squareHeights a b) where
  r := 1
  m := fun _ => 0
  eR := oneEquiv a b
  eC := oneEquiv a b
  cA := fun _ _ => a
  dA := fun _ _ => (1, 0)
  cB := fun _ _ => 0
  dB := fun _ _ => 0
  cA_ne := fun _ _ => ha
  cA_mem := fun _ _ => Subring.subset_closure ⟨⟨⟨0, by simp [squareNet]⟩, ⟨0, by simp [squareNet]⟩, (1, 0), a⟩, by simp only [squareNet]; exact List.Mem.head _, rfl⟩
  cB_mem := fun _ _ => Subring.zero_mem _
  hout := by
    intro x y h
    exact absurd (Subsingleton.elim x.1 y.1) h
  hin := by
    intro a' t t'
    have ht : t = 0 := Fin.ext (by have := t.2; simp at this; omega)
    have ht' : t' = 0 := Fin.ext (by have := t'.2; simp at this; omega)
    subst ht ht'
    rw [squareHeights_lapTop]
    simp [cycMat]

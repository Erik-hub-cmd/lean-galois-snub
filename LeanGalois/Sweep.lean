import LeanGalois.CRSF
import LeanGalois.Maps

/-!
# Svepolikheten (Lemma 4, steg 1(ii)), kombinatorisk form

Geometrin i steg 1 (räta tågspår, konvexa svarta områden) ersätts av **höjddata** för en
riktning `nv ∈ ℤ²`: varje nod `i` (svart område) har ett intervall `[lo i, hi i]` (områdets
utsträckning i `⟨nv,·⟩`), och varje kant `k` (korsning) har en höjd `y k` som ligger i källans
intervall och, efter förskjutningen, i målets: `y k - ⟨nv, shift⟩ ∈ [lo tgt, hi tgt]`.
(För ett geodetiskt nät: `y k = ⟨nv, korsningspunkten⟩`.)

**Sats (`sweep`)**: varje monom `v` i `det Δ` har `⟨nv, v⟩ ≤ Σ_i (hi i - lo i)`.

Beviset: CRSF-utvecklingen; en cykel som passerar noderna `i₀, i₁, …` har
`⟨nv, [γ]⟩ = Σ (utgång_k - ingång_{k+1}) = Σ (utgång_k - ingång_k) ≤ Σ bredd` (teleskop).
-/

noncomputable section

open LP2 Matrix FunMat Function AddMonoidAlgebra

namespace LP2

variable {K : Type*} [CommRing K]

/-- Alla monom i `p` har `⟨n, v⟩ ≤ W` (reell nivå). -/
def IsTopR (n : ℤ × ℤ) (W : ℝ) (p : LP2 K) : Prop :=
  ∀ v ∈ p.coeff.support, (dot n v : ℝ) ≤ W

variable {n : ℤ × ℤ}

lemma IsTopR.mono {W W' : ℝ} {p : LP2 K} (h : IsTopR n W p) (hW : W ≤ W') : IsTopR n W' p :=
  fun v hv => (h v hv).trans hW

lemma isTopR_add {W : ℝ} {p q : LP2 K} (hp : IsTopR n W p) (hq : IsTopR n W q) :
    IsTopR n W (p + q) := by
  intro v hv
  rw [coeff_add] at hv
  rcases Finset.mem_union.1 (Finsupp.support_add hv) with h | h
  exacts [hp v h, hq v h]

lemma isTopR_neg {W : ℝ} {p : LP2 K} (hp : IsTopR n W p) : IsTopR n W (-p) := by
  intro v hv; apply hp v; simpa [coeff_neg] using hv

lemma isTopR_sub {W : ℝ} {p q : LP2 K} (hp : IsTopR n W p) (hq : IsTopR n W q) :
    IsTopR n W (p - q) := by
  rw [sub_eq_add_neg]; exact isTopR_add hp (isTopR_neg hq)

lemma isTopR_zero {W : ℝ} : IsTopR n W (0 : LP2 K) := by
  intro v hv; simp at hv

lemma isTopR_single {W : ℝ} (v : ℤ × ℤ) (a : K) (h : (dot n v : ℝ) ≤ W) :
    IsTopR n W (single v a) := by
  intro w hw
  rw [coeff_single] at hw
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hw)]
  exact h

lemma isTopR_mono' {W : ℝ} (v : ℤ × ℤ) (h : (dot n v : ℝ) ≤ W) : IsTopR n W (mono v : LP2 K) :=
  isTopR_single v 1 h

lemma isTopR_one {W : ℝ} (h : 0 ≤ W) : IsTopR n W (1 : LP2 K) :=
  isTopR_single 0 1 (by simpa [dot] using h)

lemma isTopR_C {W : ℝ} (a : K) (h : 0 ≤ W) : IsTopR n W (C a) :=
  isTopR_single 0 a (by simpa [dot] using h)

lemma isTopR_mul {W₁ W₂ : ℝ} {p q : LP2 K} (hp : IsTopR n W₁ p) (hq : IsTopR n W₂ q) :
    IsTopR n (W₁ + W₂) (p * q) := by
  intro v hv
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset p q hv)
  have : dot n (x + y) = dot n x + dot n y := by simp only [dot, Prod.fst_add, Prod.snd_add]; ring
  rw [this]; push_cast
  exact add_le_add (hp x hx) (hq y hy)

lemma isTopR_prod {ι : Type*} (s : Finset ι) (p : ι → LP2 K) (W : ι → ℝ)
    (h : ∀ i ∈ s, IsTopR n (W i) (p i)) : IsTopR n (∑ i ∈ s, W i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isTopR_one (K := K) (n := n) le_rfl
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact isTopR_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma isTopR_sum {ι : Type*} (s : Finset ι) (p : ι → LP2 K) {W : ℝ}
    (h : ∀ i ∈ s, IsTopR n W (p i)) : IsTopR n W (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isTopR_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isTopR_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma mono_sum {ι : Type*} (s : Finset ι) (d : ι → ℤ × ℤ) :
    (mono (∑ i ∈ s, d i) : LP2 K) = ∏ i ∈ s, mono (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mono_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, mono_add, ih]

lemma dot_sum {ι : Type*} (s : Finset ι) (d : ι → ℤ × ℤ) :
    dot n (∑ i ∈ s, d i) = ∑ i ∈ s, dot n (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dot]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp only [dot, Prod.fst_add, Prod.snd_add]; ring

end LP2

namespace FunMat

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ι)

lemma sum_cyc {M : Type*} [AddCommMonoid M] (i : ι) (F : ι → M) :
    ∑ x ∈ cyc g i, F x = ∑ k ∈ Finset.range (minimalPeriod g i), F (g^[k] i) := by
  rw [cyc, Finset.sum_image]
  intro a ha b hb hab
  exact iterate_injOn_Iio_minimalPeriod (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) hab

/-- `g` permuterar sin cykel: `Σ_{x ∈ γ} F (g x) = Σ_{x ∈ γ} F x`. -/
lemma sum_cyc_comp {M : Type*} [AddCommGroup M] (i : ι) (F : ι → M) :
    ∑ x ∈ cyc g i, F (g x) = ∑ x ∈ cyc g i, F x := by
  rw [sum_cyc g i (fun x => F (g x)), sum_cyc g i F]
  simp only [← iterate_succ_apply' g]
  set L := minimalPeriod g i
  have h := Finset.sum_range_succ (fun k => F (g^[k] i)) L
  have h' := Finset.sum_range_succ' (fun k => F (g^[k] i)) L
  rw [iterate_minimalPeriod] at h
  simp only [iterate_zero, id_eq] at h'
  rw [h] at h'
  exact add_right_cancel h'.symm

lemma cycles_pairwiseDisjoint : (cycles g : Set (Finset ι)).PairwiseDisjoint id := by
  intro γ₁ h₁ γ₂ h₂ hne
  simp only [Finset.mem_coe] at h₁ h₂
  unfold cycles at h₁ h₂
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h₁
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h₂
  rw [Function.onFun, id, id, Finset.disjoint_left]
  intro x hxi hxj
  apply hne
  rw [← cyc_eq_of_mem g (Finset.mem_filter.1 hi).2 hxi, cyc_eq_of_mem g (Finset.mem_filter.1 hj).2 hxj]

lemma sum_cycles_le (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∑ γ ∈ cycles g, ∑ i ∈ γ, w i ≤ ∑ i, w i := by
  have h := Finset.sum_biUnion (cycles_pairwiseDisjoint g) (f := w)
  simp only [id] at h
  rw [← h]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hw i)

lemma cyc_of_fixed {i x : ι} (hi : i ∈ periodicPts g) (hx : x ∈ cyc g i) (hfix : g x = x) :
    cyc g i = {x} := by
  rw [← cyc_eq_of_mem g hi hx]
  have h1 : minimalPeriod g x = 1 :=
    minimalPeriod_eq_one_iff_isFixedPt.2 hfix
  simp [cyc, h1]

end FunMat

/-! ## Höjddata och svepolikheten -/

variable {K : Type*} [CommRing K] {n : ℕ}

/-- Höjddata för riktningen `nv`. -/
structure Heights (E : List (Edge n K)) (nv : ℤ × ℤ) where
  lo : Fin n → ℝ
  hi : Fin n → ℝ
  y : Fin E.length → ℝ
  lo_le_hi : ∀ i, lo i ≤ hi i
  src_lo : ∀ k, lo (E.get k).src ≤ y k
  src_hi : ∀ k, y k ≤ hi (E.get k).src
  tgt_lo : ∀ k, lo (E.get k).tgt ≤ y k - dot nv (E.get k).shift
  tgt_hi : ∀ k, y k - dot nv (E.get k).shift ≤ hi (E.get k).tgt

/-- Riktningen längs `f(i)` från `i`. -/
def choiceDir (E : List (Edge n K)) (f : Fin n → Fin E.length) (i : Fin n) : ℤ × ℤ :=
  if i = (E.get (f i)).src then (E.get (f i)).shift else -(E.get (f i)).shift

lemma Edge.other_eq_self {e : Edge n K} {i : Fin n} (h : e.Incident i) :
    e.other i = i ↔ e.src = e.tgt := by
  unfold Edge.other
  constructor
  · intro ho
    split_ifs at ho with hs
    · exact hs ▸ ho.symm
    · rcases h with h' | h'
      · exact absurd h' hs
      · exact absurd ho.symm (by rw [h']; intro hh; exact hs (h' ▸ hh.symm ▸ rfl))
  · intro hst
    split_ifs with hs
    · rw [hs, hst]
    · rcases h with h' | h'
      · exact absurd h' hs
      · rw [h', hst]

namespace Heights

variable {E : List (Edge n K)} {nv : ℤ × ℤ} (H : Heights E nv) (f : Fin n → Fin E.length)

/-- Höjden där kanten `k` lämnar `i` (i `i`:s koordinater). -/
def exitK (k : Fin E.length) (i : Fin n) : ℝ :=
  if i = (E.get k).src then H.y k else H.y k - dot nv (E.get k).shift

/-- Höjden där den kommer in i andra änden (i dess koordinater). -/
def entK (k : Fin E.length) (i : Fin n) : ℝ :=
  if i = (E.get k).src then H.y k - dot nv (E.get k).shift else H.y k

def exitH (i : Fin n) : ℝ := H.exitK (f i) i
def entH (i : Fin n) : ℝ := H.entK (f i) i

lemma exitK_le (k : Fin E.length) (i : Fin n) (hinc : (E.get k).Incident i) :
    H.exitK k i ≤ H.hi i := by
  unfold exitK
  split_ifs with h
  · rw [h]; exact H.src_hi _
  · rcases hinc with h' | h'
    · exact absurd h' h
    · rw [h']; exact H.tgt_hi _

lemma lo_le_entK (k : Fin E.length) (i : Fin n) :
    H.lo ((E.get k).other i) ≤ H.entK k i := by
  unfold entK Edge.other
  split_ifs with h
  · exact H.tgt_lo _
  · exact H.src_lo _

lemma dot_dirK (k : Fin E.length) (i : Fin n) :
    (dot nv (if i = (E.get k).src then (E.get k).shift else -(E.get k).shift) : ℝ) =
      H.exitK k i - H.entK k i := by
  unfold exitK entK
  split_ifs
  · ring
  · simp only [dot, Prod.fst_neg, Prod.snd_neg]; push_cast; ring

variable {f}

lemma exitH_le (hinc : ∀ i, (E.get (f i)).Incident i) (i : Fin n) : H.exitH f i ≤ H.hi i :=
  H.exitK_le (f i) i (hinc i)

lemma lo_le_entH (i : Fin n) : H.lo (choiceMap E f i) ≤ H.entH f i :=
  H.lo_le_entK (f i) i

lemma dot_dir (i : Fin n) : (dot nv (choiceDir E f i) : ℝ) = H.exitH f i - H.entH f i :=
  H.dot_dirK (f i) i

lemma phase_eq_dir (hinc : ∀ i, (E.get (f i)).Incident i) (i : Fin n)
    (hg : choiceMap E f i ≠ i) : choicePhase E f i = mono (choiceDir E f i) := by
  have hst : (E.get (f i)).src ≠ (E.get (f i)).tgt := fun hst =>
    hg ((Edge.other_eq_self (hinc i)).2 hst)
  unfold choicePhase choiceDir
  rw [Edge.phase_of_ne _ _ hst]

/-- En cykels faktor ligger under nivån `Σ_{i ∈ γ} bredd i`. -/
lemma cycle_factor_top (hinc : ∀ i, (E.get (f i)).Incident i) (γ : Finset (Fin n))
    (hγ : γ ∈ cycles (choiceMap E f)) :
    IsTopR nv (∑ i ∈ γ, (H.hi i - H.lo i)) (1 - ∏ i ∈ γ, choicePhase E f i) := by
  set g := choiceMap E f
  have hW : 0 ≤ ∑ i ∈ γ, (H.hi i - H.lo i) :=
    Finset.sum_nonneg fun i _ => sub_nonneg.2 (H.lo_le_hi i)
  have hγ' := hγ
  unfold cycles at hγ'
  obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hγ'
  have hper := (Finset.mem_filter.1 hi₀).2
  by_cases hfix : ∃ x ∈ cyc g i₀, g x = x
  · -- en ögla
    obtain ⟨x, hx, hgx⟩ := hfix
    rw [cyc_of_fixed g hper hx hgx, Finset.prod_singleton, Finset.sum_singleton]
    have hst : (E.get (f x)).src = (E.get (f x)).tgt := (Edge.other_eq_self (hinc x)).1 hgx
    have hxs : x = (E.get (f x)).src := by
      rcases hinc x with h' | h'
      · exact h'
      · exact h'.trans hst.symm
    set e := E.get (f x)
    have h1 := H.src_lo (f x)
    have h2 := H.src_hi (f x)
    have h3 := H.tgt_lo (f x)
    have h4 := H.tgt_hi (f x)
    have hlo : H.lo e.src = H.lo x := by rw [← hxs]
    have hhi : H.hi e.src = H.hi x := by rw [← hxs]
    have hlo' : H.lo e.tgt = H.lo x := by rw [← hst, ← hxs]
    have hhi' : H.hi e.tgt = H.hi x := by rw [← hst, ← hxs]
    rw [hlo] at h1; rw [hhi] at h2; rw [hlo'] at h3; rw [hhi'] at h4
    have hphase : choicePhase E f x = mono e.shift + mono (-e.shift) - 1 := by
      unfold choicePhase Edge.phase; rw [if_pos hst]
    rw [hphase]
    have hneg : dot nv (-e.shift) = -dot nv e.shift := by
      simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring
    refine isTopR_sub (isTopR_one (by linarith)) (isTopR_sub (isTopR_add ?_ ?_) (isTopR_one (by linarith)))
    · exact isTopR_mono' _ (by linarith)
    · apply isTopR_mono'; rw [hneg]; push_cast; linarith
  · push Not at hfix
    have hprod : ∏ i ∈ cyc g i₀, choicePhase E f i = mono (∑ i ∈ cyc g i₀, choiceDir E f i) := by
      rw [mono_sum]
      exact Finset.prod_congr rfl fun i hi => phase_eq_dir hinc i (hfix i hi)
    rw [hprod]
    refine isTopR_sub (isTopR_one hW) (isTopR_mono' _ ?_)
    rw [dot_sum]
    push_cast
    simp only [H.dot_dir, Finset.sum_sub_distrib]
    have h1 : ∑ i ∈ cyc g i₀, H.exitH f i ≤ ∑ i ∈ cyc g i₀, H.hi i :=
      Finset.sum_le_sum fun i _ => H.exitH_le hinc i
    have h2 : ∑ i ∈ cyc g i₀, H.lo (g i) ≤ ∑ i ∈ cyc g i₀, H.entH f i :=
      Finset.sum_le_sum fun i _ => H.lo_le_entH i
    rw [sum_cyc_comp g i₀ H.lo] at h2
    linarith

end Heights

/-- **Svepolikheten**: varje monom `v` i `det Δ` har `⟨nv, v⟩ ≤ Σ_i (hi i - lo i)`. -/
theorem sweep (E : List (Edge n K)) (nv : ℤ × ℤ) (H : Heights E nv) :
    IsTopR nv (∑ i, (H.hi i - H.lo i)) (Net.mk n E).specPoly := by
  rw [specPoly_crsf]
  apply isTopR_sum
  intro f _
  unfold choiceTerm
  split_ifs with hinc
  · have hW : ∑ γ ∈ cycles (choiceMap E f), ∑ i ∈ γ, (H.hi i - H.lo i) ≤ ∑ i, (H.hi i - H.lo i) :=
      sum_cycles_le _ _ fun i => sub_nonneg.2 (H.lo_le_hi i)
    have h := isTopR_mul (isTopR_prod (n := nv) Finset.univ (fun i => C (E.get (f i)).cond)
      (fun _ => (0 : ℝ)) (fun i _ => isTopR_C _ le_rfl))
      (isTopR_prod _ _ _ fun γ hγ => H.cycle_factor_top hinc γ hγ)
    simp only [Finset.sum_const_zero, zero_add] at h
    exact h.mono hW
  · exact isTopR_zero

/-! ## Toppsidan (steg 1(ii)–(iii)): bara täta cykeltäckningar bidrar -/

namespace LP2

variable {K : Type*} [CommRing K] {n : ℤ × ℤ}

/-- Delen av `p` på den reella nivån `⟨n, v⟩ = W`. -/
def faceR (n : ℤ × ℤ) (W : ℝ) (p : LP2 K) : LP2 K :=
  ofCoeff (p.coeff.filter fun v => (dot n v : ℝ) = W)

lemma faceR_add (W : ℝ) (p q : LP2 K) : faceR n W (p + q) = faceR n W p + faceR n W q := by
  simp [faceR, coeff_add, Finsupp.filter_add, ofCoeff_add]

lemma faceR_zero (W : ℝ) : faceR n W (0 : LP2 K) = 0 := by
  simp only [faceR, coeff_zero, Finsupp.filter_zero]; rfl

lemma faceR_neg (W : ℝ) (p : LP2 K) : faceR n W (-p) = -faceR n W p := by
  have h := faceR_add (n := n) W p (-p)
  rw [add_neg_cancel, faceR_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

lemma faceR_sub (W : ℝ) (p q : LP2 K) : faceR n W (p - q) = faceR n W p - faceR n W q := by
  rw [sub_eq_add_neg, faceR_add, faceR_neg, ← sub_eq_add_neg]

lemma faceR_sum {ι : Type*} (s : Finset ι) (W : ℝ) (p : ι → LP2 K) :
    faceR n W (∑ i ∈ s, p i) = ∑ i ∈ s, faceR n W (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [faceR_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, faceR_add, ih]

lemma coeff_faceR (W : ℝ) (p : LP2 K) (v : ℤ × ℤ) :
    (faceR n W p).coeff v = if (dot n v : ℝ) = W then p.coeff v else 0 := by
  simp [faceR, coeff_ofCoeff, Finsupp.filter_apply]

lemma faceR_eq_zero_of_lt {W W' : ℝ} {p : LP2 K} (h : IsTopR n W' p) (hlt : W' < W) :
    faceR n W p = 0 := by
  ext v
  rw [coeff_faceR, coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs with hv
  · by_contra h0
    have := h v (Finsupp.mem_support_iff.2 h0)
    linarith
  · rfl

lemma faceR_eq_self {W : ℝ} {p : LP2 K} (h : ∀ v ∈ p.coeff.support, (dot n v : ℝ) = W) :
    faceR n W p = p := by
  ext v
  rw [coeff_faceR]
  split_ifs with hv
  · rfl
  · by_contra h0
    exact hv (h v (Finsupp.mem_support_iff.2 (Ne.symm h0)))

lemma faceR_single (W : ℝ) (v : ℤ × ℤ) (a : K) :
    faceR n W (single v a) = if (dot n v : ℝ) = W then single v a else 0 := by
  split_ifs with h
  · apply faceR_eq_self
    intro w hw
    rw [coeff_single] at hw
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hw)]; exact h
  · ext w
    rw [coeff_faceR, coeff_single, coeff_zero, Finsupp.coe_zero, Pi.zero_apply,
      Finsupp.single_apply]
    split_ifs with h1 h2 <;> first | rfl | (subst h2; exact absurd h1 h)

/-- Toppdelen av en produkt (reella nivåer). -/
lemma faceR_mul {p q : LP2 K} {a b : ℝ} (hp : IsTopR n a p) (hq : IsTopR n b q) :
    faceR n (a + b) (p * q) = faceR n a p * faceR n b q := by
  classical
  set fp := faceR n a p
  set fq := faceR n b q
  set rp := p - fp
  set rq := q - fq
  have hsupp : ∀ (x y : LP2 K) (A B : ℝ → Prop),
      (∀ v ∈ x.coeff.support, A (dot n v)) → (∀ v ∈ y.coeff.support, B (dot n v)) →
      ∀ v ∈ (x * y).coeff.support, ∃ i j : ℝ, A i ∧ B j ∧ (dot n v : ℝ) = i + j := by
    intro x y A B hx hy v hv
    obtain ⟨u, hu, w, hw, rfl⟩ := Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset x y hv)
    refine ⟨_, _, hx u hu, hy w hw, ?_⟩
    simp only [dot, Prod.fst_add, Prod.snd_add]; push_cast; ring
  have hfp : ∀ v ∈ fp.coeff.support, (dot n v : ℝ) = a := by
    intro v hv
    rw [Finsupp.mem_support_iff, coeff_faceR] at hv
    by_contra h; exact hv (if_neg h)
  have hfq : ∀ v ∈ fq.coeff.support, (dot n v : ℝ) = b := by
    intro v hv
    rw [Finsupp.mem_support_iff, coeff_faceR] at hv
    by_contra h; exact hv (if_neg h)
  have hrp : ∀ v ∈ rp.coeff.support, (dot n v : ℝ) < a := by
    intro v hv
    have hv' : p.coeff v - fp.coeff v ≠ 0 := by simpa [rp, coeff_sub] using hv
    rw [coeff_faceR] at hv'
    by_contra h
    split_ifs at hv' with h'
    · exact hv' (sub_self _)
    · have hpv : p.coeff v ≠ 0 := by simpa using hv'
      have := hp v (Finsupp.mem_support_iff.2 hpv)
      exact h' (le_antisymm this (not_lt.1 h))
  have hrq : ∀ v ∈ rq.coeff.support, (dot n v : ℝ) < b := by
    intro v hv
    have hv' : q.coeff v - fq.coeff v ≠ 0 := by simpa [rq, coeff_sub] using hv
    rw [coeff_faceR] at hv'
    by_contra h
    split_ifs at hv' with h'
    · exact hv' (sub_self _)
    · have hqv : q.coeff v ≠ 0 := by simpa using hv'
      have := hq v (Finsupp.mem_support_iff.2 hqv)
      exact h' (le_antisymm this (not_lt.1 h))
  have hdec : p * q = fp * fq + (fp * rq + rp * fq + rp * rq) := by
    simp only [rp, rq]; ring
  have h1 : ∀ v ∈ (fp * fq).coeff.support, (dot n v : ℝ) = a + b := by
    intro v hv
    obtain ⟨i, j, hi, hj, h⟩ := hsupp fp fq (· = a) (· = b) hfp hfq v hv
    rw [h, hi, hj]
  have hlow : IsTopR n (a + b) (fp * rq + rp * fq + rp * rq) ∧
      ∀ v ∈ (fp * rq + rp * fq + rp * rq).coeff.support, (dot n v : ℝ) < a + b := by
    have key : ∀ v ∈ (fp * rq + rp * fq + rp * rq).coeff.support, (dot n v : ℝ) < a + b := by
      intro v hv
      simp only [coeff_add] at hv
      rcases Finset.mem_union.1 (Finsupp.support_add hv) with hv | hv
      · rcases Finset.mem_union.1 (Finsupp.support_add hv) with hv | hv
        · obtain ⟨i, j, hi, hj, h⟩ := hsupp fp rq (· = a) (· < b) hfp hrq v hv
          rw [h]; linarith
        · obtain ⟨i, j, hi, hj, h⟩ := hsupp rp fq (· < a) (· = b) hrp hfq v hv
          rw [h]; linarith
      · obtain ⟨i, j, hi, hj, h⟩ := hsupp rp rq (· < a) (· < b) hrp hrq v hv
        rw [h]; linarith
    exact ⟨fun v hv => (key v hv).le, key⟩
  have hface_low : faceR n (a + b) (fp * rq + rp * fq + rp * rq) = 0 := by
    ext v
    rw [coeff_faceR, coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
    split_ifs with h
    · by_contra h0
      have := hlow.2 v (Finsupp.mem_support_iff.2 h0)
      linarith
    · rfl
  rw [hdec, faceR_add, hface_low, add_zero, faceR_eq_self h1]

lemma faceR_prod {ι : Type*} (s : Finset ι) (p : ι → LP2 K) (W : ι → ℝ)
    (h : ∀ i ∈ s, IsTopR n (W i) (p i)) :
    faceR n (∑ i ∈ s, W i) (∏ i ∈ s, p i) = ∏ i ∈ s, faceR n (W i) (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    apply faceR_eq_self
    intro v hv
    have h1 : (1 : LP2 K) = single 0 1 := rfl
    rw [h1, coeff_single] at hv
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hv)]; simp [dot]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    rw [faceR_mul (h a (Finset.mem_insert_self a s))
      (isTopR_prod s p W fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

lemma faceR_C_mul_eq {W : ℝ} (c : K) (p : LP2 K) : faceR n W (C c * p) = C c * faceR n W p := by
  rw [C_mul_eq_smul, C_mul_eq_smul]
  ext v
  simp only [coeff_faceR, coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  split_ifs <;> simp

lemma faceR_C_mul_eq_prod {ι : Type*} [Fintype ι] {W : ℝ} (c : ι → K) (p : LP2 K) :
    faceR n W ((∏ i, C (c i)) * p) = (∏ i, C (c i)) * faceR n W p := by
  rw [← map_prod, faceR_C_mul_eq]

end LP2

namespace Heights

variable {E : List (Edge n K)} {nv : ℤ × ℤ} (H : Heights E nv)

/-- Bredden av nod `i`. -/
abbrev w (i : Fin n) : ℝ := H.hi i - H.lo i

lemma sum_cycles_lt (g : Fin n → Fin n) (hpos : ∀ i, H.lo i < H.hi i)
    (hnot : ∃ i, i ∉ periodicPts g) :
    ∑ γ ∈ cycles g, ∑ i ∈ γ, H.w i < ∑ i, H.w i := by
  obtain ⟨j, hj⟩ := hnot
  have h := Finset.sum_biUnion (cycles_pairwiseDisjoint g) (f := H.w)
  simp only [id] at h
  rw [← h]
  apply Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ j)
  · intro hmem
    obtain ⟨γ, hγ, hjγ⟩ := Finset.mem_biUnion.1 hmem
    exact not_mem_of_not_periodic g hj γ hγ hjγ
  · exact sub_pos.2 (hpos j)
  · intro i _ _; exact sub_nonneg.2 (H.lo_le_hi i)

lemma sum_cycles_eq (g : Fin n → Fin n) (hall : ∀ i, i ∈ periodicPts g) :
    ∑ γ ∈ cycles g, ∑ i ∈ γ, H.w i = ∑ i, H.w i := by
  have h := Finset.sum_biUnion (cycles_pairwiseDisjoint g) (f := H.w)
  simp only [id] at h
  rw [← h]
  congr 1
  ext i
  simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
  refine ⟨cyc g i, ?_, self_mem_cyc g (hall i)⟩
  unfold cycles
  exact Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hall i⟩, rfl⟩

end Heights

/-- **Toppsidan.** Om alla bredder är positiva är delen av `det Δ` på nivån `Σ bredder`
en summa över val där **varje nod ligger på en cykel**, med varje cykels toppdel. -/
theorem top_face (E : List (Edge n K)) (nv : ℤ × ℤ) (H : Heights E nv)
    (hpos : ∀ i, H.lo i < H.hi i) :
    faceR nv (∑ i, H.w i) (Net.mk n E).specPoly =
      ∑ f : Fin n → Fin E.length,
        if (∀ i, (E.get (f i)).Incident i) ∧ (∀ i, i ∈ periodicPts (choiceMap E f)) then
          (∏ i, C (E.get (f i)).cond) *
            ∏ γ ∈ cycles (choiceMap E f), faceR nv (∑ i ∈ γ, H.w i) (1 - ∏ i ∈ γ, choicePhase E f i)
        else 0 := by
  rw [specPoly_crsf, faceR_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  unfold choiceTerm
  by_cases hinc : ∀ i, (E.get (f i)).Incident i
  · rw [if_pos hinc]
    have htop := isTopR_prod (n := nv) _ _ _ fun γ hγ => H.cycle_factor_top hinc γ hγ
    by_cases hall : ∀ i, i ∈ periodicPts (choiceMap E f)
    · rw [if_pos ⟨hinc, hall⟩, faceR_C_mul_eq_prod, ← H.sum_cycles_eq _ hall]
      simp only [Heights.w]
      rw [faceR_prod _ _ _ fun γ hγ => H.cycle_factor_top hinc γ hγ]
    · rw [if_neg (fun h => hall h.2), faceR_C_mul_eq_prod]
      push Not at hall
      rw [faceR_eq_zero_of_lt htop (H.sum_cycles_lt _ hpos hall), mul_zero]
  · rw [if_neg hinc, if_neg (fun h => hinc h.1), faceR_zero]

namespace Heights

variable {E : List (Edge n K)} {nv : ℤ × ℤ} (H : Heights E nv) {f : Fin n → Fin E.length}

/-- **En cykel utan ögla**: toppdelen av dess faktor är `-z^{[γ]}` om cykeln är *tät*
(varje nod lämnas vid sin maxhöjd och nästa nod nås vid sin minhöjd), annars 0. -/
theorem cycle_face (hinc : ∀ i, (E.get (f i)).Incident i) (hpos : ∀ i, H.lo i < H.hi i)
    (i₀ : Fin n) (hper : i₀ ∈ periodicPts (choiceMap E f))
    (hnofix : ∀ x ∈ cyc (choiceMap E f) i₀, choiceMap E f x ≠ x) :
    faceR nv (∑ i ∈ cyc (choiceMap E f) i₀, H.w i)
        (1 - ∏ i ∈ cyc (choiceMap E f) i₀, choicePhase E f i) =
      if ∀ i ∈ cyc (choiceMap E f) i₀,
          H.exitH f i = H.hi i ∧ H.entH f i = H.lo (choiceMap E f i) then
        -mono (∑ i ∈ cyc (choiceMap E f) i₀, choiceDir E f i)
      else 0 := by
  set g := choiceMap E f
  set γ := cyc g i₀
  have hprod : ∏ i ∈ γ, choicePhase E f i = mono (∑ i ∈ γ, choiceDir E f i) := by
    rw [mono_sum]
    exact Finset.prod_congr rfl fun i hi => phase_eq_dir hinc i (hnofix i hi)
  have hWpos : 0 < ∑ i ∈ γ, H.w i :=
    Finset.sum_pos (fun i _ => sub_pos.2 (hpos i)) ⟨i₀, self_mem_cyc g hper⟩
  have h1 : faceR nv (∑ i ∈ γ, H.w i) (1 : LP2 K) = 0 := by
    have h1' : (1 : LP2 K) = single 0 1 := rfl
    rw [h1', faceR_single, if_neg]
    simp only [dot, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero, Int.cast_zero]
    exact hWpos.ne
  -- `⟨nv, [γ]⟩ = Σ (utgång - ingång)` och slackerna
  have hdot : (dot nv (∑ i ∈ γ, choiceDir E f i) : ℝ) =
      ∑ i ∈ γ, H.w i - ∑ i ∈ γ, ((H.hi i - H.exitH f i) + (H.entH f i - H.lo (g i))) := by
    rw [dot_sum]; push_cast
    simp only [H.dot_dir]
    have hc := sum_cyc_comp g i₀ H.lo
    simp only [Heights.w, Finset.sum_sub_distrib, Finset.sum_add_distrib] at *
    rw [hc]; ring
  have hslack : ∀ i ∈ γ, 0 ≤ (H.hi i - H.exitH f i) + (H.entH f i - H.lo (g i)) := fun i _ =>
    add_nonneg (sub_nonneg.2 (H.exitH_le hinc i)) (sub_nonneg.2 (H.lo_le_entH i))
  rw [hprod, faceR_sub, h1, zero_sub]
  have hm : (mono (∑ i ∈ γ, choiceDir E f i) : LP2 K) = single (∑ i ∈ γ, choiceDir E f i) 1 := rfl
  rw [hm, faceR_single]
  by_cases htight : ∀ i ∈ γ, H.exitH f i = H.hi i ∧ H.entH f i = H.lo (g i)
  · rw [if_pos htight, if_pos]
    rw [hdot]
    have : ∑ i ∈ γ, ((H.hi i - H.exitH f i) + (H.entH f i - H.lo (g i))) = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [(htight i hi).1, (htight i hi).2]; ring
    rw [this, sub_zero]
  · rw [if_neg htight, if_neg, neg_zero]
    intro heq
    apply htight
    rw [hdot] at heq
    have hz : ∑ i ∈ γ, ((H.hi i - H.exitH f i) + (H.entH f i - H.lo (g i))) = 0 := by linarith
    intro i hi
    have := (Finset.sum_eq_zero_iff_of_nonneg hslack).1 hz i hi
    have ha := sub_nonneg.2 (H.exitH_le hinc i)
    have hb := sub_nonneg.2 (H.lo_le_entH (f := f) i)
    constructor <;> linarith

end Heights

# lean-galois

A Lean 4 formalisation of the algebraic part of the **Galois obstruction for the snub square network**:
no finite sequence of local moves (Y–Δ, Δ–Y, series and parallel reductions and splittings, dead branches),
on the network's own torus or on any finite cover, turns the snub square resistor network into a minimal network.

This repository accompanies the paper

> Erik Ersson, *Exact two-point resistances on the snub square lattice via a hidden isoradial square lattice*
> (preprint, 2026), Theorem 3.6 and Appendix G.

The appendix (G.4) describes exactly what is machine-checked and which hypotheses remain; this README is a summary.

## Status

* Lean `v4.37.0-rc1`, Mathlib commit [`81cb93d`](https://github.com/leanprover-community/mathlib4/commit/81cb93dd9daa2d3d9cf275707da390fb66adadb0).
* About 4000 lines in 20 files. No `sorry`, no new axioms.
* `lake env lean Axioms.lean` prints the axioms of every main theorem; each one depends only on
  `propext`, `Classical.choice` and `Quot.sound`.

## Building

Install Lean with [elan](https://github.com/leanprover/elan) (the file `lean-toolchain` selects the right version), then

```sh
lake exe cache get   # download the prebuilt Mathlib files (optional but much faster)
lake build
lake env lean Axioms.lean
```

Without the Mathlib cache, `lake build` compiles the needed parts of Mathlib from source (about 20 minutes on 4 cores).
The GitHub Actions workflow in `.github/workflows/build.yml` runs these steps on every push.

## What is formalised

**Encoding** (`LeanGalois/Basic.lean`). A network on a torus is a number `n` of vertices in a fundamental domain and a
list of edges `⟨src, tgt, shift, cond⟩`; the edge joins `src` in cell 0 to `tgt` in cell `shift ∈ ℤ²`. Loops and
multiple edges are allowed. `Net.laplacian` is the Bloch Laplacian over the Laurent polynomial ring `K[ℤ²]`
(a loop of class `ℓ` contributes `c(2 − z^ℓ − z^(−ℓ))`), and `Net.specPoly G = det Δ_G`.

**Validation** (`Examples.lean`). Exact spectral polynomials of the square, hexagonal and snub square networks, the
latter for an arbitrary diagonal conductance `l` (Lemma 1), including the side polynomial
`X² − 2(2l²+4l+1)XZ + Z²` (`snub_face`).

**The obstruction** (`Galois.lean`, `Moves.lean`, `Concrete.lean`). Fix a subfield `F ⊆ ℝ`, `l ∈ F`, `l > 0`,
`κ > 0` with `κ² = l(l+2)` and `κ ∉ F`.

* `t_pow_not_mem` (Lemma 3): with `t = 1 + l + κ`, no power `t^m`, `m ≥ 1`, lies in `F`.
* `sats_10_1'`, `sats_10_1`: a network with conductances in `F` whose determinant is a nonzero constant multiple of
  that of the snub square is not minimal; hence no sequence of moves that preserve "conductances in `F`" and change
  the determinant by nonzero constants reaches a minimal network.

**All local moves** (`StarMesh.lean`, `Local.lean`). `specPoly_star`: star–mesh elimination multiplies the
determinant by the sum of the arm conductances (Schur complement). `LocalMove F` contains reordering, parallel
reduction and splitting, edge reversal, relabelling, contractible loops, star→mesh and mesh→star (this covers dead
branches, series reduction and splitting, Y→Δ and Δ→Y). `sats_10_1_local`.

**Covers** (`Maps.lean`, `Cover.lean`, `Obstruct.lean`, `Smith.lean`).

* `specPoly_liftX` (Lemma 2): `det Δ_lift(X^d, Z) = ∏_{k<d} det Δ_G(ζ^k X, Z)` by a discrete Fourier argument.
* `Obstructed`: an invariant (a side polynomial with a zero `(x, z)` such that no monomial along the side takes a
  value in `F` there), preserved by local moves, `GL₂(ℤ)` changes of basis and lifts; `snub_obstructed`.
* `sats_10_1_cover`: no mixture of local moves and cover steps reaches a minimal network.
* `lattice_smith`, `cover_reachable`, `sats_10_1_smith`: every rank-2 sublattice `Λ ⊆ ℤ²` is reached by Smith normal
  form and six cover steps.

**Lemma 4, the side polynomials of minimal networks** (`FunMat.lean`, `CRSF.lean`, `Sweep.lean`, `TopDet.lean`,
`Block.lean`, `Zigzag.lean`, `Lemma4.lean`, `ZigzagExample.lean`).

* `FunMat.det_funMat`, `specPoly_crsf`: expansion of `det Δ` over (oriented) cycle-rooted spanning forests.
* `sweep`, `top_face`, `Heights.cycle_face`, `top_det`: from height data, the Newton polygon lies in the zonogon and
  each top face is the determinant of the "tight" edges.
* `det_cycMat`, `det_blocks`, `face_splits`: with zigzag data, each side polynomial is
  `c · z^M · ∏_a (α_a ± β_a z^{s_a})` with `α_a, β_a` products of conductances.
* `sats_10_1_geo`, `sats_10_1_geo_snub_rat`: the theorem with Lemma 4 replaced by the two hypotheses below.
* `squareZigzag`: height and zigzag data exist for the square lattice, so the hypotheses are not vacuous.
* `sats_10_1_snub_rat`, `sats_10_1_local_snub_rat`, `sats_10_1_cover_snub_rat`: the concrete case `F = ℚ`, `l = 1`,
  `κ = √3`.

## What is *not* formalised (hypotheses checked by hand in the paper)

1. **`Schrijver`**: a minimal network can be brought to a geodesic one by local moves
   (A. Schrijver, *On the uniqueness of kernels*, J. Combin. Theory Ser. B 55 (1992), lemma in §4). Cited.
2. **`Geo`**: a geodesic network has height data and zigzag data for every top face
   (elementary plane geometry of the zigzag paths).
3. The network on the cover `T_Λ` is *defined* as `coverSmith φ d₁ d₂ G`; there is no independent construction of
   the `T_Λ` network proved to agree with it.
4. The reduction in Theorem 3.6(a) from an arbitrary diagonal conductance to `λ = 1`.

## Files

| File | Contents |
| --- | --- |
| `Basic.lean` | networks, Bloch Laplacian, side polynomials, `SideSplits` |
| `Examples.lean` | square, hexagonal and snub square spectral polynomials |
| `Galois.lean`, `Moves.lean`, `Concrete.lean` | Lemma 3, the main theorem (`sats_10_1`, named after Section 10 of an earlier draft), elementary moves, `F = ℚ` |
| `StarMesh.lean`, `Local.lean` | star–mesh determinant identity, all local moves |
| `Maps.lean`, `Cover.lean`, `Obstruct.lean`, `Smith.lean` | lifts, Lemma 2, the invariant, covers |
| `FunMat.lean`, `CRSF.lean` | cycle-rooted spanning forest expansion |
| `Sweep.lean`, `TopDet.lean`, `Block.lean`, `Zigzag.lean`, `Lemma4.lean`, `ZigzagExample.lean` | Lemma 4 |
| `Imports.lean` | Mathlib imports |
| `Axioms.lean` | `#print axioms` for the main theorems |

## License

Apache License 2.0 (the same license as Mathlib); see `LICENSE`.
To cite this code, see `CITATION.cff` (GitHub shows a "Cite this repository" button).

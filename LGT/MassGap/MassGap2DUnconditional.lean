/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Unconditional 2D Mass Gap (time-open geometry)

`mass_gap_2d` (MassGap2D.lean) takes the correlation bound itself as
the hypothesis `hBridge`. This file proves that bound, with no such
hypothesis, for d = 2, every β ≥ 0 and every compact G whose Haar
probability measure is bi-invariant (in particular G = U(n)).

## Geometry

Plaquettes are 2-cells of (ℤ/Nℤ)² with direction 0 ("time") and
direction 1 ("space"). We allow any action set `plaq` contained in the
*cylinder*: plaquettes whose anchor has time coordinate ≤ N - 2. So
time has open ends and space is periodic. Free-boundary boxes are
subsets of this set.

The full periodic torus (`plaq = univ`) is excluded on purpose. There
the plaquette holonomies satisfy one global constraint (for abelian
G: ∏ U_p = 1), so distinct plaquettes are correlated at every
distance. Those correlations are tiny, of order (I₁(β)/I₀(β))^{N²}
for U(1), but proving bounds on them needs different tools.

## Method

On the cylinder the plaquette holonomies are exactly independent.
List the plaquettes by time. The plaquette p with the largest time
coordinate owns the link `ownLink p = p.boundaryLinks 1`, which
appears in no other plaquette of `plaq`. Since U_p = a · U(ownLink p) · b
with a, b independent of that link, integrating it out against the
bi-invariant Haar measure detaches p (`integral_mul_freeLink`).
Induction gives

  ∫ ∏_{p ∈ plaq} φ_p(U_p) d(productHaar) = ∏_{p ∈ plaq} ∫ φ_p dHaar.

So `connected2pt (plaqObs p) (plaqObs q) = 0` for p ≠ q, and the
Doeblin-shaped bound 4n²(1 - e^{-2nβ})^{dist} follows.

In the language of the transfer matrix (Chatterjee §15.7): after
axial gauge fixing, each column is a Markov chain whose normaliser
Z(V) = ∫ q(V, W) dW does not depend on V (right invariance). So the
chain is a random walk, and its increments, the plaquette
holonomies, are i.i.d. Doeblin mixing is therefore not needed.

## Bi-invariance is necessary

`HasHaarProbability` only requires a probability measure. Without
invariance the bound fails: for G = U(1) with "Haar" = 0.7·δ₁ + 0.3·δᵢ
and β = 0, two adjacent plaquettes have connected 2-point function
≈ 0.0113, while the right-hand side is 4·(1 - e⁰)¹ = 0.

## Main results

- `YM2D.integral_mul_freeLink` — integrating out a free link
- `YM2D.integral_prod_plaquettes` — exact plaquette factorization
- `YM2D.connected2pt_plaqObs_eq_zero` — zero correlation for p ≠ q, any β ∈ ℝ
- `YM2D.mass_gap_2d_unconditional` — the `hBridge` bound, proved
- `YM2D.mass_gap_2d_unconditional_exp` — the exponential form of `mass_gap_2d`
- `YM2D.mass_gap_2d_unconditional_UN` — U(n), with Mathlib's Haar measure
-/

import LGT.MassGap.MassGap2D
import LGT.GaugeField.UnitaryGroup

set_option linter.unusedSectionVars false

open MeasureTheory GaussianField

noncomputable section

namespace YM2D

/-! ## Integrating out a free link -/

section FreeLink

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H]
variable (μ : Measure H) [IsProbabilityMeasure μ]
  [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]

/-- **Free-link integration.** Under a product of bi-invariant
probability measures, a coordinate `U i` that enters only through
`a U * U i * b U`, where `F`, `a`, `b` do not depend on `U i`, can be
integrated out: the factor detaches with its Haar average.

Proof: right-translate coordinate `i` by `g` (a measure-preserving
map), average over `g`, swap the integrals, and use bi-invariance in
the inner integral. -/
theorem integral_mul_freeLink (i : ι) (F : (ι → H) → ℝ) (a b : (ι → H) → H)
    (φ : H → ℝ)
    (hF : Measurable F) (CF : ℝ) (hFb : ∀ U, |F U| ≤ CF)
    (ha : Measurable a) (hb : Measurable b)
    (hφ : Measurable φ) (Cφ : ℝ) (hφb : ∀ g, |φ g| ≤ Cφ)
    (hFi : ∀ U x, F (Function.update U i x) = F U)
    (hai : ∀ U x, a (Function.update U i x) = a U)
    (hbi : ∀ U x, b (Function.update U i x) = b U) :
    ∫ U, F U * φ (a U * U i * b U) ∂(Measure.pi fun _ : ι => μ) =
      (∫ U, F U ∂(Measure.pi fun _ : ι => μ)) * ∫ g, φ g ∂μ := by
  set P : Measure (ι → H) := Measure.pi fun _ : ι => μ with hP
  -- Right translation of coordinate `i` by `g`.
  let R : H → (ι → H) → (ι → H) := fun g U j =>
    (if j = i then (fun x : H => x * g) else id) (U j)
  have hR : ∀ g, MeasurePreserving (R g) P P := by
    intro g
    refine measurePreserving_pi (fun _ => μ) (fun _ => μ) (fun j => ?_)
    by_cases hj : j = i
    · rw [if_pos hj]; exact measurePreserving_mul_right μ g
    · rw [if_neg hj]; exact MeasurePreserving.id μ
  have hR_upd : ∀ g U, R g U = Function.update U i (U i * g) := by
    intro g U
    funext j
    by_cases hj : j = i
    · subst hj; simp [R]
    · simp [R, hj]
  set Gf : (ι → H) → ℝ := fun U => F U * φ (a U * U i * b U) with hGf
  have hGf_meas : Measurable Gf :=
    hF.mul (hφ.comp ((ha.mul (measurable_pi_apply i)).mul hb))
  have hGR : ∀ g U, Gf (R g U) = F U * φ (a U * U i * g * b U) := by
    intro g U
    simp only [hGf, hR_upd, hFi, hai, hbi, Function.update_self, mul_assoc]
  -- Step 1: each translate has the same integral.
  have h1 : ∀ g, ∫ U, Gf (R g U) ∂P = ∫ U, Gf U ∂P := by
    intro g
    have h := integral_map (μ := P) (hR g).measurable.aemeasurable
      (f := Gf) (by rw [(hR g).map_eq]; exact hGf_meas.aestronglyMeasurable)
    rw [(hR g).map_eq] at h
    exact h.symm
  -- Step 2: the inner Haar average.
  have h_inner : ∀ U, ∫ g, F U * φ (a U * U i * g * b U) ∂μ =
      F U * ∫ g, φ g ∂μ := by
    intro U
    rw [integral_const_mul]
    congr 1
    have e1 : ∀ g, φ (a U * U i * g * b U) = (fun y => φ (a U * U i * y)) (g * b U) := by
      intro g; simp only [mul_assoc]
    simp_rw [e1]
    rw [integral_mul_right_eq_self (fun y => φ (a U * U i * y)) (b U),
      integral_mul_left_eq_self φ (a U * U i)]
  -- Integrability for the swap.
  have hCF : 0 ≤ CF := le_trans (abs_nonneg _) (hFb fun _ => 1)
  have hint : Integrable
      (Function.uncurry fun (g : H) (U : ι → H) => F U * φ (a U * U i * g * b U))
      (μ.prod P) := by
    refine Integrable.of_bound ?_ (CF * Cφ) (Filter.Eventually.of_forall fun x => ?_)
    · exact ((hF.comp measurable_snd).mul (hφ.comp
        ((((ha.comp measurable_snd).mul ((measurable_pi_apply i).comp measurable_snd)).mul
          measurable_fst).mul (hb.comp measurable_snd)))).aestronglyMeasurable
    · simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hFb _) (hφb _) (abs_nonneg _) hCF
  calc ∫ U, Gf U ∂P
      = ∫ _g, (∫ U, Gf U ∂P) ∂μ := by simp
    _ = ∫ g, ∫ U, Gf (R g U) ∂P ∂μ := by simp_rw [h1]
    _ = ∫ g, ∫ U, F U * φ (a U * U i * g * b U) ∂P ∂μ := by simp_rw [hGR]
    _ = ∫ U, ∫ g, F U * φ (a U * U i * g * b U) ∂μ ∂P := integral_integral_swap hint
    _ = ∫ U, F U * ∫ g, φ g ∂μ ∂P := by simp_rw [h_inner]
    _ = (∫ U, F U ∂P) * ∫ g, φ g ∂μ := integral_mul_const _ _

end FreeLink

/-! ## 2D lattice incidence -/

section Lattice

variable {N : ℕ}

/-- In 2D every plaquette has directions (0, 1). -/
theorem plaq2_dirs (p : LatticePlaquette 2 N) : p.dir1 = 0 ∧ p.dir2 = 1 := by
  have h := p.h_lt
  have h2 := p.dir2.isLt
  rw [Fin.lt_def] at h
  constructor <;> ext <;> simp <;> omega

/-- A 2D plaquette is determined by its anchor site. -/
theorem plaq2_ext {p q : LatticePlaquette 2 N} (h : p.site = q.site) : p = q := by
  obtain ⟨hp1, hp2⟩ := plaq2_dirs p
  obtain ⟨hq1, hq2⟩ := plaq2_dirs q
  cases p; cases q
  simp only at h hp1 hp2 hq1 hq2
  subst h hp1 hp2 hq1 hq2
  rfl

/-- Time coordinate of a plaquette anchor. -/
def tIdx (p : LatticePlaquette 2 N) : ℕ := (p.site 0).val

/-- The cylinder condition: the anchor's time coordinate is at most N - 2,
so the plaquette does not wrap around in time. -/
def IsCylinderPlaquette (p : LatticePlaquette 2 N) : Prop := (p.site 0).val + 1 < N

/-- The link owned by a plaquette: its second boundary link, the
spatial link at time t + 1. -/
def ownLink (p : LatticePlaquette 2 N) : LatticeLink 2 N := p.boundaryLinks 1

/-- Shifting in time increases the time coordinate by one when nothing wraps. -/
theorem val_siteShift_zero (x : FinLatticeSites 2 N) (hx : (x 0).val + 1 < N) :
    ((siteShift 2 N x 0) 0).val = (x 0).val + 1 := by
  have hN : 1 < N := by omega
  have h1 : (1 : ZMod N).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hN]
  simp only [siteShift, Function.update_self]
  rw [ZMod.val_add_of_lt (by rw [h1]; exact hx), h1]

/-- The owned link of a cylinder plaquette is none of its other boundary links. -/
theorem boundaryLink_ne_ownLink_self (p : LatticePlaquette 2 N)
    (hp : IsCylinderPlaquette p) (k : Fin 4) (hk : k ≠ 1) :
    p.boundaryLinks k ≠ ownLink p := by
  obtain ⟨h1, h2⟩ := plaq2_dirs p
  have hne : p.dir1 ≠ p.dir2 := ne_of_lt p.h_lt
  fin_cases k
  · simp [ownLink, LatticePlaquette.boundaryLinks, hne]
  · exact absurd rfl hk
  · simp [ownLink, LatticePlaquette.boundaryLinks, hne]
  · simp only [ownLink, LatticePlaquette.boundaryLinks, ne_eq, LatticeLink.mk.injEq,
      and_true]
    intro h
    have := congrArg (fun x => (x 0).val) h
    simp only at this
    rw [h1, val_siteShift_zero p.site hp] at this
    omega

/-- The owned link of the latest cylinder plaquette lies on no other
plaquette that is not later in time. -/
theorem boundaryLink_ne_ownLink_of_le (p q : LatticePlaquette 2 N)
    (hp : IsCylinderPlaquette p) (hqp : q ≠ p) (ht : tIdx q ≤ tIdx p) (k : Fin 4) :
    q.boundaryLinks k ≠ ownLink p := by
  obtain ⟨hp1, hp2⟩ := plaq2_dirs p
  obtain ⟨hq1, hq2⟩ := plaq2_dirs q
  fin_cases k
  · simp [ownLink, LatticePlaquette.boundaryLinks, hp2, hq1]
  · simp only [ownLink, LatticePlaquette.boundaryLinks, ne_eq, LatticeLink.mk.injEq,
      hp1, hq1, hp2, hq2, and_true]
    intro h
    exact hqp (plaq2_ext (siteShift_injective (d := 2) (N := N) 0 h))
  · simp [ownLink, LatticePlaquette.boundaryLinks, hp2, hq1]
  · simp only [ownLink, LatticePlaquette.boundaryLinks, ne_eq, LatticeLink.mk.injEq,
      hp1, hq2, hp2, and_true]
    intro h
    have := congrArg (fun x => (x 0).val) h
    simp only at this
    rw [val_siteShift_zero p.site hp] at this
    simp only [tIdx] at ht
    omega

variable {G : Type*} [Group G]

/-- A plaquette holonomy ignores links off its boundary. -/
theorem plaquetteHolonomy_update_of_ne (U : LatticeLink 2 N → G) (q : LatticePlaquette 2 N)
    (ℓ : LatticeLink 2 N) (x : G) (h : ∀ k, q.boundaryLinks k ≠ ℓ) :
    plaquetteHolonomy (Function.update U ℓ x : GaugeConnection G 2 N) q =
      plaquetteHolonomy (U : GaugeConnection G 2 N) q := by
  simp only [plaquetteHolonomy, Function.update_of_ne (h _)]

/-- The holonomy as a two-sided translate of the owned link. -/
theorem plaquetteHolonomy_eq_shear (U : LatticeLink 2 N → G) (p : LatticePlaquette 2 N) :
    plaquetteHolonomy (U : GaugeConnection G 2 N) p =
      U (p.boundaryLinks 0) * U (ownLink p) *
        ((U (p.boundaryLinks 2))⁻¹ * (U (p.boundaryLinks 3))⁻¹) := by
  simp only [plaquetteHolonomy, ownLink, mul_assoc]

end Lattice

/-! ## Exact factorization of the plaquette variables -/

section Factorization

variable {N : ℕ} [Fintype (LatticeLink 2 N)]
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μ : Measure G) [IsProbabilityMeasure μ]
  [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]

theorem measurable_plaquetteHolonomy (p : LatticePlaquette 2 N) :
    Measurable (fun U : LatticeLink 2 N → G =>
      plaquetteHolonomy (U : GaugeConnection G 2 N) p) := by
  simp only [plaquetteHolonomy]
  fun_prop

/-- **Exact factorization.** If every plaquette in `plaq` lies in the
cylinder, the plaquette holonomies are independent Haar-distributed
variables under the product Haar measure:

  ∫ ∏_{p ∈ plaq} φ_p(U_p) = ∏_{p ∈ plaq} ∫ φ_p dμ.

Induction on `plaq` peels off the latest plaquette in time, whose
owned link is free (`integral_mul_freeLink`). -/
theorem integral_prod_plaquettes (plaq : Finset (LatticePlaquette 2 N))
    (hplaq : ∀ p ∈ plaq, IsCylinderPlaquette p)
    (φ : LatticePlaquette 2 N → G → ℝ) (hφ : ∀ p, Measurable (φ p))
    (C : ℝ) (hφb : ∀ p g, |φ p g| ≤ C) :
    ∫ U, ∏ p ∈ plaq, φ p (plaquetteHolonomy (U : GaugeConnection G 2 N) p)
        ∂(Measure.pi fun _ : LatticeLink 2 N => μ) =
      ∏ p ∈ plaq, ∫ g, φ p g ∂μ := by
  induction plaq using Finset.induction_on_max_value (f := tIdx) with
  | empty => simp
  | insert a s ha hmax ih =>
    have hcyl : ∀ p ∈ s, IsCylinderPlaquette p :=
      fun p hp => hplaq p (Finset.mem_insert_of_mem hp)
    have ha_cyl : IsCylinderPlaquette a := hplaq a (Finset.mem_insert_self a s)
    have hC : 0 ≤ C := le_trans (abs_nonneg _) (hφb a 1)
    have h0 := boundaryLink_ne_ownLink_self a ha_cyl 0 (by decide)
    have h2 := boundaryLink_ne_ownLink_self a ha_cyl 2 (by decide)
    have h3 := boundaryLink_ne_ownLink_self a ha_cyl 3 (by decide)
    have hfree := integral_mul_freeLink μ (ownLink a)
      (fun U => ∏ p ∈ s, φ p (plaquetteHolonomy (U : GaugeConnection G 2 N) p))
      (fun U => U (a.boundaryLinks 0))
      (fun U => (U (a.boundaryLinks 2))⁻¹ * (U (a.boundaryLinks 3))⁻¹) (φ a)
      (Finset.measurable_prod s fun p _ => (hφ p).comp (measurable_plaquetteHolonomy p))
      (C ^ s.card)
      (fun U => by
        rw [Finset.abs_prod]
        calc ∏ p ∈ s, |φ p (plaquetteHolonomy (U : GaugeConnection G 2 N) p)|
            ≤ ∏ _p ∈ s, C :=
              Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun p _ => hφb p _)
          _ = C ^ s.card := Finset.prod_const _)
      (measurable_pi_apply _)
      ((measurable_pi_apply _).inv.mul (measurable_pi_apply _).inv)
      (hφ a) C (hφb a)
      (fun U x => Finset.prod_congr rfl fun q hq => by
        rw [plaquetteHolonomy_update_of_ne U q (ownLink a) x
          (boundaryLink_ne_ownLink_of_le a q ha_cyl (ne_of_mem_of_not_mem hq ha)
            (hmax q hq))])
      (fun U x => Function.update_of_ne h0 _ _)
      (fun U x => by
        simp only [Function.update_of_ne h2, Function.update_of_ne h3])
    simp_rw [Finset.prod_insert ha]
    calc ∫ U, φ a (plaquetteHolonomy (U : GaugeConnection G 2 N) a) *
            ∏ p ∈ s, φ p (plaquetteHolonomy (U : GaugeConnection G 2 N) p)
            ∂(Measure.pi fun _ : LatticeLink 2 N => μ)
        = ∫ U, (∏ p ∈ s, φ p (plaquetteHolonomy (U : GaugeConnection G 2 N) p)) *
            φ a (U (a.boundaryLinks 0) * U (ownLink a) *
              ((U (a.boundaryLinks 2))⁻¹ * (U (a.boundaryLinks 3))⁻¹))
            ∂(Measure.pi fun _ : LatticeLink 2 N => μ) := by
          congr 1; funext U; rw [mul_comm, plaquetteHolonomy_eq_shear]
      _ = (∫ U, ∏ p ∈ s, φ p (plaquetteHolonomy (U : GaugeConnection G 2 N) p)
            ∂(Measure.pi fun _ : LatticeLink 2 N => μ)) * ∫ g, φ a g ∂μ := hfree
      _ = (∫ g, φ a g ∂μ) * ∏ p ∈ s, ∫ g, φ p g ∂μ := by rw [ih hcyl, mul_comm]

end Factorization

/-! ## Finite-product bookkeeping -/

section ProdLemmas

variable {N : ℕ}

/-- Indicator exponent: 1 at `p`, 0 elsewhere. -/
def ind (p r : LatticePlaquette 2 N) : ℕ := if r = p then 1 else 0

theorem ind_le (p r : LatticePlaquette 2 N) : ind p r ≤ 1 := by
  unfold ind; split_ifs <;> omega

theorem prod_pow_ind (s : Finset (LatticePlaquette 2 N)) (p : LatticePlaquette 2 N)
    (hp : p ∈ s) (x : LatticePlaquette 2 N → ℝ) :
    ∏ r ∈ s, x r ^ ind p r = x p := by
  rw [← Finset.mul_prod_erase s _ hp, ind, if_pos rfl, pow_one,
    Finset.prod_eq_one (fun r hr => by rw [ind, if_neg (Finset.ne_of_mem_erase hr), pow_zero]),
    mul_one]

theorem prod_split_two (s : Finset (LatticePlaquette 2 N)) (p q : LatticePlaquette 2 N)
    (hp : p ∈ s) (hq : q ∈ s) (hpq : p ≠ q) (f : LatticePlaquette 2 N → ℝ) :
    ∏ r ∈ s, f r = f p * (f q * ∏ r ∈ (s.erase p).erase q, f r) := by
  rw [Finset.mul_prod_erase (s.erase p) f (Finset.mem_erase.mpr ⟨hpq.symm, hq⟩),
    Finset.mul_prod_erase s f hp]

theorem prod_rest_eq (s : Finset (LatticePlaquette 2 N)) (p q : LatticePlaquette 2 N)
    (e : LatticePlaquette 2 N → ℕ) (he : ∀ r, r ≠ p → r ≠ q → e r = 0) (f : ℕ → ℝ) :
    ∏ r ∈ (s.erase p).erase q, f (e r) = ∏ _r ∈ (s.erase p).erase q, f 0 :=
  Finset.prod_congr rfl fun r hr => by
    rw [he r (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hr))
      (Finset.ne_of_mem_erase hr)]

theorem prod_erase_eq (s : Finset (LatticePlaquette 2 N)) (p : LatticePlaquette 2 N)
    (e : LatticePlaquette 2 N → ℕ) (he : ∀ r, r ≠ p → e r = 0) (f : ℕ → ℝ) :
    ∏ r ∈ s.erase p, f (e r) = ∏ _r ∈ s.erase p, f 0 :=
  Finset.prod_congr rfl fun r hr => by rw [he r (Finset.ne_of_mem_erase hr)]

end ProdLemmas

/-! ## Single-plaquette weight and its moments -/

section SinglePlaquette

variable (G : Type*) (n : ℕ) [Group G] [HasGaugeTrace G n]
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]

/-- The single-plaquette Boltzmann factor exp(-β(n - Re Tr g)). -/
def plaqWeight (β : ℝ) (g : G) : ℝ := Real.exp (-(β * wilsonPlaquetteCost G n g))

theorem plaqWeight_pos (β : ℝ) (g : G) : 0 < plaqWeight G n β g := Real.exp_pos _

theorem continuous_reTr (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n))) :
    Continuous (gaugeReTr G n) := by
  unfold gaugeReTr gaugeTrace
  exact Complex.continuous_re.comp
    (continuous_finsetSum _ (fun i _ => (continuous_apply_apply i i).comp hRep_cont))

theorem measurable_reTr (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n))) :
    Measurable (gaugeReTr G n) :=
  (continuous_reTr G n hRep_cont).measurable

theorem measurable_plaqWeight (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (β : ℝ) : Measurable (plaqWeight G n β) := by
  unfold plaqWeight wilsonPlaquetteCost
  exact (measurable_const.mul (measurable_const.sub (measurable_reTr G n hRep_cont))).neg.exp

/-- Uniform bounds on the plaquette cost: 0 ≤ n - Re Tr g ≤ 2n. -/
theorem cost_bounds (hTrace : ∀ g : G, |gaugeReTr G n g| ≤ n) (g : G) :
    0 ≤ wilsonPlaquetteCost G n g ∧ wilsonPlaquetteCost G n g ≤ 2 * n := by
  unfold wilsonPlaquetteCost
  have := abs_le.mp (hTrace g)
  constructor <;> linarith [this.1, this.2]

theorem plaqWeight_le (hTrace : ∀ g : G, |gaugeReTr G n g| ≤ n) (β : ℝ) (g : G) :
    plaqWeight G n β g ≤ Real.exp (|β| * (2 * n)) := by
  unfold plaqWeight
  apply Real.exp_le_exp.mpr
  obtain ⟨h0, h2⟩ := cost_bounds G n hTrace g
  have h1 : -(β * wilsonPlaquetteCost G n g) = (-β) * wilsonPlaquetteCost G n g := by ring
  rw [h1]
  calc (-β) * wilsonPlaquetteCost G n g ≤ |β| * wilsonPlaquetteCost G n g :=
        mul_le_mul_of_nonneg_right (neg_le_abs β) h0
    _ ≤ |β| * (2 * n) := mul_le_mul_of_nonneg_left h2 (abs_nonneg β)

theorem plaqWeight_ge (hTrace : ∀ g : G, |gaugeReTr G n g| ≤ n) (β : ℝ) (g : G) :
    Real.exp (-(|β| * (2 * n))) ≤ plaqWeight G n β g := by
  unfold plaqWeight
  apply Real.exp_le_exp.mpr
  obtain ⟨h0, h2⟩ := cost_bounds G n hTrace g
  apply neg_le_neg
  calc β * wilsonPlaquetteCost G n g ≤ |β| * wilsonPlaquetteCost G n g :=
        mul_le_mul_of_nonneg_right (le_abs_self β) h0
    _ ≤ |β| * (2 * n) := mul_le_mul_of_nonneg_left h2 (abs_nonneg β)

/-- The bound used for all factorized integrands Re Tr(g)^e · w(g), e ≤ 2. -/
theorem abs_pow_mul_plaqWeight_le (hTrace : ∀ g : G, |gaugeReTr G n g| ≤ n) (β : ℝ)
    (e : ℕ) (he : e ≤ 2) (g : G) :
    |gaugeReTr G n g ^ e * plaqWeight G n β g| ≤
      ((n : ℝ) + 1) ^ 2 * Real.exp (|β| * (2 * n)) := by
  rw [abs_mul, abs_pow, abs_of_pos (plaqWeight_pos G n β g)]
  have h1 : |gaugeReTr G n g| ^ e ≤ ((n : ℝ) + 1) ^ 2 :=
    calc |gaugeReTr G n g| ^ e ≤ ((n : ℝ) + 1) ^ e :=
          pow_le_pow_left₀ (abs_nonneg _) (by linarith [hTrace g]) e
      _ ≤ ((n : ℝ) + 1) ^ 2 :=
          pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) he
  exact mul_le_mul h1 (plaqWeight_le G n hTrace β g) (plaqWeight_pos G n β g).le
    (by positivity)

variable [HasHaarProbability G]

/-- Haar moments of the single-plaquette law: m_j = ∫ (Re Tr g)^j w(g) dg. -/
def plaqMoment (β : ℝ) (j : ℕ) : ℝ :=
  ∫ g, gaugeReTr G n g ^ j * plaqWeight G n β g ∂(haarG G)

theorem integrable_pow_mul_plaqWeight (hTrace : ∀ g : G, |gaugeReTr G n g| ≤ n)
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (β : ℝ) (e : ℕ)
    (he : e ≤ 2) :
    Integrable (fun g => gaugeReTr G n g ^ e * plaqWeight G n β g) (haarG G) :=
  integrable_of_bound
    (((measurable_reTr G n hRep_cont).pow_const e).mul (measurable_plaqWeight G n hRep_cont β))
    (abs_pow_mul_plaqWeight_le G n hTrace β e he)

theorem plaqMoment_zero_pos (hTrace : ∀ g : G, |gaugeReTr G n g| ≤ n)
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (β : ℝ) :
    0 < plaqMoment G n β 0 := by
  unfold plaqMoment
  simp only [pow_zero, one_mul]
  exact lt_of_lt_of_le (Real.exp_pos _)
    (integral_ge_const_of_ge
      (integrable_of_bound (measurable_plaqWeight G n hRep_cont β)
        (fun g => by
          rw [abs_of_pos (plaqWeight_pos G n β g)]; exact plaqWeight_le G n hTrace β g))
      (plaqWeight_ge G n hTrace β))

theorem abs_plaqMoment_one_le (hTrace : ∀ g : G, |gaugeReTr G n g| ≤ n)
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (β : ℝ) :
    |plaqMoment G n β 1| ≤ n * plaqMoment G n β 0 := by
  have hi1 := integrable_pow_mul_plaqWeight G n hTrace hRep_cont β 1 (by norm_num)
  have hi0 := integrable_pow_mul_plaqWeight G n hTrace hRep_cont β 0 (by norm_num)
  unfold plaqMoment
  calc |∫ g, gaugeReTr G n g ^ 1 * plaqWeight G n β g ∂(haarG G)|
      ≤ ∫ g, |gaugeReTr G n g ^ 1 * plaqWeight G n β g| ∂(haarG G) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ g, (n : ℝ) * (gaugeReTr G n g ^ 0 * plaqWeight G n β g) ∂(haarG G) := by
        apply integral_mono hi1.abs (hi0.const_mul _)
        intro g
        simp only [pow_one, pow_zero, one_mul, abs_mul,
          abs_of_pos (plaqWeight_pos G n β g)]
        exact mul_le_mul_of_nonneg_right (hTrace g) (plaqWeight_pos G n β g).le
    _ = n * ∫ g, gaugeReTr G n g ^ 0 * plaqWeight G n β g ∂(haarG G) :=
        integral_const_mul _ _

theorem plaqMoment_two_nonneg (β : ℝ) : 0 ≤ plaqMoment G n β 2 := by
  unfold plaqMoment
  exact integral_nonneg fun g => mul_nonneg (sq_nonneg _) (plaqWeight_pos G n β g).le

theorem plaqMoment_two_le (hTrace : ∀ g : G, |gaugeReTr G n g| ≤ n)
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (β : ℝ) :
    plaqMoment G n β 2 ≤ (n : ℝ) ^ 2 * plaqMoment G n β 0 := by
  have hi2 := integrable_pow_mul_plaqWeight G n hTrace hRep_cont β 2 (by norm_num)
  have hi0 := integrable_pow_mul_plaqWeight G n hTrace hRep_cont β 0 (by norm_num)
  unfold plaqMoment
  rw [← integral_const_mul]
  apply integral_mono hi2 (hi0.const_mul _)
  intro g
  simp only [pow_zero, one_mul]
  apply mul_le_mul_of_nonneg_right _ (plaqWeight_pos G n β g).le
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hTrace g) 2

end SinglePlaquette

/-! ## Correlations of plaquette observables -/

section YM

variable (G : Type*) (n : ℕ) [Group G] [HasGaugeTrace G n]
variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable [HasHaarProbability G] [(haarG G).IsMulLeftInvariant] [(haarG G).IsMulRightInvariant]
variable (N : ℕ) [Fintype (LatticeLink 2 N)]

theorem boltzmannWeight_eq_prod (β : ℝ) (U : GaugeConnection G 2 N)
    (plaq : Finset (LatticePlaquette 2 N)) :
    boltzmannWeight G n 2 N β U plaq =
      ∏ p ∈ plaq, plaqWeight G n β (plaquetteHolonomy U p) := by
  unfold boltzmannWeight wilsonAction plaqWeight
  rw [← Finset.sum_neg_distrib, Real.exp_sum]

theorem measurable_boltzmannWeight_2d
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (β : ℝ) (plaq : Finset (LatticePlaquette 2 N)) :
    Measurable (fun U : GaugeConnection G 2 N => boltzmannWeight G n 2 N β U plaq) := by
  simp_rw [boltzmannWeight_eq_prod G n N β _ plaq]
  exact Finset.measurable_prod plaq fun p _ =>
    (measurable_plaqWeight G n hRep_cont β).comp (measurable_plaquetteHolonomy p)

/-- Factorized moments: on the cylinder,
∫ ∏_p (Re Tr U_p)^{e_p} · e^{-S} d(productHaar) = ∏_p m_{e_p}. -/
theorem integral_moments (hTrace : ∀ g : G, |gaugeReTr G n g| ≤ n)
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (β : ℝ)
    (plaq : Finset (LatticePlaquette 2 N)) (hplaq : ∀ p ∈ plaq, IsCylinderPlaquette p)
    (e : LatticePlaquette 2 N → ℕ) (he : ∀ p, e p ≤ 2) :
    ∫ U, (∏ p ∈ plaq, gaugeReTr G n (plaquetteHolonomy U p) ^ e p) *
        boltzmannWeight G n 2 N β U plaq ∂(productHaar G 2 N) =
      ∏ p ∈ plaq, plaqMoment G n β (e p) := by
  have h := integral_prod_plaquettes (haarG G) plaq hplaq
    (fun p g => gaugeReTr G n g ^ e p * plaqWeight G n β g)
    (fun p => ((measurable_reTr G n hRep_cont).pow_const (e p)).mul
      (measurable_plaqWeight G n hRep_cont β))
    _ (fun p g => abs_pow_mul_plaqWeight_le G n hTrace β (e p) (he p) g)
  unfold plaqMoment
  refine Eq.trans ?_ h
  show (∫ U : LatticeLink 2 N → G, _ ∂(Measure.pi fun _ : LatticeLink 2 N => haarG G)) = _
  congr 1
  funext U
  rw [boltzmannWeight_eq_prod, ← Finset.prod_mul_distrib]

theorem partitionFn_eq_prod (hTrace : ∀ g : G, |gaugeReTr G n g| ≤ n)
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (β : ℝ)
    (plaq : Finset (LatticePlaquette 2 N)) (hplaq : ∀ p ∈ plaq, IsCylinderPlaquette p) :
    partitionFn G n 2 N β plaq = ∏ _p ∈ plaq, plaqMoment G n β 0 := by
  refine Eq.trans ?_
    (integral_moments G n N hTrace hRep_cont β plaq hplaq (fun _ => 0) (fun _ => by norm_num))
  unfold partitionFn
  congr 1
  funext U
  simp

theorem integral_plaqObs_mul_weight (hTrace : ∀ g : G, |gaugeReTr G n g| ≤ n)
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (β : ℝ)
    (plaq : Finset (LatticePlaquette 2 N)) (hplaq : ∀ p ∈ plaq, IsCylinderPlaquette p)
    (p : LatticePlaquette 2 N) (hp : p ∈ plaq) :
    ∫ U, plaqObs G n 2 N p U * boltzmannWeight G n 2 N β U plaq ∂(productHaar G 2 N) =
      ∏ r ∈ plaq, plaqMoment G n β (ind p r) := by
  refine Eq.trans ?_ (integral_moments G n N hTrace hRep_cont β plaq hplaq (ind p)
    (fun r => (ind_le p r).trans (by norm_num)))
  congr 1
  funext U
  rw [prod_pow_ind plaq p hp (fun r => gaugeReTr G n (plaquetteHolonomy U r))]
  rfl

theorem integral_plaqObs_mul_plaqObs_mul_weight (hTrace : ∀ g : G, |gaugeReTr G n g| ≤ n)
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (β : ℝ)
    (plaq : Finset (LatticePlaquette 2 N)) (hplaq : ∀ p ∈ plaq, IsCylinderPlaquette p)
    (p q : LatticePlaquette 2 N) (hp : p ∈ plaq) (hq : q ∈ plaq) :
    ∫ U, (plaqObs G n 2 N p U * plaqObs G n 2 N q U) * boltzmannWeight G n 2 N β U plaq
        ∂(productHaar G 2 N) =
      ∏ r ∈ plaq, plaqMoment G n β (ind p r + ind q r) := by
  refine Eq.trans ?_ (integral_moments G n N hTrace hRep_cont β plaq hplaq
    (fun r => ind p r + ind q r)
    (fun r => by
      have := ind_le p r; have := ind_le q r; show ind p r + ind q r ≤ 2; omega))
  congr 1
  funext U
  simp only [pow_add, Finset.prod_mul_distrib]
  rw [prod_pow_ind plaq p hp (fun r => gaugeReTr G n (plaquetteHolonomy U r)),
    prod_pow_ind plaq q hq (fun r => gaugeReTr G n (plaquetteHolonomy U r))]
  rfl

private theorem connected_algebra (m0 m1 R : ℝ) (h0 : m0 ≠ 0) (hR : R ≠ 0) :
    m1 * (m1 * R) / (m0 * (m0 * R)) -
      (m1 * (m0 * R) / (m0 * (m0 * R))) * (m0 * (m1 * R) / (m0 * (m0 * R))) = 0 := by
  field_simp
  ring

/-- **Exact decorrelation.** On the cylinder, distinct plaquette
observables are uncorrelated for every coupling β ∈ ℝ. -/
theorem connected2pt_plaqObs_eq_zero
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (β : ℝ)
    (plaq : Finset (LatticePlaquette 2 N)) (hplaq : ∀ p ∈ plaq, IsCylinderPlaquette p)
    (p q : LatticePlaquette 2 N) (hp : p ∈ plaq) (hq : q ∈ plaq) (hpq : p ≠ q) :
    connected2pt G n 2 N β plaq (plaqObs G n 2 N p) (plaqObs G n 2 N q) = 0 := by
  have hTrace : ∀ g : G, |gaugeReTr G n g| ≤ n :=
    fun g => abs_le.mpr ⟨by linarith [hTrace_lower g], hTrace_upper g⟩
  have hm0 := plaqMoment_zero_pos G n hTrace hRep_cont β
  have hR : 0 < ∏ _r ∈ (plaq.erase p).erase q, plaqMoment G n β 0 :=
    Finset.prod_pos fun _ _ => hm0
  have hX : ∏ r ∈ plaq, plaqMoment G n β (ind p r + ind q r) =
      plaqMoment G n β 1 *
        (plaqMoment G n β 1 * ∏ _r ∈ (plaq.erase p).erase q, plaqMoment G n β 0) := by
    rw [prod_split_two plaq p q hp hq hpq,
      prod_rest_eq plaq p q (fun r => ind p r + ind q r)
        (fun r h1 h2 => by simp [ind, h1, h2]) (plaqMoment G n β)]
    simp [ind, hpq, Ne.symm hpq]
  have hYp : ∏ r ∈ plaq, plaqMoment G n β (ind p r) =
      plaqMoment G n β 1 *
        (plaqMoment G n β 0 * ∏ _r ∈ (plaq.erase p).erase q, plaqMoment G n β 0) := by
    rw [prod_split_two plaq p q hp hq hpq,
      prod_rest_eq plaq p q (ind p) (fun r h1 _ => by simp [ind, h1]) (plaqMoment G n β)]
    simp [ind, Ne.symm hpq]
  have hYq : ∏ r ∈ plaq, plaqMoment G n β (ind q r) =
      plaqMoment G n β 0 *
        (plaqMoment G n β 1 * ∏ _r ∈ (plaq.erase p).erase q, plaqMoment G n β 0) := by
    rw [prod_split_two plaq p q hp hq hpq,
      prod_rest_eq plaq p q (ind q) (fun r _ h2 => by simp [ind, h2]) (plaqMoment G n β)]
    simp [ind, hpq]
  have hZ : partitionFn G n 2 N β plaq =
      plaqMoment G n β 0 *
        (plaqMoment G n β 0 * ∏ _r ∈ (plaq.erase p).erase q, plaqMoment G n β 0) := by
    rw [partitionFn_eq_prod G n N hTrace hRep_cont β plaq hplaq,
      prod_split_two plaq p q hp hq hpq (fun _ => plaqMoment G n β 0)]
  simp only [connected2pt, ymExpect]
  rw [integral_plaqObs_mul_plaqObs_mul_weight G n N hTrace hRep_cont β plaq hplaq p q hp hq,
    integral_plaqObs_mul_weight G n N hTrace hRep_cont β plaq hplaq p hp,
    integral_plaqObs_mul_weight G n N hTrace hRep_cont β plaq hplaq q hq,
    hX, hYp, hYq, hZ]
  exact connected_algebra _ _ _ hm0.ne' hR.ne'

/-- The diagonal term: the variance of a plaquette observable is at most n². -/
theorem abs_connected2pt_plaqObs_self_le
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (β : ℝ)
    (plaq : Finset (LatticePlaquette 2 N)) (hplaq : ∀ p ∈ plaq, IsCylinderPlaquette p)
    (p : LatticePlaquette 2 N) (hp : p ∈ plaq) :
    |connected2pt G n 2 N β plaq (plaqObs G n 2 N p) (plaqObs G n 2 N p)| ≤ (n : ℝ) ^ 2 := by
  have hTrace : ∀ g : G, |gaugeReTr G n g| ≤ n :=
    fun g => abs_le.mpr ⟨by linarith [hTrace_lower g], hTrace_upper g⟩
  have hm0 := plaqMoment_zero_pos G n hTrace hRep_cont β
  have hR : 0 < ∏ _r ∈ plaq.erase p, plaqMoment G n β 0 := Finset.prod_pos fun _ _ => hm0
  have hX : ∏ r ∈ plaq, plaqMoment G n β (ind p r + ind p r) =
      plaqMoment G n β 2 * ∏ _r ∈ plaq.erase p, plaqMoment G n β 0 := by
    rw [← Finset.mul_prod_erase plaq (fun r => plaqMoment G n β (ind p r + ind p r)) hp,
      prod_erase_eq plaq p (fun r => ind p r + ind p r) (fun r h => by simp [ind, h])
        (plaqMoment G n β)]
    simp [ind]
  have hY : ∏ r ∈ plaq, plaqMoment G n β (ind p r) =
      plaqMoment G n β 1 * ∏ _r ∈ plaq.erase p, plaqMoment G n β 0 := by
    rw [← Finset.mul_prod_erase plaq (fun r => plaqMoment G n β (ind p r)) hp,
      prod_erase_eq plaq p (ind p) (fun r h => by simp [ind, h]) (plaqMoment G n β)]
    simp [ind]
  have hZ : partitionFn G n 2 N β plaq =
      plaqMoment G n β 0 * ∏ _r ∈ plaq.erase p, plaqMoment G n β 0 := by
    rw [partitionFn_eq_prod G n N hTrace hRep_cont β plaq hplaq,
      ← Finset.mul_prod_erase plaq (fun _ => plaqMoment G n β 0) hp]
  simp only [connected2pt, ymExpect]
  rw [integral_plaqObs_mul_plaqObs_mul_weight G n N hTrace hRep_cont β plaq hplaq p p hp hp,
    integral_plaqObs_mul_weight G n N hTrace hRep_cont β plaq hplaq p hp, hX, hY, hZ,
    mul_div_mul_right _ _ hR.ne', mul_div_mul_right _ _ hR.ne']
  -- Now |m₂/m₀ - (m₁/m₀)²| ≤ n², with 0 ≤ m₂/m₀ ≤ n² and |m₁/m₀| ≤ n.
  have hA : |plaqMoment G n β 1 / plaqMoment G n β 0| ≤ n := by
    rw [abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
    exact abs_plaqMoment_one_le G n hTrace hRep_cont β
  have hB0 : 0 ≤ plaqMoment G n β 2 / plaqMoment G n β 0 :=
    div_nonneg (plaqMoment_two_nonneg G n β) hm0.le
  have hB1 : plaqMoment G n β 2 / plaqMoment G n β 0 ≤ (n : ℝ) ^ 2 := by
    rw [div_le_iff₀ hm0]; exact plaqMoment_two_le G n hTrace hRep_cont β
  set A := plaqMoment G n β 1 / plaqMoment G n β 0
  set B := plaqMoment G n β 2 / plaqMoment G n β 0
  have hAA : A * A ≤ (n : ℝ) ^ 2 := by
    rw [← abs_mul_abs_self A, sq]
    exact mul_self_le_mul_self (abs_nonneg A) hA
  rw [abs_sub_le_iff]
  constructor <;> nlinarith [mul_self_nonneg A]

/-- **Unconditional 2D mass gap (Doeblin form).** This is the bound
that `mass_gap_2d` takes as its hypothesis `hBridge`, now proved for
d = 2, every β ≥ 0, every compact G with bi-invariant Haar measure,
and every action set `plaq` on the time-open cylinder. -/
theorem mass_gap_2d_unconditional [NeZero N] (β : ℝ) (hβ : 0 ≤ β)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (plaq : Finset (LatticePlaquette 2 N)) (hplaq : ∀ p ∈ plaq, IsCylinderPlaquette p)
    (p q : LatticePlaquette 2 N) (hp : p ∈ plaq) (hq : q ∈ plaq) :
    |connected2pt G n 2 N β plaq (plaqObs G n 2 N p) (plaqObs G n 2 N q)| ≤
      4 * (↑n : ℝ) ^ 2 * (1 - ymDoeblinLowerBound n β) ^ plaquetteDist 2 N p q := by
  by_cases hpq : p = q
  · subst hpq
    have hd : plaquetteDist 2 N p p = 0 := latticePlaquetteDist_self 2 N p
    rw [hd, pow_zero, mul_one]
    have := abs_connected2pt_plaqObs_self_le G n N hTrace_lower hTrace_upper hRep_cont β
      plaq hplaq p hp
    nlinarith [sq_nonneg (n : ℝ)]
  · rw [connected2pt_plaqObs_eq_zero G n N hTrace_lower hTrace_upper hRep_cont β plaq hplaq
      p q hp hq hpq, abs_zero]
    have hε : ymDoeblinLowerBound n β ≤ 1 := by
      unfold ymDoeblinLowerBound
      exact Real.exp_le_one_iff.mpr (by have := Nat.cast_nonneg (α := ℝ) n; nlinarith)
    exact mul_nonneg (by positivity) (pow_nonneg (by linarith) _)

/-- **Unconditional 2D mass gap (exponential form).** The conclusion of
`mass_gap_2d`, with its `hBridge` hypothesis discharged by
`mass_gap_2d_unconditional`. The rate -log(1 - e^{-2nβ}) is positive
for β > 0 and n ≥ 1 (`mass_gap_2d_rate_pos`) and does not depend on N. -/
theorem mass_gap_2d_unconditional_exp [NeZero N] (β : ℝ) (hβ : 0 ≤ β)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (plaq : Finset (LatticePlaquette 2 N)) (hplaq : ∀ p ∈ plaq, IsCylinderPlaquette p)
    (p q : LatticePlaquette 2 N) (hp : p ∈ plaq) (hq : q ∈ plaq) :
    |connected2pt G n 2 N β plaq (plaqObs G n 2 N p) (plaqObs G n 2 N q)| ≤
      4 * (↑n) ^ 2 * Real.exp (-(-Real.log (1 - ymDoeblinLowerBound n β)) *
        ↑(plaquetteDist 2 N p q)) :=
  mass_gap_2d G n 2 N β hβ hTrace_lower hTrace_upper hRep_cont plaq
    (integrable_of_bound (measurable_boltzmannWeight_2d G n N hRep_cont β plaq)
      (fun U => by
        rw [abs_of_pos (boltzmannWeight_pos G n 2 N β U plaq)]
        exact boltzmannWeight_le_one G n 2 N β hβ U plaq hTrace_upper))
    p q
    (mass_gap_2d_unconditional G n N β hβ hTrace_lower hTrace_upper hRep_cont plaq hplaq
      p q hp hq)

end YM

/-! ## Haar measure on compact groups is right invariant -/

open Measure in
/-- On a compact second-countable group, a Haar probability measure is
also right invariant: `map (· * g) μ` is a left-invariant Haar measure,
hence a scalar multiple of μ, and comparing total masses forces the
scalar to be 1. -/
theorem isMulRightInvariant_of_compact {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [SecondCountableTopology K]
    [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsHaarMeasure μ] [IsProbabilityMeasure μ] : μ.IsMulRightInvariant := by
  constructor
  intro g
  have h := isMulLeftInvariant_eq_smul (map (· * g) μ) μ
  have hc : haarScalarFactor (map (· * g) μ) μ = 1 := by
    have h1 := congrArg (fun ν : Measure K => ν Set.univ) h
    simp only [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ,
      Set.preimage_univ, measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
      mul_one] at h1
    exact_mod_cast h1.symm
  rw [hc, one_smul] at h
  exact h

/-! ## U(n) specialization -/

section UnitaryGroup

/-- Links of (ℤ/Nℤ)^d form a finite type. -/
@[reducible] def latticeLinkFintype {d N : ℕ} [NeZero N] : Fintype (LatticeLink d N) :=
  Fintype.ofEquiv (FinLatticeSites d N × Fin d)
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun l => (l.site, l.dir)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

attribute [local instance] latticeLinkFintype

instance isHaarMeasure_unitaryHaar (n : ℕ) : Measure.IsHaarMeasure (unitaryHaar n) := by
  unfold unitaryHaar; infer_instance

instance isMulLeftInvariant_haarG_unitaryGroup (n : ℕ) :
    (haarG (Matrix.unitaryGroup (Fin n) ℂ)).IsMulLeftInvariant :=
  show (unitaryHaar n).IsMulLeftInvariant from inferInstance

instance isMulRightInvariant_haarG_unitaryGroup (n : ℕ) :
    (haarG (Matrix.unitaryGroup (Fin n) ℂ)).IsMulRightInvariant :=
  show (unitaryHaar n).IsMulRightInvariant from isMulRightInvariant_of_compact _

/-- **Unconditional 2D mass gap for U(n).** For every N, every β ≥ 0, and
every action set on the time-open cylinder (which includes every
free-boundary box), plaquette correlations under the Wilson action
with Mathlib's Haar measure on U(n) satisfy the `mass_gap_2d` bound,
with no hypotheses left. -/
theorem mass_gap_2d_unconditional_UN (n N : ℕ) [NeZero N] (β : ℝ) (hβ : 0 ≤ β)
    (plaq : Finset (LatticePlaquette 2 N)) (hplaq : ∀ p ∈ plaq, IsCylinderPlaquette p)
    (p q : LatticePlaquette 2 N) (hp : p ∈ plaq) (hq : q ∈ plaq) :
    |connected2pt (Matrix.unitaryGroup (Fin n) ℂ) n 2 N β plaq
        (plaqObs (Matrix.unitaryGroup (Fin n) ℂ) n 2 N p)
        (plaqObs (Matrix.unitaryGroup (Fin n) ℂ) n 2 N q)| ≤
      4 * (↑n) ^ 2 * Real.exp (-(-Real.log (1 - ymDoeblinLowerBound n β)) *
        ↑(plaquetteDist 2 N p q)) :=
  mass_gap_2d_unconditional_exp (Matrix.unitaryGroup (Fin n) ℂ) n N β hβ
    (unitaryGroup_gaugeReTr_neg_le n) (unitaryGroup_gaugeReTr_le n)
    (unitaryGroup_rep_continuous n) plaq hplaq p q hp hq

/-- For U(n), distinct cylinder plaquettes are exactly uncorrelated at every β ∈ ℝ. -/
theorem connected2pt_plaqObs_eq_zero_UN (n N : ℕ) [NeZero N] (β : ℝ)
    (plaq : Finset (LatticePlaquette 2 N)) (hplaq : ∀ p ∈ plaq, IsCylinderPlaquette p)
    (p q : LatticePlaquette 2 N) (hp : p ∈ plaq) (hq : q ∈ plaq) (hpq : p ≠ q) :
    connected2pt (Matrix.unitaryGroup (Fin n) ℂ) n 2 N β plaq
        (plaqObs (Matrix.unitaryGroup (Fin n) ℂ) n 2 N p)
        (plaqObs (Matrix.unitaryGroup (Fin n) ℂ) n 2 N q) = 0 :=
  connected2pt_plaqObs_eq_zero (Matrix.unitaryGroup (Fin n) ℂ) n N
    (unitaryGroup_gaugeReTr_neg_le n) (unitaryGroup_gaugeReTr_le n)
    (unitaryGroup_rep_continuous n) β plaq hplaq p q hp hq hpq

end UnitaryGroup

end YM2D

end

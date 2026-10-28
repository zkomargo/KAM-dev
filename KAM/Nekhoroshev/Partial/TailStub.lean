/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Nekhoroshev.Partial.Constants
public import KAM.Nekhoroshev.Partial.Coordinates
public import KAM.Frozen.Nekhoroshev.Defs.IsPartialPerturbation
public import KAM.Frozen.Nekhoroshev.Defs.InnerCore
public import KAM.Frozen.Nekhoroshev.Defs.ComplexifyPhase
public import KAM.Frozen.Planetary.Defs.DegenerateHamiltonian

/-!
# LOCAL STAGING ONLY (never committed): N11 Appendix A signatures of unlanded inputs
-/

@[expose] public noncomputable section

open Set Metric
open scoped BigOperators

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.NormalForm

variable {n k : ℕ}

def block_setting (a : PartialData n k) (μ : ℝ) (Ic : Fin n → ℝ) (r : ℝ) : PartialBlock n k :=
  ⟨Ic, innerCore a.D (3*(constants a).d μ/4), r, (constants a).d μ/4⟩

def signedH (a : PartialData n k) (σ : ℝ) (I : Fin n → ℂ) : ℂ :=
  (σ:ℂ)*a.h I/(2*(Real.pi:ℂ))

def signedF (_a : PartialData n k) (σ μ : ℝ) (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ)
    (z : EC n k) : ℂ :=
  (σ*μ/(2*Real.pi):ℝ)*P (Fin.append (fun i => (2*Real.pi:ℂ)*z.1 i) (slowPair z).1,
    Fin.append (fastAction z) (slowPair z).2)

/-- Pull physical slow coordinates back by the fixed block scale. -/
def slowScale (lam : ℝ) (z : EC n k) : EC n k :=
  (z.1, Fin.append (fastAction z)
    (Fin.append (fun i => (lam:ℂ)*(slowPair z).1 i) (fun i => (lam:ℂ)*(slowPair z).2 i)))

def blockPert (a : PartialData n k) (μ σ : ℝ) (Ic : Fin n → ℝ) (r : ℝ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) : EC n k → ℂ :=
  signedF a σ μ P ∘ slowScale (block_setting a μ Ic r).lam

theorem hessian (a : PartialData n k) (hne : a.G.Nonempty) :
    a.m ≤ a.Mc ∧ ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (∀ Ic ∈ a.G, ∀ R : ℝ, 0 < R → R ≤ (constants a).r0 →
        FastConvex Ic R (constants a).m1 (constants a).M1 (signedH a σ)) ∧
      (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.actionNbhd a.G' a.ρ →
        (constants a).g1 ≤ ‖KAM.frequencyMap (signedH a σ) I‖) := sorry

theorem domain (a : PartialData n k) {μ σ R : ℝ} {Ic : Fin n → ℝ}
    (hμ : 0 < μ) (hσ : DefiniteSign a σ) (hIc : Ic ∈ a.G) (hR : 0 < R) (hRR : R ≤ (constants a).r0)
    (hd : (constants a).d μ ≤ a.ρ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) (hP : IsPartialPerturbation a.G' a.D a.ρ P) :
    let b := block_setting a μ Ic R
    polyNbhd {KAM.realInclusion n Ic} R ⊆ KAM.actionNbhd a.G' a.ρ ∧
    ext_class b R (constants a).s (blockPert a μ σ Ic R P) ∧
    WBound b.base R (constants a).s (blockPert a μ σ Ic R P) ((constants a).eps μ) := sorry

/-- The geometric output consumed by Part 11; covering itself is an upstream theorem.
No new representation of the Part 8 lattice enumeration is introduced. -/
theorem block_data (a : PartialData n k) (hne : a.G.Nonempty) {μ σ : ℝ} (hμ : 0 < μ)
    (hε : (constants a).eps μ ≤ (constants a).eps0) (hσ : DefiniteSign a σ)
    (hκ : 6 ≤ (constants a).kappa μ) {Ic : Fin n → ℝ} (hIc : Ic ∈ a.G) :
    let c := constants a
    ∃ Λ : AddSubgroup (Fin n → ℤ), ∃ r : ℝ,
      Λ ≠ ⊤ ∧ c.rTheta μ ≤ r ∧ r ≤ c.R0/c.K μ ∧ 0 < r ∧
      IsNonresonant {KAM.realInclusion n Ic} (c.K μ/Real.sqrt n) ((9/8)*c.M1*c.K μ*r)
        (Λ:Set (Fin n → ℤ)) (signedH a σ) ∧
      (∃ δ : ℝ, 0 ≤ δ ∧ δ < c.m1*r/32 ∧ NearResonance (Λ:Set (Fin n → ℤ)) (signedH a σ) Ic δ) ∧
      FreqLipschitz {KAM.realInclusion n Ic} r (Real.sqrt n*c.M1) (signedH a σ) ∧
      c.eps μ ≤ c.m1*r^2/2^14 ∧
      c.eps μ ≤ ((9/8)*c.M1*c.K μ*r)*r/(2^7*9*(c.K μ/Real.sqrt n)) := sorry

/-- Physical period-one coordinates (no block-dependent coordinate scale). -/
def physicalDomain (Ic : Fin n → ℝ) (R w : ℝ) (S : Set (KAM.Planetary.Phase k)) : Set (ER n k) :=
  {z | ‖fastAction z-Ic‖ < R ∧ ∃ v ∈ S, ‖slowPair z-v‖ < w}

theorem domain_field (a : PartialData n k) {μ σ R : ℝ} {Ic : Fin n → ℝ}
    (hμ : 0 < μ) (hσ : DefiniteSign a σ) (hIc : Ic ∈ a.G) (hR : 0 < R) (hRR : R ≤ (constants a).r0)
    (hd : (constants a).d μ ≤ a.ρ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) (hP : IsPartialPerturbation a.G' a.D a.ρ P) :
    let b := block_setting a μ Ic R
    let H := KAM.Planetary.degenerateHamiltonian (realPart a.h) (fun _ w => (P (complexifyPhase w)).re) μ
    EqOn (fun z => σ • realWfield (2*Real.pi) (converted H) z)
      (realWfield (2*Real.pi) (fun z => (liftFast (signedH a σ) (extCx z)+signedF a σ μ P (extCx z)).re))
      (physicalDomain Ic R b.w b.S) := sorry

/-- The selected frozen definiteness witness is retained for assembly. -/
theorem hessian_at_sign (a : PartialData n k) (hne : a.G.Nonempty) {σ : ℝ}
    (hσ : DefiniteSign a σ) :
    a.m ≤ a.Mc ∧ ∀ Ic ∈ a.G, ∀ R : ℝ, 0 < R → R ≤ (constants a).r0 →
      FastConvex Ic R (constants a).m1 (constants a).M1 (signedH a σ) := sorry

theorem nonresonant (b : PartialBlock n k) {s K α L p ε : ℝ}
    {h : (Fin n → ℂ) → ℂ} {f : EC n k → ℂ}
    (hh : ExtNFHyp b s K α L p ε {0} h f)
    (hsmall : ε ≤ α*b.rB/(2^7*conjExp p*K))
    (F : ER n k → ER n k)
    (hF : EqOn F (realWfield b.c (realHamiltonianExt b b.rB (liftFast h+f))) (b.realDom b.rB))
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ∀ u ∈ J, HasDerivAt y (F (y u)) u)
    (hinit : fastAction (y 0) = b.Ic) (hx : b.lam • slowPair (y 0) ∈ b.S)
    {t1 : ℝ} (ht1 : t1 ∈ J) (ht : |t1| ≤ s*b.rB/(5*ε)*Real.exp ((2*Real.pi*K*s)/6))
    (hstop : ∀ u ∈ uIcc 0 t1, b.lam • slowPair (y u) ∈ b.S) :
    ∀ u ∈ uIcc 0 t1, ‖fastAction (y u)-b.Ic‖ ≤ b.rB/2 := sorry

theorem resonant (b : PartialBlock n k) {s K α m M ε : ℝ}
    {Λ : AddSubgroup (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ} {f : EC n k → ℂ}
    (hh : ExtNFHyp b s K α (Real.sqrt n*M) (9/8) ε (Λ:Set (Fin n → ℤ)) h f)
    (hconv : FastConvex b.Ic b.rB m M h) (hne : NearResonance (Λ:Set (Fin n → ℤ)) h b.Ic (m*b.rB/32))
    (hsmall : ε ≤ m*b.rB^2/2^14)
    (F : ER n k → ER n k)
    (hF : EqOn F (realWfield b.c (realHamiltonianExt b b.rB (liftFast h+f))) (b.realDom b.rB))
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ∀ u ∈ J, HasDerivAt y (F (y u)) u)
    (hinit : fastAction (y 0) = b.Ic) (hx : b.lam • slowPair (y 0) ∈ b.S)
    {t1 : ℝ} (ht1 : t1 ∈ J) (ht : |t1| ≤ s*m*b.rB/(240*M*ε)*Real.exp ((2*Real.pi*K*s)/6))
    (hstop : ∀ u ∈ uIcc 0 t1, b.lam • slowPair (y u) ∈ b.S) :
    ∀ u ∈ uIcc 0 t1, euclid (fastAction (y u)-b.Ic) ≤ b.rB/2 := sorry

end KAM.Nekhoroshev

end

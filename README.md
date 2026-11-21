# From Theta Lifts to the Critical Line

**Independent Paper Reconstruction & Audit of the Alpöge–Claude Argument for Dirichlet $L$-Functions**

> **Edition:** Revised 21 November 2026 (250 pp.) — **Conditional Paper Proof Complete (Theorem 1.3)**  
> **Provenance:** Full end-to-end breakdown and initial paper reconstruction carried out by **GPT-6.2 Astra**, consuming approximately **70% of a single Pro 100 weekly quota**.  
> **Active Focus:** Continuing work on the core arithmetic estimates **(15.1)** and **(15.2)**.

---

## Overview

This repository contains an independent, human-readable mathematical reconstruction and dependency audit of the 20 November 2026 Lean 4 formalization of the Riemann Hypothesis (RH) and Dirichlet Generalized Riemann Hypothesis (GRH) announced by L. Alpöge with Claude (pinned community mirror revision `40e56bab0265`, Lean `4.33.1`).

The 250-page exposition extracts the mathematical structure of the formal proof (~175,187 compiled modules; ~1.48M declarations per root closure), supplies self-contained paper proofs using standard literature where available, audits critical signs, normalizations, and quantifier orders, and isolates the exact arithmetic inequalities **(15.1)** and **(15.2)** that remain open on paper.

---

## Core Targets: Equations (15.1) and (15.2)

The manuscript proves **Theorem 1.3** unconditionally on paper: **all critical-line assertions for $\zeta(s)$ and every Dirichlet $L$-function $L(s,\chi)$ (Theorem 1.1)** follow from arbitrarily late window bounds on the weighted prime-power discrepancy, via either of two uniform arithmetic estimates.

### 1. Pointwise Translate Estimate — (15.1)

For every primitive Dirichlet character $\psi$, every sufficiently small $\varepsilon > 0$, and every $Y_0$, there exists $Y \ge \max(1, Y_0)$ such that at every scale $x \in [Y, Y^{3/2}]$ there are common host, frame, and weight data $\mathcal{D}_x$ satisfying the scale, coset-share, rank, and discarded-character hypotheses of Sections 10 and 15, and for **every** translate $u \in A_0(\mathcal{D}_x)$:

$$D_u = \sum_{t \in T} \sum_{j=1}^{m} \bigl(\mathrm{ASK}_{u,t,j} - \mathrm{MAIN}_{u,t,j}\bigr) \le x^{5\varepsilon}\!\left(n_T a_E + \frac{n_T a_E m^2}{k} + 2 n m^2 b x^\varepsilon + \frac{m b n_2 k x^{2\varepsilon}}{n^2}\right) =: E_x(\mathcal{D}_x). \tag{15.1}$$

### 2. Weaker Signed Translate-Average Estimate — (15.2)

Theorem 1.3 also follows upon replacing the pointwise translate condition (15.1) with its **uniform average over the subgroup $A_0(\mathcal{D}_x)$**:

$$\frac{1}{|A_0(\mathcal{D}_x)|} \sum_{u \in A_0(\mathcal{D}_x)} D_u(\mathcal{D}_x) \le E_x(\mathcal{D}_x). \tag{15.2}$$

Key reductions established on paper around **(15.2)**:

- **Exact Four-Twist Evaluation (Proposition 10.4 & Corollary 10.5):** The normalized translate mean $\frac{2\bar{D}}{B\delta}$ is computed explicitly in terms of four primitive twists ($\psi^a$, $\psi^a J_q$, $\psi^a J_d$, $\psi^a J_q J_d$) for each power of $\psi$, with the three discarded twists bounded uniformly by Theorem 6.4. For $\psi = 1$ (ordinary $\zeta$), the main term reduces to four real functions: $G[1] + G[J_q] - G[J_d] - G[J_q J_d]$.
- **Discrete Test at Integer Squares (Corollary 10.6):** For the critical-line implication, it suffices to supply the common data and **(15.2)** solely at the **integer squares** inside each window $[Y, Y^{3/2}]$.
- **Single Translate-Averaged Slope Comparison (Section 8.6 & Section 11.1):** Forming a labelled direct sum across translates before composing the first edge yields a **single normalized trace/slope comparison** (**Theorem 8.12**, **Corollary 8.13**) that allows ranks and frame defects to vary with $u$ and tracks explicit subadditive lattice-denominator and archimedean repair costs $\mathcal{J}$ (**Lemma 8.11**) and exceptional target-slope tails $T_{\mathrm{out}}$.
- **Reduction of (15.2) to One Mean Division, One Slope Comparison, and One Signed Loss (Proposition 11.3, Corollaries 11.4–11.5):** On the actual numerical scales ($e_{\mathrm{div}} \le 2$, $e_{\mathrm{loss}} = 0$), writing $\Delta = \mathbb{E}(\mathcal{A}_u - G_u + \kappa I_u) - (1+\kappa)L_P$, **(15.2)** follows from the mean division bound (11.1), the frame/variation hypotheses, and the explicit defect-reserve inequality (with no extra logarithmic loss in $|A_0|$):
  $$\Delta + \frac{4\mathcal{J}}{1 - \delta_*} + T_{\mathrm{out}} \le (y^5 - y^3) P \qquad \bigl(y = x^\varepsilon\bigr). \tag{11.4}$$
  When $\mathcal{J} = T_{\mathrm{out}} = 0$ and $\Delta \le 0$, this tightens the window bound directly to $G_{\mathcal{F}_\psi}(x) \le x^{1/2+7\varepsilon}$.

> **Scope Notice:** On the paper arguments available in this edition, both **(15.1)** and **(15.2)** remain open (including for $\psi = 1$). Full machine-checked verdicts apply to the pinned upstream Lean export.

---

## Paper Coverage & Remaining Inputs Toward (15.1) and (15.2)

| Section(s) | Pages | Topic | Paper Status | Established on Paper | Remaining Arithmetic Inputs for (15.1) / (15.2) |
| :--- | :---: | :--- | :---: | :--- | :--- |
| **§1, §12, §13** | 2–3, 237–241 | One-sided window zero exclusion & critical-line deduction | **Complete** | Polar divisor (Prop 12.1), exponential concentration (Lemma 12.2), signed derivative bound & pole isolation (Lemmas 12.3–12.4, Thm 12.5), full GRH/RH deduction | None |
| **§10** | 226–232 | Fourier extraction, translate mean & square test | **Complete** | Inertia-orthogonality discrepancy (Lemma 10.1), four-loss extraction (Prop 10.3), translate mean & discarded-twist bound (Prop 10.4, Cor 10.5), integer-square test (Cor 10.6) | None (reduces Theorem 1.1 to (15.1) or (15.2)) |
| **§4.1–4.2, §6, §7** | 18–21, 87–95 | Auxiliary primes, CM host fields, orbits & thin scales | **Complete** | $O(Q^{1/4})$ auxiliary-box density (Lemma 4.1), Siegel-zero-safe selection of $(q,d)$ (Thm 6.4), cyclotomic CM host & half-different lattice (Prop 7.1, Lemma 7.2), rank fit (Lemma 7.3), orbit-avoiding set & biased top set (Prop 7.4, Lemma 7.5), thin-coordinate decay (Prop 7.6), CM scalar bound (Prop 7.8) | Simultaneous automorphic realization across translates (§11) |
| **§2, §3** | 3–18 | Weighted-trace Galois representations & crystalline lattices | **Partial** | Trace interpolation & semisimple realization (Prop 2.1–2.2), lacunary rank extraction (Prop 3.2), crystalline closure via T. Liu (Thm 3.5), rectangular period comparisons (Prop 3.6–3.7), classical cuspidal local compatibility, principal level & adjoint Selmer vanishing (Prop 3.8–3.11) | Singular-weight geometric seeds & simultaneous Hecke congruences (2.1); independent construction of linked bounded-height integral period frames |
| **§4.3–4.4, §5** | 21–87 | Integral cohomology, deformation rings & Selmer budgets | **Partial** | Low-layer $H^2$ bound $C_K=32$ (Thm 5.4), cyclotomic descent & moving two-rank $R_2$ (Prop 5.3), multigraded Koszul intersection bound (Thm 5.20), rank-3/4 trace products (Cor 5.22, 5.27), endoscopic, odd-orthogonal & imprimitive quartic attachments (Prop 5.30–5.39), two-power Bernoulli unit (Thm 5.45), all-depth vanishing families & Case III emptiness for two-power order targets including $\psi=1$ (Prop 5.47–5.50, Cor 5.51), all-prime Selmer budget on $16fe \le x^{\varepsilon/204}$ (Thm 5.52, Cor 5.53) | Coverage of remaining deformation components (even 2D block of Lemma 5.34, strongly irreducible rank-3/4 points & char-$\ell$ test curves, seed local vanishing, good-point component propagation, one-sided exclusions); complementary Selmer budget up to $t = \lfloor v^{401} \rfloor$ (§5.20) |
| **§8, §11** | 95–107, 232–237 | Theta-chain arithmetic geometry, translate-mean slope comparison & family assembly | **Framework Complete** | Chain composition & period budgets (Prop 8.1, Lemma 8.2), shifted dual determinant cost (Prop 8.3, Cor 8.4), descended height & nearly tight frame coercivity (Lemmas 8.5–8.6), finite-layer HN bound (Thm 8.7), direct-sum lattice repair & single translate-averaged slope comparison (Lemma 8.11, Thm 8.12, Cor 8.13), mean reduction & defect reserve (Prop 11.3, Cor 11.4–11.5) | Concrete local chain valuation bounds, recorded gains on actual descended columns, archimedean frame/compression inputs, and family-level simultaneous realization (Formal input 11.2) |
| **§9.1–9.5** | 107–157 | Global theta period matching & rank recursions | **Complete** | Split, inert, and real local matching quotients; global proportionality $I(\Phi) = c I'(\Phi')$ and both uniform rank recursions across all allowed signatures (Thm 9.38) | None |
| **§9.6–9.9** | 157–226 | Theta denominators, Bergman bounds, CM degrees & arithmetic Hilbert–Samuel | **Near-Complete** | Semiabelian denominator clearing $D_M^2$ (Thm 9.54), short harmonic generators (Prop 9.61), doubled graph identity & spanning on marked period charts (Prop 9.69, 9.76–9.80), cusp/half-max/flag-volume & Bergman bound $\beta_*$ (Prop 9.72, 9.74, Cor 9.75), integral Moret–Bailly key (Thm 9.82), product CM & splitting-model vertical orders (Prop 9.85, Thm 9.87), final-weight integral spanning sections on good indefinite covers (Thm 9.70, Cor 9.88), normed-filtration degree bound (Prop 9.40–9.45, 9.89–9.90) | All-scale compatible existence of good deep covers `Y.Good(e,o)` / `Y.Match`; integral flag & toroidal subcanonical sheaf comparisons; uniform-threshold restriction, Chow-height & `MeanAll` comparisons |

---

## Machine Verification & Local Artifacts (§14)

Full independent replay of all 175,187 compiled upstream modules is reported externally (Sutherland / LUMI runs via Lean kernel, `nanoda`, `con-leche`, and `lean4lean`, using strictly `Classical.choice`, `propext`, and `Quot.sound`). This project additionally records local verification artifacts under `verification/`:

- **`verification/arithmetic-prefix-receipt.json`** — SHA-256 verification and export indices for a `1,539,032,259`-byte unmodified prefix (`140,192` raw declaration records; SHA-256 `dfabcd8e32844354b199a7f360c1f11ffe8d7c0bcf67ab6e04c7d36ddbedb08b`) covering `Formalism.VW.rh_of_every`, `Deduction.poleData`, `Deduction.landau_window`, `Deduction.ch_core`, `Deduction.ch_top`, and `UpperTheory.Comparison2.core_gm`, independently checked locally by **Nanoda 0.4.17** (`145,327` internal declarations, 0 errors) and **ConLeche** (`140,188` accepted declarations, `137,728` deferred checks).
- **`verification/WindowBridge.lean`** — Standalone Lean `4.36.0` / Mathlib `v4.36.0` proof of the logarithmic exceptional-set window selection lemma ($J = 4(2C/\eta)^R$).
- **`verification/CriticalLineBridge.lean`** — Standalone Mathlib verification of the Section 13 quantifier implication from arbitrarily late arithmetic windows to the zero-free half-plane $\operatorname{Re} s > 1/2$.
- **`verification/TranslateMean.lean`** — Standalone Mathlib verification of the finite-group character projection and uniform error averaging underlying Proposition 10.4.

---

## Compute & Development Log

- **Initial Full Breakdown & Reconstruction:** Completed by **GPT-6.2 Astra** using ~**70% of a single Pro 100 weekly quota**, producing the end-to-end 250-page exposition, dependency audit, and the direct-sum translate-mean slope framework (§8.6, §11.1).
- **Current Stage:** Ongoing work focused specifically on discharging the remaining arithmetic-geometric inputs for **(15.1)** and **(15.2)**.

---

## Primary References

- L. Alpöge, *Announcement of a proof of the Riemann hypothesis*, 20 November 2026.
- L. Alpöge with Claude, *Lean formalization of RH and Dirichlet GRH*, pinned community mirror release of 20 November 2026 (`40e56bab0265`, Lean `4.33.1`).
- A. V. Sutherland, *Verification files for the Lean proof of the Riemann Hypothesis* (`nanoda`, `con-leche`, `lean4lean`, kernel replay status).
- Complete list of 74 cited mathematical works: see `References` (pp. 246–250 of the manuscript).

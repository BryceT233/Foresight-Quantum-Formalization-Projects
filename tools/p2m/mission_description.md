## Motivation

Simulating quantum dynamics is the most compelling near-term application of quantum computers, and almost every algorithm for it rests on **product formulas**: the ideal evolution $e^{tH}$ under a Hamiltonian $H=\sum_{\gamma=1}^{\Gamma}H_\gamma$ is approximated by a product of exponentials of the individual summands. The error of that approximation decides the cost, because the number of short steps needed is set by how fast the error shrinks.

Textbook analyses bound this error by the **1-norm** $\sum_\gamma\|H_\gamma\|$. For lattice models that quantity grows with the number of terms, so the predicted cost is far worse than what is observed in practice. The paper formalized here, Childs–Su–Tran–Wiebe–Zhu, *A Theory of Trotter Error* (arXiv:1912.08854), proved that the error of a $p$th-order formula is instead controlled by a **nested-commutator coefficient**: for many physically relevant Hamiltonians this is far smaller than the 1-norm, and for geometrically local systems it is asymptotically independent of the system size. This turned product-formula cost estimates into a commutator-scaling theory and made the paper's bound the standard reference for the area.

The result is **proved** in the literature. What this mission tracks is **formalization**: the paper's argument has been machine-checked in Lean 4 against Mathlib, and the work here is to expose that development as a set of independently attackable statements, to close the parts of the paper that remain unformalized, and to let later work build on the formal definitions rather than on the prose.

## Setting

Let $\mathbb{A}$ be a **complete normed ring** that is also a normed $\mathbb{R}$-algebra with $\|1\|\le 1$, and let $\|\cdot\|$ denote the algebra norm. This is deliberately more general than the paper, which states its results for matrices and the spectral norm: the paper's argument uses only submultiplicativity ($\|xy\|\le\|x\|\,\|y\|$), the normalization $\|1\|\le1$, completeness (so the exponential series and the interval integrals converge), and — in the anti-Hermitian case — the fact that $\|e^{tA}\|=1$ for anti-Hermitian $A$. Every complete normed algebra has those properties, so the statements below hold in that generality and specialize back to the paper's by taking $\mathbb{A}$ to be a matrix algebra. Throughout, $\|\cdot\|$ is the algebra norm and not a spectral norm.

Fix integers $\Upsilon\ge1$ (the number of **stages**) and $\Gamma\ge1$ (the number of summands). A **product formula** is the family of data
$$\mathscr S(t)=\prod_{\upsilon=1}^{\Upsilon}\prod_{\gamma=1}^{\Gamma}e^{\,t\,a_{(\upsilon,\gamma)}H_{\pi_\upsilon(\gamma)}},$$
consisting of real **coefficients** $a_{(\upsilon,\gamma)}$ with $|a_{(\upsilon,\gamma)}|\le1$, a **permutation** $\pi_\upsilon$ of the $\Gamma$ summands for each stage, and the **generators** $H_\gamma$. In Lean this data is the structure `ProductFormulaData Υ Γ`, and $\mathscr S(t)$ is its `eval`.

Write $H:=\sum_{\gamma=1}^{\Gamma}H_\gamma$. The formula is of **order** $p$ when $\mathscr S(t)=e^{tH}+O(t^{p+1})$ as $t\to0$; the formalization encodes this as `ProductFormulaData.IsOrderOf p H`.

Three error objects occur, distinguished by how the error is factored out of $\mathscr S$:
- the **additive** error $\mathscr A(t)$, defined by $\mathscr S(t)=e^{tH}+\mathscr A(t)$;
- the **multiplicative** error $\mathscr M(t)$, defined by $\mathscr S(t)=e^{tH}(I+\mathscr M(t))$;
- the **exponentiated** error $\mathscr E(\tau)$, defined through the time-ordered exponential $\mathscr S(t)=\expT\big(\int_0^t\mathrm d\tau\,(H+\mathscr E(\tau))\big)$.

The **iterated adjoint** is $\ad_A^q$, the $q$-fold commutator with $A$ ($\ad_A^0 B=B$, $\ad_A^{q+1}B=[A,\ad_A^qB]$), and the **commutator coefficient** attached to a multi-layer conjugation is
$$\alpha_{\mathrm{comm}}^{(p)}(A_s,\dots,A_1,B)=\sum_{q_1+\cdots+q_s=p}\binom{p}{q_1\ \cdots\ q_s}\bigl\|\ad_{A_s}^{q_s}\cdots\ad_{A_1}^{q_1}(B)\bigr\| .$$
The paper also uses the coarser commutator sum $\tilde\alpha_{\mathrm{comm}}=\sum_{\gamma_1,\dots,\gamma_{p+1}}\bigl\|[H_{\gamma_{p+1}},[\cdots,[H_{\gamma_2},H_{\gamma_1}]]]\bigr\|$; note that the formalization keeps these two distinct, as `αCommConj` and `αComm` respectively, whereas the prose overloads the single symbol $\alpha_{\mathrm{comm}}$.

## Formalization targets

### Goal — Theorem 11, commutator scaling of Trotter error

Let $H=\sum_{\gamma=1}^{\Gamma}H_\gamma$, let $t\ge0$, let $\mathscr S$ be a $p$th-order product formula, and let $\tilde\alpha_{\mathrm{comm}}$ be as above. Then
$$\|\mathscr A(t)\|=O\!\Bigl(\tilde\alpha_{\mathrm{comm}}\,t^{p+1}e^{2t\Upsilon\sum_\gamma\|H_\gamma\|}\Bigr),\qquad
\|\mathscr M(t)\|=O\!\Bigl(\tilde\alpha_{\mathrm{comm}}\,t^{p+1}e^{2t\Upsilon\sum_\gamma\|H_\gamma\|}\Bigr),$$
and if every $H_\gamma$ is **anti-Hermitian** the exponential factor disappears:
$$\|\mathscr A(t)\|=O\!\bigl(\tilde\alpha_{\mathrm{comm}}\,t^{p+1}\bigr),\qquad
\|\mathscr M(t)\|=O\!\bigl(\tilde\alpha_{\mathrm{comm}}\,t^{p+1}\bigr).$$

This is the goal because it is the weakest stable statement: it fixes only the shape of the truth. Any improvement to the prefactor changes the constant but not this assertion, whereas a goal carrying hard-coded constants would be invalidated by the next improvement.

### Supporting levels already available

Weaker statements that the goal is assembled from, each of which is a milestone below: the pointwise bounds with explicit constants (Theorem 10 and the norm estimates that follow it), the order-condition equivalence (Theorem 9), the three error representations (Theorem 8), the 1-norm bound (Lemma 6), and the concrete Lie–Trotter and Suzuki prefactors (Propositions 13 and 14). Each is a self-contained target in its own right.

### Open level — Corollary 12, the Trotter number

The paper's Corollary 12 deduces from the goal that $r=O\bigl(\tilde\alpha_{\mathrm{comm}}^{1/p}t^{1+1/p}/\epsilon^{1/p}\bigr)$ steps suffice for accuracy $\epsilon$ when the $H_\gamma$ are anti-Hermitian. **This corollary is not yet formalized** — only its 1-norm analogue (Corollary 7) is. It is the natural first contribution to this mission.

## Significance

*The result itself.* The bound replaces a quantity that grows with the number of Hamiltonian terms by one built from nested commutators. For a geometrically local Hamiltonian the nested commutators of overlapping terms vanish, so $\tilde\alpha_{\mathrm{comm}}$ is asymptotically independent of system size; for power-law and electronic-structure models the same replacement gives strictly better step counts than the 1-norm analysis. Without it, cost estimates for product-formula simulation are pessimistic by a factor that grows with the system, which is exactly the regime that matters.

*Formalizing it.* The paper's argument is a long chain — time-ordered exponentials, an order-condition characterization, a conjugation expansion, a telescoping norm estimate, and a Taylor/integral bookkeeping of multinomial coefficients — in which every constant and every hypothesis is load-bearing. Machine-checking it pins down the quantifier order, the role of completeness and of the normed-algebra structure, the difference between the two commutator coefficients, and the places where the anti-Hermitian hypothesis is what removes the exponential factor; the development also isolates reusable analysis infrastructure (interval integrals, iterated derivatives, multinomial expansions of ordered products, nested-commutator norm estimates) that is independent of the final Trotter statement.

Status, stated plainly: the results above are **proved in the paper** and for the milestones listed, **already formalized** in Lean 4 against Mathlib; the artifacts are linked from each milestone. What this mission adds is the decomposition itself and the unformalized remainder — Corollary 12, the fourth-order small-prefactor bounds (Propositions 29 and 30), the induced-1-norm counting argument for $\tilde\alpha_{\mathrm{comm}}$, and the model-specific application theorems of the appendices. Contributions that formalize those, or that simplify the existing development, are welcome.

## Difficulty

The central difficulty is that the paper's proof obtains its asymptotic bound by a chain of inequalities that must be tracked exactly rather than estimated, and the intermediate objects do not have the form the final statement suggests.

The naive plan — differentiate the product formula $p+1$ times, bound each derivative by the 1-norm, and appeal to Taylor's theorem — is precisely the argument the paper improves on, and it produces the 1-norm scaling, not commutator scaling; it cannot reach the goal. The actual route must first **represent** the error as a sum of nested commutators and only then bound each term, and the representation is not of the original error but of a remainder after cancelling the low-order terms. Cancelling those terms is where the order condition enters, and it is used in an indirect form (an equivalence between four $O(\cdot)$ conditions on four different objects) rather than by differentiating directly, because the direct approach becomes unmanageable at general order.

Two further steps resist casual treatment. The norm bound on the remainder must telescope over the layers of the conjugation, and each layer contributes an exponential factor tied to the norms of the operators *outside* it, so tracking which factors combine into the global $e^{2|\tau|\sum\|A_k\|}$ is delicate. And the scalar coefficient of each summand is a multinomial times a factorial ratio that must be recomputed — not merely bounded — to identify it with $\alpha_{\mathrm{comm}}$; a solver who bounds the coefficient lands on a weaker true statement and may not notice.

## Formalization scope

The development is stated for an abstract **complete normed ring** $\mathbb A$ that is a normed $\mathbb R$-algebra (`NormedRing`, `NormedAlgebra ℝ`, `CompleteSpace`, `NormOneClass`) rather than for matrices or bounded operators on a Hilbert space. This is a strengthening rather than a restriction — the paper's argument never uses anything specific to the spectral norm — so each theorem below implies the paper's statement by instantiating $\mathbb A$ with a matrix algebra. The norm is the abstract algebra norm and results must not be read as spectral-norm statements. The anti-Hermitian branch additionally assumes `StarRing`, `CStarRing`, `Nontrivial`, and `StarModule ℝ`, with the hypothesis stated as $\operatorname{star}(H_\gamma)=-H_\gamma$.

Committed conventions, all of which differ from the prose and are therefore a solver's wasted day if not stated: indices are **zero-based** (`Fin Γ`, `Fin Υ`) where the paper is one-based; products are written **right to left**; the order parameter satisfies $p\ge1$ and the stage count $\Upsilon>0$; boundedness of the coefficients is a hypothesis of the data ($|a_{(\upsilon,\gamma)}|\le1$, exposed as `coeff_abs_le_one`) rather than a side condition; and $\mathscr S$ is `ProductFormulaData.eval`, with `IsOrderOf` encoding the $p$th-order property. The paper's two coefficients are two different Lean objects, `αCommConj` (the multinomial-weighted sum of nested-commutator norms) and `αComm` (the coarser sum over index tuples); statements must say which one they mean.

Unbounded generators, operator domains, closed operators, and infinite-dimensional spectral theory are **out of scope** — the formalization is deliberately algebraic. A statement obtained by instantiating $\mathbb A$ with a trivial algebra, or resting on a hypothesis no interesting instance satisfies, does not count as a formalization of the corresponding paper result.

Definitions and infrastructure a complete development needs: the product-formula data structure and its evaluation, the time-ordered exponential with its Duhamel and interaction-picture lemmas, the order-condition characterization, the conjugation expansion and its remainder, multinomial/factorial identities, and interval-integral and iterated-derivative lemmas. The integral, iterated-derivative, multinomial and ordered-product components are reusable well beyond this mission, and contributions that extract them into standalone reusable lemmas are as valuable as progress on the remaining paper results.

## Selected references

- A. M. Childs, Y. Su, M. C. Tran, N. Wiebe, S. Zhu, *Theory of Trotter Error with Commutator Scaling*, Phys. Rev. X **11**, 011020 (2021); arXiv:1912.08854. <https://arxiv.org/abs/1912.08854>
- S. Chen, K. Marwaha, X. Lu, H. Yuen, T. Peng, *Prove2Me: An Open Collaborative Platform for Scaling Math Formalization* (2026). <https://prove2.me>
- The Lean 4 formalization and Mathlib: <https://github.com/BryceT233/Foresight-Quantum-Formalization-Projects>
- D. Berry, G. Ahokas, R. Cleve, B. C. Sanders, *Efficient quantum algorithms for simulating sparse Hamiltonians*, Comm. Math. Phys. **270**, 359–371 (2007). <https://arxiv.org/abs/quant-ph/0508139>

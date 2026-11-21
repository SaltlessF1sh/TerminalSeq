# Proof of Exact Stabilization Order $\mathrm{Stab}(G_{\kappa,\theta}) = \kappa + \theta$

---

## 0. The Functor $G_{\kappa,\theta}$, Terminal Sequence, and Basic Properties

Let $\kappa, \theta$ be infinite regular cardinals with $\omega \le \theta \le \kappa$, and let $\mathrm{Reg}_{<\theta}$ be the set of infinite regular cardinals $\mu < \theta$. For each $\mu \in \mathrm{Reg}_{<\theta}$ and any set $X$, define the equivalence relation on $X^\mu$ by
$$a \equiv_{<\mu} b \iff \bigl|\{ i < \mu : a(i) \neq b(i) \}\bigr| < \mu.$$
Since $\mu$ is regular, unions of fewer than two sets of cardinality $<\mu$ still have cardinality $<\mu$, so $\equiv_{<\mu}$ is transitive. Define the endofunctor $G_{\kappa,\theta} : \mathbf{Set} \to \mathbf{Set}$ by
$$G_{\kappa,\theta}(X) = \mathcal{P}_{<\kappa}(X) \;\sqcup\; \bigsqcup_{\mu \in \mathrm{Reg}_{<\theta}} \bigl(X^\mu / {\equiv_{<\mu}}\bigr),$$
where $\mathcal{P}_{<\kappa}(X) = \{ S \subseteq X : |S| < \kappa \}$. On a map $h : X \to Y$, $G_{\kappa,\theta}(h)$ acts by direct image $S \mapsto h[S]$ on the left summand and post-composition $(\mu, [a]) \mapsto (\mu, [h \circ a])$ on the right summand. For brevity we write $\mathsf{L}(S)$ and $\mathsf{R}(\mu, [a])$ for the left and right injections into $G_{\kappa,\theta}(X)$.

### Terminal Sequence $(A_\alpha, f_\alpha^\beta)$
By transfinite recursion on $\mathrm{Ord}$, the terminal sequence of $G_{\kappa,\theta}$ satisfies:
- $A_0 = 1 = \{*\}$;
- $A_{\alpha+1} = G_{\kappa,\theta}(A_\alpha)$ with $f_{\alpha+1}^{\beta+1} = G_{\kappa,\theta}(f_\alpha^\beta)$ for $\alpha \le \beta$;
- for limit ordinals $\lambda$, $A_\lambda = \varprojlim_{\alpha < \lambda} A_\alpha = \bigl\{ (x_\alpha)_{\alpha < \lambda} \in \prod_{\alpha<\lambda} A_\alpha \mid \forall \alpha \le \beta < \lambda,\; f_\alpha^\beta(x_\beta) = x_\alpha \bigr\}$ with $f_\alpha^\lambda$ the $\alpha$-th projection.

The transitions satisfy $f_\alpha^\alpha = \mathrm{id}$ and $f_\alpha^\gamma = f_\alpha^\beta \circ f_\beta^\gamma$ ($\alpha \le \beta \le \gamma$). Moreover, $\emptyset \in \mathcal{P}_{<\kappa}(A_0)$ implies $A_1 \neq \emptyset$, hence $A_\alpha \neq \emptyset$ for all $\alpha$. We say $G_{\kappa,\theta}$ **stabilizes at $\gamma$** if $f_\gamma^{\gamma+1}$ is bijective; the least such ordinal is $\mathrm{Stab}(G_{\kappa,\theta})$.

### Proposition 0.1 ($\kappa$-Accessibility and Preservation of Injections)
For infinite regular $\kappa$ and $\theta \le \kappa$:
1. $G_{\kappa,\theta}$ preserves injective maps;
2. $G_{\kappa,\theta}$ is $\kappa$-accessible: for every $X$ and $u \in G_{\kappa,\theta}(X)$, there exists $Y \subseteq X$ with $|Y| < \kappa$ such that $u \in \mathrm{im}\bigl(G_{\kappa,\theta}(\iota_{Y \hookrightarrow X})\bigr)$.

**Proof**:
1. The two summands stay disjoint. If $h$ is injective, then $h[S_1] = h[S_2] \implies S_1 = S_2$, and $\{i : h(a(i)) \neq h(b(i))\} = \{i : a(i) \neq b(i)\}$, so $[h \circ a] = [h \circ b] \implies [a] = [b]$.
2. If $u = \mathsf{L}(S)$, take $Y = S$ ($|S| < \kappa$). If $u = \mathsf{R}(\mu, [a])$ with $\mu < \theta \le \kappa$, take $Y = a[\mu]$ ($|Y| \le \mu < \kappa$). $\blacksquare$

### Proposition 0.2 (Tail Monicity)
For infinite regular $\kappa$ and $\theta \le \kappa$, every tail transition $f_\alpha^\beta : A_\beta \to A_\alpha$ ($\kappa \le \alpha \le \beta$) is injective; in particular, $f_\kappa^{\kappa+1}$ is injective.

**Proof**: If $Y \subseteq A_\kappa$ satisfies $|Y| < \kappa$, each pair $x \neq y \in Y$ is separated by $f_{\alpha(x,y)}^\kappa$ for some $\alpha(x,y) < \kappa$. Since $|Y \times Y| < \kappa$ and $\kappa$ is regular, $\alpha_0 := \sup_{x \neq y \in Y} \alpha(x,y) < \kappa$, so $f_{\alpha_0}^\kappa|_Y$ is injective.

Now suppose $f_\kappa^{\kappa+1}(x) = f_\kappa^{\kappa+1}(y)$ for $x, y \in A_{\kappa+1} = G_{\kappa,\theta}(A_\kappa)$. Pick $<\kappa$-sized supports $Y_x, Y_y \subseteq A_\kappa$ by Proposition 0.1 and set $Y = Y_x \cup Y_y \cup \{a_0\}$ ($0 < |Y| < \kappa$). Take $\alpha < \kappa$ such that $f_\alpha^\kappa|_Y$ is injective. Because $Y \neq \emptyset$, $f_\alpha^\kappa \circ \iota_Y : Y \hookrightarrow A_\alpha$ admits a left inverse $r : A_\alpha \to Y$. Since $G_{\kappa,\theta}(f_\alpha^\kappa)(x) = G_{\kappa,\theta}(f_\alpha^\kappa)(y)$, applying $G_{\kappa,\theta}(r)$ to the preimages on $Y$ yields $x = y$. Transfinite induction (using Proposition 0.1 at successors and limit projections at limits) yields injectivity of $f_\alpha^\beta$ for all $\kappa \le \alpha \le \beta$. $\blacksquare$

---

## Step 1: Non-Surjectivity of $f_\kappa^{\kappa+1}$, Yielding $\mathrm{Stab}(G_{\kappa,\theta}) \ge \kappa$

This step uses only the bounded powerset summand $\mathcal{P}_{<\kappa}$ and regularity of $\kappa$.

### 1.1 Construction of $q_\alpha(\beta)$
By transfinite recursion on $\alpha \le \kappa$, for every $\alpha \le \kappa$ and every ordinal $\beta \in \mathrm{Ord}$, define $q_\alpha(\beta) \in A_\alpha$:
1. **$q_0(\beta) := * \in A_0$**;
2. **Successor ($\alpha = \delta + 1 \le \kappa$)**:
   $$q_{\delta+1}(\beta) := \mathsf{L}\Bigl(\bigl\{ q_\delta(\gamma) \mid \gamma < \min(\beta,\; \delta+1) \bigr\}\Bigr) \in G_{\kappa,\theta}(A_\delta) = A_{\delta+1}$$
   (since $\delta + 1 < \kappa$, the set has cardinality $\le |\delta+1| < \kappa$);
3. **Limit ($l \le \kappa$ limit)**: $q_l(\beta) := \bigl(q_\alpha(\beta)\bigr)_{\alpha < l} \in A_l$.

In a rigorous development, the compatibility of the limit tuples is proved simultaneously with Lemmas 1 and 2 below.

### 1.2 Lemma 1 (Truncation Criterion)
For all $\alpha \le \kappa$ and all ordinals $\beta, \gamma \in \mathrm{Ord}$,
$$q_\alpha(\beta) = q_\alpha(\gamma) \iff \min(\alpha, \beta) = \min(\alpha, \gamma).$$

**Proof** (transfinite induction on $\alpha$):
- **Base ($\alpha = 0$)**: $q_0(\beta) = * = q_0(\gamma)$ and $\min(0, \beta) = 0 = \min(0, \gamma)$.
- **Successor ($\alpha = \delta + 1$)**: We have
  $$q_{\delta+1}(\beta) = q_{\delta+1}(\gamma) \iff \{q_\delta(i) \mid i < \min(\beta, \delta+1)\} = \{q_\delta(i) \mid i < \min(\gamma, \delta+1)\}.$$
  For all $i, j < \delta + 1$ (so $i, j \le \delta$), the induction hypothesis gives $q_\delta(i) = q_\delta(j) \iff \min(\delta, i) = \min(\delta, j) \iff i = j$. Thus $i \mapsto q_\delta(i)$ is injective on $\{i : i < \delta + 1\}$, so equality of the sets is equivalent to equality of the index bounds $\min(\beta, \delta+1) = \min(\gamma, \delta+1)$.
- **Limit ($l$ limit)**:
  $$q_l(\beta) = q_l(\gamma) \iff \forall \alpha < l,\; q_\alpha(\beta) = q_\alpha(\gamma) \iff \forall \alpha < l,\; \min(\alpha, \beta) = \min(\alpha, \gamma).$$
  - ($\Leftarrow$) Immediate since $\min(\alpha, \beta) = \min(\alpha, \min(l, \beta))$ for $\alpha < l$.
  - ($\Rightarrow$) Suppose toward contradiction that $\mu := \min(l, \beta) < \min(l, \gamma) \le l$. Since $\mu < l$ and $l$ is a limit ordinal, $\mu + 1 < l$. Taking $\alpha = \mu + 1$ yields $\min(\mu+1, \beta) = \beta = \mu$ whereas $\min(\mu+1, \gamma) = \mu + 1$, contradiction. $\blacksquare$

### 1.3 Lemma 2 (Projection Compatibility)
For all $\alpha \le \eta \le \kappa$ and every $\beta \in \mathrm{Ord}$, $f_\alpha^\eta\bigl(q_\eta(\beta)\bigr) = q_\alpha(\beta)$.

**Proof** (transfinite induction on $\eta$):
For $\alpha = \eta$ this is trivial. For $\alpha < \eta$:
- **Successor ($\eta = \xi + 1$)**: By induction it suffices to check $f_\xi^{\xi+1}\bigl(q_{\xi+1}(\beta)\bigr) = q_\xi(\beta)$:
  1. **$\xi = 0$**: Trivial since $|A_0| = 1$.
  2. **$\xi = \delta + 1$**: Here $f_{\delta+1}^{\delta+2} = G_{\kappa,\theta}(f_\delta^{\delta+1})$, so by the induction hypothesis,
     $$f_{\delta+1}^{\delta+2}(q_{\delta+2}(\beta)) = \mathsf{L}\Bigl(\bigl\{ q_\delta(i) \mid i < \min(\beta, \delta+2) \bigr\}\Bigr).$$
     Since $q_\delta(\delta+1) = q_\delta(\delta)$ by Lemma 1, the image set coincides with $\{q_\delta(i) \mid i < \min(\beta, \delta+1)\}$, which defines $q_{\delta+1}(\beta)$.
  3. **$\xi$ limit**: For any $\alpha < \xi$, we have $\alpha + 1 < \xi$, and $f_\alpha^\xi \circ f_\xi^{\xi+1} = f_\alpha^{\alpha+1} \circ G_{\kappa,\theta}(f_\alpha^\xi)$. By the induction hypothesis,
     $$f_\alpha^\xi\bigl(f_\xi^{\xi+1}(q_{\xi+1}(\beta))\bigr) = f_\alpha^{\alpha+1}\Bigl(\mathsf{L}\bigl\{ q_\alpha(i) \mid i < \min(\beta, \xi+1) \bigr\}\Bigr).$$
     By Lemma 1, $q_\alpha(i) = q_\alpha(\alpha)$ for all $i \ge \alpha + 1$, so the set inside equals $\{q_\alpha(i) \mid i < \min(\beta, \alpha+1)\}$, giving $f_\alpha^{\alpha+1}(q_{\alpha+1}(\beta)) = q_\alpha(\beta)$.
- **Limit ($\eta$ limit)**: By definition of the limit projection, $f_\alpha^\eta(q_\eta(\beta)) = q_\alpha(\beta)$ for every $\alpha < \eta$. $\blacksquare$

### 1.4 Non-Surjectivity at Stage $\kappa$
Set $b_\kappa := q_\kappa(\kappa) \in A_\kappa$. Suppose $f_\kappa^{\kappa+1}(x) = b_\kappa$ for some $x \in A_{\kappa+1}$:
- If $x = \mathsf{R}(\mu, [a])$, projecting to stage $1$ gives $\mathsf{R}(\mu, [f_0^\kappa \circ a]) = f_1^\kappa(b_\kappa) = q_1(\kappa) = \mathsf{L}(\{*\})$ by Lemma 2, contradiction.
- If $x = \mathsf{L}(S)$ with $S \subseteq A_\kappa$ and $|S| < \kappa$:
  1. For each fixed $s \in A_\kappa$, at most one $\gamma < \kappa$ can satisfy $f_{\gamma+1}^\kappa(s) = q_{\gamma+1}(\gamma)$: if $\gamma_1 < \gamma_2 < \kappa$ both satisfied this, projecting via $f_{\gamma_1+1}^{\gamma_2+1}$ and Lemma 2 would give $q_{\gamma_1+1}(\gamma_1) = q_{\gamma_1+1}(\gamma_2)$, forcing $\gamma_1 = \gamma_1 + 1$ by Lemma 1.
  2. Since $|S| < \kappa$ and $\kappa$ is regular, taking the unique hit index $\gamma_s < \kappa$ for each $s \in S$ (or $0$ if none exists) gives $\alpha := \bigl(\sup_{s \in S} \gamma_s\bigr) + 1 < \kappa$, so no $s \in S$ satisfies $f_{\alpha+1}^\kappa(s) = q_{\alpha+1}(\alpha)$.
  3. On the other hand, projecting $f_\kappa^{\kappa+1}(\mathsf{L}(S)) = q_\kappa(\kappa)$ to stage $\alpha + 2 < \kappa$ yields $f_{\alpha+1}^\kappa[S] = \{ q_{\alpha+1}(i) \mid i < \alpha + 2 \}$, which contains $q_{\alpha+1}(\alpha)$ — contradiction.

Hence $f_\kappa^{\kappa+1}$ is not surjective, and by upward persistence of stabilization, no $\delta < \kappa$ can stabilize. $\blacksquare$

---

## Step 2: Rank Filtration $(B_\beta)$, Pruning Rank, and $\mathrm{Stab}(G_{\kappa,\theta}) = \kappa + \theta$

Since $f_\alpha^\beta$ is injective for all $\kappa \le \alpha \le \beta$, define the descending filtration on $A_\kappa$:
$$B_0 = A_\kappa, \qquad B_\beta := \mathrm{im}\bigl(f_\kappa^{\kappa+\beta} : A_{\kappa+\beta} \to A_\kappa\bigr) \subseteq A_\kappa \qquad (\beta \in \mathrm{Ord}).$$
For $U \subseteq A_\kappa$, write $H(U) \subseteq G_{\kappa,\theta}(A_\kappa)$ for the elements supported in $U$: $\mathsf{L}(S) \in H(U) \iff S \subseteq U$, and $\mathsf{R}(\mu, [a]) \in H(U) \iff \bigl|\{i < \mu : a(i) \notin U\}\bigr| < \mu$.

### 2.1 Lemma 3 (Basic Properties and Recursion of $B_\beta$)
1. $\beta_1 \le \beta_2 \implies B_{\beta_2} \subseteq B_{\beta_1}$, and each $B_\beta$ is nonempty.
2. **Successor**: $B_{\beta+1} = f_\kappa^{\kappa+1}[H(B_\beta)]$.
3. **Limit**: For every limit ordinal $l$, $B_l = \bigcap_{\beta < l} B_\beta$.
4. $f_{\kappa+\beta}^{\kappa+\beta+1}$ is surjective iff $B_{\beta+1} = B_\beta$.

**Proof**:
1. From $f_\kappa^{\kappa+\beta_2} = f_\kappa^{\kappa+\beta_1} \circ f_{\kappa+\beta_1}^{\kappa+\beta_2}$ and $A_{\kappa+\beta} \neq \emptyset$.
2. Because $f_{\kappa+1}^{\kappa+\beta+1} = G_{\kappa,\theta}(f_\kappa^{\kappa+\beta})$ and $f_\kappa^{\kappa+\beta} : A_{\kappa+\beta} \xrightarrow{\sim} B_\beta$, $\mathrm{im}(f_{\kappa+1}^{\kappa+\beta+1}) = H(B_\beta)$; composing with $f_\kappa^{\kappa+1}$ yields $B_{\beta+1} = f_\kappa^{\kappa+1}[H(B_\beta)]$.
3. Only ($\supseteq$) is non-trivial. Let $c \in \bigcap_{\beta < l} B_\beta$ and pick $x_\beta \in A_{\kappa+\beta}$ with $f_\kappa^{\kappa+\beta}(x_\beta) = c$ for each $\beta < l$. For any $\beta \le \gamma < l$, $f_\kappa^{\kappa+\beta}\bigl(f_{\kappa+\beta}^{\kappa+\gamma}(x_\gamma)\bigr) = f_\kappa^{\kappa+\gamma}(x_\gamma) = c = f_\kappa^{\kappa+\beta}(x_\beta)$; injectivity of $f_\kappa^{\kappa+\beta}$ automatically forces $f_{\kappa+\beta}^{\kappa+\gamma}(x_\gamma) = x_\beta$. Thus $(x_\beta)_{\beta < l}$ extends to a compatible cone element $x \in A_{\kappa+l}$ with $f_\kappa^{\kappa+l}(x) = c \in B_l$.
4. Immediate from injectivity of $f_\kappa^{\kappa+\beta}$. $\blacksquare$

### 2.2 Pruning Rank $\rho$, Delay Operators $\sigma, \tau_\mu$, and Rank Realization
For $x \in B_0$, write $\rho(x) = \beta$ when $x \in B_\beta \setminus B_{\beta+1}$. By Lemma 3(4), $\exists x,\; \rho(x) = \beta \iff B_{\beta+1} \subsetneq B_\beta \iff f_{\kappa+\beta}^{\kappa+\beta+1}$ is not surjective.

Define the delay operators on $A_\kappa$:
$$\sigma(x) := f_\kappa^{\kappa+1}\bigl(\mathsf{L}(\{x\})\bigr), \qquad \tau_\mu(a) := f_\kappa^{\kappa+1}\bigl(\mathsf{R}(\mu, [a])\bigr) \quad (\mu \in \mathrm{Reg}_{<\theta},\; a : \mu \to A_\kappa).$$

#### Lemma 4 (Membership Criteria)
For every ordinal $\beta$:
1. $\sigma(x) \in B_{\beta+1} \iff x \in B_\beta$;
2. $\tau_\mu(a) \in B_{\beta+1} \iff \bigl|\{i < \mu : a(i) \notin B_\beta\}\bigr| < \mu$.

**Proof**: Immediate from $B_{\beta+1} = f_\kappa^{\kappa+1}[H(B_\beta)]$ and injectivity of $f_\kappa^{\kappa+1}$. $\blacksquare$

Consequently:
- If $\rho(x) = \alpha$, then $\rho(\sigma(x)) = \alpha + 1$.
- If $l < \theta$ is a limit ordinal, let $\mu := \mathrm{cof}(l) \in \mathrm{Reg}_{<\theta}$ ($\mu \le |l| < \theta$) and choose a strictly increasing cofinal sequence $(c_j)_{j<\mu}$ in $l$. If $\rho(x_{c_j}) = c_j$ for all $j < \mu$, then $x_l := \tau_\mu\bigl((x_{c_j})_{j<\mu}\bigr)$ satisfies $\rho(x_l) = l$:
  1. For each $\beta < l$, some $i_0 < \mu$ satisfies $j \ge i_0 \implies c_j \ge \beta \implies x_{c_j} \in B_\beta$, so $\{j < \mu : x_{c_j} \notin B_\beta\} \subseteq i_0$ has cardinality $<\mu$; hence $x_l \in \bigcap_{\beta<l} B_{\beta+1} = B_l$.
  2. For every $j < \mu$, $c_j + 1 < l$ implies $x_{c_j} \notin B_{c_j+1} \supseteq B_l$, so $\{j < \mu : x_{c_j} \notin B_l\} = \mu$ has cardinality $\ge \mu$; hence $x_l \notin B_{l+1}$.

By transfinite induction starting from $x_0 := b_\kappa \in B_0 \setminus B_1$ (Step 1), every rank $\alpha < \theta$ is realized by some $x_\alpha \in B_\alpha \setminus B_{\alpha+1}$. Hence $G_{\kappa,\theta}$ cannot stabilize at any $\delta < \kappa + \theta$. $\blacksquare$

### 2.3 Regularity Closure at $\theta$ and Exact Stabilization

#### Lemma 5 (Stabilization of Small Sets Along $(B_\beta)$)
If $S \subseteq A_\kappa$ satisfies $|S| < \theta$, then there exists $\beta_* < \theta$ such that $S \cap B_{\beta_*} = S \cap B_\theta$.

**Proof**: For each $s \in S \setminus B_\theta$, pick $\gamma_s < \theta$ with $s \notin B_{\gamma_s}$ (using $B_\theta = \bigcap_{\gamma<\theta} B_\gamma$), and set $\gamma_s = 0$ for $s \in S \cap B_\theta$. Since $|S| < \theta$ and $\theta$ is regular, $\beta_* := \sup_{s \in S} \gamma_s < \theta$, giving $S \cap B_{\beta_*} = S \cap B_\theta$. $\blacksquare$

#### Theorem ($\theta$-Closure and Exact Stabilization)
$B_{\theta+1} = B_\theta$, and therefore $\mathrm{Stab}(G_{\kappa,\theta}) = \kappa + \theta$.

**Proof**: Let $x \in B_\theta$. Then $x \in B_1 = \mathrm{im}(f_\kappa^{\kappa+1})$, so $x = f_\kappa^{\kappa+1}(u)$ for a unique $u \in G_{\kappa,\theta}(A_\kappa)$, and injectivity of $f_\kappa^{\kappa+1}$ ensures $u \in H(B_\beta)$ for every $\beta < \theta$.
- **If $u = \mathsf{L}(S)$**: then $S \subseteq \bigcap_{\beta < \theta} B_\beta = B_\theta$, so $u \in H(B_\theta)$.
- **If $u = \mathsf{R}(\mu, [a])$** ($\mu < \theta$): put $S = \mathrm{im}(a) \subseteq A_\kappa$ ($|S| \le \mu < \theta$). By Lemma 5, choose $\beta_* < \theta$ with $S \cap B_{\beta_*} = S \cap B_\theta$. Then $\{i < \mu : a(i) \notin B_\theta\} = \{i < \mu : a(i) \notin B_{\beta_*}\}$ has cardinality $< \mu$ since $u \in H(B_{\beta_*})$, so $u \in H(B_\theta)$.

Hence $x = f_\kappa^{\kappa+1}(u) \in B_{\theta+1}$, so $B_{\theta+1} = B_\theta$. By Lemma 3(4) and Proposition 0.2, $f_{\kappa+\theta}^{\kappa+\theta+1}$ is bijective, while no $\delta < \kappa + \theta$ stabilizes. Thus $\mathrm{Stab}(G_{\kappa,\theta}) = \kappa + \theta$. $\blacksquare$

---

## 3. Specialization to $\kappa = \theta = \aleph_1$

When $\kappa = \theta = \aleph_1$, the unique infinite regular cardinal strictly below $\aleph_1$ is $\aleph_0$, so
$$G_{\aleph_1, \aleph_1}(X) = \mathcal{P}_{<\omega_1}(X) \;\sqcup\; \bigl(X^\omega / {\equiv_{\mathrm{fin}}}\bigr),$$
and the theorem yields $\mathrm{Stab}(G_{\aleph_1, \aleph_1}) = \omega_1 + \omega_1 = \omega_1 \cdot 2$.

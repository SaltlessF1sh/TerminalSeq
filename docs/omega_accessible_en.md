# Stabilization Points of $\omega$-Accessible Set Functors: $\operatorname{Stab}(F) \in \{0, 1, \omega, \omega + \omega\}$

---

## 0. Preliminaries

Let $F : \mathbf{Set} \to \mathbf{Set}$ be an endofunctor. Its terminal sequence $(A_\alpha, f_\alpha^\beta : A_\beta \to A_\alpha)_{\alpha \le \beta}$ is defined by transfinite recursion:
- $A_0 = 1$ (singleton set);
- $A_{\alpha+1} = F(A_\alpha)$ and $f_{\alpha+1}^{\beta+1} = F(f_\alpha^\beta)$;
- for limit ordinals $\lambda$, $A_\lambda = \varprojlim_{\alpha < \lambda} A_\alpha$ is the limit of compatible families, with projections $f_\alpha^\lambda$.

We say $F$ **stabilizes at $\gamma$** if $p_\gamma := f_\gamma^{\gamma+1} : A_{\gamma+1} \to A_\gamma$ is bijective (which then persists to all $\delta \ge \gamma$); the least stabilizing ordinal is $\operatorname{Stab}(F)$.

$F$ is **$\omega$-accessible** (finitary) if for every set $X$ and every $u \in F(X)$, there is a finite subset $S \subseteq X$ with $u \in \operatorname{im}(F(i_S))$, where $i_S : S \hookrightarrow X$ is the inclusion. For $z_0 \in X$, we also write $i_{\{z_0\}} : 1 \to X$ for the constant map $* \mapsto z_0$.

---

## 1. Four Basic Lemmas

### Lemma 1.1 (Trnková)
> Let $F : \mathbf{Set} \to \mathbf{Set}$ and $A, B \subseteq X$. If $A \cap B \neq \emptyset$, then
> $$\operatorname{im}(F(i_A)) \cap \operatorname{im}(F(i_B)) = \operatorname{im}(F(i_{A \cap B})).$$

**Proof**:
($\supseteq$) Immediate from $i_{A \cap B} = i_A \circ i_{A\cap B \hookrightarrow A} = i_B \circ i_{A\cap B \hookrightarrow B}$.
($\subseteq$) Pick $c \in A \cap B$ and define retractions $e_A, e_B : X \to X$ by
$$e_A(x) = \begin{cases} x, & x \in A, \\ c, & x \notin A, \end{cases} \qquad e_B(x) = \begin{cases} x, & x \in B, \\ c, & x \notin B. \end{cases}$$
Then $e_A \circ i_A = i_A$, $e_B \circ i_B = i_B$, and $e_A \circ e_B = i_{A \cap B} \circ q$ for the map $q : X \to A \cap B$ sending $X \setminus (A \cap B)$ to $c$. If $t \in \operatorname{im}(F(i_A)) \cap \operatorname{im}(F(i_B))$, writing $t = F(i_A)(u_A) = F(i_B)(u_B)$ gives $F(e_A)(t) = t$ and $F(e_B)(t) = t$. Hence
$$t = F(e_A)(F(e_B)(t)) = F(e_A \circ e_B)(t) = F(i_{A \cap B})(F(q)(t)) \in \operatorname{im}(F(i_{A \cap B})). \quad \square$$

---

### Lemma 1.2
> Let $F : \mathbf{Set} \to \mathbf{Set}$ and $A, B \subseteq X$ be disjoint ($A \cap B = \emptyset$). If $x \in \operatorname{im}(F(i_A)) \cap \operatorname{im}(F(i_B))$, then for every $z_0 \in X$, $x \in \operatorname{im}(F(i_{\{z_0\}}))$.

**Proof**:
Fix $z_0 \in X$ and define $f : X \to X$ by $f(y) = z_0$ for $y \in A$ and $f(y) = y$ for $y \notin A$.
1. Since $A \cap B = \emptyset$, $f \circ i_B = i_B$, so $x \in \operatorname{im}(F(i_B))$ implies $F(f)(x) = x$.
2. Meanwhile $f \circ i_A = i_{\{z_0\}} \circ {!}_A$ where ${!}_A : A \to 1$. Writing $x = F(i_A)(a)$ gives
   $$x = F(f)(x) = F(f \circ i_A)(a) = F(i_{\{z_0\}})\bigl(F({!}_A)(a)\bigr) \in \operatorname{im}(F(i_{\{z_0\}})). \quad \square$$

---

### Lemma 1.3
> Let $F : \mathbf{Set} \to \mathbf{Set}$. Suppose there exist a set $X$ and maps $q : X \to A_1$, $s : A_1 \to X$ with $q \circ s = \mathrm{id}_{A_1}$, and suppose $F({!}_X) : F(X) \to F(1)$ is bijective. Then $p_1 : F(A_1) \to A_1$ is bijective, so $\operatorname{Stab}(F) \le 1$.

**Proof**:
From $q \circ s = \mathrm{id}_{A_1}$ we get $F(q) \circ F(s) = \mathrm{id}_{F(A_1)}$, so $F(s)$ is injective. Also ${!}_X \circ s = {!}_1$ and ${!}_1 \circ q = {!}_X$.
- Since $F(!_X) = F(!_1) \circ F(q)$ is surjective, $F(!_1)$ is surjective;
- Since $F(!_1) = F(!_X) \circ F(s)$ is a composite of injections, $F(!_1)$ is injective.

Thus $F(!_1) : F(A_1) \to F(1)$ is bijective, which identifies with $p_1 : A_2 \to A_1$ via $A_1 \cong F(1)$. $\square$

---

### Lemma 1.4
> If $A_1 = F(1) \neq \emptyset$, then for every ordinal $\alpha \ge 1$ there exists a section $s_\alpha : A_1 \to A_\alpha$ such that $f_1^\alpha \circ s_\alpha = \mathrm{id}_{A_1}$. In particular, $|A_\alpha| \ge |A_1|$ and every $A_\alpha \neq \emptyset$.

**Proof**:
Each $c \in F(1) = A_1$ defines a constant coalgebra $1 \xrightarrow{c} F(1)$, which generates by transfinite recursion a unique compatible family of elements $s_\alpha(c) \in A_\alpha$ pushed forward via constant maps $1 \to A_\delta$ at successor stages and projection limits at limit stages, satisfying $f_1^\alpha(s_\alpha(c)) = c$ (Worrell 2005). Hence $s_\alpha$ is injective and $|A_\alpha| \ge |A_1|$. $\square$

---

## 2. Excluding Non-Trivial Successor Convergence Points

### Proposition 2.1
> Let $F : \mathbf{Set} \to \mathbf{Set}$ be $\omega$-accessible and $|X| \ge 2$. If there exists a proper subset $T \subsetneq X$ such that $F(i_T) : F(T) \to F(X)$ is surjective, then for every $z \in X$, both $F(i_{\{z\}}) : F(1) \xrightarrow{\sim} F(X)$ and $F({!}_X) : F(X) \xrightarrow{\sim} F(1)$ are bijective.

**Proof**:
- **Step 1**: Choose $g \in X \setminus T$. Since $T \subseteq X \setminus \{g\}$, surjectivity of $F(i_T)$ makes $F(i_{X\setminus\{g\}})$ surjective. Conjugating by the swap bijection $(g\; b) : X \xrightarrow{\sim} X$ shows $F(i_{X\setminus\{b\}})$ is surjective for every $b \in X$.
- **Step 2**: Fix $z \in X$ and $x \in F(X)$; we show $x \in \operatorname{im}(F(i_{\{z\}}))$:
  - **Case 1 ($|X| = M$ finite, $M \ge 2$)**: Since $\{z\} = \bigcap_{b \in X \setminus \{z\}} (X \setminus \{b\})$ with every finite sub-intersection containing $z$, repeated **Lemma 1.1** yields $\operatorname{im}(F(i_{\{z\}})) = \bigcap_{b \neq z} \operatorname{im}(F(i_{X\setminus\{b\}})) = F(X)$.
  - **Case 2 ($|X|$ infinite)**: Pick a finite support $B_0 \subseteq X$ for $x$ by $\omega$-accessibility. If $B_0 = \emptyset$, then $\emptyset \hookrightarrow X$ factors through $i_{\{z\}}$, so $x \in \operatorname{im}(F(i_{\{z\}}))$. If $B_0 \neq \emptyset$, then $X \setminus B_0 = \bigcap_{b \in B_0} (X \setminus \{b\})$ is infinite (hence nonempty); iterated **Lemma 1.1** over the finite set $B_0$ gives $x \in \operatorname{im}(F(i_{X \setminus B_0}))$, and **Lemma 1.2** yields $x \in \operatorname{im}(F(i_{\{z\}}))$.
- **Step 3**: From $1 \xrightarrow{i_{\{z\}}} X \xrightarrow{{!}_X} 1$ we have $F({!}_X) \circ F(i_{\{z\}}) = \mathrm{id}_{F(1)}$. Together with Step 2 (surjectivity of $F(i_{\{z\}})$), $F(i_{\{z\}})$ is bijective, and therefore so is its inverse $F({!}_X)$. $\square$

---

### Theorem 2.2
> Let $F : \mathbf{Set} \to \mathbf{Set}$ be $\omega$-accessible. Then $\operatorname{Stab}(F) \neq \alpha + 1$ for every ordinal $\alpha \ge 1$.

**Proof**:
Suppose toward contradiction that $\operatorname{Stab}(F) = \alpha + 1$ with $\alpha \ge 1$.
- If $A_1 = \emptyset$, existence of $A_2 \to A_1 = \emptyset$ forces $A_2 = \emptyset$, so $p_1 : \emptyset \to \emptyset$ is bijective while $p_0 : \emptyset \to 1$ is not, yielding $\operatorname{Stab}(F) = 1$, impossible.
- If $|A_1| = 1$, $p_0 : A_1 \to A_0$ is already bijective, yielding $\operatorname{Stab}(F) = 0$, impossible.

Hence $|A_1| \ge 2$, and by **Lemma 1.4**, $|A_\delta| \ge |A_1| \ge 2$ for every $\delta \ge 1$.

Because $\operatorname{Stab}(F) = \alpha + 1$, $p_{\alpha+1} = F(p_\alpha)$ is bijective while $p_\alpha : A_{\alpha+1} \to A_\alpha$ is not bijective.
- **Case 1 ($p_\alpha$ not surjective)**: Set $T := \operatorname{im}(p_\alpha) \subsetneq A_\alpha$. Factoring $p_\alpha = i_T \circ q$, surjectivity of $F(p_\alpha)$ gives surjectivity of $F(i_T)$. Since $|A_\alpha| \ge 2$, **Proposition 2.1** on $X = A_\alpha$ gives $F(A_\alpha) \cong F(1)$, and **Lemma 1.3** + **Lemma 1.4** yield $\operatorname{Stab}(F) \le 1$, contradicting $\alpha + 1 > 1$.
- **Case 2 ($p_\alpha$ surjective, not injective)**: Choose $y_0 \in A_\alpha$ and $x_1 \neq x_2 \in A_{\alpha+1}$ with $p_\alpha(x_1) = p_\alpha(x_2) = y_0$. Take a right inverse $\sigma_0$ of $p_\alpha$ and define sections $\sigma_1, \sigma_2 : A_\alpha \to A_{\alpha+1}$ differing only at $y_0$, with $\sigma_k(y_0) = x_k$. Since $p_\alpha \circ \sigma_k = \mathrm{id}_{A_\alpha}$ and $F(p_\alpha) = p_{\alpha+1}$ is bijective, $F(\sigma_1) = F(\sigma_2) = p_{\alpha+1}^{-1}$ are bijective. Let $T_0 := \sigma_1(A_\alpha \setminus \{y_0\})$ and $S_k := \operatorname{im}(\sigma_k) = T_0 \cup \{x_k\}$. Because $|A_\alpha| \ge 2$, $T_0 \neq \emptyset$; since $x_1 \notin T_0$, $T_0 \subsetneq A_{\alpha+1}$ and $S_1 \cap S_2 = T_0$. Surjectivity of $F(\sigma_k)$ implies surjectivity of $F(i_{S_k})$, and **Lemma 1.1** yields surjectivity of $F(i_{T_0})$. Applying **Proposition 2.1** to $X = A_{\alpha+1}$ and $T_0$, then **Lemma 1.3** + **Lemma 1.4**, again yields $\operatorname{Stab}(F) \le 1$, contradiction. $\square$

---

## 3. Worrell's Upper Bound and the 4-Point Classification

### Theorem 3.1 (Worrell's Upper Bound)
> Every $\omega$-accessible set functor $F : \mathbf{Set} \to \mathbf{Set}$ stabilizes by $\omega + \omega$.

**Proof**:
If $A_1 = \emptyset$, $F$ stabilizes at $1 \le \omega + \omega$. Otherwise all $A_\alpha$ are nonempty by **Lemma 1.4**, and $\omega$-accessibility implies tail monicity: $f_\alpha^\beta : A_\beta \to A_\alpha$ is injective for all $\omega \le \alpha \le \beta$. In particular, $p_{\omega+\omega}$ is injective.

To show $p_{\omega+\omega}$ is surjective, let $y \in A_{\omega+\omega}$ and put $y_1 := f_{\omega+1}^{\omega+\omega}(y) \in A_{\omega+1} = F(A_\omega)$. For every $k \in \mathbb{N}$, naturality gives $y_1 = F(f_\omega^{\omega+k})\bigl(f_{\omega+k+1}^{\omega+\omega}(y)\bigr) \in \operatorname{im}(F(i_{C_k}))$, where $C_k := \operatorname{im}(f_\omega^{\omega+k}) \subseteq A_\omega$ forms a descending chain. By injectivity of each $f_\omega^{\omega+k}$, any element of $\bigcap_{k \in \mathbb{N}} C_k$ lifts coherently to $A_{\omega+\omega}$, so $\bigcap_{k \in \mathbb{N}} C_k = C_\omega := \operatorname{im}(f_\omega^{\omega+\omega})$.

By $\omega$-accessibility, pick a finite support $S \subseteq A_\omega$ for $y_1$. Choosing $N \in \mathbb{N}$ above the first exit index of every $s \in S \setminus C_\omega$ ensures $S \cap C_N \subseteq C_\omega$. Either $S \cap C_N \neq \emptyset$ (**Lemma 1.1**) or $S \cap C_N = \emptyset$ (**Lemma 1.2** with $z_0 = f_\omega^{\omega+\omega}(y) \in C_\omega$); in both cases $y_1 \in \operatorname{im}(F(i_{C_\omega}))$. Inverting the bijection $A_{\omega+\omega} \xrightarrow{\sim} C_\omega$ gives $x \in F(A_{\omega+\omega}) = A_{\omega+\omega+1}$ with $f_{\omega+1}^{\omega+\omega+1}(x) = y_1 = f_{\omega+1}^{\omega+\omega}(y)$. Finally, injectivity of $f_{\omega+1}^{\omega+k+1}$ forces $f_{\omega+k+1}^{\omega+\omega+1}(x) = f_{\omega+k+1}^{\omega+\omega}(y)$ for every $k \in \mathbb{N}$, hence $x$ and $y$ agree on all coordinates $< \omega + \omega$, giving $p_{\omega+\omega}(x) = y$. $\square$

---

### Theorem 3.2 (Four-Point Convergence Classification)
> Every $\omega$-accessible set functor $F : \mathbf{Set} \to \mathbf{Set}$ has a unique exact stabilization ordinal $\operatorname{Stab}(F)$, and
> $$\operatorname{Stab}(F) \in \{0,\; 1,\; \omega,\; \omega + \omega\}.$$

**Proof**:
By **Theorem 3.1**, $\gamma := \operatorname{Stab}(F) \le \omega + \omega$. **Theorem 2.2** rules out all finite ordinals $n \ge 2$ and all ordinals $\omega + (n + 1)$ ($n \in \mathbb{N}$) strictly between $\omega$ and $\omega + \omega$, leaving precisely $\{0, 1, \omega, \omega + \omega\}$. $\square$

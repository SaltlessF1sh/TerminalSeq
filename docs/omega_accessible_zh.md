# $\omega$-可达集合函子的收敛点分类：$\operatorname{Stab}(F) \in \{0, 1, \omega, \omega + \omega\}$

---

## 0. 预备定义

设 $F : \mathbf{Set} \to \mathbf{Set}$ 为集合范畴上的端函子。其终端序列（final sequence）$(A_\alpha, f_\alpha^\beta : A_\beta \to A_\alpha)_{\alpha \le \beta}$ 按超限递归定义为：
- $A_0 = 1$（单点集）；
- $A_{\alpha+1} = F(A_\alpha)$，$f_{\alpha+1}^{\beta+1} = F(f_\alpha^\beta)$；
- 对极限序数 $\lambda$，$A_\lambda = \varprojlim_{\alpha < \lambda} A_\alpha$ 为相容圆锥的极限，$f_\alpha^\lambda$ 为标准投影。

若 $p_\gamma := f_\gamma^{\gamma+1} : A_{\gamma+1} \to A_\gamma$ 为双射，则称 $F$ 在 $\gamma$ 处**稳定**（由超限归纳，稳定性质对一切 $\delta \ge \gamma$ 向上保持）。使之稳定的最小序数称为 $F$ 的精确收敛序数，记作 $\operatorname{Stab}(F)$。

称 $F$ 是 **$\omega$-可达的**（$\omega$-accessible / finitary），若对任意集合 $X$ 与 $u \in F(X)$，存在有限子集 $S \subseteq X$，使得 $u \in \operatorname{im}(F(i_S))$，其中 $i_S : S \hookrightarrow X$ 为包含映射。对单点 $z_0 \in X$，亦将常值映射 $1 \to X$（$* \mapsto z_0$）记作 $i_{\{z_0\}}$。

---

## 1. 四个基本引理

### Lemma 1.1（Trnková）
> 设 $F : \mathbf{Set} \to \mathbf{Set}$，$A, B \subseteq X$。若 $A \cap B \neq \emptyset$，则
> $$\operatorname{im}(F(i_A)) \cap \operatorname{im}(F(i_B)) = \operatorname{im}(F(i_{A \cap B})).$$

**证明**：
- **($\supseteq$)** 由于 $A \cap B \subseteq A$ 且 $A \cap B \subseteq B$，有 $F(i_{A \cap B}) = F(i_A) \circ F(i_{A\cap B \hookrightarrow A}) = F(i_B) \circ F(i_{A\cap B \hookrightarrow B})$，故 $\operatorname{im}(F(i_{A \cap B})) \subseteq \operatorname{im}(F(i_A)) \cap \operatorname{im}(F(i_B))$。
- **($\subseteq$)** 任取 $c \in A \cap B$，定义两个收缩自映射 $e_A, e_B : X \to X$：
  $$e_A(x) = \begin{cases} x, & x \in A, \\ c, & x \notin A, \end{cases} \qquad e_B(x) = \begin{cases} x, & x \in B, \\ c, & x \notin B. \end{cases}$$
  则 $e_A \circ i_A = i_A$，$e_B \circ i_B = i_B$，且复合映射满足
  $$e_A \circ e_B(x) = \begin{cases} x, & x \in A \cap B, \\ c, & \text{其余}, \end{cases}$$
  从而存在收缩投影 $q : X \to A \cap B$ 使得 $e_A \circ e_B = i_{A \cap B} \circ q$。

  任取 $t \in \operatorname{im}(F(i_A)) \cap \operatorname{im}(F(i_B))$，记 $t = F(i_A)(u_A) = F(i_B)(u_B)$。则
  $$F(e_A)(t) = F(e_A \circ i_A)(u_A) = t, \qquad F(e_B)(t) = F(e_B \circ i_B)(u_B) = t.$$
  因此
  $$t = F(e_A)\bigl(F(e_B)(t)\bigr) = F(e_A \circ e_B)(t) = F(i_{A \cap B})\bigl(F(q)(t)\bigr) \in \operatorname{im}(F(i_{A \cap B})).\quad \square$$

---

### Lemma 1.2
> 设 $F : \mathbf{Set} \to \mathbf{Set}$，$A, B \subseteq X$ 满足 $A \cap B = \emptyset$。若存在 $x \in \operatorname{im}(F(i_A)) \cap \operatorname{im}(F(i_B))$，则对任意 $z_0 \in X$，$x$ 可被 $z_0$ 支撑，即 $x \in \operatorname{im}(F(i_{\{z_0\}}))$。

**证明**：
任取 $z_0 \in X$，定义映射 $f : X \to X$：
$$f(y) = \begin{cases} z_0, & y \in A, \\ y, & y \notin A. \end{cases}$$
1. 由于 $A \cap B = \emptyset$，在 $B$ 上 $f$ 与恒等映射相同，即 $f \circ i_B = i_B$。由 $x \in \operatorname{im}(F(i_B))$ 得 $F(f)(x) = x$。
2. 另一方面，$f$ 将 $A$ 常值映到 $z_0$，即 $f \circ i_A = i_{\{z_0\}} \circ {!}_A$（其中 ${!}_A : A \to 1$）。记 $x = F(i_A)(a)$，于是
   $$x = F(f)(x) = F(f \circ i_A)(a) = F(i_{\{z_0\}})\bigl(F({!}_A)(a)\bigr) \in \operatorname{im}(F(i_{\{z_0\}})).\quad \square$$

---

### Lemma 1.3
> 设 $F : \mathbf{Set} \to \mathbf{Set}$，若存在集合 $X$ 与映射 $q : X \to A_1$、$s : A_1 \to X$ 满足 $q \circ s = \mathrm{id}_{A_1}$（即 $A_1$ 是 $X$ 的收缩核），且 $F({!}_X) : F(X) \to F(1)$ 为双射，则 $p_1 : F(A_1) \to A_1$ 为双射，从而 $\operatorname{Stab}(F) \le 1$。

**证明**：
由 $q \circ s = \mathrm{id}_{A_1}$ 得 $F(q) \circ F(s) = \mathrm{id}_{F(A_1)}$，故 $F(s)$ 是单射；又由 $1$ 的终对象性质，有 ${!}_X \circ s = {!}_1$ 及 ${!}_1 \circ q = {!}_X$。
- 因为 $F(!_X) = F(!_1) \circ F(q)$ 是满射，所以 $F(!_1) : F(A_1) \to F(1)$ 是满射；
- 因为 $F(!_1) = F(!_X) \circ F(s)$ 是双射与单射的复合，所以 $F(!_1)$ 是单射。

因此 $F(!_1) : F(A_1) \to F(1)$ 是双射。注意到 $A_1 = F(A_0) \cong F(1)$ 且 $A_2 = F(A_1)$，$p_1 : A_2 \to A_1$ 即为 $F(!_1)$，故 $p_1$ 为双射。$\square$

---

### Lemma 1.4
> 设 $F : \mathbf{Set} \to \mathbf{Set}$。若 $A_1 = F(1) \neq \emptyset$，则对一切序数 $\alpha \ge 1$，存在截面映射 $s_\alpha : A_1 \to A_\alpha$ 满足 $f_1^\alpha \circ s_\alpha = \mathrm{id}_{A_1}$。特别地，$|A_\alpha| \ge |A_1|$，且一切 $A_\alpha \neq \emptyset$。

**证明**：
任取 $c \in F(1) = A_1$，即得一个常值 $F$-余代数 $1 \xrightarrow{c} F(1)$。按照超限归纳，每个序数 $\alpha$ 上的 $A_\alpha$ 均唯一携带与终端序列相容的锥元素 $s_\alpha(c) \in A_\alpha$（在每个后继步由常值映射 $1 \to A_\delta$ 通过 $F$ 向前推进，极限步由相容性拼接），且向第 $1$ 层的投影 $f_1^\alpha(s_\alpha(c))$ 恒等于 $c$（见 Worrell 2005）。于是 $f_1^\alpha \circ s_\alpha = \mathrm{id}_{A_1}$，$s_\alpha$ 为单射，进而 $|A_\alpha| \ge |A_1|$。$\square$

---

## 2. 排除 $\ge 2$ 的后继收敛点

### Proposition 2.1
> 设 $F : \mathbf{Set} \to \mathbf{Set}$ 是 $\omega$-可达的，$|X| \ge 2$ 为集合。若存在真子集 $T \subsetneq X$ 使得 $F(i_T) : F(T) \to F(X)$ 是满射，则对任意 $z \in X$，$F(i_{\{z\}}) : F(1) \xrightarrow{\sim} F(X)$ 与 $F({!}_X) : F(X) \xrightarrow{\sim} F(1)$ 均为双射。

**证明**：
- **Step 1**：取 $g \in X \setminus T$，则 $T \subseteq X \setminus \{g\}$。由 $F(i_T) = F(i_{X\setminus\{g\}}) \circ F(i_{T \hookrightarrow X\setminus\{g\}})$ 满射，知 $F(i_{X\setminus\{g\}})$ 也满射。
  对任意 $b \in X$，对换自同构 $\sigma = (g\; b) : X \xrightarrow{\sim} X$ 限制给出双射 $\sigma|_{X\setminus\{g\}} : X \setminus \{g\} \xrightarrow{\sim} X \setminus \{b\}$ 且满足 $i_{X\setminus\{b\}} \circ \sigma|_{X\setminus\{g\}} = \sigma \circ i_{X\setminus\{g\}}$。由于 $F(\sigma)$ 与 $F(\sigma|_{X\setminus\{g\}})$ 皆为双射，立得 $F(i_{X\setminus\{b\}})$ 对一切 $b \in X$ 都是满射。

- **Step 2**：任取 $z \in X$ 与 $x \in F(X)$，证明 $x \in \operatorname{im}(F(i_{\{z\}}))$：
  - **Case 1（$|X| = M$ 有限，$M \ge 2$）**：因为 $\{z\} = \bigcap_{b \in X \setminus \{z\}} (X \setminus \{b\})$，且每个有限子交皆非空（均包含 $z$），反复使用 **Lemma 1.1** 得
    $$F(X) = \bigcap_{b \in X \setminus \{z\}} \operatorname{im}\bigl(F(i_{X\setminus\{b\}})\bigr) = \operatorname{im}(F(i_{\{z\}})),$$
    故 $x \in \operatorname{im}(F(i_{\{z\}}))$。
  - **Case 2（$|X|$ 无限）**：由 $F$ 的 $\omega$-可达性，存在有限子集 $B_0 \subseteq X$ 使得 $x \in \operatorname{im}(F(i_{B_0}))$。
    - 若 $B_0 = \emptyset$，则空映射 $\emptyset \hookrightarrow X$ 经由 $1 \xrightarrow{z} X$ 分解，即得 $x \in \operatorname{im}(F(i_{\{z\}}))$；
    - 若 $B_0 \neq \emptyset$，因 $B_0$ 有限而 $X$ 无限，$X \setminus B_0 = \bigcap_{b \in B_0} (X \setminus \{b\})$ 仍非空（事实上无限）。对有限集 $B_0$ 反复应用 **Lemma 1.1** 得 $\operatorname{im}(F(i_{X \setminus B_0})) = \bigcap_{b \in B_0} \operatorname{im}(F(i_{X\setminus\{b\}})) = F(X)$，从而 $x \in \operatorname{im}(F(i_{B_0})) \cap \operatorname{im}(F(i_{X \setminus B_0}))$。由 **Lemma 1.2** 即得 $x \in \operatorname{im}(F(i_{\{z\}}))$。

- **Step 3**：由 Step 2，$F(i_{\{z\}}) : F(1) \to F(X)$ 是满射。又 $1 \xrightarrow{i_{\{z\}}} X \xrightarrow{{!}_X} 1$ 复合为 $\mathrm{id}_1$，故 $F({!}_X) \circ F(i_{\{z\}}) = \mathrm{id}_{F(1)}$，这同时说明 $F(i_{\{z\}})$ 单射（从而双射），进而其左逆 $F({!}_X)$ 也必为双射。$\square$

---

### Theorem 2.2
> 设 $F : \mathbf{Set} \to \mathbf{Set}$ 是 $\omega$-可达的，则对一切序数 $\alpha \ge 1$，$\operatorname{Stab}(F) \neq \alpha + 1$。

**证明**：
反设存在 $\alpha \ge 1$ 使得 $\gamma := \operatorname{Stab}(F) = \alpha + 1$。

首先排除 $|A_1| < 2$ 的情形：
- 若 $A_1 = \emptyset$，由存在投影 $A_2 \to A_1 = \emptyset$ 强制 $A_2 = \emptyset$，故 $p_1 : A_2 \to A_1$ 是空双射而 $p_0 : \emptyset \to 1$ 不满，得 $\operatorname{Stab}(F) = 1$，与 $\alpha + 1 > 1$ 矛盾；
- 若 $|A_1| = 1$，则 $p_0 : A_1 \to A_0$ 本身已是双射，得 $\operatorname{Stab}(F) = 0$，仍矛盾。

于是 $|A_1| \ge 2$。由 **Lemma 1.4**，对一切序数 $\delta \ge 1$ 均有 $|A_\delta| \ge |A_1| \ge 2$。

因 $\operatorname{Stab}(F) = \alpha + 1$，$p_{\alpha+1} = F(p_\alpha) : F(A_{\alpha+1}) \to F(A_\alpha)$ 是双射，而 $p_\alpha : A_{\alpha+1} \to A_\alpha$ 不是双射。对 $p_\alpha$ 分两种情形讨论：

- **Case 1（$p_\alpha$ 不满）**：令 $T := \operatorname{im}(p_\alpha) \subsetneq A_\alpha$。将 $p_\alpha$ 分解为 $A_{\alpha+1} \twoheadrightarrow T \xrightarrow{i_T} A_\alpha$。由 $F(p_\alpha) = F(i_T) \circ F(q)$ 是双射（特别是满射），可知 $F(i_T)$ 满射。由于 $|A_\alpha| \ge 2$，对 $X = A_\alpha$ 与真子集 $T$ 应用 **Proposition 2.1** 得 $F(A_\alpha) \cong F(1)$（即 $F({!}_{A_\alpha})$ 为双射）；又由 **Lemma 1.4**，$f_1^\alpha : A_\alpha \to A_1$ 有右逆截面 $s_\alpha : A_1 \to A_\alpha$，由 **Lemma 1.3** 立得 $\operatorname{Stab}(F) \le 1$，与 $\alpha + 1 > 1$ 矛盾。

- **Case 2（$p_\alpha$ 满但不单）**：存在 $y_0 \in A_\alpha$ 与不同的两点 $x_1 \neq x_2 \in A_{\alpha+1}$ 满足 $p_\alpha(x_1) = p_\alpha(x_2) = y_0$。由 $p_\alpha$ 满射性选取一右逆 $\sigma_0 : A_\alpha \to A_{\alpha+1}$，并在 $y_0$ 处分别改值为 $x_1, x_2$ 构造两个截面 $\sigma_1, \sigma_2 : A_\alpha \to A_{\alpha+1}$：
  $$\sigma_k(y) = \begin{cases} x_k, & y = y_0, \\ \sigma_0(y), & y \neq y_0 \end{cases} \qquad (k = 1, 2).$$
  因 $p_\alpha \circ \sigma_1 = p_\alpha \circ \sigma_2 = \mathrm{id}_{A_\alpha}$，有 $F(p_\alpha) \circ F(\sigma_k) = \mathrm{id}_{F(A_\alpha)}$；又 $F(p_\alpha) = p_{\alpha+1}$ 为双射，故 $F(\sigma_1) = F(\sigma_2) = p_{\alpha+1}^{-1} : F(A_\alpha) \to F(A_{\alpha+1})$ 皆为双射，特别地 $\operatorname{im}(F(\sigma_k)) = F(A_{\alpha+1})$。

  令 $T_0 := \sigma_1(A_\alpha \setminus \{y_0\})$，$S_k := \operatorname{im}(\sigma_k) = T_0 \cup \{x_k\}$（$k = 1, 2$）。
  - 由 $p_\alpha \circ \sigma_1 = \mathrm{id}_{A_\alpha}$ 知 $x_1 \notin T_0$，故 $T_0 \subsetneq A_{\alpha+1}$ 且 $S_1 \cap S_2 = T_0$；又因 $|A_\alpha| \ge 2$，必存在 $y_1 \neq y_0$，故 $T_0 \neq \emptyset$。
  - 将 $\sigma_k$ 分解为 $A_\alpha \xrightarrow{\sim} S_k \xrightarrow{i_{S_k}} A_{\alpha+1}$，由 $\operatorname{im}(F(\sigma_k)) = F(A_{\alpha+1})$ 得 $\operatorname{im}(F(i_{S_k})) = F(A_{\alpha+1})$。
  - 由 **Lemma 1.1**，
    $$\operatorname{im}(F(i_{T_0})) = \operatorname{im}(F(i_{S_1 \cap S_2})) = \operatorname{im}(F(i_{S_1})) \cap \operatorname{im}(F(i_{S_2})) = F(A_{\alpha+1}),$$
    故 $F(i_{T_0}) : F(T_0) \to F(A_{\alpha+1})$ 是满射。

  于是对 $X = A_{\alpha+1}$（$|X| \ge 2$）与非空真子集 $T_0$ 应用 **Proposition 2.1** 得 $F(A_{\alpha+1}) \cong F(1)$，再由 **Lemma 1.3** 与 **Lemma 1.4**（取 $s_{\alpha+1} : A_1 \to A_{\alpha+1}$）仍得 $\operatorname{Stab}(F) \le 1$，矛盾！

综上，对所有序数 $\alpha \ge 1$，皆有 $\operatorname{Stab}(F) \neq \alpha + 1$。$\square$

---

## 3. Worrell 上界 $\operatorname{Stab}(F) \le \omega + \omega$ 与四点分类定理

### Theorem 3.1（Worrell 上界）
> 任何 $\omega$-可达的集合端函子 $F : \mathbf{Set} \to \mathbf{Set}$ 至迟在 $\omega + \omega$ 处稳定。

**证明**：
若 $A_1 = \emptyset$，则如前所述 $F$ 在 $1 \le \omega + \omega$ 处稳定。以下设 $A_1 \neq \emptyset$。
1. **尾部单射性**：由 **Lemma 1.4** 一切 $A_\alpha \neq \emptyset$；结合 $F$ 的 $\omega$-可达性（即 $\aleph_0$-可达性，且 $\aleph_0$ 正则），由一般尾单射定理知对一切 $\omega \le \alpha \le \beta$，$f_\alpha^\beta : A_\beta \to A_\alpha$ 均为单射。特别地 $p_{\omega+\omega} : A_{\omega+\omega+1} \to A_{\omega+\omega}$ 已是单射，只需证其满射。
2. 任取 $y \in A_{\omega+\omega}$，令 $y_1 = f_{\omega+1}^{\omega+\omega}(y) \in A_{\omega+1} = F(A_\omega)$。对每个 $k \in \mathbb{N}$，利用 $f_{\omega+1}^{\omega+k+1} = F(f_\omega^{\omega+k})$ 及自然性，得 $y_1 = F(f_\omega^{\omega+k})\bigl(f_{\omega+k+1}^{\omega+\omega}(y)\bigr)$，从而若记 $C_k := \operatorname{im}(f_\omega^{\omega+k}) \subseteq A_\omega$（满足 $C_{k+1} \subseteq C_k$），则对一切 $k \in \mathbb{N}$ 均有 $y_1 \in \operatorname{im}(F(i_{C_k}))$。
3. 再记 $C_\omega := \operatorname{im}(f_\omega^{\omega+\omega}) \subseteq A_\omega$。若 $z \in \bigcap_{k \in \mathbb{N}} C_k$，对每个 $k$ 取 $z_k \in A_{\omega+k}$ 使 $f_\omega^{\omega+k}(z_k) = z$，由 $f_\omega^{\omega+k}$ 的单射性自动推得 $f_{\omega+k}^{\omega+m}(z_m) = z_k$（$k \le m$），从而 $(z_k)$ 拼成 $z_\infty \in A_{\omega+\omega}$ 满足 $f_\omega^{\omega+\omega}(z_\infty) = z$，即 $\bigcap_{k \in \mathbb{N}} C_k = C_\omega$。
4. 对 $y_1 \in F(A_\omega)$ 应用 $\omega$-可达性取有限支集 $S \subseteq A_\omega$ 使 $y_1 \in \operatorname{im}(F(i_S))$。对每个最终离开 $C_k$ 的 $s \in S \setminus C_\omega$ 取其首次不在 $C_k$ 中的下标，由于 $S$ 有限，这些有限个下标存在最大值 $N \in \mathbb{N}$，使得 $S \cap C_N \subseteq \bigcap_{k \in \mathbb{N}} C_k = C_\omega$。
5. 分两情形将 $y_1$ 拉回到 $F(C_\omega)$：
   - 若 $S \cap C_N \neq \emptyset$，由 **Lemma 1.1** 得 $y_1 \in \operatorname{im}(F(i_{S \cap C_N})) \subseteq \operatorname{im}(F(i_{C_\omega}))$；
   - 若 $S \cap C_N = \emptyset$，由 **Lemma 1.2** 得 $y_1 \in \operatorname{im}(F(i_{\{z_0\}}))$（取 $z_0 := f_\omega^{\omega+\omega}(y) \in C_\omega$），仍得 $y_1 \in \operatorname{im}(F(i_{C_\omega}))$。
6. 因 $f_\omega^{\omega+\omega} : A_{\omega+\omega} \to C_\omega$ 是单满射（双射），故存在 $x \in F(A_{\omega+\omega}) = A_{\omega+\omega+1}$ 满足 $f_{\omega+1}^{\omega+\omega+1}(x) = F(f_\omega^{\omega+\omega})(x) = y_1 = f_{\omega+1}^{\omega+\omega}(y)$。
7. 对任意 $k \in \mathbb{N}$，有
   $$f_{\omega+1}^{\omega+k+1}\bigl(f_{\omega+k+1}^{\omega+\omega+1}(x)\bigr) = f_{\omega+1}^{\omega+\omega+1}(x) = f_{\omega+1}^{\omega+\omega}(y) = f_{\omega+1}^{\omega+k+1}\bigl(f_{\omega+k+1}^{\omega+\omega}(y)\bigr).$$
   由 $f_{\omega+1}^{\omega+k+1}$ 单射得对一切 $k \in \mathbb{N}$ 均有 $f_{\omega+k+1}^{\omega+\omega+1}(x) = f_{\omega+k+1}^{\omega+\omega}(y)$，从而在一切 $< \omega + \omega$ 坐标上投影相等，即 $p_{\omega+\omega}(x) = y$。$\square$

---

### Theorem 3.2（$\omega$-可达集合函子的四点收敛定理）
> 对任何 $\omega$-可达的集合端函子 $F : \mathbf{Set} \to \mathbf{Set}$，其精确收敛序数 $\operatorname{Stab}(F)$ 存在、唯一，且必然属于
> $$\{0,\; 1,\; \omega,\; \omega + \omega\}.$$

**证明**：
由 **Theorem 3.1** 及序数的良基性，最小稳定序数 $\gamma := \operatorname{Stab}(F)$ 存在唯一且满足 $\gamma \le \omega + \omega$：
- 若 $\gamma < \omega$：$0, 1$ 保留；任何有限序数 $n \ge 2$ 均可表作 $(n - 1) + 1$（$n - 1 \ge 1$），被 **Theorem 2.2** 排除。
- 若 $\gamma = \omega$：保留。
- 若 $\omega < \gamma < \omega + \omega$：必存在 $n \in \mathbb{N}$ 使 $\gamma = \omega + (n + 1) = (\omega + n) + 1$，且 $\omega + n \ge 1$，同样被 **Theorem 2.2** 排除。
- 若 $\gamma = \omega + \omega$：保留。

故 $\operatorname{Stab}(F) \in \{0, 1, \omega, \omega + \omega\}$。$\square$

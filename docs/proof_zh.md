# 集合函子 $G_{\kappa,\theta}$ 精确稳定阶 $\operatorname{Stab}(G_{\kappa,\theta}) = \kappa + \theta$ 的证明

---

## 0. 函子定义、终端序列与基本性质

设 $\kappa, \theta$ 为无穷正则基数，且满足 $\omega \le \theta \le \kappa$。记 $\mathrm{Reg}_{<\theta}$ 为所有严格小于 $\theta$ 的无穷正则基数 $\mu$ 构成的集合。对每个 $\mu \in \mathrm{Reg}_{<\theta}$，在函数空间 $X^\mu$ 上定义等价关系：
$$a \equiv_{<\mu} b \iff \bigl|\{ i < \mu : a(i) \neq b(i) \}\bigr| < \mu.$$
由于 $\mu$ 为正则基数（从而小差异集之并的基数仍严格小于 $\mu$），$\equiv_{<\mu}$ 是等价关系。据此定义集合端函子 $G_{\kappa,\theta} : \mathbf{Set} \to \mathbf{Set}$：
$$G_{\kappa,\theta}(X) = \mathcal{P}_{<\kappa}(X) \;\sqcup\; \bigsqcup_{\mu \in \mathrm{Reg}_{<\theta}} \bigl(X^\mu / {\equiv_{<\mu}}\bigr),$$
其中 $\mathcal{P}_{<\kappa}(X) = \{ S \subseteq X : |S| < \kappa \}$。给定映射 $h : X \to Y$，$G_{\kappa,\theta}(h)$ 在左分支取直接像 $S \mapsto h[S]$（由 $|h[S]| \le |S| < \kappa$ 良定义），在右分支逐分量复合 $[a] \mapsto [h \circ a]$（由 $\{ i : h(a(i)) \neq h(b(i)) \} \subseteq \{ i : a(i) \neq b(i) \}$ 良定义）。为记号简洁，以下亦将左分支嵌入记作 $\mathsf{L}(S)$、右分支嵌入记作 $\mathsf{R}(\mu, [a])$。

### 终端序列 $(A_\alpha, f_\alpha^\beta)$
在序数 $\mathrm{Ord}$ 上通过超限递归定义 $G_{\kappa,\theta}$ 的终端序列：
- **初项**：$A_0 = 1 = \{*\}$（终对象）；
- **后继步**：$A_{\alpha+1} = G_{\kappa,\theta}(A_\alpha)$，衔接态射满足 $f_{\alpha+1}^{\beta+1} = G_{\kappa,\theta}(f_\alpha^\beta)$；
- **极限步**：对极限序数 $\lambda$，$A_\lambda = \varprojlim_{\alpha < \lambda} A_\alpha$ 为相容族 $\bigl\{ (x_\alpha)_{\alpha < \lambda} \in \prod_{\alpha<\lambda} A_\alpha \mid \forall \alpha \le \beta < \lambda,\; f_\alpha^\beta(x_\beta) = x_\alpha \bigr\}$，$f_\alpha^\lambda$ 为第 $\alpha$ 个投影映射。

全体过渡映射满足 $f_\alpha^\alpha = \mathrm{id}$ 与 $f_\alpha^\gamma = f_\alpha^\beta \circ f_\beta^\gamma$（$\alpha \le \beta \le \gamma$）。此外，因 $\emptyset \in \mathcal{P}_{<\kappa}(1)$，恒有 $A_1 \neq \emptyset$，从而对一切序数 $\alpha$ 均有 $A_\alpha \neq \emptyset$。若 $f_\gamma^{\gamma+1}$ 为双射，则称 $G_{\kappa,\theta}$ 在 $\gamma$ 处**稳定**（此时对一切 $\delta \ge \gamma$，$f_\gamma^\delta$ 与 $f_\delta^{\delta+1}$ 均为双射）；使之稳定的最小序数称为精确稳定阶 $\operatorname{Stab}(G_{\kappa,\theta})$。

### 命题 0.1（$\kappa$-可及性与保持单射）
当 $\kappa$ 为无穷正则基数且 $\theta \le \kappa$ 时：
1. **$G_{\kappa,\theta}$ 保持单射**：若 $h : X \hookrightarrow Y$ 为单射，则 $G_{\kappa,\theta}(h)$ 亦为单射；
2. **$G_{\kappa,\theta}$ 是 $\kappa$-可及的**：对任意集合 $X$ 与 $u \in G_{\kappa,\theta}(X)$，存在基数 $|Y| < \kappa$ 的子集 $Y \subseteq X$ 使 $u \in \operatorname{im}\bigl(G_{\kappa,\theta}(\iota_{Y \hookrightarrow X})\bigr)$。

**证明**：
1. 左右不交并分支互不相混。在左分支，若 $h[S_1] = h[S_2]$ 则由 $h$ 单射得 $S_1 = S_2$；在右分支，若 $[h \circ a] = [h \circ b]$，则 $\{ i : a(i) \neq b(i) \} = \{ i : h(a(i)) \neq h(b(i)) \}$ 的基数严格小于 $\mu$，故 $[a] = [b]$。
2. 若 $u = \mathsf{L}(S)$，直接取 $Y = S$（$|S| < \kappa$）；若 $u = \mathsf{R}(\mu, [a])$（$\mu < \theta \le \kappa$），取 $Y = a[\mu] \subseteq X$，则 $|Y| \le \mu < \kappa$ 且 $a$ 通过 $Y$ 分解。$\blacksquare$

### 命题 0.2（尾部单态性）
若 $\kappa$ 为无穷正则基数且 $\theta \le \kappa$，则对一切 $\kappa \le \alpha \le \beta$，转移映射 $f_\alpha^\beta : A_\beta \to A_\alpha$ 均为单射；特别地，$f_\kappa^{\kappa+1}$ 是单射。

**证明**：先证 $f_\kappa^{\kappa+1}$ 单射。若 $Y \subseteq A_\kappa$ 满足 $|Y| < \kappa$，则对任意 $x \neq y \in Y$ 存在 $\alpha(x,y) < \kappa$ 使 $f_{\alpha(x,y)}^\kappa(x) \neq f_{\alpha(x,y)}^\kappa(y)$；因 $|Y \times Y| < \kappa$ 且 $\kappa$ 正则，$\alpha_0 := \sup_{x \neq y \in Y} \alpha(x,y) < \kappa$，于是 $f_{\alpha_0}^\kappa|_Y$ 为单射。

现设 $x, y \in A_{\kappa+1} = G_{\kappa,\theta}(A_\kappa)$ 且 $f_\kappa^{\kappa+1}(x) = f_\kappa^{\kappa+1}(y)$。由 $\kappa$-可及性取基数 $< \kappa$ 的支集 $Y_x, Y_y \subseteq A_\kappa$，并取 $Y = Y_x \cup Y_y \cup \{a_0\}$（$a_0 \in A_\kappa$ 任取），仍有 $0 < |Y| < \kappa$。取如上 $\alpha < \kappa$ 使 $f_\alpha^\kappa|_Y$ 单射，则 $f_\alpha^\kappa \circ \iota_Y : Y \hookrightarrow A_\alpha$ 为非空集合间的单射，必存在左逆 $r : A_\alpha \to Y$。由于 $f_\alpha^\kappa \circ f_\kappa^{\kappa+1}(x) = f_\alpha^\kappa \circ f_\kappa^{\kappa+1}(y)$，即 $G_{\kappa,\theta}(f_\alpha^\kappa)(x) = G_{\kappa,\theta}(f_\alpha^\kappa)(y)$，而 $x, y$ 分别由 $Y$ 上元素经 $\iota_Y$ 映入，在两端作用 $G_{\kappa,\theta}(r)$ 即得 $x = y$。

再对 $\beta \ge \kappa$ 作超限归纳：后继步由命题 0.1（$G_{\kappa,\theta}$ 保持单射）传递，极限步由 $\varprojlim$ 投影唯一性传递，故全部 $f_\alpha^\beta$（$\kappa \le \alpha \le \beta$）皆为单射。$\blacksquare$

---

## 第一阶段（Step 1）：证明 $f_\kappa^{\kappa+1}$ 不满射，从而 $\operatorname{Stab}(G_{\kappa,\theta}) \ge \kappa$

本阶段仅用到左分支 $\mathcal{P}_{<\kappa}(X)$ 与 $\kappa$ 的正则性（对 $\theta$ 无任何额外要求）。

### 1.1 对角家族 $q_\alpha(\beta)$ 的构造
对 $\alpha \le \kappa$ 与全部序数 $\beta \in \mathrm{Ord}$，按关于 $\alpha$ 的超限递归定义元素 $q_\alpha(\beta) \in A_\alpha$：
1. **$\alpha = 0$**：$q_0(\beta) = * \in A_0$；
2. **后继步（$\alpha = \delta + 1 \le \kappa$）**：
   $$q_{\delta+1}(\beta) := \mathsf{L}\Bigl(\bigl\{ q_\delta(\gamma) \mid \gamma < \min(\beta,\; \delta+1) \bigr\}\Bigr) \in G_{\kappa,\theta}(A_\delta) = A_{\delta+1};$$
   因 $|\min(\beta, \delta+1)| \le |\delta+1| < \kappa$（$\delta+1 \le \kappa$ 且若 $\delta+1 = \kappa$ 则矛盾于极限性，故实际 $\delta+1 < \kappa$），该子集确实属于 $\mathcal{P}_{<\kappa}(A_\delta)$；
3. **极限步（$l \le \kappa$ 为极限序数）**：$q_l(\beta) := \bigl(q_\alpha(\beta)\bigr)_{\alpha < l} \in A_l$。

为证明极限步中的元确实相容地落入 $A_l$，同时确立下面两条核心引理（在严格形式化中可与合法性一并归纳证得）。

### 1.2 引理 1（截断等同判据）
对一切 $\alpha \le \kappa$ 与一切序数 $\beta, \gamma \in \mathrm{Ord}$，
$$q_\alpha(\beta) = q_\alpha(\gamma) \iff \min(\alpha, \beta) = \min(\alpha, \gamma).$$

**证明**（对 $\alpha$ 作超限归纳）：
- **基始步（$\alpha = 0$）**：$q_0(\beta) = * = q_0(\gamma)$，且 $\min(0, \beta) = 0 = \min(0, \gamma)$，成立。
- **后继步（$\alpha = \delta + 1$）**：
  $$q_{\delta+1}(\beta) = q_{\delta+1}(\gamma) \iff \{q_\delta(i) \mid i < \min(\beta, \delta+1)\} = \{q_\delta(i) \mid i < \min(\gamma, \delta+1)\}.$$
  但对一切 $i < \delta+1$（即 $i \le \delta$）与 $j < \delta+1$，由归纳假设：
  $$q_\delta(i) = q_\delta(j) \iff \min(\delta, i) = \min(\delta, j) \iff i = j$$
  （因 $i, j \le \delta$，均有 $\min(\delta, i) = i$ 与 $\min(\delta, j) = j$）。故映射 $i \mapsto q_\delta(i)$ 在 $\{i : i < \delta+1\}$ 上是单射！从而两个集合相等当且仅当指标集合本身相等，即 $\min(\beta, \delta+1) = \min(\gamma, \delta+1)$。
- **极限步（$l$ 为极限序数）**：
  $$q_l(\beta) = q_l(\gamma) \iff \forall \alpha < l,\; q_\alpha(\beta) = q_\alpha(\gamma) \iff \forall \alpha < l,\; \min(\alpha, \beta) = \min(\alpha, \gamma).$$
  - ($\Leftarrow$) 若 $\min(l, \beta) = \min(l, \gamma)$，显然对一切 $\alpha < l$ 有 $\min(\alpha, \beta) = \min(\alpha, \min(l, \beta)) = \min(\alpha, \min(l, \gamma)) = \min(\alpha, \gamma)$。
  - ($\Rightarrow$) 设 $\forall \alpha < l,\; \min(\alpha, \beta) = \min(\alpha, \gamma)$，反设 $\min(l, \beta) \neq \min(l, \gamma)$。不妨设 $\mu := \min(l, \beta) < \min(l, \gamma) \le l$。因 $\mu < l$ 且 $l$ 为极限序数，有 $\mu + 1 < l$。取 $\alpha = \mu + 1$：因 $\mu < \min(l, \gamma) \le \gamma$ 故 $\min(\mu+1, \gamma) = \mu + 1$，而 $\beta = \mu < \mu + 1$ 故 $\min(\mu+1, \beta) = \mu$，与假设矛盾！$\blacksquare$

### 1.3 引理 2（投影相容性）
对一切 $\alpha \le \eta \le \kappa$ 与一切 $\beta \in \mathrm{Ord}$，均有 $f_\alpha^\eta\bigl(q_\eta(\beta)\bigr) = q_\alpha(\beta)$。

**证明**（对 $\eta$ 作超限归纳）：
- 若 $\alpha = \eta$，$f_\eta^\eta = \mathrm{id}$ 平凡成立。下设 $\alpha < \eta$。
- **后继步（$\eta = \xi + 1$）**：只需证明 $f_\xi^{\xi+1}\bigl(q_{\xi+1}(\beta)\bigr) = q_\xi(\beta)$（再用 $f_\alpha^{\xi+1} = f_\alpha^\xi \circ f_\xi^{\xi+1}$ 与归纳假设即得对所有 $\alpha \le \xi$ 成立）。对 $\xi$ 分类讨论：
  1. $\xi = 0$：$A_0 = \{*\}$，故 $f_0^1(q_1(\beta)) = * = q_0(\beta)$。
  2. $\xi = \delta + 1$（后继序数）：此时 $f_{\delta+1}^{\delta+2} = G_{\kappa,\theta}(f_\delta^{\delta+1})$，在左分支上即逐元取像：
     $$f_{\delta+1}^{\delta+2}\bigl(q_{\delta+2}(\beta)\bigr) = \mathsf{L}\Bigl(\bigl\{ f_\delta^{\delta+1}(q_{\delta+1}(i)) \mid i < \min(\beta, \delta+2) \bigr\}\Bigr) = \mathsf{L}\Bigl(\bigl\{ q_\delta(i) \mid i < \min(\beta, \delta+2) \bigr\}\Bigr).$$
     因对 $i = \delta + 1$（当 $\beta > \delta+1$ 时）有 $q_\delta(\delta+1) = q_\delta(\delta)$（由引理 1，$\min(\delta, \delta+1) = \delta = \min(\delta, \delta)$），该集合正等于 $\{ q_\delta(i) \mid i < \min(\beta, \delta+1) \}$，即 $q_{\delta+1}(\beta)$。
  3. $\xi$ 为极限序数：只需比较二者到每个 $\alpha < \xi$ 的投影。因 $\xi$ 极限，对任意 $\alpha < \xi$ 有 $\alpha + 1 < \xi$；利用 $f_\alpha^\xi \circ f_\xi^{\xi+1} = f_\alpha^{\alpha+1} \circ f_{\alpha+1}^{\xi+1}$ 以及 $f_{\alpha+1}^{\xi+1} = G_{\kappa,\theta}(f_\alpha^\xi)$，结合归纳假设得
     $$f_\alpha^\xi\bigl(f_\xi^{\xi+1}(q_{\xi+1}(\beta))\bigr) = f_\alpha^{\alpha+1}\Bigl(\mathsf{L}\bigl\{ f_\alpha^\xi(q_\xi(i)) \mid i < \min(\beta, \xi+1) \bigr\}\Bigr) = f_\alpha^{\alpha+1}\Bigl(\mathsf{L}\bigl\{ q_\alpha(i) \mid i < \min(\beta, \xi+1) \bigr\}\Bigr).$$
     由于 $\forall i \ge \alpha+1$ 均有 $q_\alpha(i) = q_\alpha(\alpha)$（引理 1），集合 $\{ q_\alpha(i) \mid i < \min(\beta, \xi+1) \}$ 恰好等于 $\{ q_\alpha(i) \mid i < \min(\beta, \alpha+1) \}$，即其内层就是 $q_{\alpha+1}(\beta)$，故上式等于 $f_\alpha^{\alpha+1}(q_{\alpha+1}(\beta)) = q_\alpha(\beta)$。
- **极限步（$\eta$ 为极限序数）**：对一切 $\alpha < \eta$，$f_\alpha^\eta(q_\eta(\beta))$ 按极限投影定义即为第 $\alpha$ 分量 $q_\alpha(\beta)$。$\blacksquare$

### 1.4 非满射性与第一阶段结论
令见证元素为 $b_\kappa := q_\kappa(\kappa) \in A_\kappa$。断言 $b_\kappa \notin \operatorname{im}(f_\kappa^{\kappa+1})$。

**证明**：反设存在 $x \in A_{\kappa+1} = G_{\kappa,\theta}(A_\kappa)$ 使 $f_\kappa^{\kappa+1}(x) = b_\kappa$。分两分支导出矛盾：
- **右分支 $x = \mathsf{R}(\mu, [a])$**：将 $f_\kappa^{\kappa+1}(x) = q_\kappa(\kappa)$ 用 $f_1^\kappa$ 投影到第 $1$ 级。左端为 $f_1^{\kappa+1}(\mathsf{R}(\mu, [a])) = \mathsf{R}(\mu, [f_0^\kappa \circ a])$ 仍落在右分支；右端按引理 2 等于 $q_1(\kappa) = \mathsf{L}(\{*\})$ 落在左分支，矛盾。
- **左分支 $x = \mathsf{L}(S)$**，其中 $S \subseteq A_\kappa$ 且 $|S| < \kappa$：
  1. **唯一命中性质**：对每个固定的 $s \in A_\kappa$，至多存在一个 $\gamma < \kappa$ 使 $f_{\gamma+1}^\kappa(s) = q_{\gamma+1}(\gamma)$。确实，若同时有 $\gamma_1 < \gamma_2 < \kappa$ 满足，则用 $f_{\gamma_1+1}^{\gamma_2+1}$ 向下投影并用引理 2 得
     $$q_{\gamma_1+1}(\gamma_1) = f_{\gamma_1+1}^\kappa(s) = f_{\gamma_1+1}^{\gamma_2+1}\bigl(q_{\gamma_2+1}(\gamma_2)\bigr) = q_{\gamma_1+1}(\gamma_2).$$
     由引理 1，$\gamma_1 = \min(\gamma_1+1, \gamma_1) = \min(\gamma_1+1, \gamma_2) = \gamma_1 + 1$（因 $\gamma_2 \ge \gamma_1+1$），矛盾。
  2. 对每个 $s \in S$，记其唯一命中的索引为 $\gamma_s < \kappa$（不存在时取 $0$）。因 $|S| < \kappa$ 且 **$\kappa$ 是正则基数**，上确界 $\alpha := \bigl(\sup_{s \in S} \gamma_s\bigr) + 1 < \kappa$，于是没有任何 $s \in S$ 满足 $f_{\alpha+1}^\kappa(s) = q_{\alpha+1}(\alpha)$。
  3. 然而将 $f_\kappa^{\kappa+1}(\mathsf{L}(S)) = q_\kappa(\kappa)$ 投影到第 $\alpha + 2 < \kappa$ 级：一方面左端是 $f_{\alpha+2}^{\kappa+1}(\mathsf{L}(S)) = \mathsf{L}(f_{\alpha+1}^\kappa[S])$，另一方面右端按引理 2 为 $q_{\alpha+2}(\kappa) = \mathsf{L}(\{ q_{\alpha+1}(i) \mid i < \alpha + 2 \})$。故 $f_{\alpha+1}^\kappa[S] = \{ q_{\alpha+1}(i) \mid i < \alpha + 2 \}$。特别地，$q_{\alpha+1}(\alpha)$ 必在 $f_{\alpha+1}^\kappa[S]$ 中，即存在 $s \in S$ 命中 $\alpha$，矛盾！

因此 $f_\kappa^{\kappa+1}$ 不满射，且由稳定的向上封闭性，任何满足稳定的序数 $\delta$ 必有 $\delta \ge \kappa$。$\blacksquare$

---

## 第二阶段（Step 2）：下降滤子 $(B_\beta)$、剪枝秩与 $\operatorname{Stab}(G_{\kappa,\theta}) = \kappa + \theta$

由命题 0.2，$f_\alpha^\beta$ 在全部 $\kappa \le \alpha \le \beta$ 上皆为单射。问题归结为判定何时变为满射。在 $A_\kappa$ 上定义子对象降链（滤子）：
$$B_0 = A_\kappa, \qquad B_\beta := \operatorname{im}\bigl(f_\kappa^{\kappa+\beta} : A_{\kappa+\beta} \to A_\kappa\bigr) \subseteq A_\kappa \qquad (\beta \in \mathrm{Ord}).$$
对任意子集 $U \subseteq A_\kappa$，记 $H(U) \subseteq G_{\kappa,\theta}(A_\kappa)$ 为受限于 $U$ 的子函子像集（即 $G_{\kappa,\theta}(U)$ 在 $G_{\kappa,\theta}(A_\kappa)$ 中的自然嵌入像）：
- 对 $u = \mathsf{L}(S)$，$u \in H(U) \iff S \subseteq U$；
- 对 $u = \mathsf{R}(\mu, [a])$，$u \in H(U) \iff \exists b \equiv_{<\mu} a,\; \forall i < \mu,\; b(i) \in U \iff \bigl|\{ i < \mu : a(i) \notin U \}\bigr| < \mu$。

### 2.1 引理 3（$B_\beta$ 的基本性质与递推刻画）
1. **单调递降**：若 $\beta_1 \le \beta_2$，则 $B_{\beta_2} \subseteq B_{\beta_1}$，且每个 $B_\beta \neq \emptyset$。
2. **后继步**：$B_{\beta+1} = f_\kappa^{\kappa+1}\bigl[H(B_\beta)\bigr]$。
3. **极限步**：对任何极限序数 $l$，$B_l = \bigcap_{\beta < l} B_\beta$。
4. **局部满射等价**：$f_{\kappa+\beta}^{\kappa+\beta+1}$ 为满射当且仅当 $B_{\beta+1} = B_\beta$。

**证明**：
1. 对 $\beta_1 \le \beta_2$，由 $f_\kappa^{\kappa+\beta_2} = f_\kappa^{\kappa+\beta_1} \circ f_{\kappa+\beta_1}^{\kappa+\beta_2}$ 得 $B_{\beta_2} \subseteq B_{\beta_1}$；因 $A_{\kappa+\beta} \neq \emptyset$ 故 $B_\beta \neq \emptyset$。
2. 因 $f_{\kappa+1}^{\kappa+\beta+1} = G_{\kappa,\theta}(f_\kappa^{\kappa+\beta})$ 而 $f_\kappa^{\kappa+\beta} : A_{\kappa+\beta} \xrightarrow{\sim} B_\beta$（到像集的双射），恰有 $\operatorname{im}(f_{\kappa+1}^{\kappa+\beta+1}) = H(B_\beta)$；再复合 $f_\kappa^{\kappa+1}$ 即得 $B_{\beta+1} = f_\kappa^{\kappa+1}[H(B_\beta)]$。
3. ($\subseteq$) 显然由第 1 条得出。($\supseteq$) 设 $c \in \bigcap_{\beta < l} B_\beta$，即对每个 $\beta < l$ 存在 $x_\beta \in A_{\kappa+\beta}$ 使 $f_\kappa^{\kappa+\beta}(x_\beta) = c$。对任意 $\beta \le \gamma < l$，计算
   $$f_\kappa^{\kappa+\beta}\bigl(f_{\kappa+\beta}^{\kappa+\gamma}(x_\gamma)\bigr) = f_\kappa^{\kappa+\gamma}(x_\gamma) = c = f_\kappa^{\kappa+\beta}(x_\beta),$$
   由命题 0.2（$f_\kappa^{\kappa+\beta}$ 单射）立即自动推出 $f_{\kappa+\beta}^{\kappa+\gamma}(x_\gamma) = x_\beta$！因此 $(x_\beta)_{\beta < l}$ 满足全部中间层相容性（低层 $\alpha < \kappa$ 可由 $x_0 \in A_\kappa$ 往下投影统一补全），从而拼成 $x \in A_{\kappa+l}$ 满足 $f_\kappa^{\kappa+l}(x) = c \in B_l$。
4. 由 $f_\kappa^{\kappa+\beta}$ 单射，$f_{\kappa+\beta}^{\kappa+\beta+1}(A_{\kappa+\beta+1}) = A_{\kappa+\beta} \iff f_\kappa^{\kappa+\beta}\bigl(\operatorname{im}(f_{\kappa+\beta}^{\kappa+\beta+1})\bigr) = f_\kappa^{\kappa+\beta}(A_{\kappa+\beta}) \iff B_{\beta+1} = B_\beta$。$\blacksquare$

### 2.2 剪枝秩 $\rho$、延迟算子 $\sigma, \tau_\mu$ 与全体 $< \theta$ 秩的实现
对 $x \in B_0 = A_\kappa$，若存在序数 $\beta$ 使 $x \in B_\beta \setminus B_{\beta+1}$，称 $\rho(x) = \beta$ 为 $x$ 的**剪枝秩**。由引理 3(4)，存在 $\rho(x) = \beta \iff B_{\beta+1} \subsetneq B_\beta \iff f_{\kappa+\beta}^{\kappa+\beta+1}$ 不满射。

定义两类 $A_\kappa$ 上的延迟算子：
- **后继延迟算子**：$\sigma(x) := f_\kappa^{\kappa+1}\bigl(\mathsf{L}(\{x\})\bigr)$；
- **极限延迟算子**（对每个 $\mu \in \mathrm{Reg}_{<\theta}$ 与序列 $a : \mu \to A_\kappa$）：$\tau_\mu(a) := f_\kappa^{\kappa+1}\bigl(\mathsf{R}(\mu, [a])\bigr)$。

#### 引理 4（延迟算子的成员判据）
对任意序数 $\beta$：
1. $\sigma(x) \in B_{\beta+1} \iff x \in B_\beta$；
2. $\tau_\mu(a) \in B_{\beta+1} \iff \bigl|\{ i < \mu : a(i) \notin B_\beta \}\bigr| < \mu$。

**证明**：利用引理 3(2) $B_{\beta+1} = f_\kappa^{\kappa+1}[H(B_\beta)]$ 与命题 0.2（$f_\kappa^{\kappa+1}$ 单射），$\sigma(x) \in B_{\beta+1} \iff \mathsf{L}(\{x\}) \in H(B_\beta) \iff \{x\} \subseteq B_\beta \iff x \in B_\beta$；同理 $\tau_\mu(a) \in B_{\beta+1} \iff \mathsf{R}(\mu, [a]) \in H(B_\beta) \iff \bigl|\{ i < \mu : a(i) \notin B_\beta \}\bigr| < \mu$。$\blacksquare$

据此立刻得到以下两个延迟机制：
- **后继延迟**：若 $\rho(x) = \alpha$（即 $x \in B_\alpha \setminus B_{\alpha+1}$），则 $\rho(\sigma(x)) = \alpha + 1$。
- **极限延迟**：设 $l < \theta$ 为极限序数，记 $\mu := \operatorname{cof}(l)$。因 $l$ 为极限序数且 $l < \theta$，$\mu$ 是无穷正则基数且 $\mu \le |l| < \theta$，即 $\mu \in \mathrm{Reg}_{<\theta}$。取在 $l$ 中严格递增的共尾序列 $(c_j)_{j<\mu}$。若 $\rho(x_{c_j}) = c_j$ 对一切 $j < \mu$ 成立，令 $x_l := \tau_\mu\bigl((x_{c_j})_{j<\mu}\bigr)$，则 $\rho(x_l) = l$：
  1. 对任给 $\beta < l$，由共尾性取 $i_0 < \mu$ 使 $j \ge i_0 \implies c_j \ge \beta \implies x_{c_j} \in B_{c_j} \subseteq B_\beta$；故 $\{j < \mu : x_{c_j} \notin B_\beta\} \subseteq i_0$ 基数 $< \mu$，由引理 4 得 $x_l \in B_{\beta+1} \subseteq B_\beta$，再由引理 3(3) 得 $x_l \in \bigcap_{\beta < l} B_\beta = B_l$。
  2. 反之，对一切 $j < \mu$ 均有 $c_j + 1 < l$，故 $B_l \subseteq B_{c_j+1}$，从而 $x_{c_j} \notin B_{c_j+1} \implies x_{c_j} \notin B_l$。于是 $\{j < \mu : x_{c_j} \notin B_l\} = \mu$ 基数不小于 $\mu$，由引理 4 得 $x_l \notin B_{l+1}$。

**推论（全部 $< \theta$ 秩的实现）**：对一切 $\alpha < \theta$ 作超限归纳（取 $x_0 = b_\kappa \in B_0 \setminus B_1$，后继步用 $\sigma$，极限步用 $\tau_{\operatorname{cof}(l)}$），对每一个 $\alpha < \theta$ 均存在 $x_\alpha \in B_\alpha \setminus B_{\alpha+1}$。特别地，对任意 $\delta = \kappa + \alpha < \kappa + \theta$，$f_\delta^{\delta+1}$ 都不是满射，从而 $\operatorname{Stab}(G_{\kappa,\theta}) \ge \kappa + \theta$。$\blacksquare$

### 2.3 $\theta$-正则闭合与最终收尾：$B_{\theta+1} = B_\theta$

#### 引理 5（小集合下降截断稳定）
设 $S \subseteq B_0 = A_\kappa$ 满足 $|S| < \theta$。则存在 $\beta_* < \theta$ 使得 $S \cap B_{\beta_*} = S \cap B_\theta$。

**证明**：因 $B_\theta \subseteq B_\beta$ 对一切 $\beta < \theta$ 成立，恒有 $S \cap B_\theta \subseteq S \cap B_\beta$。反之对每个 $s \in S \setminus B_\theta$，由 $B_\theta = \bigcap_{\gamma < \theta} B_\gamma$ 存在 $\gamma_s < \theta$ 使 $s \notin B_{\gamma_s}$（对 $s \in S \cap B_\theta$ 置 $\gamma_s = 0$）。由于 $|S| < \theta$ 且 **$\theta$ 为正则基数**，上确界
$$\beta_* := \sup_{s \in S} \gamma_s < \theta.$$
对任意 $s \in S \cap B_{\beta_*}$，若 $s \notin B_\theta$ 则 $\gamma_s \le \beta_* \implies B_{\beta_*} \subseteq B_{\gamma_s} \implies s \in B_{\gamma_s}$，矛盾。故 $S \cap B_{\beta_*} = S \cap B_\theta$。$\blacksquare$

#### 定理（$\theta$ 处闭合与精确稳定阶）
$B_{\theta+1} = B_\theta$，且 $\operatorname{Stab}(G_{\kappa,\theta}) = \kappa + \theta$。

**证明**：只需证 $B_\theta \subseteq B_{\theta+1}$。任取 $x \in B_\theta$。由于 $x \in B_\theta \subseteq B_1 = \operatorname{im}(f_\kappa^{\kappa+1})$，存在唯一 $u \in G_{\kappa,\theta}(A_\kappa)$ 使 $x = f_\kappa^{\kappa+1}(u)$；又对一切 $\beta < \theta$ 均有 $x \in B_\theta \subseteq B_{\beta+1} = f_\kappa^{\kappa+1}[H(B_\beta)]$，结合 $f_\kappa^{\kappa+1}$ 的单射性得 $\forall \beta < \theta,\; u \in H(B_\beta)$。分两分支证明 $u \in H(B_\theta)$：
- **左分支 $u = \mathsf{L}(S)$**：对一切 $\beta < \theta$ 有 $S \subseteq B_\beta$，故 $S \subseteq \bigcap_{\beta < \theta} B_\beta = B_\theta$，从而 $u \in H(B_\theta)$。
- **右分支 $u = \mathsf{R}(\mu, [a])$**（$\mu < \theta$）：令 $S = \operatorname{im}(a) \subseteq A_\kappa$，则 $|S| \le \mu < \theta$。由引理 5 取 $\beta_* < \theta$ 使 $S \cap B_{\beta_*} = S \cap B_\theta$。由于 $u \in H(B_{\beta_*})$，我们有 $\bigl|\{i < \mu : a(i) \notin B_{\beta_*}\}\bigr| < \mu$。而对任意 $i < \mu$，$a(i) \in S$，故 $a(i) \in B_\theta \iff a(i) \in B_{\beta_*}$。从而
  $$\{i < \mu : a(i) \notin B_\theta\} = \{i < \mu : a(i) \notin B_{\beta_*}\},$$
  基数仍严格小于 $\mu$，即 $u \in H(B_\theta)$。

由此 $x = f_\kappa^{\kappa+1}(u) \in f_\kappa^{\kappa+1}[H(B_\theta)] = B_{\theta+1}$。

于是 $B_{\theta+1} = B_\theta$，由引理 3(4) 与命题 0.2 即知 $f_{\kappa+\theta}^{\kappa+\theta+1}$ 为双射；配合第一阶段与推论对全部 $\delta < \kappa + \theta$ 的否定，精确稳定阶恰好为
$$\operatorname{Stab}(G_{\kappa,\theta}) = \kappa + \theta. \qquad \blacksquare$$

---

## 3. 特化：$\kappa = \theta = \aleph_1$

取 $\kappa = \theta = \aleph_1$：此时满足 $\mu < \aleph_1$ 的无穷正则基数仅有 $\mu = \aleph_0$，于是
$$G_{\aleph_1, \aleph_1}(X) = \mathcal{P}_{<\omega_1}(X) \;\sqcup\; \bigl(X^\omega / {\equiv_{\mathrm{fin}}}\bigr),$$
由上述主定理立即给出其精确稳定阶为
$$\operatorname{Stab}(G_{\aleph_1, \aleph_1}) = \omega_1 + \omega_1 = \omega_1 \cdot 2.$$

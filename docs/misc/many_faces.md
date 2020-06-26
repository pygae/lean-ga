# The Many Faces of Geometric Algebra

> This file can be previewed with rendered mathematical formulas [here](https://stackedit.io/viewer#!url=https://raw.githubusercontent.com/pygae/lean-ga/master/docs/misc/many_faces.md).

Geometric Algebra (GA) or Clifford Algebra can be defined in many ways. We summarize the definitions here to inspire proper ways to formalize GA.

Some definitions are very elementary but hard to make rigorous. Some may seem rigorous but still hard to formalize. Some are very rigorous and can be formalized but fail to remain intuitive or elegant.

<del>Definitions are grouped by similarity. The definitions in the same group would have subtle yet important differences, that's why they deserve to be listed here.</del>

Definitions are mostly direct quotes from the source, with slight modifications for readability or brevity.

> The following are work-in-progress and not necessarily well organized.

### Lynn

> source: [All Hail Geometric Algebra!](https://crypto.stanford.edu/~blynn/haskell/ga.html) by [Ben Lynn](https://crypto.stanford.edu/~blynn/)

We can trivially define a product with nice properties on any set: just take [the free monoid](https://en.wikipedia.org/wiki/Free_monoid). Similarly, we can define a vector product with nice properties thanks to [free algebras](https://en.wikipedia.org/wiki/Free_algebra).

By constraining our free algebra with one simple relation, we obtain the vaunted geometric algebra. We define the geometric product by subjecting the free product to the following constraint: for any vector $\mathbf{v}$,

$$ \mathbf{v v} = \mathbf{v} \cdot \mathbf{v}$$

We could [generalize by replacing the dot product with any quadratic form, and by considering any vector space over any field](https://en.wikipedia.org/wiki/Geometric_algebra), but we focus on the standard dot product on $\mathbb{R}^{n},$ where the resulting geometric algebra is denoted $\mathbb{G}^{n}$

We could have instead written $\mathbf{v}^{2}=|\mathbf{v}|^{2},$ but this hides our need for the [polarization identity](https://en.wikipedia.org/wiki/Polarization_identity):

$$
\mathbf{u} \cdot \mathbf{v}=\frac{1}{2}((\mathbf{u}+\mathbf{v}) \cdot(\mathbf{u}+\mathbf{v})-\mathbf{u} \cdot \mathbf{u}-\mathbf{v} \cdot \mathbf{v})
$$

From our constraint, this is:

$$
\mathbf{u} \cdot \mathbf{v}=\frac{1}{2}\left((\mathbf{u}+\mathbf{v})^{2}-\mathbf{u}^{2}-\mathbf{v}^{2}\right)
$$

By elementary algebra, this implies:

$$
\mathbf{u} \cdot \mathbf{v}=\frac{1}{2}(\mathbf{u} \mathbf{v}+\mathbf{v} \mathbf{u})
$$

Hence when $\mathbf{u}$ and $\mathbf{v}$ are orthogonal, we have $\mathbf{u v}=-\mathbf{v u}$ .

### Chisolm 2012

A geometric algebra is a set $\mathcal{G}$ with two composition laws, addition and multiplication (also called the geometric product$),$ that obey these axioms.

Axiom 1. $\mathcal{G}$ is a ring with unit. The additive identity is called 0 and the multiplicative identity is called 1.

Axiom 2. $\mathcal{G}$ contains a field $\mathcal{G}_0$ of characteristic zero which includes 0 and 1.

Axiom 3. $\mathcal{G}$ contains a subset $\mathcal{G}_1$ closed under addition, and $\lambda \in \mathcal{G}_0$, $v \in \mathcal{G}_1$ implies $\lambda v = v \lambda \in \mathcal{G}_1$.

Axiom 4. The square of every vector is a scalar.

<del>Axiom 5. The inner product is nondegenerate.</del>

Axiom 6. If $\mathcal{G}_0 = \mathcal{G}_1$, then $\mathcal{G} = \mathcal{G}_0$. Otherwise,  $\mathcal{G}$ is the direct sum of all the $\mathcal{G}_r$.

For each $r$, let the grade operator $\left< \right>_r : \mathcal{G} \to \mathcal{G}_r$ project each $A \in \mathcal{G}$ onto its unique grade-$r$ component.
Then
(a) $A$ is an $r$-vector iff $A = \left<A\right>_r$.
(b) $\left<A+B\right>_r$ = $\left<A\right>_r$ + $\left<B\right>_r$.
(c) $\left< \lambda A \right>_r$ = $\left< A \lambda \right>_r$ = $\lambda \left<A\right>_r$.
(d) $\left<\left<A\right>_r\right>_s = <\left<A\right>_r\delta_{rs}$. (Thus the $\left< \right>_r$ are independent projection operators.)
(e) $\sum_r \left<A\right>_r = A$ for any $A \in \mathcal{G}$. (Thus the $\left< \right>_r$ are a complete set of projection operators.)
(f) $\left<A\right>_r = 0$ if $r \lt 0$ for all $A \in \mathcal{G}$.
Because we take the scalar part of multivectors so often, I will let $\left<A\right>$ mean $\left<A\right>_0$.

### Buchholz 2005

> Source: Chapter 2 Clifford Algebra in [A Theory of Neural Computation
with Clifford Algebras](https://macau.uni-kiel.de/servlets/MCRFileNodeServlet/dissertation_derivate_00001402/d1402.pdf) by Sven Buchholz. See also [the full version](./buchholz2005.md).

#### Definition 2.16 (Clifford Algebra)

Let $(\mathrm{X}, \mathrm{Q})$ be an arbitrary finite dimensional real quadratic space and let $\mathcal{A}$ be a real associative algebra with identity. Furthermore, let
$\alpha: \mathbb{R} \rightarrow \mathcal{A}$ and $v: \mathrm{X} \rightarrow \mathcal{A}$ be linear injections such that
(i) $\mathcal{A}$ is generated as an algebra by its distinct subspaces $\{v(v) \mid v \in X\}$ and $\{\alpha(a) \mid a \in \mathbb{R}\}$
(ii) $\forall v \in X:(v(v))^{2}=\alpha(Q(v))$

Then $\mathcal{A}$ is said to be a Clifford algebra for $(\mathrm{X}, \mathrm{Q})$. The elements of a Clifford algebra are
called multivectors. The product of a Clifford algebra is named geometric product. The signature of the quadratic space is also the signature of the algebra.

### Clifford 1882

> Source: 14.1 Clifford's original defintion in **Clifford Algebra in Clifford Algebras and Spinors** by P. Lounesto

Grassmann's exterior algebra $\wedge \mathbb{R}^{n}$ of the linear space $\mathbb{R}^{n}$ is an associative algebra of dimension $2^{n} .$ In terms of a basis $\left\{\mathbf{e}_{1}, \mathbf{e}_{2}, \ldots, \mathbf{e}_{n}\right\}$ for $\mathbb{R}^{n}$ the exterior algebra $\wedge \mathbb{R}^{n}$ has a basis

$$

\begin{array}{l}
1 \\
\mathbf{e}_{1}, \mathbf{e}_{2}, \ldots, \mathbf{e}_{n} \\
\mathbf{e}_{1} \wedge \mathbf{e}_{2}, \mathbf{e}_{1} \wedge \mathbf{e}_{3}, \ldots, \mathbf{e}_{1} \wedge \mathbf{e}_{n}, \mathbf{e}_{2} \wedge \mathbf{e}_{3}, \ldots, \mathbf{e}_{n-1} \wedge \mathbf{e}_{n} \\
\vdots \\
\mathbf{e}_{1} \wedge \mathbf{e}_{2} \wedge \ldots \wedge \mathbf{e}_{n}
\end{array}
$$

The exterior algebra has a unity 1 and satisfies the multiplication rules
$$
\begin{array}{l}
\mathbf{e}_{i} \wedge \mathbf{e}_{j}=-\mathbf{e}_{j} \wedge \mathbf{e}_{i} \quad \text { for } \quad i \neq j \\
\mathbf{e}_{i} \wedge \mathbf{e}_{i}=0
\end{array}
$$
Clifford 1882 kept the first rule but altered the second rule, and arrived at the multiplication rules
$$
\begin{array}{l}
\mathbf{e}_{i} \mathbf{e}_{j}=-\mathbf{e}_{j} \mathbf{e}_{i} \quad \text { for } \quad i \neq j \\
\mathbf{e}_{i} \mathbf{e}_{i}=1
\end{array}
$$
This time $\left\{\mathbf{e}_{1}, \mathbf{e}_{2}, \ldots, \mathbf{e}_{n}\right\}$ is an orthonormal basis for the positive definite Euclidean space $\mathbb{R}^{n} .$ An associative algebra of dimension $2^{n}$ so defined is the Clifford algebra $\mathcal{C} \ell_{n}$.

### Basis-free version of Clifford's definition

> Source: 14.2 Basis-free version of Clifford's definition in **Clifford Algebra in Clifford Algebras and Spinors** by P. Lounesto

Here we consider as an example the exterior algebra $\wedge \mathbb{R}^{4}$ of the 4 -dimensional real linear space $\mathbb{R}^{4}$. Provide the linear space $\mathbb{R}^{4}$ with a quadratic form
$$
Q(\mathbf{x})=x_{0}^{2}-x_{1}^{2}-x_{2}^{2}-x_{3}^{2}
$$
and associate to $Q$ the symmetric bilinear form
$$
\langle\mathbf{x}, \mathbf{y}\rangle=\frac{1}{2}[Q(\mathbf{x}+\mathbf{y})-Q(\mathbf{x})-Q(\mathbf{y})]
$$
This makes $\mathbb{R}^{4}$ isometric with the Minkowski space-time $\mathbb{R}^{1,3}$. Then define the left contraction $u \mathrm{J} v \in \wedge \mathbb{R}^{1,3}$ by
(a) $\mathbf{x}\rfloor\mathbf{y}=\langle\mathbf{x}, \mathbf{y}\rangle$
(b) $\mathbf{x}\rfloor(u \wedge v)=(\mathbf{x}\rfloor u) \wedge v + \hat{u} \wedge(\mathbf{x} \rfloor v)$
(c) $(u \wedge v)\rfloor w=u\rfloor(v \perp w)$

for $\mathbf{x}, \mathbf{y} \in \mathbb{R}^{1,3}$ and $u, v, w \in \wedge \mathbb{R}^{1,3}$, where $\hat{u}$ is the grade involute of $u \in \bigwedge V$, defined for a k-vector $u \in \bigwedge^k V$ by $\hat{u} = (-1)^k u$

The identity (b) says that $x$ operates like a derivation and the identity (c) makes $\bigwedge \mathbb{R}^{1,3}$ a left module over $\bigwedge \mathbb{R}^{1,3}$ Then introduce the Clifford product of $\mathbf{x} \in \mathbb{R}^{1,3}$ and $u \in \bigwedge \mathbb{R}^{1,3}$ by the formula
$$
\mathbf{x} u = \mathbf{x} \rfloor u + \mathbf{x} \wedge u
$$

and extend this product by linearity and associativity to all of $\bigwedge \mathbb{R}^{1,3}$. Provided with the Clifford product (the linear space underlying) the exterior algebra $\bigwedge \mathbb{R}^{1,3}$ becomes the Clifford algebra $\mathcal{C} \ell_{1,3}$

### Definition by generators and relations

> Source: 14.3 Definition by generators and relations in **Clifford Algebra in Clifford Algebras and Spinors** by P. Lounesto

The following definition is favored by physicists. It is suitable for non-degenerate quadratic forms, especially the real quadratic spaces $\mathbb{R}^{p, q}$.

Definition. An associative algebra over $\mathbb{F}$ with unity 1 is the Clifford algebra $\mathcal{C} \ell(Q)$ of a non-degenerate $Q$ on $V$ if it contains $V$ and $\mathbb{F}=\mathbb{F} \cdot 1$ as distinct subspaces so that
(1) $\mathbf{x}^{2}=Q(\mathbf{x})$ for any $\mathbf{x} \in V$
(2) $V$ generates $\mathcal{C} \ell(Q)$ as an algebra over $\mathbb{F}$
(3) $\mathcal{C} \ell(Q)$ is not generated by any proper subspace of $V$

### Universal object of quadratic algebras

> Source: 14.4 Universal object of quadratic algebras in **Clifford Algebra in Clifford Algebras and Spinors** by P. Lounesto

The Clifford algebra $\mathcal{C} \ell(Q)$ is the universal associative algebra over $\mathbb{F}$ generated by $V$ with the relations $\mathbf{x}^{2}=Q(\mathbf{x}), \mathbf{x} \in V$

Let $Q$ be the quadratic form on a linear space $V$ over a field $\mathbb{F}$, and let $A$ be an associative algebra over $\mathbb{F}$ with unity $1_{A} .$ A linear mapping $V \rightarrow A$, $\mathbf{x} \rightarrow \varphi_{\mathbf{x}}$ such that
$$
\left(\varphi_{x}\right)^{2}=Q(x) \cdot 1_{A} \quad \text { for all } x \in V
$$
is called a Clifford map.

The subalgebra of $A$ generated by $\mathbb{F}=\mathbb{F} \cdot 1_{A}$ and $V$ (or more precisely by the images of $\mathbb{F}$ and $V$ in $A$ ) will be called a quadratic algebra.

The Clifford algebra $\mathcal{C} \ell(Q)$ is a quadratic algebra with a Clifford $\operatorname{map} V \rightarrow \mathcal{C} \ell(Q), \quad \mathbf{x} \rightarrow \gamma_{\mathbf{x}}$ such that for any Clifford map $\varphi: V \rightarrow A$ there
exists a unique algebra homomorphism $\psi: \mathcal{C} \ell(Q) \rightarrow A$ making the following diagram commutative:
$$
\begin{array}{c}
V \stackrel{\gamma}{\longrightarrow} \mathcal{C} \ell(Q) \\
\varphi \searrow \quad \downarrow \psi \\
\quad A
\end{array} \quad \varphi_{\mathbf{x}}=\psi\left(\gamma_{\mathbf{x}}\right)
$$
This definition says that all Clifford maps may be obtained from $\gamma: V \rightarrow \mathcal{C} \ell(Q)$ which is thereby universal.

### Clifford algebra as a quotient of the tensor algebra

> Source: 14.5 Clifford algebra as a quotient of the tensor algebra in **Clifford Algebra in Clifford Algebras and Spinors** by P. Lounesto

Chevalley 1954 p. 37 constructs the Clifford algebra $\mathcal{C} \ell(Q)$ as the quotient algebra $\otimes V / I(Q)$ of the tensor algebra $\otimes V$ with respect to the two-sided ideal $I(Q)$ generated by the elements $\mathbf{x} \otimes \mathbf{x}-Q(\mathbf{x})$ where $\mathbf{x} \in V .$ See also $N .$ Bourbaki 1959 p. 139 and $T . Y .$ Lam 1973 p. $103 .$ The tensor algebra approach gives a proof of existence by construction - suitable for an algebraist who is interested in rapid access to the main properties of Clifford algebras over commutative rings.

In characteristic zero we may avoid quotient structures by making the exterior algebra $\bigwedge V$ concrete as the subspace of antisymmetric tensors in $\otimes V .$ For example, if $\mathbf{x}, \mathbf{y} \in V,$ then $\mathbf{x} \wedge \mathbf{y}=\frac{1}{2}(\mathbf{x} \otimes \mathbf{y}-\mathbf{y} \otimes \mathbf{x}) \in \bigwedge^{2} V .$

More generally, a simple $k$ -vector $\mathbf{x}_{1} \wedge \mathbf{x}_{2} \wedge \ldots \wedge \mathbf{x}_{k}$ is identified with
$$
Alt\left(\mathbf{x}_{1} \otimes \mathbf{x}_{2} \otimes \ldots \otimes \mathbf{x}_{k}\right)=\frac{1}{k !} \sum_{\pi} \operatorname{sign}(\pi) \mathbf{x}_{\pi(1)} \otimes \mathbf{x}_{\pi(2)} \otimes \ldots \otimes \mathbf{x}_{\pi(k)}
$$
where the linear operator $Alt: \otimes V \rightarrow \wedge V$, called alternation, is a projection operator $Alt(\bigotimes V)=\bigwedge V$ satisfying $u \wedge v=Alt(u \otimes v)$.

Similarly, we may obtain an isomorphism of linear spaces $\wedge V \rightarrow \mathcal{C} \ell(Q)$ by identifying simple $k$ -vectors with antisymmetrized Clifford products

$$
\mathbf{x}_{1} \wedge \mathbf{x}_{2} \wedge \ldots \wedge \mathbf{x}_{k} \rightarrow \mathbf{x}_{1} \dot{\wedge} \mathbf{x}_{2} \dot{\wedge} \ldots \dot{\wedge} \mathbf{x}_{k}=\frac{1}{k !} \sum_{\pi} \operatorname{sign}(\pi) \mathbf{x}_{\pi(1)} \mathbf{x}_{\pi(2)} \ldots \mathbf{x}_{\pi(k)}
$$

thus splitting the Clifford algebra $\mathcal{C} \ell(Q)$ into fixed subspaces of $k$ -vectors $\bigwedge^{k} V \subset \mathcal{C} \ell(Q)$. Any orthogonal basis $\mathbf{e}_{1}, \mathbf{e}_{2}, \ldots, \mathbf{e}_{n}$ of $V$ gives a correspon-
dence
$$
\mathbf{e}_{i_{1}} \wedge \mathbf{e}_{i_{2}} \wedge \ldots \wedge \mathbf{e}_{i_{k}} \rightarrow \mathbf{e}_{i_{1}} \dot{\wedge} \mathbf{e}_{i_{2}} \dot{\wedge} \ldots \dot{\wedge} \mathbf{e}_{i_{k}}=\mathbf{e}_{i_{1}} \mathbf{e}_{i_{2}} \ldots \mathbf{e}_{i_{k}}
$$
of bases for $\wedge V$ and $\mathcal{C} \ell(Q)$

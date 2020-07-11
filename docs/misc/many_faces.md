# The Many Faces of Geometric Algebra

> This file can be previewed with rendered mathematical formulas [here](https://stackedit.io/viewer#!url=https://raw.githubusercontent.com/pygae/lean-ga/master/docs/misc/many_faces.md).

Geometric Algebra (GA) or Clifford Algebra can be defined in many ways. We summarize the definitions here to inspire proper ways to formalize GA.

Some definitions are very elementary but hard to make rigorous. Some may seem rigorous but still hard to formalize. Some are very rigorous and can be formalized but fail to remain intuitive or elegant.

<del>Definitions are grouped by similarity. The definitions in the same group would have subtle yet important differences, that's why they deserve to be listed here.</del>

Definitions are mostly direct quotes from the source, with slight modifications for readability or brevity.

> The following are work-in-progress and not necessarily well organized.

### Hestenes 1984

> Source: Hestenes, David, and Garret Sobczyk. Clifford algebra to geometric calculus: a unified language for mathematics and physics. Vol. 5. Springer Science & Business Media, 2012.

An element of the Geometric Algebra $\mathscr{G}$ will be called a multivector. We assume that $\mathscr{G}$ is algebraically closed, that is, that the sum or product of any pair of multivectors is a unique multivector. The geometric sum and product of multivectors $A, B, C, \ldots$ have the following properties:

Addition is commutative;
$$
A+B=B+A
$$
Addition and multiplication are associative;
$$
\begin{array}{l}
(A+B)+C=A+(B+C) \\
(A B) C=A(B C)
\end{array}
$$
Multiplication is distributive with respect to addition;
$$
A(B+C)=A B+A C
$$
$$
(B+C) A=B A+C A
$$
There exist unique additive and multiplicative identities 0 and 1
$$
\begin{array}{l}
A+0=A \\
1 A=A
\end{array}
$$
Every multivector $A$ has a unique additive inverse $-A$
$$
A+(-A)=0
$$

Geometric algebra is set apart from other associatve algebras by a few additional axioms which classify multivectors into different types or, as we shall say, grades. We assume that any multivector $A$ can be written as the sum
$$
A=\langle A\rangle_{0}+\langle A\rangle_{1}+\langle A\rangle_{2}+\cdots=\sum_{r}\langle A\rangle_{r}
$$

The quantity $\langle A\rangle_{r}$ is called the $r$ -vector part of $A .$ If $A=\langle A\rangle_{r}$ for some positive integer $r,$ then $A$ is said to be homogeneous of grade $r$ and will be called an $r$ -vector. The terms scalar, vector, bivector, trivector,.... are often used as alternatives to the terms 0 -vector, 1 -vector, 2 -vector, 3 -vector, $\ldots$ respectively. The grade operator $\langle\ldots .\rangle_{r}$ enjoys the properties

$$
\begin{array}{l}
\langle A+B\rangle_{r}=\langle A\rangle_{r}+\langle B\rangle_{r} \\
\langle\lambda A\rangle_{r}=\lambda\langle A\rangle_{r}=\langle A\rangle_{r} \lambda, \quad \text { if } \lambda=\langle\lambda\rangle_{0} \\
\left\langle\langle A\rangle_{r}\right\rangle_{r}=\langle A\rangle_{r}
\end{array}
$$

Axioms (1.10) and (1.11) (i.e. the 1st one and 2nd one immediately above) imply that the space $\mathscr{G}^{r}$ of all $r$ -vectors is a linear subspace of $\mathscr{G},$ and, indeed, that $\mathscr{G}$ itself is a linear space. Axiom (1.11) also implies that the scalars compose a commutative subalgebra of $\mathscr{G}$. Without further ado, we assume that the space $\mathscr{G}^{0}$ of all scalars is identical with the set of real numbers. As argued elsewhere in this book, we regard any wider definition of the scalars (for example as the complex numbers) to be entirely unnecessary and, indeed, inimical to the purposes of geometric algebra.

Equation (1.12) (i.e. the 3rd one immediately above) exhibits the characteristic property of a projection operator, so $\langle A\rangle_{r}$ can be regarded as the projection of $A$ into the space $\mathscr{G}^{r}$. Actually, (1.12) need not be regarded as an axiom, because it can be derived with the help of our remaining axioms which fix the relations among multivectors of different grade. Multiplication of vectors is related to scalars by the assumption that the 'square' of any nonzero vector $a$ is equal to the square of a unique positive scalar lal called the magnitude of $a$, that is

$$
A_{r}=a_{1} a_{2} \ldots a_{r}
$$
where
$$
\begin{array}{c}
a_{j} a_{k}=-a_{k} a_{j} \\
\text { for } j, k=1,2, \dots, r, \text { and } j \neq k
\end{array}
$$
As a final axiom, we assume that for every nonzero $r$ -blade $A_{r},$ there exists a nonzero vector $a$ in $\mathscr{G}$ such that $A_{r} a$ is an $(r+1)$ -blade. This guarantees the existence of nontrivial blades of every finite grade. In fact, it implies that each $\mathscr{G}$ r and, of course, all of $\mathscr{G}$ is a linear space of infinite dimension. This leads ultimately to delicate questions of convergence for homogeneous multivectors with infinite grade. But we will not be concerned with such questions in this book.

### Lawson 1989

> Source: H.B. Lawson and M.-L. Michelsohn. Spin Geometry. Princeton University Press, Princeton NJ, 1989. But the quote and the comments come from Doran 1994.

One starts with a vector space $V$ over a commutative field $k$, and supposes that $q$ is a quadratic form on $V$. The tensor algebra of $V$ is defined as
$$
\mathcal{T}(V)=\sum_{r=0}^{\infty} \otimes^{r} V
$$
where $\otimes$ is the tensor product. One next defines an ideal $\mathcal{I}_{q}(V)$ in $\mathcal{T}(V)$ generated by all elements of the form $v \otimes v+q(v) 1$ for $v \in V$. The Clifford algebra is then defined as the quotient
$$
C l(V, q) \equiv \mathcal{T}(V) / \mathcal{I}_{q}(V)
$$

This definition is mathematically correct, but has a number of drawbacks:

1. The definition involves the tensor product, $\otimes$, which has to be defined initially.
2. The definition uses two concepts, tensor algebras and ideals, which are irrelevant to the properties of the resultant geometric algebra.
3. Deriving the essential properties of the Clifford algebra from this definition requires further work, and none of these properties are intuitively obvious from the axioms.
4. The definition is completely useless for introducing geometric algebra to a physicist or an engineer. It contains too many concepts that are the preserve of pure mathematics.

The above considerations lead us propose the following principle:
The axioms of an algebraic system should deal directly with the objects
of interest.

That is to say, the axioms should offer some intuitive feel of the properties of the system they are defining.

### Doran 1994

> Source: Doran, Christopher John Leslie. Geometric algebra and its application to mathematical physics. Diss. University of Cambridge, 1994. http://geometry.mrao.cam.ac.uk/wp-content/uploads/2015/02/DoranThesis.pdf

A geometric algebra $\mathcal{G}$ is a graded linear space, the elements of which are called multivectors. The grade- 0 elements are called scalars and are identified with the field of real numbers (we will have no cause to consider a geometric algebra over the complex field). The grade-1 elements are called vectors, and can be thought of as directed line segments. The elements of $\mathcal{G}$ are defined to have an addition, and each graded subspace is closed under this. A product is also defined which is associative and distributive, though non-commutative (except for multiplication by a scalar). The final axiom (which distinguishes a geometric algebra from other associative algebras) is that the square of any vector is a scalar. Given two vectors, $a$ and $b$, we find that
$$
\begin{aligned}
(a+b)^{2} &=(a+b)(a+b) \\
&=a^{2}+(a b+b a)+b^{2}
\end{aligned}
$$
It follows that
$$
a b + b a = (a +b)^{2} - a^{2} - b^{2}
$$

and hence that $(a b+b a)$ is also a scalar. The geometric product of 2 vectors $a, b$ can therefore be decomposed as
$$
a b=a \cdot b+a \wedge b
$$
where
$$
a \cdot b \equiv \frac{1}{2}(a b + b a)
$$
is the standard scalar, or inner, product (a real scalar), and
$$
a \wedge b \equiv \frac{1}{2}(a b - b a)
$$
is the antisymmetric outer product of two vectors, originally introduced by Grassmann.

### Lynn

> Source: [All Hail Geometric Algebra!](https://crypto.stanford.edu/~blynn/haskell/ga.html) by [Ben Lynn](https://crypto.stanford.edu/~blynn/)

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

Let $(\mathrm{X}, \mathrm{Q})$ be an arbitrary finite dimensional real quadratic space and let $\mathcal{A}$ be a real associative algebra with identity. Furthermore, let
$\alpha: \mathbb{R} \rightarrow \mathcal{A}$ and $v: \mathrm{X} \rightarrow \mathcal{A}$ be linear injections such that
(i) $\mathcal{A}$ is generated as an algebra by its distinct subspaces $\{v(v) \mid v \in X\}$ and $\{\alpha(a) \mid a \in \mathbb{R}\}$
(ii) $\forall v \in X:(v(v))^{2}=\alpha(Q(v))$

Then $\mathcal{A}$ is said to be a Clifford algebra for $(\mathrm{X}, \mathrm{Q})$. The elements of a Clifford algebra are
called multivectors. The product of a Clifford algebra is named geometric product. The signature of the quadratic space is also the signature of the algebra.

### Clifford 1882

> Source: 14.1 Clifford's original defintion in **Clifford Algebras and Spinors** by P. Lounesto

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

> Source: 14.2 Basis-free version of Clifford's definition in **Clifford Algebras and Spinors** by P. Lounesto

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

> Source: 14.3 Definition by generators and relations in **Clifford Algebras and Spinors** by P. Lounesto

The following definition is favored by physicists. It is suitable for non-degenerate quadratic forms, especially the real quadratic spaces $\mathbb{R}^{p, q}$.

Definition. An associative algebra over $\mathbb{F}$ with unity 1 is the Clifford algebra $\mathcal{C} \ell(Q)$ of a non-degenerate $Q$ on $V$ if it contains $V$ and $\mathbb{F}=\mathbb{F} \cdot 1$ as distinct subspaces so that
(1) $\mathbf{x}^{2}=Q(\mathbf{x})$ for any $\mathbf{x} \in V$
(2) $V$ generates $\mathcal{C} \ell(Q)$ as an algebra over $\mathbb{F}$
(3) $\mathcal{C} \ell(Q)$ is not generated by any proper subspace of $V$

### Universal object of quadratic algebras

> Source: 14.4 Universal object of quadratic algebras in **Clifford Algebras and Spinors** by P. Lounesto

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

> Source: 14.5 Clifford algebra as a quotient of the tensor algebra in **Clifford Algebras and Spinors** by P. Lounesto

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

### Mother Algebra

> Source: Doran, Chris, David Hestenes, Frank Sommen, and Nadine Van Acker. "Lie groups as spin groups." Journal of Mathematical Physics 34, no. 8 (1993): 3642-3669.

> Grassmannian argue that GA is more fundamental than CA, because it makes no assumptions about a metric on the vector space that generates it. On the contrary, Cliffordians argue that CA is more fundamental than GA, because it contains GA as a subalgebra.

To reconcile the contemporary views of Grassmann and Clifford algebras, we begin with a standard definition of the Grassmann algebra $\Lambda_{n}=\Lambda\left(\mathcal{V}^{n}\right)$ of an $n$ -dimensional real vector space $\mathcal{V}^{n} .$ This associative algebra is generated from $\mathcal{V}^{n}$ by Grassmann's outer product under the assumption that the product of several vectors vanishes if and only if the vectors are linearly dependent. With the notation in Eq. (2.1) for the outer product, the outer product
$$
v_{1} \wedge v_{2} \wedge \ldots \wedge v_{k}
$$
of $k$ linearly independent vectors is called a $k$ -blade, and a linear combination of $k$ -blades is called a $k$ -vector. The set of all $k$ -vectors is a linear space
$$
\Lambda_{n}^{k}=\Lambda^{k}\left(\mathcal{V}^{n}\right)
$$
with dimension given by the binomial coefficient $\left(\begin{array}{l}n \\ k\end{array}\right) .$ With the notations $\Lambda_{n}^{1}=\mathcal{V}^{n}$ and $\Lambda_{n}^{0}=\Re$ for the real scalars, the entire Grassmann algebra can be expressed as a $2^{n}-$ dimensional linear space
$$
\Lambda_{n}=\sum_{k=0}^{n} \Lambda_{n}^{k}
$$
This completes our description of Grassmann's "exterior algebra," but ore mathematical structure is needed for applications. Standard practice is to introduce this structure by defining the space of linear forms on $\Lambda_{n} .$ However, we think there is a better procedure which is closer to Grassmann's original approach.

We introduce an $n$ -dimensional vector space $\mathcal{V}^{n *}$ dual to $\mathcal{V}^{n}$ with "duality" defined by the following condition: If $\left\{w_{i}\right\}$ is a basis for $\mathcal{V}^{n},$ then there is a basis $\left\{w_{i}^{*}\right\}$ for $\mathcal{V}^{n *}$ defining unique scalar-valued mappings denoted by

$$
\mathcal{V}_{i}^{n *} \cdot \mathcal{V}_{j}^{n}=\frac{1}{2} \delta_{i, j}, \quad \text { for } i, j=1,2, \ldots, n
$$
The dual space generates its own Grassmann algebra
$$
\Lambda^{*}\left(\mathcal{V}^{n}\right)=\Lambda_{n}^{*}=\sum_{k=0}^{n} \Lambda_{n}^{k^{*}}
$$
The inner product (2.5) can be extended to a product between $k$ -vectors, so that each $k$ vector in $\mathcal{V}^{n *}$ determines a unique $k$ -form on $\mathcal{V}^{n},$ that is, a linear mapping of $\Lambda_{n}^{k}$ into the scalars. In other words, $\Lambda_{n}^{k^{*}}$ can be regarded as the linear space of all $k$ -forms.

This much is equivalent to the standard theory of linear forms, though Eq. (2.5) is not a standard notation defining one-forms. The notation has been adopted here so Eq. (2.5) can be interpreted as Grassmann's inner product, and $\Lambda_{n}$ and $\Lambda_{n}^{*}$ can be imbedded in a single geometric algebra with a single central product defined by Eq. $(2.1) .$ One way to do that is by identifying $\Lambda_{n}$ with $\Lambda_{n}^{*}$ but then Eq. (2.5) defines a nondegenerate metric on $\mathcal{V}^{n},$ and Grassmannians claim that that is a loss in generality. Cliffordians counter that the loss is illusory, for the interpretation of Eq. (2.5) as a metric tensor is not necessary if it is not wanted; with one variable held fixed, it can equally well be interpreted as a "contraction" defining a linear form. Be that as it may, there really is an advantage to keeping $\Lambda_{n}$ and $\Lambda_{n}^{*}$ distinct, in fact maximally distinct, as we see next. We turn $\Lambda_{n}$ and $\Lambda_{n}^{*}$ into geometric algebras by defining the inner products
$$
w_{i} \cdot w_{j}=0 \quad \text { and } \quad w_{i}^{*} \cdot w_{j}^{*}=0
$$
so Eq. (2.1) gives
$$
w_{i} \wedge w_{j}=w_{i} w_{j}=-w_{j} w_{i} \quad \text { and } \quad w_{i}^{*} \wedge w_{j}^{*}=w_{i}^{*} w_{j}^{*}=-w_{j}^{*} w_{i}^{*}
$$
Also we assume that the $w_{i}$ and the $w_{i}^{*}$ are linearly independent vectors spanning a $2 n-$ dimensional vector space
$$
\mathcal{R}^{n, n}=\mathcal{V}^{n} \otimes \mathcal{V}^{n *}
$$
with an inner product defined by Eqs. (2.5) and $(2.7 \mathrm{a}) .$ This generates a $2^{2 n}$ -dimensional geometric algebra which we denote by
$$
\mathcal{R}_{n, n}=\mathcal{G}\left(\mathcal{R}^{n, n}\right)=\sum_{k=0}^{n} \mathcal{R}_{n, n}^{k}
$$
with $k$ -vector subspaces $\mathcal{R}_{n, n}^{k}=\mathcal{G}^{k}\left(\mathcal{R}^{n, n}\right)=\mathcal{G}^{k}\left(\mathcal{R}_{n, n}\right) .$ Anticipating the conclusion that it will prove to be an ideal tool for characterizing linear and multilinear functions on an $n$ -dimensional vector space, let us refer to $\mathcal{R}_{n, n}$ as the mother algebra.

### Geometric Algebra Coordinate Frames

> Source: Eid, A.H.: An extended implementation framework for geometric algebra operations on systems of coordinate frames of arbitrary signature. Adv. Appl. Clifford Algebras 28(1), 16 (2018)
> But the quoted construction here (which is better summarized) came from Eid, Ahmad Hosny. "A Low-Memory Time-Efficient Implementation of Outermorphisms for Higher-Dimensional Geometric Algebras." Advances in Applied Clifford Algebras 30.2 (2020): 1-20.

A GACF is completely defined using two components:

1. An ordered set of $n$ basis vectors $\boldsymbol{F}_{1}^{n}=\left\langle f_{0}, f_{1}, \ldots, f_{n-1}\right\rangle$ defining the dimensions of the GACF's base vector space.
2. A symmetric real bilinear form $\mathbf{B}: \boldsymbol{F}_{1}^{n} \times \boldsymbol{F}_{1}^{n} \rightarrow \mathbb{R}, \mathbf{B}\left(f_{i}, f_{j}\right)=\mathbf{B}\left(f_{j}, f_{i}\right)=$
$f_{i} \cdot f_{j}$ determining the inner product of basis vectors and given by a symmetric $n \times n$ bilinear form matrix $\mathbf{A}_{\mathcal{F}}=\left[f_{i} \cdot f_{j}\right]$ called the Inner Product Matrix (IPM) of the GACF.

A GACF can be of two types: orthogonal or non-orthogonal. The IPM of an orthogonal GACF is diagonal $\left(f_{i} \cdot f_{i}=d_{i}, f_{i} \cdot f_{j}=0 \forall i \neq j\right)$ while the IPM of a non-orthogonal GACF is non-diagonal $\left(f_{i} \cdot f_{j}=f_{j} \cdot f_{i}=b_{i j} \exists i \neq j: b_{i j} \neq 0\right)$

A Euclidean GACF is orthogonal with all $d_{i}=1$ We construct three additional components to serve GA computations within the GACF:

1. The ordered set of $2^{n}$ basis blades of all grades $\boldsymbol{F}^{n}=\left\langle F_{0}, F_{1}, \cdots, F_{2^{n}-1}\right\rangle$ This set is automatically determined by the set of basis vectors $\boldsymbol{F}_{1}^{n}$. This component is independent of the metric represented by $\mathbf{A}_{\mathcal{F}}$ as they are created using the metric-independent outer product of basis vectors in $\boldsymbol{F}_{1}^{n}$
$F_{i}=\prod_{\wedge}\left(\boldsymbol{F}_{1}^{n}, i\right)$
$=\left\{\begin{array}{ll}1, & i=0 \\ f_{m}, & i=2^{m}, m \in\{0,1, \ldots, n-1\} \\ f_{i_{1}} \wedge f_{i_{2}} \wedge \cdots \wedge f_{i_{r}}, \quad i=2^{i_{1}}+2^{i_{2}}+\cdots+2^{i_{r}} & i_{i}<i_{2}<\cdots<i_{r}\end{array}\right.$
2. The geometric product; a bilinear operator on multivectors $G_{\mathcal{F}}: \boldsymbol{F}^{n} \times$ $\boldsymbol{F}^{n} \rightarrow \mathcal{G}^{p, q}, r$ defined using the geometric product of pairs of basis blades, which are generally multivectors, $G_{\mathcal{F}}\left(F_{i}, F_{j}\right)=F_{i} F_{j}=\sum_{k=0}^{2^{n}-1} g_{k} F_{k}, g_{k} \in R$. This bilinear operator is automatically determined by the set of basis vectors $\boldsymbol{F}_{1}^{n}$ and the bilinear form $\mathbf{B}$
3. If the bilinear form is not orthogonal, a base orthogonal GACF $\mathcal{E}\left(\boldsymbol{E}_{1}^{n}, \mathbf{A}_{\mathcal{E}}\right)$ of the same dimension is needed, in addition to an orthogonal Changeof-Basis Matrix (CBM) C. The orthogonal CBM is used to express basis vectors of $\mathcal{F}$ as linear combinations of basis vectors of $\mathcal{E},$ and defines a Change of Basis Automorphism (CBA) $\overline{\mathbf{C}}$ that can invariantly transform linear operations on multivectors between $\mathcal{E}$ and $\mathcal{F}$. We can either define $\mathbf{C}$ implicitly from the orthonormal eigen vectors of $\mathbf{A}_{\mathcal{F}},$ or the user can directly supply $\mathcal{E}\left(\boldsymbol{E}_{1}^{n}, \mathbf{A}_{\mathcal{E}}\right)$ and $\mathbf{C}$ to define the IPM of $\mathcal{F}$. The details of this component are described in [8] (Eid, A.H.: An extended implementation framework for geometric algebra operations on systems of coordinate frames of arbitrary signature. Adv. Appl. Clifford Algebras 28(1), 16 (2018) )

Using these five components any multivector $X=\sum_{i=0}^{2^{n}-1} x_{i} F_{i}, x_{i} \in \mathbb{R}$ can be represented by a column vector of real coefficients $\left[x_{i}\right]_{\mathcal{F}} .$ All common operations on multivectors are easily encoded using this framework for both orthogonal and non-orthogonal GACFs. Such operations include common bilinear products, outermorphisms, and versor transformations, as detailed in [8],

### Macdonald 2015

> Source: Macdonald, Alan. "A survey of geometric algebra and geometric calculus." Advances in Applied Clifford Algebras 27.1 (2017): 853-891. http://www.faculty.luther.edu/~macdonal/GA&GC.pdf

The geometric algebra $\mathbb{G}^{n} .$ The geometric algebra $\mathbb{G}^{n}$ is an extension of the inner product space $\mathbb{R}^{n},$ with more objects and operations. First, $\mathbb{G}^{n}$ is an associative algebra with a $1 .$ That is, it is a vector space with a product satisfying properties $\mathrm{G} 1-\mathrm{G} 4$ for all scalars $a$ and $A, B, C \in \mathbb{G}^{n}:$
$\mathrm{G} 1 . A(B+C)=A B+A C,(B+C) A=B A+C A$
$\mathrm{G} 2 .(a A) B=A(a B)=a(A B)$
G3. $(A B) C=A(B C)$
$\mathrm{G} 4.1 A=A 1=A$
The product is called the geometric product. It is not commutative. Members of $\mathbb{G}^{n}$ are called multivectors. This allows us to reserve the term "vector" for vectors in $\mathbb{R}^{n} .$ (They are also multivectors.) This is a convenient terminology. Vectors are denoted in lower case bold. We list two more properties.
G5. The geometric product of $\mathbb{G}^{n}$ is linked to the algebraic structure of $\mathbb{R}^{n}$ $\mathrm{by}$
$$
\mathbf{u u}=\mathbf{u} \cdot \mathbf{u}=|\mathbf{u}|^{2} \text { for all } \mathbf{u} \in \mathbb{R}^{n}
$$
This shows that nonzero vectors have an inverse in $\mathbb{G}^{n}: \mathbf{u}^{-1}=\mathbf{u} /|\mathbf{u}|^{2}$

G6. Every orthonormal basis for $\mathbb{R}^{n}$ determines a canonical basis (defined below $)$ for the vector space $\mathbb{G}^{n}$

That's it! That's the geometric algebra. We have not proved that the mathematical structure just described exists. For that, see [14] (A. Macdonald, An Elementary Construction of the Geometric Algebra. Adv. Appl.
Cliff. Alg. 12 (2002), 1-6. (Improved version: http://www.faculty.luther.edu/~macdonal/GAConstruct.pdf ).).

Before proceeding, we need Eq. (1.2) below. In the next equation, Step is a polarization identity. Verify it by multiplying out the inner product on the right side. Step (2) follows from Eq. (1.1). Verify Step (3) by multiplying out the geometric product on the left side.
$$
\begin{aligned}
\mathbf{u} \cdot \mathbf{v} & \stackrel{1}{=} \frac{1}{2}((\mathbf{u}+\mathbf{v}) \cdot(\mathbf{u}+\mathbf{v})-\mathbf{u} \cdot \mathbf{u}-\mathbf{v} \cdot \mathbf{v}) \\
& \stackrel{2}{=} \frac{1}{2}\left((\mathbf{u}+\mathbf{v})^{2}-\mathbf{u}^{2}-\mathbf{v}^{2}\right) \stackrel{3}{=} \frac{1}{2}(\mathbf{u v}+\mathbf{v} \mathbf{u})
\end{aligned}
$$
If $\mathbf{u}$ and $\mathbf{v}$ are orthogonal, then this gives
$$
\mathbf{v} \mathbf{u}=-\mathbf{u v} . \quad(\mathbf{u}, \mathbf{v} \text { orthogonal })
$$
$$
\text { Example: }\left(1+\mathbf{e}_{1} \mathbf{e}_{2}\right)\left(\mathbf{e}_{1}-2 \mathbf{e}_{2}\right)=-\mathbf{e}_{1}-3 \mathbf{e}_{2}
$$
If $\mathbf{u}$ and $\mathbf{v}$ are orthogonal and nonzero, then from Eq. (1.2)
$$
(\mathbf{u v})^{2}=\mathbf{u v u v}=-\mathbf{u u v v}=-|\mathbf{u}|^{2}|\mathbf{v}|^{2}<0
$$
Therefore $\mathbf{u v}$ is not a scalar or a vector. It is something new.

### Elementary Construction

> Source: A. Macdonald, An Elementary Construction of the Geometric Algebra. Adv. Appl. Cliff. Alg. 12 (2002), 1-6. http://www.faculty.luther.edu/~macdonal/GAConstruct.pdf 
> The deinition in it is not actually included due to lack of generality. Here we're only interested in the desciption of the motivation to have an elementary construction and the comparisons of constructions, plus listing axioms of vector space and algebra for easy potential reference.

My goal is to provide a construction of $\mathrm{GA}(n)$ suitable for someone with only an elementary knowledge of $\mathbf{R}^{n} .$ The construction is simple, elementary, direct, and motivated. Two features of the construction help make this so. First, the construction uses only elementary properties of $\mathbf{R}^{n}$. Some constructions use more advanced mathematical structures, such as tensor products. (Our construction is compared to others in Section 7.) **The geometric algebra $\mathrm{GA}(n)$ is a fundamental mathematical structure which is part of the essence of Euclidean space. It therefore deserves a construction not using less fundamental structures than $\mathbf{R}^{n}$.**

Second, the construction is based directly upon the two fundamental identities which distinguish $\operatorname{GA}(n):$ If $e$ and $f$ are orthonormal vectors in $\mathbf{R}^{n},$ then
$$
\begin{array}{l}
e e=1 \\
e f=-f e
\end{array}
$$
Eqs.
(1) and (2) motivate our construction. $\mathrm{GA}(n)$ is a $2^{n}$ dimensional vector space containing $\mathbf{R}^{n}$ which is also an associative algebra with identity. Its vectors are called multivectors. In addition, Eqs.
(1) and (2) are satisfied. We list the vector space and algebra axioms for reference. Let $a$ and $b$ be scalars and $u, v,$ and $w$ be multivectors. Then

V1. $u+v=v+u$
V2. $(u+v)+w=u+(v+w)$
V3. $u+0=u$
V4. $u+(-u)=0$
V5. $1 u=u$
V6. $a(b u)=(a b) u$
V7. $a(u+v)=a u+a v$
V8. $(a+b) u=a u+b u$

A1. $u(v w)=(u v) w$
A2. $u(v+w)=u v+u w \quad (v+w) u=v u+w u$
A3. $(a u) v=u(a v)=a(u v)$
A4. $1 u=u 1=u$

7 Other Constructions. Emil Artin has given an elegant and simple elementary construction of $\mathrm{GA}(n)$ [2, p .186]. Our construction is better motivated and, I think, somewhat simpler.

Marcel Riesz' construction in his Maryland lectures [6, Sec. 1.2-1.4] is incomplete. Riesz introduces products of the form Eq.
(3) for orthonormal basis vectors $\left\{e_{i}\right\}$ and stipulates that $e_{i} e_{i}=1$ and $e_{i} e_{j}=-e_{j} e_{i}$ for $i \neq j .$ (Our Eqs. (1) and (2) But to show that these rules can be consistently applied, he needs something analogous to our lemma, which he does not supply. And once it is supplied, the associativity of the geometric product is trivial, as we have seen. Then Riesz's proof of the associativity in Sec. 1.3 becomes superfluous.

Ambjorn Naeve and Lars Svensson have given a construction which uses concepts from abstract algebra (rings, totally ordered sets, ideals) [5], although it could be reexpressed in more elementary terms.
R.D. Arthan has given a "minmalist" construction of the geometric algebra
[1].
Pertti Lounesto has catalogued several nonelementary constructions of $\mathrm{GA}(n)$ including those using a Grassman algebra, a tensor product, and a universal algebra [4]. **These constructions obscure the simplicity and elementary nature of the geometric algebra.**

### Bromborsky 2014

> Source: Bromborsky, Alan. "An introduction to geometric algebra and calculus." (2014).

Let $\mathcal{V}(p, q)$ be a finite dimensional vector space of signature $(p, q)^{1}$ over $\Re .$ Then $\forall a, b, c \in \mathcal{V}$ there exists a geometric product with the properties -
$$
\begin{aligned}
(a b) c &=a(b c) \\
a(b+c) &=a b+a c \\
(a+b) c &=a c+b c \\
a a & \in \Re
\end{aligned}
$$

If $a^{2} \neq 0$ then $a^{-1}=\frac{1}{a^{2}} a$.

### Perwass 2009

> Source: Perwass, Christian, et al. Geometric algebra with applications in engineering. Vol. 4. Berlin: Springer, 2009.

Let $\mathbb{R}^{p, q}$ denote a $(p+q)$ -dimensional vector space over the reals $\mathbb{R} .$ Furthermore, let a commutative scalar product be defined as $\ast : \mathbb{R}^{p, q} \times \mathbb{R}^{p, q} \rightarrow \mathbb{R}$ That is, for $\boldsymbol{a}, \boldsymbol{b} \in \mathbb{R}^{p, q}$
$$
\boldsymbol{a} * \boldsymbol{b}=\boldsymbol{b} * \boldsymbol{a} \quad \in \mathbb{R}
$$

Axiom 3.1 (Geometric Algebra)

Let $\mathbb{A}\left(\mathbb{R}^{p, q}\right)$  denote the associative algebra over the quadratic space $\left(\mathbb{R}^{p, q}, \ast\right)$ and let o denote the algebraic product.

Note that the field $\mathbb{R}$ and the vector space $\mathbb{R}^{p, q}$ can both be regarded as subspaces of $\mathbb{A}\left(\mathbb{R}^{p, q}\right)$. The algebra $\mathbb{A}\left(\mathbb{R}^{p, q}\right)$ is said to be a geometric algebra if for
$\boldsymbol{a} \in \mathbb{R}^{p, q} \subset \mathbb{A}\left(\mathbb{R}^{p, q}\right), \boldsymbol{a} \circ \boldsymbol{a}=\boldsymbol{a} \ast \boldsymbol{a}$

The geometric algebra over $\mathbb{R}^{p, q}$ is denoted by $\mathbb{G}\left(\mathbb{R}^{p, q}\right)$ or simply $\mathbb{G}_{p, q}$ and the algebra product is called the Clifford or geometric product. Although the geometric product is denoted here by $\circ$, it is represented later by juxtaposition for brevity.

In the following, all axioms of a geometric algebra are given explicitly. First of all, the elements of $\mathbb{G}_{p, q},$ which are called multivectors, satisfy the axioms of a vector space over the field $\mathbb{R}$

Axiom 3.2 The following two operations exist in $\mathbb{G}_{p, q}$ :
1. Multivector addition. For any two elements $\boldsymbol{A}, \boldsymbol{B} \in \mathbb{G}_{p, q}$ there exists an element $\boldsymbol{C}=\boldsymbol{A}+\boldsymbol{B} \in \mathbb{G}_{p, q},$ their sum.
2. Scalar multiplication. For any element $\boldsymbol{A} \in \mathbb{G}_{p, q}$ and any scalar $\alpha \in \mathbb{R}$ there exists an element $\alpha \boldsymbol{A} \in \mathbb{G}_{p, q},$ the $\alpha$ -multiple of $\boldsymbol{A}$
Axiom 3.3 (Vector Space) Let $\boldsymbol{A}, \boldsymbol{B}, \boldsymbol{C} \in \mathbb{G}_{p, q}$ and $\alpha, \beta \in \mathbb{R}$
1. Associativity of multivector addition:
$$
(\boldsymbol{A}+\boldsymbol{B})+\boldsymbol{C}=\boldsymbol{A}+(\boldsymbol{B}+\boldsymbol{C})
$$
2. Commutativity:
$$
\boldsymbol{A}+\boldsymbol{B}=\boldsymbol{B}+\boldsymbol{A}
$$
3. Identity element of addition. There exists an element $0 \in \mathbb{G}_{p, q},$ the zero element, such that
$$
A+0=A
$$
4. Associativity of scalar multiplication:
$$
\alpha(\beta \boldsymbol{A})=(\alpha \beta) \boldsymbol{A}
$$
5. Commutativity of scalar multiplication:
$$
\alpha \boldsymbol{A}=\boldsymbol{A} \alpha
$$
6. Identity element of scalar multiplication. The identity element $1 \in \mathbb{R}$ satisfies
$$
1 A=A
$$
7. Distributivity of multivector sums:
$$
\alpha(\boldsymbol{A}+\boldsymbol{B})=\alpha \boldsymbol{A}+\alpha \boldsymbol{B}
$$
8. Distributivity of scalar sums:
$$
(\alpha+\beta) \boldsymbol{A}=\alpha \boldsymbol{A}+\beta \boldsymbol{A}
$$

It follows from these axioms that for each $\boldsymbol{A} \in \mathbb{G}_{p, q}$ there exists an element $-\boldsymbol{A}:=(-1) \boldsymbol{A}$ such that
$$
\boldsymbol{A}-\boldsymbol{A}:=\boldsymbol{A}+(-\boldsymbol{A})=\boldsymbol{A}+(-1) \boldsymbol{A}=(1+(-1)) \boldsymbol{A}=0 \boldsymbol{A}=0
$$

Axiom 3.4 The axioms related to the algebraic product, i.e. the geometric product, are as follows. Let $\boldsymbol{A}, \boldsymbol{B}, \boldsymbol{C} \in \mathbb{G}_{p, q}$ and $\alpha, \beta \in \mathbb{R}$
1. The algebra is closed under the geometric product:
$$
\boldsymbol{A} \circ \boldsymbol{B} \in \mathbb{G}_{p, q}
$$
2. Associativity:
$$
(\boldsymbol{A} \circ \boldsymbol{B}) \circ \boldsymbol{C}=\boldsymbol{A} \circ(\boldsymbol{B} \circ \boldsymbol{C})
$$
3. Distributivity:
$$
\boldsymbol{A} \circ(\boldsymbol{B}+\boldsymbol{C})=\boldsymbol{A} \circ \boldsymbol{B}+\boldsymbol{A} \circ \boldsymbol{C} \quad \text { and } \quad(\boldsymbol{B}+\boldsymbol{C}) \circ \boldsymbol{A}=\boldsymbol{B} \circ \boldsymbol{A}+\boldsymbol{C} \circ \boldsymbol{A}
$$
4. Scalar multiplication:
$$
\alpha \circ \boldsymbol{A}=\boldsymbol{A} \circ \alpha=\alpha \boldsymbol{A}
$$
All axioms given so far define an associative algebra. What actually separates Clifford algebra from other algebras is the defining equation.
Axiom 3.5 Let $a \in \mathbb{R}^{p, q} \subset \mathbb{G}_{p, q} ;$ then
$$
\boldsymbol{a} \circ \boldsymbol{a}=\boldsymbol{a} * \boldsymbol{a} \in \mathbb{R}
$$
That is, the geometric product of a vector (not a multivector in general) with itself maps to an element of the field $\mathbb{R}$


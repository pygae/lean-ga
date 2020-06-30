# The Many Faces of Geometric Algebra

> This file can be previewed with rendered mathematical formulas [here](https://stackedit.io/viewer#!url=https://raw.githubusercontent.com/pygae/lean-ga/master/docs/misc/many_faces.md).

Geometric Algebra (GA) or Clifford Algebra can be defined in many ways. We summarize the definitions here to inspire proper ways to formalize GA.

Some definitions are very elementary but hard to make rigorous. Some may seem rigorous but still hard to formalize. Some are very rigorous and can be formalized but fail to remain intuitive or elegant.

<del>Definitions are grouped by similarity. The definitions in the same group would have subtle yet important differences, that's why they deserve to be listed here.</del>

Definitions are mostly direct quotes from the source, with slight modifications for readability or brevity.

> The following are work-in-progress and not necessarily well organized.

### Hestenes 1984

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

algebra. With these in mind, we adopt the following definition. A geometric algebra $\mathcal{G}$ is a graded linear space, the elements of which are called multivectors. The grade- 0 elements are called scalars and are identified with the field of real numbers (we will have no cause to consider a geometric algebra over the complex field). The grade-1 elements are called vectors, and can be thought of as directed line segments. The elements of $\mathcal{G}$ are defined to have an addition, and each graded subspace is closed under this. A product is also defined which is associative and distributive, though non-commutative (except for multiplication by a scalar). The final axiom (which distinguishes a geometric algebra from other associative algebras) is that the square of any vector is a scalar. Given two vectors, $a$ and $b$, we find that
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

### Mother Algebra

> Source: Doran, Chris, David Hestenes, Frank Sommen, and Nadine Van Acker. "Lie groups as spin groups." Journal of Mathematical Physics 34, no. 8 (1993): 3642-3669.

> Grassmannian argue that GA is more fundamental than CA, because it makes no assumptions about a metric on the vector space that generates it. On the contrary, Cli?ordians argue that CA is more fundamental than GA, because it contains GA as a subalgebra.

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
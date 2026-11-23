# Boundedness of higher-dimensional twisted paraproducts

This is a formalization of the Lebesgue space bounds for higher-dimensional twisted
paraproducts. The proof was developed and the blueprint was subsequently generated with
GPT-6.2 Astra Ultra. The formalization was done with GPT-6.2 Sol Light.

## Main theorem

Let $`d\ge2`$ be an integer.
For $`s\ge 0`$ and a smooth function $`m:\mathbb{R}^d\setminus \lbrace 0\rbrace\to \mathbb{C}`$ let

```math
[m]_s=\max_{|\alpha|\le s}\sup_{\zeta\ne0} |\zeta|^{|\alpha|}\,|\partial^\alpha m(\zeta)|.
```

For a tuple $`\mathbf{f}=(f_1,\ldots, f_d)`$ of Schwartz functions $`f_i:\mathbb{R}^d\to \mathbb{C}`$ and $`x\in \mathbb{R}^d`$, define

```math
T_m(\mathbf{f})(x)=\int_{(\mathbb{R}^d)^d}m(\xi_1^1,\ldots,\xi_d^d)
    \Big( \prod_{i=1}^d\widehat f_i(\xi^i)\Big)\,
    e^{2\pi i x\cdot(\xi^1+\cdots + \xi^d)}\,d\xi^1\cdots d\xi^d .
```

For a smooth function $`\Omega:S^{d-1}\to \mathbb{C}`$ with $`\int_{S^{d-1}}\Omega = 0`$, let
$`K(y)=|y|^{-d}\Omega(y/|y|)`$ for $`y\ne0`$. For $`0\lt \epsilon\lt R\lt \infty`$, define

```math
T_{K,\epsilon,R}(\mathbf{f})(x)=\int_{\epsilon\lt |y|\lt R} K(y)
    \Big(  \prod_i f_i(x-y_i e_i)\Big)\, d y ,
```

where $`e_i`$ is the $`i`$-th coordinate vector.

**Theorem.**
Let $`d\ge 2`$ be an integer, $`1\lt p,p_1,\ldots,p_d\lt \infty`$, and $`1/p=\sum_{i=1}^d1/p_i`$.
There exist $`s\in\mathbb N`$ and $`C_{d, p_1,\ldots, p_d}\lt \infty`$ such that for every smooth $`m:\mathbb{R}^d\setminus \lbrace 0\rbrace\to \mathbb{C}`$
with $`[m]_s\lt \infty`$ and every tuple $`\mathbf{f}=(f_1,\ldots, f_d)`$ of Schwartz functions $`f_i:\mathbb{R}^d\to \mathbb{C}`$,

```math
\Vert T_m(\mathbf{f})\Vert_{L^p(\mathbb{R}^d)}
    \le C_{d, p_1,\ldots, p_d}\, [m]_s\prod_{i=1}^d\Vert f_i\Vert_{L^{p_i}(\mathbb{R}^d)} .
```

For every $`K`$ as above there exists $`C_{d,p_1,\ldots, p_d,\Omega}\lt \infty`$ such that for every tuple $`\mathbf{f}=(f_1,\ldots, f_d)`$ of Schwartz functions $`f_i:\mathbb{R}^d\to \mathbb{C}`$,

```math
\sup_{0\lt \epsilon\lt R\lt \infty}\Vert T_{K,\epsilon,R}(\mathbf{f})\Vert_{L^p(\mathbb{R}^d)}
    \le C_{d,p_1,\ldots, p_d,\Omega} \prod_i\Vert f_i\Vert_{L^{p_i}(\mathbb{R}^d)} .
```

The truncations $`T_{K,\epsilon,R}(\mathbf{f})`$ converge in $`L^p`$ as $`\epsilon\to 0,\,R\to \infty`$.

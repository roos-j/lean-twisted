# Boundedness of higher-dimensional twisted paraproducts

This is a formalization of Lebesgue space bounds for higher-dimensional twisted paraproducts in the full open Banach range. This used to be an open problem until now. The proof and the formalization blueprint were generated with GPT-6.2 Astra Ultra. The formalization was done with GPT-6.2 Sol Light.

## Main theorem

Let $`d\ge2`$ be an integer.
For $`s\ge 0`$ and a smooth function $`m:\mathbb{R}^d\setminus \lbrace 0\rbrace\to \mathbb{C}`$ define

```math
[m]_s=\max_{\lvert\alpha\rvert\le s}\,\sup_{\zeta\ne0}\, \lvert\zeta\rvert^{\lvert\alpha\rvert}\,\bigl\lvert\partial^\alpha m(\zeta)\bigr\rvert .
```

For Schwartz functions $`f_i:\mathbb{R}^d\to \mathbb{C}`$ and $`x\in \mathbb{R}^d`$, define

```math
T_m(f_1,\ldots,f_d)(x)=\int_{(\mathbb{R}^d)^d}m(\xi_1^1,\ldots,\xi_d^d)
    \Big( \prod_{i=1}^d\widehat{f}_i(\xi^i)\Big)\,
    e^{2\pi i x\cdot(\xi^1+\cdots + \xi^d)}\,d\xi^1\cdots d\xi^d .
```


**Theorem.**
Let $`d\ge 2`$ be an integer, $`1\lt p,p_1,\ldots,p_d\lt \infty`$, and $`1/p=\sum_{i=1}^d1/p_i`$.
There exist $`s\in\mathbb N`$ and $`C \lt \infty`$ such that for every $`m:\mathbb{R}^d\setminus \lbrace 0\rbrace\to \mathbb{C}`$
with $`[m]_s\lt \infty`$ and any Schwartz functions $`f_1,\ldots,f_d:\mathbb{R}^d\to \mathbb{C}`$,

```math
\lVert T_m(f_1,\ldots,f_d)\rVert_{L^p(\mathbb{R}^d)}
    \le C \, [m]_s\prod_{i=1}^d\lVert f_i\rVert_{L^{p_i}(\mathbb{R}^d)} .
```
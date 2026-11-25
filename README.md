# Boundedness of higher-dimensional twisted paraproducts

This is a formalization of Lebesgue space bounds for higher-dimensional twisted paraproducts in the full open Banach range. This was an open problem; see [Prior results](#prior-results) below. The proof and the formalization blueprint were generated with GPT-6.2 Astra Ultra. The formalization was done with GPT-6.2 Sol Light.

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

## Prior results

Boundedness of $`T_m`$ in the full open Banach range
$`1\lt p,p_1,\ldots,p_d\lt\infty`$ was open for every $`d\ge 2`$:

- **$`d=2`$.** Kovač [Kov12, Theorem 1] proved the bound for $`1\lt p_1,p_2\lt\infty`$ with  $`1/p_1+1/p_2\gt 1/2`$, that is, for target exponents $`p\lt 2`$ (this range also includes
  quasi-Banach exponents $`p\le 1`$). The remaining part $`p\ge 2`$ of the Banach range is not covered: [Kov12, §1] does not treat it, and
  [DR21, §1] refers to extending the range of exponents for the twisted paraproduct as an open question.
- **$`d=3`$.** Durcik and Roos [DR21, §1 and §3] proved the bound for $`1\lt p\lt 4/3`$ and  $`1\lt p_1,p_2,p_3\lt 4`$ (stated there in dual form).
- **$`d\ge 4`$.** No bounds were known for any exponents, see [DR21, §1].

The theorem above covers the full open Banach range in every dimension $`d\ge 2`$.

### References

- [DR21] P. Durcik, J. Roos, *Averages of simplex Hilbert transforms*, Proc. Amer. Math. Soc. 149 (2021), no. 2, 633–647.
- [Kov12] V. Kovač, *Boundedness of the twisted paraproduct*, Rev. Mat. Iberoam. 28 (2012), no. 4, 1143–1164.

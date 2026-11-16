# Code sources

Author notices and license files accompany the third-party sources.

| Component | Source | Implementation |
|---|---|---|
| MSK | [Minster, Saibaba and Kilmer](https://github.com/rlminste/rand_tensor_decompositions), commit `4c21d4cf5f696c5ce205aa863a922f2f71cff7ff` | Adapted rhosvd/randsthosvd/randsvd with SS test matrices and compact outputs. MIT license. |
| KRP | [Saibaba, Verma and Ballard](https://github.com/bhisham123/KRP-Random-Projections), commit `7bcf1db9c54e7a7931af5edf4a7219d371573b2f` | Adapted Khatri–Rao sketch/QR Tucker decomposition. MIT license. |
| RTSMS | [Hashemi and Nakatsukasa](https://github.com/bhashemi/rtsms), commit `d1841319d14dc8cd24a80c1368fb8b336ecb7aa8` | SS compression and auxiliary least-squares sketches; HOSVD/STHOSVD wrappers. MIT license. |
| Stable-MLN | [Bucci and Robol](https://github.com/alb95/MLN), commit `7d35add5fac5659b29fd0857781cd237ff12272e` | Adapted lit_mln and stable_nystrom_inversion; sequential variant follows Bucci and Hashemi, Appl. Math. Lett. 159:109271 (2025). License: unspecified in the source repository. |
| Sparse sign | [Epperly](https://github.com/eepperly/Iterative-Sketching-Is-Stable/blob/main/code/sparsesign.c) | C/MEX generator with a sign-bit boundary correction. License: unspecified in the source repository. |
| Tensor Toolbox | [Sandia Tensor Toolbox](https://www.tensortoolbox.org/) | Tensor classes and tensor products. BSD 2-Clause license. |
| Tensorlab | [Tensorlab](https://www.tensorlab.net/) | tmprod, tens2mat, cpdgen and kr; original author notices retained. |
| MLB | Minster, Li and Ballard, SIAM J. Sci. Comput. 46(2):A1186–A1213 (2024) | Implementation based on the paper; global SS and structured KronSS two-stage HOSVD/STHOSVD. |
| Shift | Che, Wei, Wu and Yan, arXiv:2506.04840 | Implementation based on the paper; one shifted power iteration. |
| RP and MP-RP | This paper | Matrix kernels, tensor wrappers, structured contractions, experiment and plotting scripts. |

The helpers getsize, mat2tens and pilot_srand are supplied with this implementation. Dataset sources are listed in [data/README.md](data/README.md).

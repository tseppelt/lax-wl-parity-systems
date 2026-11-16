For a fixed $k \geq 3$, the problem $k$-WL Distinguishing asks whether the $k$-dimensional
Weisfeiler–Leman algorithm ($k$-WL) distinguishes two given colored graphs. This submission
formalizes the unconditional time lower bound of Curticapean, Liu, Neuen and Seppelt: for every
$\varepsilon > 0$, no deterministic multitape Turing machine solves $k$-WL Distinguishing in time
$O(n^{k-1-\varepsilon})$, where $n$ is the number of vertices.

The proof combines the deterministic time hierarchy theorem with a quasi-linear reduction. A
Turing machine running in time $O(n^{k-1})$ is simulated on an input of length $n$ by a
register program with $k - 1$ registers over the alphabet $\mathbb F_2^\ell$ of size
$\Theta(n)$. Register programs are compiled into implicit parity systems, succinctly
represented systems of linear equations over $\mathbb F_2$, and these into pairs of colored
graphs on which the bijective $(k+1)$-pebble game, and hence $k$-WL, exactly simulates unit
propagation in the parity system.

The same construction yields two further lower bounds, which the submission also states. First,
the iteration number of $k$-WL is $\Omega_k(n^{k-1})$: there are arbitrarily large pairs of
$n$-vertex graphs that $k$-WL distinguishes, but only after $\Omega_k(n^{k-1})$ rounds. Second,
there are such pairs for which every graph $F$ of treewidth at most $k$ with
$\hom(F, G_0) \neq \hom(F, G_1)$ has $2^{\Omega_k(n^{k-1})}$ vertices. This witness size lower
bound is complemented by an upper bound of $2^{O_k(n^{k-1} \log n)}$, valid for all pairs
distinguished by $k$-WL, which is also stated for uncolored graphs in the language of
homomorphism indistinguishability.

The submission states the main theorems together with the pebble game characterization of
$k$-WL, the row-space and matrix compilers for implicit parity systems, a quasi-linear reduction from
deterministic time $O(n^{k-1})$ to $k$-WL Distinguishing, and a bound on the size of
homomorphism witnesses in terms of the number of rounds. The time hierarchy theorem, the
homomorphism characterization of $k$-WL due to Dvořák and to Dell, Grohe and Rattan, and the
stabilization bound of Döring and Neuen are stated as cited results.

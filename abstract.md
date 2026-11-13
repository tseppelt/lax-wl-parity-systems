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

The submission states the main theorem together with the pebble game characterization of
$k$-WL, the matrix compiler for implicit parity systems, and a quasi-linear reduction from
deterministic time $O(n^{k-1})$ to $k$-WL Distinguishing. The time hierarchy theorem is stated
as a cited classical result.

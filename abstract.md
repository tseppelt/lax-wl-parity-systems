The $k$-dimensional Weisfeiler–Leman algorithm ($k$-WL) is a simple combinatorial algorithm that
was originally designed as a heuristic for the graph isomorphism problem, but which also has
surprising connections to areas such as logic, homomorphism counts, linear programming, proof
complexity, (symmetric) algebraic complexity, and machine learning. This submission formalizes
the lower bounds for WL of Curticapean, Liu, Neuen and Seppelt:

- **Time.** For every fixed $k \geq 3$ and $\varepsilon > 0$, no deterministic multitape Turing
  machine decides whether $k$-WL distinguishes two given colored graphs in time
  $O(n^{k-1-\varepsilon})$, where $n$ is the number of vertices. This almost matches the classical
  upper bound of $O(n^{k+1} \log n)$. When $k$ is part of the input, the problem is
  $\mathsf{EXPTIME}$-hard under polynomial-time many-one reductions, and $\mathsf{XP}$-hard under
  fpt-reductions when parameterized by $k$; moreover, no deterministic multitape Turing machine
  decides it in time $O(2^{\varepsilon N^{1/5}})$ for some $\varepsilon > 0$, where $N$ is the total
  number of vertices.
- **Iteration number.** The iteration number of $k$-WL is $\Omega_k(n^{k-1})$, matching the upper
  bound of Döring and Neuen.
- **Witness size.** There are pairs of $n$-vertex graphs distinguished by $k$-WL for which every
  graph $F$ of treewidth at most $k$ with $\hom(F, G_0) \neq \hom(F, G_1)$ has
  $2^{\Omega_k(n^{k-1})}$ vertices. This is complemented by an upper bound of
  $2^{O_k(n^{k-1} \log n)}$, also stated for uncolored graphs in the language of homomorphism
  indistinguishability.

All results are obtained via a unified framework. Implicit parity systems are succinctly
represented systems of linear equations over $\mathbb F_2$. For each implicit parity system with
$k$ coordinate blocks, the matrix compiler constructs a pair of graphs on which the bijective
$(k+1)$-pebble game, and hence $k$-WL, exactly simulates unit propagation in the system.
Deterministic computations are encoded into such systems by a recursive simulation due to
Koucký, in which the calls of one recursion depth share their locations and the call paths are
packed into the coordinate blocks; the reductions are carried out by explicit multitape Turing
machines.

Everything is proved, including the pebble game and homomorphism characterizations of $k$-WL,
the stabilization bound of Döring and Neuen, the deterministic time hierarchy theorem (for
polynomial bounds, and for the exponential bounds $2^n$ versus $2^{n/4}$), and the translations
from the archive's single-tape and multi-stack machine models used for $\mathsf{EXPTIME}$ and
many-one reductions. Membership of the problem in $\mathsf{EXPTIME}$ and $\mathsf{XP}$ is not
formalized. The class $\mathsf{XP}$ and fpt-reductions are defined here with deterministic
multitape Turing machines.

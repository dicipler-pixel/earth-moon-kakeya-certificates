---
abstract: |
  We develop certificate-based approaches to the Earth--Moon and arithmetic Kakeya construction problems. For Earth--Moon, a triangle-free subgraph bound excludes inflated cycles $C_n[K_r]$ for $n,r\geq4$. Explicit decompositions prove $\theta(C_n[K_4])=3$, and an explicit coloring proves that every biplanar subgraph of $C_7[K_4]$ is nine-colorable. A separate nineteen-vertex reduction retains its archived $100$--$102$-edge endpoint restriction.

  For arithmetic Kakeya, exact nonzero-multiple forcing is expressed through row spaces and integer primal--dual certificates. We derive a target-sensitive numerator-residue criterion and exact kernel updates, then classify the first possible escape produced by one variable site generator. On the fixed six-vertex Katz--Tao edge core, this reduces 5,166 unbounded integer-label families to 6,112 checked representatives: two generator placements come from a specified seven-direction pool, while the third direction is unrestricted. All are excluded by 25,498 integer target-dual identities. A separate 36-family exclusion covers one initially known site and one arbitrary generator.

  Connection energy measures subspace changes, but target residues distinguish useful changes from mere rank loss. Source-aware Schur elimination gives an exact coherent-reduction model. A fresh full replay verifies the preserved 481,712-configuration arithmetic census and separate 24,976-graph Earth--Moon family. The parameter families overlap that census and are not added to its counts. Historical Atlas, master-list, manuscript, and Lean scopes are reconciled without identifying their versions or promoting physical analogies to theorems. Neither benchmark construction is obtained.
---

::: titlepage
::: center
RESEARCH PREPRINTAUTHOR-REVIEW EDITION

**Certified Obstructions**

and Exact Forcing

Earth--Moon Graph Coloring

and Arithmetic Kakeya

Jeromie N. Beasley

Operator-First Persistent Geometry Initiative

17 September 2026 Version 2

Probe-sensitive search and unbounded direction families
:::
:::

# Introduction: two construction problems, one evidence discipline

A promising construction can fail for different reasons. It may violate a necessary inequality; it may satisfy every inequality that was tested but lack the required global structure; or its apparent success may depend on a computational shortcut that does not preserve the stated rules. The Earth--Moon and arithmetic Kakeya programs considered here supply explicit instances of all three situations.

The Earth--Moon benchmark asks for a graph with a two-planar edge partition and chromatic number at least ten. The arithmetic benchmark asks for an admissible constructible object whose complete forcing has score at most $67/40$. At the date of this edition, the official pages continue to list both targets as unsolved [@epochEM; @epochAK]. Our results are obstruction, classification, formal-interface, and finite-exclusion results. They do not supply either qualifying object.

The mathematical connection between the two parts is deliberately modest. Both retain a finite object, restrict its data to a suitable support, and ask whether an exact certificate permits or obstructs the desired next conclusion. Graph edges are not identified with arithmetic generator rows. A planar decomposition is not a forcing sequence. A chromatic lower bound is not a rank calculation. The common methodology concerns how these different certificates are represented, checked, and retained.

The manuscript develops the usable mathematics rather than reproducing an unfiltered chronology. Earlier assertions that failed are retained as explicit controls where they clarify the surviving statements. In particular, a false local-seeding restriction must not remain inside an allegedly exhaustive arithmetic search, and a planar near miss must not be combined with a different ten-chromatic graph as though one object possessed both properties.

## Main results and their logical roles

The Earth--Moon results begin with the elementary bound $e(H)\leq4v(H)-8$ for triangle-free subgraphs of biplanar graphs. Applied to the joins of $C_7[K_4]$, it detects a failure missed by the whole-graph Euler count. An explicit coloring argument then proves a stronger host-specific statement: deleting edges from this graph can never produce a biplanar ten-chromatic graph. The nineteen-vertex program is separate. There, complement structure gives a finite profile reduction, and archived Boolean proofs supply an additional endpoint exclusion.

The arithmetic results begin with a finite integer row system. Allowing any nonzero multiple of $(1,-1)$ makes rational feasibility equivalent to integer feasibility; requiring coefficient one would be a different problem. Summing a first-entry forcing witness over a cut proves a necessary two-direction condition. Exact dual identities explain why the converse fails. A fully specified seven-row family gives a small complete classification and an explicit projector calculation.

The formal supplement now contains two general finite bridges that were absent from earlier reviews: rational-to-integer nonzero-multiple forcing and the iterative necessary-cut theorem. The larger search corpus and the graph-theoretic topological bridges remain separately certified or unformalized. A count of Lean declarations is never used as a count of novel mathematical results.

## What Version 2 adds

The principal new computational theorem allows an unbounded integer direction instead of merely enlarging a tested finite pool. Theorem [23](#thm:onefree){reference-type="ref" reference="thm:onefree"} fixes two of the six-vertex calibration's generator placements in a declared pool and excludes every admissible third direction. Theorem [24](#thm:singleton){reference-type="ref" reference="thm:singleton"} separately excludes the target-score route with an initially known singleton. These conclusions follow from the finite first-escape classification of Lemma [21](#lem:firstescape){reference-type="ref" reference="lem:firstescape"}, not from numerical rank or a claimed amplitude symmetry.

The new algebraic bridge is Theorem [14](#thm:proberesidue){reference-type="ref" reference="thm:proberesidue"}: exact target forceability is visible in a specified coefficient of a probe-inserted determinant. It combines the recovered numerator, kernel, and positive-Gram viewpoints on the actual arithmetic relation matrix. The connection-energy and coherent-elimination sections show which information must be retained, and give controls against replacing a target response by an unweighted scalar.

## Evidence terminology

A *written theorem* below comes with its mathematical argument. A *recorded computational result* reports an explicitly delimited certificate corpus or experiment from the preserved research record. A *formal result* refers to named Lean declarations at a pinned revision with matching verification evidence. A *fresh check* means an actual calculation performed while assembling this edition. These descriptions can overlap, but none implies the others automatically.

This distinction matters especially for the $100$-edge floor and the large search census. Version 1 did not complete its large arithmetic replay. Version 2 completes that replay, while the nineteen-vertex Boolean census remains supported by its archived evidence. The new parameter-family exclusion is a written reduction plus independently checked finite certificates, not a new Lean theorem. Exact checks and remaining limits are listed in Section [14](#sec:evidence){reference-type="ref" reference="sec:evidence"}.

# Earth--Moon: definitions and the subgraph obstruction

All graphs are finite, simple, and undirected. Write $v(G)$ and $e(G)$ for vertex and edge counts, $\alpha(G)$ for independence number, $\chi(G)$ for chromatic number, and $\theta(G)$ for thickness: the least number of planar subgraphs whose edge sets cover $E(G)$. Repeated edges in a cover may be assigned to one layer, so a two-layer cover can be made an edge partition.

A graph is *biplanar* when $\theta(G)\leq2$. The benchmark certificate additionally requires a proper coloring and a matching chromatic lower bound; a drawing or an upper coloring alone does not establish the target [@epochEM]. The classical bounds are $9\leq\chi_2\leq12$, where $\chi_2$ is the supremum of chromatic numbers of biplanar graphs. SAT-based planarity generation provides relevant prior methods, including eager order encodings and lazy Kuratowski obstructions [@KSS].

::: {#lem:tfplane .lemma}
**Lemma 1** (Triangle-free planar bound). *A simple triangle-free planar graph on $N\geq3$ vertices has at most $2N-4$ edges.*
:::

::: proof
*Proof.* For a connected acyclic graph the count is $N-1\leq2N-4$. For a connected graph containing a cycle, facial boundary walks have length at least four; bridges are counted twice in the facial sum and do not create a shorter cyclic boundary. Thus $2e\geq4f$, and Euler's identity $N-e+f=2$ gives the result. A disconnected graph can be embedded with its components in disjoint regions and joined by bridges. This preserves simplicity and triangle-freeness. Applying the connected bound to the augmented graph bounds the original edge count as well. ◻
:::

::: {#thm:tfbiplanar .theorem}
**Theorem 2** (Triangle-free subgraph obstruction). *If $G$ is biplanar and $H\subseteq G$ is a triangle-free subgraph on $N\geq3$ vertices, then $$\label{eq:tfbound}
e(H)\leq4N-8.$$*
:::

::: proof
*Proof.* Restrict each of two planar edge layers of $G$ to the vertex set and edges of $H$. The resulting graphs are simple, triangle-free, and planar. After assigning any shared edges to one layer, their edge counts sum to $e(H)$. Lemma [1](#lem:tfplane){reference-type="ref" reference="lem:tfplane"} applied on the same $N$ vertices gives $e(H)\leq(2N-4)+(2N-4)$. ◻
:::

The lemma is classical planar counting. Its role here is an explicit support-sensitive certificate. The whole-graph bound $e(G)\leq6v(G)-12$ may be satisfied while a triangle-free portion violates [\[eq:tfbound\]](#eq:tfbound){reference-type="eqref" reference="eq:tfbound"}. Passing either bound remains necessary, not sufficient.

## Inflated cycles

For $n\geq4$ and $r\geq1$, let $C_n[K_r]$ be the graph with vertices $(i,a)$, where $i\in\mathbb Z/n\mathbb Z$ and $1\leq a\leq r$. Vertices in one fibre form a clique; consecutive fibres are completely joined. Let $J_{n,r}$ consist only of the edges between consecutive fibres. Then $$\begin{aligned}
v(C_n[K_r])&=nr,\\
e(C_n[K_r])&=n\binom r2+nr^2,\\
e(J_{n,r})&=nr^2.
\end{aligned}$$ The join graph $J_{n,r}$ is triangle-free. A triangle would have to use three distinct pairwise adjacent base fibres, impossible in $C_n$ for $n\geq4$.

::: {#cor:inflated .corollary}
**Corollary 3**. *For $n\geq4$ and $r\geq4$, the graph $C_n[K_r]$ is not biplanar.*
:::

::: proof
*Proof.* The join excess over [\[eq:tfbound\]](#eq:tfbound){reference-type="eqref" reference="eq:tfbound"} is $$nr^2-(4nr-8)=nr(r-4)+8>0.$$ ◻
:::

For $r=4$, the excess is exactly eight, independently of $n$. By contrast, the whole-graph Euler allowance minus the actual edge count is $$(6\cdot4n-12)-22n=2n-12.$$ Consequently, the whole-graph count already excludes $n=4,5$, is saturated at $n=6$, and does not exclude $n\geq7$. This is the corrected range of the original comparison.

For $C_7[K_4]$ specifically, the full graph has $28$ vertices and $154$ edges, below the whole-graph allowance $156$. Its $112$ join edges exceed the triangle-free allowance $104$. The contradiction is entirely combinatorial and needs no numerical spectral threshold.

# Exact thickness and a closed host-repair route

## A three-layer construction

::: {#lem:forest .lemma}
**Lemma 4** (Two-clone blow-up of a forest). *Replacing every vertex of a forest by two adjacent clones, and every forest edge by all four edges between its clone pairs, gives a planar graph.*
:::

::: proof
*Proof.* For a single tree vertex the graph is an edge. Remove a leaf from a larger tree. Restoring the leaf adds a $K_4$ sharing exactly the parent clone edge with the previously constructed graph. Planarity is preserved by an edge-sum: choose an incident face at that edge and place the new copy in that face, using a sufficiently small neighborhood. This induction applies to each tree component. Isolated components can be drawn separately. ◻
:::

::: {#thm:thickness3 .theorem}
**Theorem 5**. *For every $n\geq4$, $\theta(C_n[K_4])=3$.*
:::

::: proof
*Proof.* The lower bound follows from Corollary [3](#cor:inflated){reference-type="ref" reference="cor:inflated"}. For the upper bound, write the vertices of $C_n[K_2]$ as $a_i,b_i$, with indices modulo $n$. For $n\geq5$, partition its edges into the following three forests. The first consists of the two rail cycles after removing $a_0a_1$ and $b_1b_2$. The second consists of the cross edges $a_i b_{i+1}$ and $b_i a_{i+1}$ after removing $a_2b_3$ and $a_3b_4$. The third consists of all vertical edges $a_i b_i$ and the four removed edges.

The first forest is a pair of paths. For odd $n$, the cross edges form one $2n$-cycle; for even $n$, they form two $n$-cycles and the two removed edges belong to different cycles. The second part is therefore a forest. Contracting the vertical matching in the third part leaves a path on fibre indices $0,1,2,3,4$, together with isolated vertices, so the third part is also acyclic.

Blow up every vertex to two adjacent clones. By Lemma [4](#lem:forest){reference-type="ref" reference="lem:forest"}, each forest has a planar closed two-clone blow-up. Put the internal clone edges only in the first layer. The remaining two layers are subgraphs of their closed blow-ups and remain planar. These layers partition precisely $C_n[K_4]$.

For $n=4$, the explicit three-forest partition in Appendix [17](#app:c4){reference-type="ref" reference="app:c4"} gives the same construction. Thus the exceptional small index is supplied by a finite witness rather than by extending a formula outside its valid range. ◻
:::

For $n=7$ the resulting layer counts are $62,48,44$. The preserved rotation systems additionally give a finite embedding certificate: the face orbits have Euler characteristic two on every nontrivial connected component. These finite checks corroborate the construction; the proof for all $n\geq5$ is the forest argument, not extrapolation from finitely many examples [@BeasleyFrontier].

## The chromatic number of the host

::: {#prop:chi10 .proposition}
**Proposition 6**. *The graph $C_7[K_4]$ has independence number three and chromatic number ten.*
:::

::: proof
*Proof.* An independent set uses at most one vertex from any clique fibre, and its occupied fibres form an independent set in $C_7$. Hence its size is at most three, with equality attained on three alternating nonconsecutive fibres. Thus $\chi\geq\lceil28/3\rceil=10$.

For a ten-coloring, for each $j\in\mathbb Z/7\mathbb Z$ assign one color to one vertex in each of the three fibres $j,j+2,j+4$. Every fibre receives three different colors this way, leaving one uncolored vertex. Color the seven remaining vertices as a seven-cycle using three further colors. This gives a proper ten-coloring. ◻
:::

More generally, $\alpha(C_n[K_r])=\lfloor n/2\rfloor$, not $r\lfloor n/2\rfloor$. The clique condition prevents taking all $r$ vertices from an occupied fibre.

::: {#thm:nine .theorem}
**Theorem 7** (Every biplanar subgraph of this host is nine-colorable). *If $G\subseteq C_7[K_4]$ and $G$ is biplanar, then $\chi(G)\leq9$.*
:::

::: proof
*Proof.* Pad missing vertices by isolated vertices so that the common vertex set has size $28$. The join portion of $G$ has at most $104$ edges by Theorem [2](#thm:tfbiplanar){reference-type="ref" reference="thm:tfbiplanar"}; the full host has $112$ joins. In particular, some join edge $e$ is missing, and $G\subseteq C_7[K_4]-e$.

Every join edge can be transported to every other by a cycle automorphism and permutations within fibres. It suffices to delete the edge between slot zero in fibres six and zero. Give one color to slot zero in fibres $0,2,4,6$. The only adjacent pair in that four-vertex color class was the deleted edge.

For $j\in\mathbb Z/7\mathbb Z$, put $I_j=\{j,j+2,j+4\}$. Use eight further colors on these independent fibre triples, with multiplicities $$(m_0,m_1,m_2,m_3,m_4,m_5,m_6)=(1,2,1,1,1,1,1).$$ The number of demanded vertices per fibre is $(3,4,3,4,3,4,3)$, exactly the number not yet colored in each fibre. Assign different remaining vertices to these demands. Each color occupies an independent triple and the resulting coloring is proper. Restricting it colors $G$. ◻
:::

This closes an entire repair strategy, not merely one bounded deletion search. No subgraph of this host can simultaneously retain the desired ten-color lower bound and become biplanar. The statement does not exclude graphs produced by adding edges outside the host, changing the host, or using an unrelated construction.

Related prior work must be kept visible. Kirchweger, Scheucher, and Szeider excluded the nineteen-vertex graph $C_5[4,4,4,4,3]$ by SAT-based planarity methods [@KSS]. Trivedi's 2026 preprint proves a nine-colorability theorem for biplanar clique blow-ups of $C_5$ [@Trivedi]. These are not relabeled as new results of this manuscript. Our $C_7[K_4]$ subgraph argument is stated with its explicit proof and without a historical-priority claim.

## A separate finite outside-host family

The preserved extension starts with $C_7[K_4]$, removes the eight joins from vertices $24,25$ to vertices $0,1,2,3$, and then adds exactly two distinct nonedges of the *original* host. There are $\binom{28}{2}-154=224$ such nonedges and therefore $\binom{224}{2}=24,976$ members. The host numbering is $(i,a)\mapsto4i+a$ with $0\leq a<4$.

::: {#res:earthfinite .result}
**Recorded computational result 8** (Fixed outside-host exclusion). The archived checker assigns all $24,976$ members of this specified family to one of two rejection categories: $19,620$ have a certified triangle-free density violation and $5,356$ have an explicit proper nine-coloring. No member remains unresolved within this corpus [@BeasleyDAG; @BeasleyStatus].
:::

The certificate count is not a theorem about all two-edge modifications, all eight-edge deletions, or all $28$-vertex graphs. The removed set and the allowed added edges are part of the quantified domain. This finite result is separate from Theorem [7](#thm:nine){reference-type="ref" reference="thm:nine"}, since the additions leave the original host.

# The nineteen-vertex route and its endpoint restrictions

## Complement structure

Let $G$ have nineteen vertices and no independent triple. Its complement $H=\overline G$ is triangle-free, and every color class of $G$ has size at most two. Therefore $$\label{eq:matching}
\chi(G)=19-\nu(H),$$ where $\nu(H)$ is the maximum matching size. A coloring corresponds to pairing the size-two color classes along a matching of $H$; conversely, a maximum matching supplies such a coloring. In particular $\chi(G)\geq10$. This is a sufficient route to the target, not an equivalence with all possible ten-chromatic biplanar graphs.

Assume additionally that $G$ is biplanar. The planar layer bound gives $e(G)\leq102$, so $e(H)\geq69$. The standard nonbiplanarity of $K_9$ implies that $H$ has no independent nine-set [@KSS]. Since every neighborhood in $H$ is independent, $\Delta(H)\leq8$, equivalently $\delta(G)\geq10$. The hypothesis forbidding an independent nine-set is stronger than the triangle-free condition and must remain in the census.

::: {#prop:c5 .proposition}
**Proposition 9** (A five-cycle is unavoidable). *Under the preceding hypotheses, $H$ contains an induced $C_5$.*
:::

::: proof
*Proof.* The graph $H$ cannot be bipartite, since one part of a bipartition on nineteen vertices would contain an independent set of size at least ten. Let $C$ be a shortest odd cycle of length $g\geq5$. It has no chord. Any outside vertex has at most two neighbors on $C$: three or more neighbors divide $C$ into cyclic gaps of length at least two, one of which is odd, and that odd gap together with the two edges to the outside vertex creates a shorter odd cycle.

The total degree on $C$ is at most $2g+2(19-g)=38$, while the outside degree sum is at most $8(19-g)$. Consequently $$2e(H)\leq38+8(19-g).$$ If $g\geq7$, this gives $e(H)\leq67$, contradicting $e(H)\geq69$. Hence $g=5$. ◻
:::

The proof uses only complement restrictions and classical graph facts. It does not assume that $H$ itself is a five-cycle blow-up.

## The finite profile reduction

Fix an induced five-cycle $C$. For the fourteen outside vertices define $$D_C=\sum_{v\notin C}(2-|N_H(v)\cap C|),\qquad
D_{\rm out}=\sum_{v\notin C}(8-d_H(v)).$$ Both are nonnegative. Counting the degree sum on and off the cycle gives the exact identity $$\label{eq:deficits}
D_C+D_{\rm out}=150-2e(H).$$ Thus $e(H)\geq72$ forces $D_C\leq6$.

An outside vertex with two cycle neighbors has one of the five allowed nonadjacent neighbor pairs. Group it with the cycle vertex having the same two cycle neighbors. Let the five resulting nonempty regular class sizes be $a_i$. Let $b_i$ count vertices whose sole cycle neighbor is $i$, and let $z$ count vertices having no cycle neighbor. Every admissible profile satisfies $$\begin{aligned}
\sum_{i=0}^4(a_i+b_i)+z&=19, & a_i&\geq1,\quad b_i,z\geq0,\\
2z+\sum_{i=0}^4b_i&\leq6, & a_{i-1}+a_{i+1}+b_i&\leq8.
\end{aligned}$$ Vertices with a common cycle neighbor cannot be adjacent in $H$. Only consecutive regular classes can be joined. Edges involving exceptional classes remain variable subject to their actual restrictions. Dihedral symmetries of the chosen cycle and permutations inside identical-neighborhood classes can then reduce the finite profile list without asserting a global blow-up description.

::: {#res:100 .result}
**Recorded computational result 10** (Archived $100$-edge floor). The recorded threshold-$72$ census has $8,044$ profile orbits. Its semantic audit reconstructs the formulas and graph-theoretic cuts, and its reverse-unit-propagation checks reject all cases. Subject to that archived computational certificate, every biplanar nineteen-vertex graph without an independent triple satisfies $$\label{eq:window}
100\leq e(G)\leq102.$$
:::

The deduction from the census is short: exclusion of $e(H)\geq72$ gives $e(H)\leq71$, and $e(G)=171-e(H)\geq100$. The computational part must not be replaced by a claim that the profile equations alone imply this exclusion. The archive reports $4,799,908$ checked RUP additions, $327$ independent-nine cuts, $13$ triangle-free-density cuts, and corruption controls. The earlier $146$- and $1,684$-profile threshold censuses are nested, not additional disjoint graph counts [@BeasleyC5].

The two mathematical census jobs in the preserved September 9 workflow are successful. A separate source-export job in the same workflow failed; later preservation records identify a durable archive. Accordingly, this paper does not describe the entire earlier workflow as uniformly successful. The trust chain includes the written reduction, graph-to-formula interpretation, cardinality encoding, semantic cut checks, and Boolean proof checking. This is not a complete Lean proof of [\[eq:window\]](#eq:window){reference-type="eqref" reference="eq:window"}.

For a successful endpoint represented by two triangulations, each layer has $51$ edges, and therefore the overlap is $102-e(G)\leq2$. The overlap restriction belongs to endpoints satisfying all the hypotheses. It does not forbid a discovery path from passing through larger overlaps or temporarily worse independent-triple counts.

## A plateau and a different necessary-condition survivor

The saved five-triple embedded component contains $40$ states and $2,828$ legal single-flip transitions, according to its exact component enumeration. Every state retains the same five independent triples and every exit has at least six. An improving path made solely of these legal flips must therefore cross a one-unit barrier. This is a theorem about that represented component once the finite enumeration is checked, not about all decompositions or all graph moves [@BeasleyC5].

The later stellar-relocation work preserves closed spherical triangulations with $51$ edges and $34$ faces in each layer. It produces a planar $102$-edge near miss with five independent triples and a checked nine-coloring. Such a graph has the required layer structure but does not have the required chromatic number.

A *different* saved graph has $100$ edges, chromatic number ten, and clique number eight. It passes the recorded all-support triangle-free density tests: supports through size thirteen are covered by the general extremal bound, and sizes fourteen through nineteen by six separately certified unsatisfiability checks. Its thickness remains unknown. The direct partition search and two eager variants ended without resolving it; a timeout is not a nonbiplanarity proof. This candidate has the chromatic requirement but not a certified two-planar partition.

The two graphs must remain distinct throughout publication. Combining one graph's planarity with another graph's chromatic number would manufacture a nonexistent certificate. The remaining mathematical problem is their conjunction on one admissible object. Related triangle-free extremal optimization was studied by Banak, Ekim, and Taşkın [@Banak]; their degree-and-matching constraints are not silently identified with our complement-biplanarity constraints.

# Arithmetic Kakeya: the finite operational model

## Admissible objects and cost

The arithmetic portion uses the nonzero-multiple *verifiable* forcing model of the benchmark, not a coefficient-one variant [@epochAK]. Let $X\subset\mathbb Z^2$ be finite, contain $(0,0)$, and satisfy $a+b\neq0$ for every nonzero $(a,b)\in X$. A tower has dimensions $d_1,\ldots,d_k\geq1$ and vertex set $$V=[d_1]\times\cdots\times[d_k],\qquad n=\prod_i d_i.$$ At level $i$, a prefix label is repeated over all later coordinates on the adjacent-coordinate edges it generates. A zero label contributes no row and no edge cost. The expanded edge count is $$\label{eq:edgecost}
m=\sum_{i=1}^k\left(\sum_{\text{level-}i\text{ prefixes }p}\mathbf1_{f_i(p)\ne0}\right)\prod_{j>i}d_j.$$ A list $R$ of initial site generators contributes $r=|R|$ to cost, with each generator supported at one site and labelled by a nonzero element of $X$. Let $T\subsetneq V$ be the initially known set. The score is $$\label{eq:score}
S=\frac{m+r}{n-|T|}.$$ Cost is not erased by a later linear dependence. Duplicate entries in a list must either retain their cost or be removed by an explicitly justified preprocessing step.

The target threshold is $67/40$. The nearby historical arithmetic exponent $\gamma\approx1.6751308706$ is the largest real root of $x^3-4x+2$, arising in the Katz--Tao line of work [@KT; @epochAK]. The present paper does not improve that exponent. Green and Ruzsa discuss equivalent arithmetic Kakeya formulations and related constructions [@GR]; the finite search results here cover only the specified operational domains.

## Rows, support, and forcing

For each oriented labelled edge $u\to v$ with label $x\in X\setminus\{0\}$, include the integer row $e_u\otimes x-e_v\otimes x$ in $\mathbb Z^{2n}$. For each site generator $(u,x)$ include $e_u\otimes x$. Reversing an edge orientation merely negates its relation, but changing the tower's prefix rules can change which edge-labelled object is admissible.

Let $A$ be the matrix of all these rows. For a known set $K$ and unknown vertex $v$, an integer coefficient vector $c$ is a forcing witness when $$\label{eq:force}
\operatorname{supp}(A^Tc)\subseteq K\cup\{v\},\qquad
(A^Tc)|_v=(a,-a),\quad a\in\mathbb Z\setminus\{0\}.$$ Here support is by vertex blocks. Coordinates at already known vertices are unrestricted; coordinates at every other unknown vertex must vanish. A legal step adjoins $v$ to $K$. Completion means that a finite sequence of fresh legal steps starting at $T$ reaches all of $V$.

The same statement can be expressed in the quotient by coordinates supported on $K$. If $B$ is the rational span of the rows and $E_K$ is the coordinate subspace supported on $K$, then $v$ is forceable exactly when $\tau_v=e_v\otimes(1,-1)$ belongs to $B+E_K$. This equality is a rational-space formulation of the nonzero-multiple rule, not a claim about a saturated integer lattice.

# Exact forcing, denominators, and dual certificates

::: {#thm:denom .theorem}
**Theorem 11** (Rational and integer nonzero-multiple forcing). *For a finite integer row system, a rational witness satisfying [\[eq:force\]](#eq:force){reference-type="eqref" reference="eq:force"} with nonzero rational target coefficient exists if and only if an integer witness with nonzero integer target coefficient exists.*
:::

::: proof
*Proof.* An integer witness is rational. Conversely, multiply all rational row coefficients by a common positive denominator $D$. The resulting coefficients are integers. The support equations are homogeneous and remain zero where required. The target becomes $(Da,-Da)$ with $Da\ne0$, and its coordinates are integers because the rows and the cleared coefficients are integers. ◻
:::

This proof does not show that the target coefficient can be made one. The two admissible integer rows $(2,0)$ and $(0,2)$ generate $(2,-2)$ over the integers but not $(1,-1)$. They do generate $(1,-1)$ over the rationals. This explicit boundary control prevents the denominator argument from being promoted to a coefficient-one theorem.

## A coefficient-space kernel criterion

Let $s$ be the number of rows. For a target $v$ and known set $K$, form a matrix $C_{K,v}$ whose rows are the columns of $A$ at every unknown vertex other than $v$, followed by the sum of the two columns at $v$. Let $b_v$ be the first target column, viewed as a row in $\mathbb Q^s$. Then $$\label{eq:kernelcriterion}
v\text{ is forceable from }K
\quad\Longleftrightarrow\quad
\exists c\in\ker C_{K,v}\text{ with }b_vc\ne0.$$ The constraints encode exactly the vanishing support and anti-diagonal target equations. By finite-dimensional linear algebra, $$\label{eq:dual}
\ker C_{K,v}\subseteq\ker b_v
\quad\Longleftrightarrow\quad
b_v\in\operatorname{rowspan}_{\mathbb Q}(C_{K,v}).$$ Thus failure to force has an exact dual certificate $y^TC_{K,v}=b_v$. Clearing denominators yields $$\label{eq:integerdual}
z^TC_{K,v}=D b_v,\qquad z\in\mathbb Z^q,\quad D\in\mathbb Z\setminus\{0\}.$$ A checker need only multiply integers to verify this identity. For every legal $c$ it gives $D b_vc=0$, so the required nonzero target is impossible.

::: {#prop:terminal .proposition}
**Proposition 12** (A terminal certificate excludes every continuation). *Suppose a known set $K$ is reached by checked legal steps. If every $v\notin K$ has a dual certificate [\[eq:integerdual\]](#eq:integerdual){reference-type="eqref" reference="eq:integerdual"}, then no legal continuation from $K$ exists. Moreover, no alternative order of fresh forcing steps from the same initial data can complete outside the least forcing closure.*
:::

::: proof
*Proof.* The first statement follows target by target from [\[eq:integerdual\]](#eq:integerdual){reference-type="eqref" reference="eq:integerdual"}. Forceability is monotone in the known set: enlarging $K$ removes zero-support constraints without invalidating a previous witness. Iteratively adjoining all currently forceable vertices therefore defines a monotone closure process that stabilizes after at most $n-|T|$ strict enlargements. Induction on any legal sequence shows that every vertex in that sequence belongs to the resulting least fixed point. Conversely, adjoining forceable vertices one at a time realizes this fixed point. A terminal set reached by such steps is therefore this closure. ◻
:::

The last assertion depends on keeping the row system fixed. A search that subsequently adds new generators changes the system and may escape an old stall. Terminal certificates cannot be reused across that change without checking their hypotheses.

## Numerical rank is not an exact certificate

For $M=10^{30}$, the two rows $(M,M+1)$ and $(M+1,M+2)$ have determinant $-1$. Floating-point rounding can destroy the distinction between their entries, while exact integer arithmetic preserves rank two. This retained stress control explains why tolerance-based rank is insufficient for the arithmetic search. Rational elimination may be used by the producer; integer multiplication is enough for the delivered primal and dual checker [@BeasleyFrontier].

# A probe-sensitive determinant criterion for exact forcing {#sec:probe}

The numerator emphasis in the amplitude-inspired notes can be made precise here without identifying a finite Kakeya relation matrix with a scattering amplitude. The recovered master list records a rank-one determinant insertion; the Atlas supplies a kernel-and-retained-output test. Their combination gives an exact criterion on the actual forcing data. This section derives that combination rather than assuming a cross-domain correspondence [@BeasleyMaster; @BeasleyProbe; @BeasleyMethod].

## Two projectors, with opposite tests

Let $R_K$ be the matrix obtained by adjoining to the original relation matrix all coordinate rows supported on the known set $K$. Define the *dual obstruction space* and its orthogonal projector by $$\mathcal N_K=\ker R_K\subset\mathbb R^{2n},\qquad P_K=\operatorname{proj}_{\mathcal N_K}.$$ For a target $v$, put $\tau_v=e_v\otimes(1,-1)$ and $$\label{eq:dualresidual}
\rho_v(K)=\tau_v^TP_K\tau_v=\|P_K\tau_v\|^2.$$ The row-space criterion proves $$\label{eq:rhozero}
v\text{ is forceable from }K\quad\Longleftrightarrow\quad\rho_v(K)=0.$$ All entries may be computed rationally when the input rows are rational. If $C$ is any full-column-rank rational basis of $\mathcal N_K$, then $P_K=C(C^TC)^{-1}C^T$.

This is not the coefficient-space projector of Section [9](#sec:family){reference-type="ref" reference="sec:family"}. For the coefficient constraint kernel, the response $bPb^T>0$ supplies a witness; for the dual-coordinate obstruction kernel, the response $\rho=0$ removes every separating obstruction. The dimensions, targets, and direction of the test must travel with the projector. A numerical value called "projector response" without these data is ambiguous.

::: {#prop:weights .proposition}
**Proposition 13** (Positive row weights cannot change exact forcing). *For any real symmetric positive-definite row weight $W$, the matrix $$L=R_K^TWR_K$$ has $\ker L=\ker R_K$. Consequently changing $W$ changes neither $P_K$ nor the exact forceable targets.*
:::

::: proof
*Proof.* For every $x$, $x^TLx=(R_Kx)^TW(R_Kx)$ vanishes exactly when $R_Kx=0$. A positive-semidefinite matrix has zero quadratic form exactly on its kernel. This proves the equality and the consequences. ◻
:::

Positive reweighting can affect conditioning and finite-precision behavior; it cannot escape an exact terminal obstruction. Nor does replacing the relation list by $L$ erase the original edge and generator costs. The input grammar, row provenance, and integer cost remain separate registers.

## The target is a numerator residue

For a fixed real target $\tau$, set $$p(\varepsilon)=\det(L+\varepsilon I),\qquad
q_\tau(\varepsilon)=\tau^T\operatorname{adj}(L+\varepsilon I)\tau.$$ These are polynomials even at $\varepsilon=0$. For $\varepsilon>0$ the matrix is positive definite, so its ordinary inverse and real log determinant are defined.

::: {#thm:proberesidue .theorem}
**Theorem 14** (Probe residue and polynomial order). *Let $L=L^T\geq0$, let $P$ project onto $\ker L$, and put $\rho=\tau^TP\tau$. Then $$\begin{aligned}
\det(L+\varepsilon I+t\tau\tau^T)
 &=p(\varepsilon)+tq_\tau(\varepsilon),\label{eq:probeinsert}\\
\rho&=\lim_{\varepsilon\downarrow0}\varepsilon\,
\frac{q_\tau(\varepsilon)}{p(\varepsilon)}\nonumber\\
&=\lim_{\varepsilon\downarrow0}\varepsilon\,
\left.\frac{\partial}{\partial t}\log\det(L+\varepsilon I+t\tau\tau^T)\right|_{t=0}.
\label{eq:probelimit}
\end{aligned}$$ If $k=\dim\ker L\geq1$ and $c$ is the product of the positive eigenvalues, with empty product one, then $$\label{eq:leadingprobe}
[\varepsilon^k]p=c>0,\qquad
[\varepsilon^{k-1}]q_\tau=c\rho.$$ There are no lower-order terms in these two polynomials. In particular, a nonzero leading obstruction occurs at order $k-1$ exactly when $\rho>0$; when $\rho=0$, the numerator has order at least $k$ or is identically zero.*
:::

::: proof
*Proof.* Multilinearity of the determinant in its columns permits at most one column from the rank-one update, giving [\[eq:probeinsert\]](#eq:probeinsert){reference-type="eqref" reference="eq:probeinsert"}; two such columns are proportional. For positive $\varepsilon$, division by $p$ gives $q_\tau/p=\tau^T(L+\varepsilon I)^{-1}\tau$. In an orthonormal eigenbasis write the positive eigenvalues as $\lambda_j$ and the corresponding target coordinates as $a_j$. Then $$p=\varepsilon^k\prod_j(\lambda_j+\varepsilon),\qquad
\frac{q_\tau}{p}=\frac{\rho}{\varepsilon}+\sum_j\frac{a_j^2}{\lambda_j+\varepsilon}.$$ The limit and coefficient statements follow directly. Differentiating the affine determinant insertion gives the log-determinant formula. If $k=0$, the same limit is zero because the inverse stays bounded; the order-$k-1$ statement is not used. ◻
:::

Apply the theorem with $L=R_K^TWR_K$ and $\tau=\tau_v$. For $k\geq1$, exact forceability is equivalent to the vanishing of one specified numerator coefficient. This is a proved finite link between numerator data and forcing, not a new scattering-amplitude relation. The regulator limit is an algebraic diagnostic of this finite matrix, not a continuum limit or a new exponent.

## What adding a generator actually changes

::: {#prop:update .proposition}
**Proposition 15** (One-row and batch updates). *Let $P$ project onto a current dual obstruction space. Adjoin one row $u^T$ and set $w=Pu$. If $w=0$, the projector is unchanged. Otherwise, $$\label{eq:update}
P_{\mathrm{new}}=P-\frac{ww^T}{w^Tw},\qquad
\rho_{\mathrm{new}}=\rho-\frac{(\tau^Tw)^2}{w^Tw}.$$ For a batch of new rows, subtract instead the orthogonal projector onto the span of their projected column vectors $Pu_i$.*
:::

::: proof
*Proof.* Within $\operatorname{im}P$, the new row imposes the single equation $w^Tx=0$. Its orthogonal complement in that space is $\operatorname{span}w$, unless $w=0$. The projector subtraction and target evaluation follow. The same argument uses the span of all projected rows for a batch. ◻
:::

For one effective new row, $\|P-P_{\mathrm{new}}\|_F^2=1$. More generally this distance is exactly the rank lost for nested projectors. Thus an unweighted projector distance can give the same score to additions with entirely different target gain. The numerator $(\tau^Tw)^2$ in [\[eq:update\]](#eq:update){reference-type="eqref" reference="eq:update"} supplies the missing target information.

A zero immediate gain is not a valid pruning rule for future additions. On one site take $\tau=(1,-1)$, first add $u_1=(1,1)$, and then add $u_2=(1,0)$. The residuals are $2,2,0$. The first admissible row has zero immediate gain, but the two rows together force the target. Monotonicity under adjoining rows does not imply a diminishing-returns law, and a greedy rule may discard useful combinations.

The accompanying rational checker verifies the polynomial coefficient identity, positive-weight invariance, and rank-one update on 50 specified finite systems of dimensions two through six. The general statements rest on the proofs above, not on extrapolating those controls.

# The cut theorem and two necessary corrections

::: {#thm:cut .theorem}
**Theorem 16** (Necessary cut-determinant condition). *Assume a fixed finite family of admissibly labelled site and edge rows completes from $T$. For every nonempty $U\subseteq V\setminus T$, the labels of site generators in $U$ together with labels of edges crossing $\partial U$ contain two vectors with nonzero determinant.*
:::

::: proof
*Proof.* Choose the first vertex of $U$ forced in a completing sequence. At that moment the known set is disjoint from $U$. Sum its forcing witness over all vertex blocks in $U$. Internal edge rows cancel. A crossing row contributes its label with a sign, and a site row in $U$ contributes its label. The total is the nonzero anti-diagonal vector $(a,-a)$ at the newly forced vertex.

If all surviving labels span a subspace of dimension at most one, then either they are all zero, which cannot yield $(a,-a)$, or they span the line through one admissible nonzero label $x$. Since the coordinates of $x$ have nonzero sum, no nonzero multiple of $x$ lies on the anti-diagonal. This is again impossible. The surviving labels must therefore span $\mathbb Q^2$, equivalently some pair has nonzero determinant. ◻
:::

The proof retains *crossing-edge* labels. Replacing them by local site generators changes the theorem and invalidates the inference. It also retains label admissibility: a forbidden anti-diagonal label would itself force a target without providing two independent labels.

## Local seeding is not necessary

On a two-vertex edge with label $(1,0)$, place generator $(0,1)$ at the first vertex and generator $(1,0)$ at the second. Neither vertex has two independent initial site generators. Nevertheless, edge transport brings $(1,0)$ to the first vertex, and subtracting its $(0,1)$ generator gives $(1,-1)$. Thus a first force can occur without the claimed local seed.

This example stalls at the other vertex and is not a complete low-score construction. A stronger control is the complete four-vertex family in Section [9](#sec:family){reference-type="ref" reference="sec:family"}: at parameter two, its first forced vertex has *no* initial site generator, while the three generators occupy three different sites. The distinction between a local seed and transported information is therefore essential even for complete forcing.

The earlier six-site, seven-direction baseline has $\binom{42}{3}=11,480$ sets of three distinct placements. Of these, $\binom63\,7^3=6,860$ use three distinct sites. A restriction demanding two generators at one site omits every one of those cases. Its negative output cannot certify the unrestricted baseline.

## Passing every cut is not sufficient

::: {#ex:cutcounter .example}
**Example 17** (All cuts pass, but no vertex forces). Use the $(2,3)$ tower. Give all three horizontal edges label $(1,0)$. On the first vertical rail use $(0,1)$ then $(1,1)$; on the second use $(0,1)$ then $(0,1)$. Place three generators: $(1,0)$ at $(1,2)$ and $(1,1)$ at each of $(2,1)$ and $(1,1)$. Start with no known vertices. Then $n=6,m=7,r=3$, so $S=5/3$.

All $63$ nonempty cuts have two independent surviving labels, but the exact forcing closure is empty. The six integer dual identities in the accompanying certificate verify that no vertex can be the first forced vertex. The retained certificate is `kt_11_6_minus_generator.json` [@BeasleyFrontier].
:::

This finite counterexample fixes the search logic. A failed cut is enough to reject completion. A passed cut requires the exact forcing test. If cuts pass, forcing fails, and a generator budget remains, a depth-first search must still examine the allowed extensions; it must not stop merely because the necessary screen has ceased rejecting.

# A complete four-vertex classification and its projector {#sec:family}

Use vertices $0,1,2,3$ in the order of the source matrix. With parameter $q\in\mathbb Q$, let the seven rows be $$\label{eq:rows}
A(q)=\begin{pmatrix}
1&0&0&0&-1&0&0&0\\
0&0&1&0&0&0&-1&0\\
1&q&-1&-q&0&0&0&0\\
0&0&0&0&0&1&0&-1\\
0&0&1&1&0&0&0&0\\
0&0&0&0&0&0&1&1\\
0&1&0&0&0&0&0&0
\end{pmatrix}.$$ The first four are edge rows; the last three are site generators. The topology is the fixed four-vertex tower. Parameter admissibility requires $q\ne-1$. The rational family is algebraically meaningful for every rational $q$; a general rational label can be replaced by an integer multiple for a corresponding integer-row comparison, while the benchmark itself requires integer input labels.

For coefficients $c=(c_0,\ldots,c_6)$, the output by vertex is $$\begin{aligned}
\label{eq:witnessfamily}
w_0&=(c_0+c_2,qc_2+c_6), &
w_1&=(c_1-c_2+c_4,-qc_2+c_4),\\
w_2&=(-c_0,c_3), &
w_3&=(-c_1+c_5,-c_3+c_5).\nonumber
\end{aligned}$$ These formulas fix all signs and coefficient conventions needed to reproduce the classification.

::: {#thm:q2 .theorem}
**Theorem 18** (Fixed-family completion). *Starting with no known vertices, the row system [\[eq:rows\]](#eq:rows){reference-type="eqref" reference="eq:rows"} completes under fresh-vertex forcing if and only if $q=2$.*
:::

::: proof
*Proof.* Consider a first force. If vertex zero is the target, vanishing at vertices two and three gives $c_0=c_3=c_1=c_5=0$. Vanishing at vertex one then gives $c_4=c_2=qc_2$. The target's first coordinate is $c_2\ne0$, so $q=1$. The remaining target-sum equation can be satisfied by choosing $c_6$.

If vertex two is first, vanishing at vertex zero gives $c_2=-c_0$ and $c_6=qc_0$. Vanishing at vertices one and three, together with $w_2$ anti-diagonal, yields $(q-2)c_0=0$. Since $-c_0\ne0$, necessarily $q=2$. If vertex one or three is first, the other zero-block equations force its two coordinates to be equal; their anti-diagonal sum condition then forces both to vanish. Neither can be a first target. Thus a first step is possible only at $q=1$ or $q=2$.

At $q=1$, vertex zero can be forced but no other vertex can subsequently be forced while the known set is contained in $\{0\}$. For target one, the zero conditions at vertices two and three make its two coordinates equal. For target two, the zero conditions at one and three force its second coordinate to vanish, and the anti-diagonal condition kills its first coordinate. For target three, the zero conditions at one and two again make its two coordinates equal. Hence the closure at $q=1$ is contained in $\{0\}$ and cannot be complete.

At $q=2$, the following integer coefficient vectors force vertices in the order $2,0,1,3$:

::: center
   Step   Target  Coefficient vector        Target block
  ------ -------- ------------------------ --------------
    1       2     $(-1,-1,1,-1,2,-1,-2)$      $(1,-1)$
    2       0     $(3,1,-1,1,-2,1,0)$         $(2,-2)$
    3       1     $(0,0,2,0,3,0,0)$           $(1,-1)$
    4       3     $(0,-1,0,1,0,0,0)$          $(1,-1)$
:::

Substituting into [\[eq:witnessfamily\]](#eq:witnessfamily){reference-type="eqref" reference="eq:witnessfamily"} verifies zero output at every still-unknown non-target vertex. Thus the sequence is legal and completes. ◻
:::

This is a classification of one fixed topology and seed arrangement over all rational parameter values and all fresh forcing orders. It is not a classification of all four-vertex or all constructible Kakeya objects. Its complete member has score $7/4$, above $67/40$.

## The exact rank-one projector

For the initial target $v=2$ at $q=2$, the coefficient constraint kernel in [\[eq:kernelcriterion\]](#eq:kernelcriterion){reference-type="eqref" reference="eq:kernelcriterion"} is the line generated by $$c_*=(-1,-1,1,-1,2,-1,-2)^T,\qquad c_*^Tc_*=13.$$ Indeed, the zero-block equations and target sum leave exactly one free parameter, as in the proof above. The orthogonal projector in coefficient space is therefore $$\label{eq:projector}
P=\frac{c_*c_*^T}{13}.$$ Direct multiplication gives $P^T=P$ and $P^2=P$, with image equal to the legal coefficient kernel. The target functional is $b=(-1,0,0,0,0,0,0)$, so $$\label{eq:response}
bPb^T=\frac{(bc_*)^2}{13}=\frac1{13}>0.$$ The response is a finite exact diagnostic of target visibility. It does not by itself identify $P$ with a contour-integral Riesz projector, prove an analytic continuation statement, or produce a physical observable. Those are different assertions with additional hypotheses. The matrix, its kernel, and its target response are already enough for the finite forcing application.

# Finite coverage, score granularity, and admissible search reuse

## A denominator barrier for near-threshold scores

::: {#prop:granularity .proposition}
**Proposition 19**. *For positive integers $p,q$ with $q<40$, $$\frac pq\leq\frac{67}{40}\quad\Longrightarrow\quad\frac pq\leq\frac53.$$ The smallest denominator of a rational number strictly between $5/3$ and $67/40$ is $43$, attained by $72/43$.*
:::

::: proof
*Proof.* If $p/q>5/3$, then $d=3p-5q$ is a positive integer. The upper bound gives $40d\leq q$, impossible for $q<40$. For a strict upper inequality and $q\leq42$, one must have $d=1$ and $q>40$. Integrality of $p=(5q+1)/3$ requires $q\equiv1\pmod3$, which excludes $41,42$. At $q=43$, $p=72$ works. At denominator $40$, $67/40$ itself is the endpoint, not a strict improvement. ◻
:::

Here the denominator relevant to a candidate is $n-|T|$ before reduction as well as after reduction for the fraction-theoretic statement. In particular, a small-tower numerical target does not open a thin interval of scores above $5/3$. The score must land on the stronger small-denominator side.

## The baseline and the expanded finite census

The corrected baseline fixes the six-vertex, seven-edge $(2,3)$ tower labelling from the retained calibration and permits seven primitive site directions: $$(-1,2),(0,1),(1,0),(1,1),(1,2),(2,-1),(2,1).$$ With $T=\varnothing$ and three distinct placements, there are $42$ placement options and $11,480$ subsets. The archived baseline has $7,360$ cut rejections and $4,120$ remaining configurations with full forcing-and-stall certificates. The latter include $1,780$ integer forcing steps and $22,940$ terminal dual identities; none completes [@BeasleyFrontier].

::: {#res:akfinite .result}
**Recorded computational result 20** (Expanded arithmetic corpus). The preserved expanded census contains $231$ certificate bundles over $33$ specified tower/label contexts. After removing declared overlaps, it covers $481,712$ distinct configurations: the $11,480$ baseline and $470,232$ additional configurations. No configuration in that finite union supplies complete forcing at the target score [@BeasleyDAG; @BeasleyReview].
:::

The contexts include specified label modifications, an orientation change, and a specified larger direction pool. They are not every possible integer labelling. For each six-vertex, seven-edge core, the covered starting sets are the empty set with generator budget three and each singleton with budget one. Starting sets of size at least two cannot meet the target with seven retained edges, since already $7/(6-|T|)\geq7/4$.

There are $481,964$ raw configuration occurrences in the overlapping bundle presentation, but $252$ repetitions are removed from the distinct count. An older $344,400$-case report overlaps later work and is not added again. Likewise, the $24,976$ Earth--Moon graphs are a separate domain, not additional arithmetic constructions. The census statement is a finite union with explicit context and budget data, not a growth law in an unrestricted height cutoff.

## Decision reuse is a theorem about retained state

A search may avoid repeating a calculation when two nodes have identical future-relevant data. In the arithmetic setting this includes the exact row space or equivalent canonical constraints, the known set, remaining generator budget, legal placement options, and the tower context. Equality of a scalar score or rank alone is insufficient. Two subspaces of equal rank can expose different targets, and two identical current row spaces can have different legal future additions.

For graph search the same caution applies to representations. Two layer decompositions of the same union graph can admit different flips. A deduplication rule justified for color testing need not be justified for exploring a particular embedded move graph. The forty-state plateau is an explicit reminder that union-level invariants and representation-level future moves carry different information.

The earlier timing experiments show why a lower operation count must not be advertised automatically as a speedup. In one retained arithmetic comparison, the number of expensive forcing evaluations dropped from $4,120$ to $1,460$, while elapsed time remained essentially unchanged because bookkeeping had its own cost. A separate certificate-production workflow was substantially faster than its earlier reference. These are measurements under different tasks, not a universal performance ratio [@BeasleyStatus].

# Exact exclusion with one unrestricted generator direction {#sec:parametric}

A finite slope pool does not exhaust the integer directions. The following extension uses the same fixed six-vertex edge core as the calibration but allows one generator label to leave every bounded slope pool. A first-escape argument turns this unbounded question into a finite, exactly checked cover.

## A finite cover of the first possible escape

Fix a finite rational row system and a proper known set $K$ that is closed under its forcing rule. Let $C$ have independent columns spanning the dual space $\mathcal N_K$, and let $$r_t=C^T\tau_t\ne0\quad(t\notin K).$$ A site $s$ can receive a row $u(a,b)^T$, where $u(a,b)=a e_{s,0}+b e_{s,1}$. Set $$A_s=C^Te_{s,0},\qquad B_s=C^Te_{s,1},\qquad
w(a,b)=aA_s+bB_s.$$

::: {#lem:firstescape .lemma}
**Lemma 21** (First-escape classification). *After adjoining $u(a,b)^T$, target $t\notin K$ is immediately forceable if and only if $$\label{eq:firstescape}
w(a,b)\ne0,\qquad r_t\in\operatorname{span}_{\mathbb Q}w(a,b).$$ For each fixed site and target, all possible labels satisfy a homogeneous linear system in the two variables $a,b$: $$\label{eq:wedge}
r_{t,i}(aA_{s,j}+bB_{s,j})-
 r_{t,j}(aA_{s,i}+bB_{s,i})=0
\quad\text{for all }i,j.$$ Its solution space has dimension zero, one, or two. After rejecting zero images and forbidden labels $a+b=0$, its first-escape possibilities have a finite set of representatives: none, one projective ray, or one nonzero-image representative for a two-dimensional solution space.*
:::

::: proof
*Proof.* Write a dual vector as $Cx$. The new row imposes $w^Tx=0$, while the target pairs with it as $r_t^Tx$. Thus the target vanishes on every surviving dual vector exactly when $\ker w^T\subseteq\ker r_t^T$. Since $r_t\ne0$, this is equivalent to [\[eq:firstescape\]](#eq:firstescape){reference-type="eqref" reference="eq:firstescape"}. Collinearity is precisely the wedge system [\[eq:wedge\]](#eq:wedge){reference-type="eqref" reference="eq:wedge"}.

In dimension one, every nonzero solution is a rational multiple of one primitive integer vector, and these multiples impose the same row-space constraint. In dimension two the wedge system is identically zero, so both $A_s$ and $B_s$ belong to the line through $r_t$. Every nonzero image then imposes the same constraint in kernel coordinates. Equivalently, all such added rows have the same span modulo the base rows and the known-coordinate rows. Consequently they have the same entire future forcing closure starting from $K$, not merely the same first step. At least one of $(1,0),(0,1),(1,1)$ has nonzero image whenever the image map is nonzero; all three labels are admissible. Zero-image labels cannot cause a first escape and need no further representative. ◻
:::

The argument includes arbitrary rational projective directions and hence every admissible integer label, primitive or not. There is no height cutoff. The two-dimensional case must not be replaced by an assertion that every label is literally equal: what agrees is the enlarged relation space modulo the known coordinates.

::: {#lem:closedbarrier .lemma}
**Lemma 22** (Closed barriers suffice). *Suppose the initial known set is contained in a proper set $T$. If, for each $v\notin T$, there is an integer vector $h_v$ such that $$R h_v=0,\qquad h_v|_T=0,\qquad \tau_v^Th_v\ne0,$$ then no legal forcing sequence from the initial data completes.*
:::

::: proof
*Proof.* Every proposed first step outside $T$ would pair to zero with $h_v$ through its representation by relation rows and coordinates already known inside $T$. Its nonzero target multiple instead pairs nontrivially. This is a contradiction. Induction keeps every legal step inside $T$. ◻
:::

The checker need not establish that $T$ was reached. Granting extra known vertices only makes forcing easier, and a proper closed superset already excludes completion. Similarly, the base set $K$ used in Lemma [21](#lem:firstescape){reference-type="ref" reference="lem:firstescape"} may be any checked closed superset of the initial known set. Any completion from the actual initial data would also complete with $K$ granted in advance.

## The fixed edge core and the new theorem

Number the tower vertices as $$0=(1,1),\quad1=(1,2),\quad2=(1,3),\quad
3=(2,1),\quad4=(2,2),\quad5=(2,3).$$ The seven oriented edges and labels are $$\begin{aligned}
&(0,3),(1,4),(2,5) &&\text{label }(1,0),\\
&(0,1),(3,4),(4,5) &&\text{label }(0,1),\\
&(1,2) &&\text{label }(1,1).
\end{aligned}$$ These are expanded independently from the preserved $(2,3)$ tower input by the checker. Let $$\label{eq:pool}
\mathcal P=\{(-1,2),(0,1),(1,0),(1,1),(1,2),(2,-1),(2,1)\}.$$ A placement is a pair of a site and a member of $\mathcal P$, giving 42 choices.

::: {#thm:onefree .theorem}
**Theorem 23** (One unrestricted direction on the fixed calibration core). *On the preceding fixed labelled tower, start with no known vertices. Choose two distinct placements from the 42 choices and one further site generator with any integer label $(a,b)\ne(0,0)$ satisfying $a+b\ne0$. None of these three-generator systems completely forces the graph under the nonzero-multiple rule.*
:::

::: proof
*Computer-assisted proof.* There are $\binom{42}{2}=861$ fixed pairs and six choices of the site for the unrestricted label, hence 5,166 site-parameter families. For each pair, the producer supplies a proper base set $K$ and an integer-column basis $C$ of $\mathcal N_K$. The independent checker verifies annihilation by all base and known-coordinate rows, independence of the columns, and $$\operatorname{rank}R_K+\operatorname{columns}(C)=12.$$ It also checks $r_t\ne0$ for every target outside $K$, establishing closure.

The checker recomputes the full wedge system [\[eq:wedge\]](#eq:wedge){reference-type="eqref" reference="eq:wedge"} using fraction-free integer elimination, whereas the producer uses rational row reduction and pivot-based collinearity equations. It requires exact agreement of the representative cover, with no missing or duplicated representatives. Across the 861 pairs there are 6,112 representative checks, counted within their fixed-pair contexts.

For every representative the supplied proper barrier contains $K$ and carries an integer separating vector for every target outside it. All 25,498 target-dual identities pass integer multiplication and support checks. Lemma [22](#lem:closedbarrier){reference-type="ref" reference="lem:closedbarrier"} excludes every representative; Lemma [21](#lem:firstescape){reference-type="ref" reference="lem:firstescape"} extends the exclusion to the complete unbounded label family. Labels that allow no first escape from $K$ are excluded by that closed set itself. The full finite certificate and both implementations accompany this edition. ◻
:::

Every putative completion here would have score $(7+3)/6=5/3$. The theorem therefore excludes genuine target-score parameter families, not merely numerically poor candidates. It includes the original distinct three-placement pool baseline and extends beyond every finite bound on the third label. It does *not* cover simultaneous unrestricted changes to two or three generators, new edge labels, or different towers. It is not a universal six-free-vertex theorem.

::: {#thm:singleton .theorem}
**Theorem 24** (One initially known site and one unrestricted generator). *On the same fixed labelled tower, no system with one initially known vertex and at most one arbitrary admissible integer site generator completely forces all six vertices.*
:::

::: proof
*Computer-assisted proof.* Apply the same first-escape cover to each of the six initial known singletons and six generator sites. The resulting 36 site-parameter families have 38 representatives. The separate certificate checker verifies every base nullspace and all 152 integer target-dual identities for proper barriers. This excludes the one-generator systems. Removing a generator cannot enlarge the forcing closure, so the zero-generator case is included. ◻
:::

With one generator the score is $8/5$. With two or more initially known vertices the fixed seven edges alone already cost at least $7/4$, above the benchmark. Consequently the entire nonempty-initial-known-set route at target score is excluded for this fixed edge-labelled core. The remaining empty-known-set search must leave the one-unrestricted-generator family of Theorem [23](#thm:onefree){reference-type="ref" reference="thm:onefree"} or change the edge data.

## Controls and counting discipline

The unchanged positive controls complete at $11/6$ and $7/4$, while deleting the specified fourth generator from the six-vertex control leaves no first force. In addition, the *parameter-class enumerator* is positively controlled: retaining the first three calibration generators and allowing an arbitrary fourth recovers completing representatives at site 2 with label $(0,1)$ and site 5 with label $(2,-1)$. The independent checker confirms these completions by rank augmentation. Deliberately dropping a representative class, zeroing a dual, and corrupting a nullspace basis are all rejected.

The fresh proof counts are summarized separately from the older finite census:

::: center
  Verified item                      Empty initial set   Singleton initial set
  -------------------------------- ------------------- -----------------------
  Fixed base contexts                              861                       6
  Site-parameter families                        5,166                      36
  Representative barriers                        6,112                      38
  Integer target-dual identities                25,498                     152
  Completing representatives                         0                       0
:::

These are overlapping parameter families, not counts of disjoint new configurations. They must not be added to 481,712. The certificate mechanism provides a written, finite-to-unbounded implication plus exact finite checking; it has not been formalized in Lean and is not an official Epoch verifier execution.

# What the formal supplement certifies {#sec:formal}

The public downstream project *Arithmetic Kakeya Finite Bridges* contains five final Lean modules and a scoped verification gate [@BeasleyLean]. Its two principal mathematical statements are Theorem [11](#thm:denom){reference-type="ref" reference="thm:denom"} for finite integer rows and the iterative necessary-cut statement underlying Theorem [16](#thm:cut){reference-type="ref" reference="thm:cut"}. A representation adapter identifies finite pair-valued rows with explicit two-coordinate rows without adding generators. It proves the named equivalence `canForce_iff_stepQ` through the integer step and denominator bridge.

The public snapshot is pinned to Lean 4.33.0 and a mathlib revision. The verification contract builds all five modules, replays them with `leanchecker`, audits declarations by defining module, allows only the standard reported axioms `propext`, `Classical.choice`, and `Quot.sound`, and rejects deliberately false boundary claims. The public verification run inspected for this edition is successful at commit `a2f239e52c7fba0c6550b5602a211e84b27ce916` (run 34888102814). No local Lean installation was available during the assembly of this manuscript, so this is current source-and-run verification, not a fresh local compilation.

Earlier formal work additionally covers the explicit four-vertex parameter classification, projector identities, local-seeding witnesses, and finite Earth--Moon counting kernels. These retain their historical revision-specific evidence. The larger historical package contained $95$ named declarations across nine modules, including supporting lemmas and unrelated topics. That number is not a claim of $95$ new Kakeya results.

::: center
  Claim                                             Certification boundary
  ------------------------------------------------- ----------------------------------------------------------------------------------------
  Rational/integer nonzero-multiple bridge          In the current public finite Lean supplement.
  Iterative necessary-cut theorem                   In the current public finite Lean supplement, with label and row hypotheses.
  Fixed four-vertex classification and projector    Historical exact formal kernels; explicit written data given here.
  Topology-to-Euler implication for planar layers   Used as standard mathematics; not promoted from finite counting alone.
  $8,044$-profile nineteen-vertex census            Archived semantic and Boolean proof checking, not complete Lean formalization.
  $481,712$ arithmetic configurations               Finite checker/corpus statement, not a Lean theorem of unrestricted search exhaustion.
  Either full Epoch target                          Not established.
:::

The separate Atlas formalization certificate was also checked against its actual source and hosted job. It certifies selected finite kernels and a 90-card classification map, not all card captions as theorems. The inspected kernel includes the corrected B56 rank obstruction, but not the strong B81 statement contradicted by the later working note. The new first-escape enumeration, probe-residue bridge, and computer-assisted unbounded-direction exclusions in this edition are outside those existing Lean runs.

The public supplement is a downstream project using mathlib, not an accepted upstream mathlib contribution. It makes no coefficient-one equivalence, converse-cut theorem, winning construction, new exponent, or analytic transport claim. Private development histories and mixer payloads are not part of that public export.

# Connection energy, targets, and coherent reduction {#sec:connection}

## A field on the graph of search states

A finite operator identity supplies an exact geometric measure of change, provided the field and connection are specified. The note *Non-normality is connection energy* takes a finite graph, Hermitian diagonal blocks $D_s$, and a skew-adjoint block matrix $A$ whose nonzero edge blocks are unitary [@BeasleyConnection]. Put $H=D+A$. Then $$\label{eq:connectionenergy}
\frac18\|[H,H^*]\|_F^2
=\sum_{\{s,t\}}\|D_s-A_{st}D_tA_{st}^*\|_F^2.$$ Indeed $[H,H^*]=-2[D,A]$, and each edge block of $[D,A]$ is $(D_s-A_{st}D_tA_{st}^*)A_{st}$. Unitary invariance and the two orientations give the factor eight. The reverse-edge sign cancels under conjugation. Thus $H$ is normal exactly when $D$ is parallel for the induced endomorphism connection. On a connected graph, such fields correspond to the Hermitian endomorphisms fixed by all loop holonomies.

The self-commutator and graph-connection frameworks are classical; the note isolates their exact identification for this block construction, with a June 18, 2026 precursor. No claim of a new general theory of connections is needed. More importantly for search, $D_s=cI$ at every state gives zero energy for every permitted graph. Normality by itself cannot certify either benchmark.

For a search-state graph, choose $D_s=P_s$, where the projector has an independently defined mathematical role. With a common labelled ambient space and identity transports, $$\label{eq:projectorenergy}
\|P_s-P_t\|_F^2=\operatorname{rank}P_s+\operatorname{rank}P_t-2\operatorname{tr}(P_sP_t).$$ The relevant graph is now a graph of represented candidates, not the candidate graph being tested for planarity. This choice detects changes of subspace, including equal-rank changes, but it is not automatically a progress functional. For nested kernels it records only rank loss; Section [7](#sec:probe){reference-type="ref" reference="sec:probe"} supplies the required target-dependent residual.

## An exact calibration in the four-vertex family

For the matrix $A(q)$ in [\[eq:rows\]](#eq:rows){reference-type="eqref" reference="eq:rows"}, the dual-coordinate kernel is the line spanned by $$h(q)=(q-1,0,-1,1,q-1,1,-1,1)^T,
\qquad N(q)=h(q)^Th(q)=2(q-1)^2+5.$$ Direct substitution gives $A(q)h(q)=0$; solving its seven equations leaves exactly this one free parameter for every rational $q$. Let $$\widehat P(q)=\frac{h(q)h(q)^T}{N(q)},\qquad
\tau_2=e_2\otimes(1,-1).$$ Then $$\begin{aligned}
\rho_2(q)&=\tau_2^T\widehat P(q)\tau_2
=\frac{(q-2)^2}{2(q-1)^2+5},\label{eq:qresidual}\\
\|\widehat P(q)-\widehat P(p)\|_F^2
&=\frac{20(q-p)^2}{[2(q-1)^2+5][2(p-1)^2+5]}.
\label{eq:qenergy}
\end{aligned}$$ To verify the second formula, use [\[eq:projectorenergy\]](#eq:projectorenergy){reference-type="eqref" reference="eq:projectorenergy"} and $h(q)^Th(p)=2(q-1)(p-1)+5$. Subtracting the squared inner product from $N(q)N(p)$ gives $10(q-p)^2$. In particular, $$\label{eq:qbridge}
\|\widehat P(q)-\widehat P(2)\|_F^2=\frac{20}{7}\rho_2(q).$$ Thus, relative to the already known completing reference, connection energy is exactly proportional to this initial-target obstruction. The projectors all have the same rank and eigenvalues. This is a genuinely target-sensitive calibration, but not a new discovery of the known $q=2$ solution or an improved score. The response $1/13$ in Section [9](#sec:family){reference-type="ref" reference="sec:family"} belongs to a different, seven-dimensional coefficient-space projector; the projector here acts on eight coordinate dimensions. Parameter $q=-1$ remains outside the benchmark label domain.

## What the preserved Earth--Moon experiment adds

The earlier September 17 assessment makes the search-state construction explicit [@BeasleyEnergyAssessment]. For each of the forty plateau states it forms the span of the legal one-flip changes in the union edge vector in $\mathbb R^{171}$. Removing an edge from one layer does not remove it from the union if the other layer retains it. The common vertex labels fix identity transport between these ambient spaces.

The exact calculation finds forty distinct move-space projectors. All 82 undirected neutral state edges have positive projector energy, including 38 comparisons with equal ranks; their summed unweighted energy is 362. The old scalar independent-triple count is constant, while the available linear subspaces change. However, the span of individually legal moves does not certify that arbitrary linear combinations, signs, or orders are feasible paths.

There are thirteen missing-edge coordinates capable of destroying one of the original five independent triples. Summing their projected squared norms gives a target exposure. Eight states have zero exposure; thirty-two have positive exposure. This is checked against the actual local moves, rather than inferred from the scalar connection energy.

The same preserved path probe follows all 758 immediate exits landing at six triples. Each retains all five original triples. It then finds 142 two-flip routes with count sequence $5\to6\to6$ that destroy an original triple. One stored route replaces $(6,15)$ by $(16,17)$ and then $(6,16)$ by $(17,18)$, destroying the original triple $(0,17,18)$. All 9,962 third flips from those selected endpoints still have at least six triples. Moreover, all 2,786 distinct union graphs encountered in that restricted probe have explicit proper nine-colorings. No endpoint in it qualifies.

These are earlier same-day calculations preserved and rerunnable in their original focused package, not an unrestricted radius-three search or a measured acceleration from connection energy. Their contribution is to distinguish changing the identity of an obstruction from reducing its scalar count. The old forty-state plateau and the newer path probe are not the same experiment.

## What the amplitudes and associahedron lineage supplies

The recovered Figueiredo thread emphasizes hidden zeros and factorization away from poles, not only denominators. The published amplitude work concerns specified particle theories and kinematic conditions [@HiddenZeros; @AllOrderSplits]. Our finite implication is instead Theorem [14](#thm:proberesidue){reference-type="ref" reference="thm:proberesidue"}: the target numerator of an explicitly constructed Gram resolvent detects exact forcing. No map from the amplituhedron or kinematic associahedron to an Earth--Moon graph is assumed.

The associahedron organizes coherent compositions. In this program, an actual algebraic realization is the September 7 Atlas determinant calculus, which retains a Schur response together with the determinant multiplier [@BeasleyCalculus]. It defines equivalence relative to an interface, allowed future attachments, and a readout. Equal isolated spectra or equal response matrices are not enough for every such readout. The public literature on compositional passive networks provides related foundational context [@BaezFong]; this elementary finite construction does not establish historical priority over that literature.

Here is a source-aware extension of the recovered determinant-only fragment. Let $$M=\begin{pmatrix}D&B\\B^T&A\end{pmatrix}>0,
\quad S=A-B^TD^{-1}B,
\quad b=\binom{b_I}{b_B},\quad c=\binom{c_I}{c_B}.$$ Define $$b'=b_B-B^TD^{-1}b_I,\qquad
c'=c_B-B^TD^{-1}c_I,\qquad
\alpha=c_I^TD^{-1}b_I.$$ Block elimination gives the paired identities $$\label{eq:sourceschur}
\det M=\det D\,\det S,\qquad
c^TM^{-1}b=\alpha+(c')^TS^{-1}b'.$$ For any admissible boundary load $K$, replace $A,S$ by $A+K,S+K$; the other retained registers do not change. Thus an exact replacement must retain $S$, the determinant multiplier, both reduced sources, and the already eliminated scalar $\alpha$.

::: {#prop:coherentschur .proposition}
**Proposition 25** (Coherence of exact elimination). *For a positive-definite finite matrix, eliminating disjoint internal sets in any order gives the same remaining Schur matrix, reduced sources, total determinant multiplier, and eliminated scalar as eliminating their union at once.*
:::

::: proof
*Proof.* For any prescribed boundary vector, the internal linear equations have a unique solution. Successive elimination computes that same solution by block Gaussian elimination, so substitution gives the same Schur matrix and reduced sources. The multiplier is $\det M_{II}$ by the block determinant identity applied to the full internal block, and the scalar is $c_I^TM_{II}^{-1}b_I$. All pivots are positive definite, so each order is admissible. ◻
:::

A fresh rational control checks all 24 orders for four internal coordinates and two boundary coordinates, followed by four boundary loads. All five registers agree. The old pair $$\begin{pmatrix}2&1\\1&2\end{pmatrix},\qquad
\begin{pmatrix}8&2\\2&2\end{pmatrix}$$ has the same reduced response $3/2$ but determinants 3 and 12, showing why a response-only replacement loses information. This is a concrete coherence calculation, not a new particle amplitude.

By contrast, an arbitrary projected product $x\star y=P(xy)$ in an associative algebra has defect $$(x\star y)\star z-x\star(y\star z)
=P\big[x(I-P)(yz)-(I-P)(xy)z\big].$$ This recovered identity says exactly which discarded intermediate terms re-enter. Homotopy transfer requires additional differential and contraction data; the presence of an associahedral diagram alone does not supply them. The source note and finite Lean coherence module retain those boundaries [@BeasleyNumerators].

## Corrections that remain outside the new proof

The older transport manuscripts supply motivation, not certification of the new search. Pairwise angular separation is not joint linear independence; the long-scale incidence bounds needed for Euclidean Kakeya are not obtained from finite census measurements. A nonorthogonal similarity also does not carry an ordinary orthogonal projector by unqualified conjugation: the pairing and probe must be transported. The new integer certificate checker avoids that issue by testing the exact row relations and target pairings directly.

The historical Atlas B81 asserted a strong commuting differential decomposition. The September 6 working note records an exact counterexample to its strengthened finite version at $(n,k)=(2,0)$: coefficient rank six and augmented rank seven. The later formalization map still lists a model-development lane, but the inspected Lean core does not prove B81. Accordingly no ambient-flatness premise from that caption enters the present theorems. Similarly, B56's old disjointness slogan has been replaced in the formal core by the narrower $\mathbb R^2\to\mathbb R^3$ nonsurjectivity obstruction. A certificate for that finite statement is not a certificate for the earlier prose [@BeasleyMethod; @BeasleyAtlasKernel].

One corrected finite matrix fact from the transport review is retained for reference. For real $A=A^T>0$, $E^T=-E$, and $B=A^{-1/2}EA^{-1/2}$ with nonzero eigenvalue pairs $\pm i\sigma_j$, $$\log\det(A+tE)-\log\det A=\sum_j\log(1+t^2\sigma_j^2)\geq0.$$ Factor through $A^{1/2}$ and use the real skew $2\times2$ blocks of $B$. The quadratic coefficient is $\|B\|_F^2/2$, not a universal negative correction. The repaired Fourier projector assembly and its changed threshold ranks likewise remain corrections to their specified model, not ingredients in the exact arithmetic exclusion [@BeasleyReview].

# Evidence, reproducibility, and publication boundaries {#sec:evidence}

## New checks and the complete arithmetic replay

The new one-unrestricted-generator producer enumerates 861 base pairs and certifies 5,166 site-parameter families. Its independent checker uses a different rank algorithm, verifies the complete first-escape cover, and checks 25,498 integer target-dual identities. It rejects three deliberately corrupted certificates. A separate singleton-known-set certificate adds 36 site-parameter families and 152 checked integer target duals. The producer's exact JSON certificates reproduce byte-for-byte on rerun; timing transcripts are not treated as immutable mathematical output.

The probe-calculus script checks 50 finite rational systems, including determinant numerator coefficients, positive-weight kernel invariance, rank-one updates, and the zero-first-gain control. A source-aware Schur calculation checks all 24 orders of four internal eliminations and four later boundary loads. These finite controls accompany general written proofs.

Crucially, the unchanged preserved aggregate checker also completes in this edition. It verifies all 231 arithmetic proof bundles, all 33 declared core families with their score-admissible initial known sets, and the deduplicated union of 481,712 arithmetic configurations. It separately verifies all 24,976 Earth--Moon modifications: 19,620 density rejections and 5,356 explicit nine-coloring rejections, with no unresolved cases. The first successful fresh transcript records approximately 25.85 seconds in this workspace. That is a replay time for this run, not a search speed law.

The historical aggregate source and inputs are included byte-for-byte; its original stored audit and the new replay audit remain separate. The earlier Version 1 incomplete attempts are not silently relabeled as successes. The new unbounded parameter exclusions overlap the old pool domains and do not increase the published distinct-configuration count by simple addition.

## Preserved focused checks and what was not re-proved

The earlier same-day focused package retains the four-vertex dual-projector calibration, arithmetic and coloring controls as described in its own report, the forty-state move-space study, and the restricted two/three-flip probe. Its exact inputs, scripts, prior outputs, and scope are preserved separately from the new parameter search. The prior Figueiredo review likewise retains its finite amplitude controls and recovered notes. Neither report is treated as independent confirmation of a theorem that it merely cites.

The nineteen-vertex threshold census remains an archived computer-assisted result. Its full Boolean proof archive was not newly reconstructed or replayed for Version 2. The preserved hard-backup record and source identifiers remain available in the author ledger, and the full backup is a separate Library artifact. Its 100-edge ten-chromatic survivor still has unknown thickness. No fresh Lean compilation, official Epoch verifier run, accepted benchmark submission, or upstream mathlib acceptance is claimed.

## Self-contained reproduction and author-only provenance

The delivered author-review package contains the manuscript and editable source; the new exact producers and independent checkers; the complete preserved arithmetic/graph aggregate corpus; the prior focused assessment packages; and an author-facing recovery ledger with the distinct master-list and Atlas versions. Python's standard library is sufficient for the principal new checks and full aggregate replay. Run from the package root:

    python repro/verify_release.py
    python repro/verify_release.py --full

The first command checks payload hashes, regenerates the new certificates, compares exact outputs, and executes the new independent checkers and probe-calculus controls. The second also reruns the entire preserved aggregate in a temporary copy, leaving the archived inputs and historical audit unchanged. The older Atlas-calculus demonstration has its own requirements and is not silently included in the standard-library verification claim.

The author ledger is not a sanitized public release. It retains private source identifiers, historical drafts and corrections, and a bounded old-chat retrieval chronology. Before posting a public supplement, separate that ledger and unrelated old master material from the intended proof/code export. The full old nineteen-vertex archive and a locally built Lean environment are not claimed to be inside this package. No original Drive file, research branch, manuscript, or library archive was overwritten.

# Remaining mathematical directions

The Earth--Moon host theorem excludes edge deletion inside $C_7[K_4]$. The nineteen-vertex restrictions narrow the possible endpoint but do not make it empty. A next successful construction must exhibit both two planar layers and the chromatic lower bound on the same graph. The 100-edge survivor's actual thickness remains a precise unresolved question. The move-space study suggests tracking which old independent triples are destroyed, not only their number, but it does not prove that a path to a winner exists.

For the fixed six-vertex arithmetic core, Theorem [24](#thm:singleton){reference-type="ref" reference="thm:singleton"} closes the entire score-admissible nonempty-initial-known-set route. Theorem [23](#thm:onefree){reference-type="ref" reference="thm:onefree"} also closes the specified empty-known-set family with two pool placements and an arbitrary third direction. Remaining possibilities include two or more jointly unrestricted generator directions, changed edge labels, other tower geometries, and larger towers. It is not enough merely to raise a bound on the third label while retaining the other premises of Theorem [23](#thm:onefree){reference-type="ref" reference="thm:onefree"}.

The finite first-escape method can be applied to another fixed rational core after its actual input rows and admissible site families are supplied. With several unrestricted generators, the collinearity conditions can become higher-degree incidence conditions; the two-variable linear classification here does not automatically cover that problem. Any claimed extension needs its own coverage theorem and finite certificate contract.

The productive common principle is to retain what a later operation can see. In arithmetic this means target pairings, exact row-space constraints, admissible future additions, and cost. In Earth--Moon it means represented planar layers, move legality, actual independent triples, and coloring certificates. Connection energy can record subspace changes, but exact primal or dual evidence must decide whether those changes meet the mathematical objective.

# Conclusion

The recovered master-equation, Atlas, and amplitude-inspired work improves the construction program when its claims are translated into explicit operations. In this edition that translation yields a target-sensitive determinant criterion, exact kernel-update formulas, a finite first-escape classification for an unbounded generator label, and two independently checked parameter-family exclusions. The complete earlier arithmetic/graph aggregate replay now passes, while historical and fresh evidence remain separately identified.

Neither benchmark construction has been obtained. The advance is nevertheless mathematical rather than cosmetic: one direction can now range over all admissible integers without leaving the proved exclusion, and the source-aware reduction and projector formulas specify what may safely be reused. The remaining search must leave those exact hypotheses rather than repeat a larger numerical version of an already closed family.

# The exceptional four-cycle forest certificate {#app:c4}

Number the vertices of $C_4[K_2]$ as $0,\ldots,7$, with fibre $i$ consisting of $2i,2i+1$. The following edge sets form a partition into forests: $$\begin{aligned}
F_1={}&\{01,02,06,34,45,46,67\},\\
F_2={}&\{03,07,12,16,24,25,57\},\\
F_3={}&\{13,17,23,35,47,56\}.
\end{aligned}$$ Here $uv$ denotes the unordered edge $\{u,v\}$. Their sizes are $7,7,6$, summing to the $20$ edges of $C_4[K_2]$. Direct connectivity/acyclicity checking verifies the three forests. Applying the two-clone construction gives layer sizes $36,28,24$, summing to the $88$ edges of $C_4[K_4]$.

For $n\geq5$, the formula in Theorem [5](#thm:thickness3){reference-type="ref" reference="thm:thickness3"} gives forest sizes $2n-2,2n-2,n+4$, and corresponding planar layer sizes $$10n-8,\qquad 8n-8,\qquad4n+16.$$ Their sum is $22n$, as required. These formulas also provide a useful implementation check independent of a drawing.

# Exact checks and certificate interfaces {#app:checks}

An arithmetic certificate stores the original admissible input, the expanded counts, each forced vertex with integer row coefficients and full output vector, and a terminal dual for every remaining vertex. Its checker reconstructs rows from the tower rather than trusting a producer-supplied matrix. It verifies support, nonzero target, target sign, fresh-vertex order, and every final dual identity, then recomputes the rational score.

A graph layer certificate stores the edge set and a rotation system. Every undirected edge yields two darts. Reversing darts and applying the cyclic neighbor permutation produces face orbits; a connected orientable rotation system with $v-e+f=2$ describes a spherical embedding. Disconnected components are checked separately, and isolated vertices are handled explicitly. A supplied proper coloring is verified by testing every edge; its logical role remains an upper bound.

The new parameter certificate additionally stores a complete rational nullspace basis for each base context, the first-escape representative cover, and proper closed-set dual barriers. The checker need not trust a claimed forcing order or an optimized numerical objective. The aggregate replay and the new parameter certificate have different schemas and remain separate packages. Section [14](#sec:evidence){reference-type="ref" reference="sec:evidence"} gives the complete entry points.

# Correction ledger

  Earlier inference or reporting risk                                                    Corrected statement
  -------------------------------------------------------------------------------------- -------------------------------------------------------------------------------------------------------------------------
  Inflated-cycle independence scaled by clique size                                      An independent set uses at most one vertex per clique; $\alpha(C_n[K_r])=\lfloor n/2\rfloor$.
  Whole-graph counting never detects the $r=4$ family                                    It already rejects $n=4,5$, is saturated at $n=6$, and passes for $n\geq7$.
  Edge deletion might repair $C_7[K_4]$ while retaining ten colors                       Every biplanar subgraph is nine-colorable by the explicit one-join-deletion coloring.
  Every first arithmetic force needs two local initial generators                        Transported relations refute this; the complete four-vertex example starts at an unseeded vertex.
  Passing all cuts certifies completion                                                  The six-vertex $5/3$ control passes all $63$ cuts and forces no vertex.
  A rational witness proves a coefficient-one integer target                             Only the nonzero-multiple equivalence is proved; integer lattices need not be saturated.
  Stop extending a branch as soon as its necessary cuts pass                             When forcing still fails and legal budget remains, extensions still require examination.
  One rank or one score determines future search behavior                                Exact subspace, known set, remaining options, budget, and represented context may all matter.
  Archived counts can be freely added                                                    Overlapping bundles and nested thresholds must be deduplicated; graph and arithmetic domains remain separate.
  A five-triple planar graph and a different ten-chromatic graph jointly certify a win   Both properties must hold for one graph with one checked certificate.
  Numerical threshold rank is exact capacity                                             It depends on matrix validity and tolerance; it cannot replace integer rank or a uniform analytic bridge.
  Older formal gaps persist unchanged                                                    The public September 14 supplement now closes the denominator and iterative cut bridges, within its finite assumptions.
  A successful mathematics job means the entire old workflow succeeded                   The two census jobs passed; the separate source-export job failed and later preservation is recorded separately.

# Provenance and edition boundaries

This edition consolidates the recovered Earth--Moon obstruction/frontier material, the September 8 combined status and decision-certificate corpus, the September 9 Earth--Moon continuation, the September 10 arithmetic research edition, the September 14 publication review and public Lean supplement, and the September 17 focused checks. Earlier raw files are not silently rewritten or counted as separately novel results merely because they appear under several upload names.

The source review recorded $72$ matching Drive records grouped into $28$ distinct fetched-content groups; that is an inventory of records, not $72$ different papers. Some historical endpoint batches were reported without their raw producer/endpoints being recovered in the later backup. Those gaps remain explicit in the author ledger. The start of an earlier chat is not inferred from the earliest date embedded in a later exported file.

No Epoch logo, endorsement, submission receipt, DOI, or upstream mathlib acceptance is asserted. The present artifact is dated as an author-review working preprint. Exact public and private source identifiers, evidence-run distinctions, hashes of the delivered files, and the remaining release gates accompany it separately.

# The sources are not a single synchronized Atlas {#app:reconciliation}

The deeper recovery distinguishes several stores. The pre-mining Mastery Equation List is 26,472 bytes; the 46,391-byte current file preserves that entire byte sequence as a prefix and appends 30 YM-R entries. The additions include the probe-determinant insertion used to motivate Section [7](#sec:probe){reference-type="ref" reference="sec:probe"}. A different five-file "mastery equations" folder preserves and audits the October 31, 2025 research conversation. That older box is not the same master list, and its physical hypotheses and failed arithmetic claims are not inputs to the present graph or forcing proofs.

The historical plain-text Atlas has B1--B84. The recovered card package contains all B1--B90 HTML and PNG cards, plus reviewed HTML additions B94--B96 and their supporting determinant-calculus note. This is 93 numbered HTML cards, not a complete contiguous B1--B96 collection. B91--B93 were not recovered in that package. The pinned GitHub main register instead has 18 reusable-result cards and 13 project pages. The separate formal branch has a 90-card classification map and selected finite kernels. These are four different inventories, not competing counts of one synchronized object.

The most relevant version controls are:

  Source item                  How it is used in this edition
  ---------------------------- -----------------------------------------------------------------------------------------------------------------------------------------------------------
  Master probe insertion       The finite determinant lemma is retained, then applied to the explicitly defined forcing Gram. No Yang--Mills or physical interpretation is imported.
  Atlas kernel and dual test   The actual target and annihilator are retained. Primal coefficient and dual-coordinate projectors have different tests.
  B16 and B95                  Pairwise separation, collective spectral count, and exact rank are different readouts. B95's reviewed three-cycle control makes the distinction explicit.
  B48 and Atlas calculus       Exact elimination retains a determinant multiplier. The source-aware extension also retains two reduced probes and the eliminated scalar.
  B70 and B83                  Kernel direction and frame/dual pairing matter. A basis change does not manufacture a new independent direction.
  B81                          The strong commuting differential ansatz has a later exact counterexample. A model-development label is not a Lean proof of it.
  B56 and B90                  The formal core certifies a nontransverse-intersection obstruction and specified local normal forms, not the stronger historical captions.
  B94--B96                     Padding and spectral-profile claims retain their reviewed scope; the phase/count return interpretation remains an unbuilt model, not an energy law.

Old-chat retrieval found amplitude/associahedron leads in 2025--2026 and the explicit July 27, 2026 numerator emphasis. These are provenance leads, not newly recovered complete transcripts or proof certificates. The original statement naming "three unknown symmetries" was not recovered. Neither the three related amplitude theories nor the three bands of a separate transport expansion is silently substituted for that missing claim. The author ledger records dates, exact recovered files, inspected revisions, and these limits.

#### Assistance and priority.

The research program is author-directed and AI-assisted. The new scripts, checks, mathematical synthesis, and manuscript revision were produced in this working session. Standard matrix identities, classical graph bounds, established amplitude results, and earlier source results retain their attribution. No comprehensive novelty claim is made for the general linear-algebra or compositional machinery.

::: thebibliography
99 Epoch AI. *The Earth--Moon Problem*. FrontierMath Open Problems. Public problem and verification specification, accessed 17 September 2026. <https://epoch.ai/frontiermath/open-problems/earth-moon>. Epoch AI. *The Arithmetic Kakeya Conjecture*. FrontierMath Open Problems. Public verifiable setup and target, accessed 17 September 2026. <https://epoch.ai/frontiermath/open-problems/arithmetic-kakeya>. M. Kirchweger, M. Scheucher, and S. Szeider. *SAT-Based Generation of Planar Graphs*. LIPIcs, vol. 271, SAT 2023, article 14, pp. 14:1--14:18. DOI: [10.4230/LIPIcs.SAT.2023.14](https://doi.org/10.4230/LIPIcs.SAT.2023.14). A. Trivedi. *Biplanar clique blow-ups of $C_5$ are 9-colourable*. Preprint, Zenodo record 22074335, version 1, stated issue date 5 August 2026; repository record created 24 August 2026. DOI: [10.5281/zenodo.22074335](https://doi.org/10.5281/zenodo.22074335). A. E. Banak, T. Ekim, and Z. C. Taşkın. *Constructing extremal triangle-free graphs using integer programming*. Discrete Optimization 50 (2023), 100802. DOI: [10.1016/j.disopt.2023.100802](https://doi.org/10.1016/j.disopt.2023.100802); arXiv:2304.01729. N. Katz and T. Tao. *New bounds on Kakeya problems*. arXiv:math/0102135 (2001). <https://arxiv.org/abs/math/0102135>. B. Green and I. Z. Ruzsa. *On the arithmetic Kakeya conjecture of Katz and Tao*. Periodica Mathematica Hungarica 78 (2019), 135--151. DOI: [10.1007/s10998-018-0270-z](https://doi.org/10.1007/s10998-018-0270-z); arXiv:1712.02108. J. N. Beasley. *Compound Eye---two problems, checked from several sides*. Frontier development edition 0.3, 7 September 2026. Preserved research report, exact graph certificates, and integer arithmetic controls. Selected original certificate bytes accompany this review edition. J. N. Beasley. *Decision-certificate search and finite exclusion corpus*. Preserved development edition 0.4, September 2026. Independent aggregate checker, $231$ arithmetic bundles, and fixed Earth--Moon modification family. Archived verification, freshly replayed in full for Version 2; original inputs and the new audit are retained separately. J. N. Beasley. *Earth--Moon and Kakeya status*, 8 September 2026. Preserved combined research edition; superseded where explicitly indicated by the September 9 and September 14 records. J. N. Beasley. *Earth--Moon continuation: verified edge window, replayed floor, and new moves*. Notes 3--5 of the 9 September 2026 workstream. Preserved source and evidence identifiers in the author ledger; successful mathematical census jobs distinguished from source-export failure. J. N. Beasley. *Arithmetic Kakeya: current research edition*. 10 September 2026. Preserved manuscript and finite search-scope documentation. J. N. Beasley research record. *Kakeya publication review*, 14 September 2026. Source inventory, corrections, finite-corpus replay record, and publication-scope audit. This is an internal research audit, not an external peer review. J. N. Beasley. *Arithmetic Kakeya Finite Bridges*. Public downstream Lean proof supplement, published 14 September 2026. Repository and current scope inspected 17 September 2026. <https://github.com/dicipler-pixel/arithmetic-kakeya-finite-bridges>. J. N. Beasley research record. *Mastery Equation List*, pre- and post-PDF-mining editions, 13 September 2026. Entries A01--A03 and YM-R28, with explicit source/status labels. Original byte sequences and comparison receipt in the author ledger. J. N. Beasley. *Complete-complex bridge*, working note COMPLETE-COMPLEX-BRIDGE-01, Section 6.1. Fixed-probe determinant insertion and response; recovered source, not a new amplitude model. J. N. Beasley research record. *Atlas calculation method* and *Atlas Catalan working note*, 6 September 2026. Exact kernel tests, frame convention, and B81 correction; historical statuses retained. J. N. Beasley research record. *Atlas calculus: when a simpler piece can stand in for a complicated one*, 7 September 2026. Finite determinant diagrams, contextual equivalence, and reviewed B94--B96 cards. J. N. Beasley research record. *Numerators, curvature, and coherent reduction*, 5 September 2026. Figueiredo/Browder/Sullivan research note with finite response and coherence identities; later scoped Lean development is separately identified. J. N. Beasley. *Atlas formalization map and finite core*, September 2026. Selected finite kernels with LC-019 evidence; 90-card map is not 90 certified card captions. Exact private-source receipt in the author ledger. J. Beasley. *Non-normality is connection energy*, version 7, 17 September 2026. One-page finite graph-transport note; source formulation traced there to 18 June 2026. J. N. Beasley research record. *Connection-energy Earth--Moon/Kakeya assessment*, 17 September 2026, earlier same-day edition. Exact dual-projector calibration and restricted planar-flip probe; self-contained source and saved certificates preserved. N. Arkani-Hamed, Q. Cao, J. Dong, C. Figueiredo, and S. He. *Hidden zeros for particle/string amplitudes and the unity of colored scalars, pions and gluons*. JHEP 10 (2024), 231; arXiv:2312.16282. <https://arxiv.org/abs/2312.16282>. N. Arkani-Hamed and C. Figueiredo. *All-order splits and multi-soft limits for particle and string amplitudes*. arXiv:2405.09608 (2024). <https://arxiv.org/abs/2405.09608>. J. C. Baez and B. Fong. *A compositional framework for passive linear networks*. Theory and Applications of Categories 33 (2018), no. 38, 1158--1222; arXiv:1504.05625. <https://arxiv.org/abs/1504.05625>.
:::

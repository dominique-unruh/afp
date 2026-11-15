# Algebraic Invariants of the Circle, Torus, and Punctured Plane

Authors: Arthur Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz.

We formalize real path lifts of based loops in the circle and prove that
their integer endpoints classify these loops up to path homotopy. For
the torus, the two coordinate lifts give a classification by pairs of
integers and an explicit fundamental-group isomorphism with Z × Z.
Every continuous circle self-map acts on first singular homology by
multiplication by its winding number. We construct a radial deformation retraction of the
punctured complex plane onto the circle and compute the reduced homology
of both spaces: it is isomorphic to the additive group of integers in
degree one and trivial in every other degree. Neither space is
contractible. The development also provides a reusable interface for
path lifting in covering spaces.

The development builds on the published Fundamental_Group_Circle entry,
Isabelle's analysis and homology libraries, and the AFP Seifert-Van-Kampen
entry through an explicit session dependency.

The checked theories provide:

- the exponential cover of the circle, real path lifts, and the integer
  endpoint classification of based loops;
- a generic pointed covering-space path-lifting interface with existence,
  pointwise uniqueness, fiber endpoints, and homotopy invariance;
- product paths and torus loops, including coordinatewise lift additivity,
  reversal, and the homotopy classification by two integer coordinates;
- a torus fundamental-group record on actual based-loop homotopy classes,
  with its explicit isomorphism to the product of two additive integer groups;
- the radial deformation retraction of the punctured complex plane onto the
  circle and its homotopy-equivalence consequences;
- named interfaces to the classical and carrier-level Seifert--van Kampen
  theorems from the AFP dependency;
- reduced homology of the circle and punctured plane: the degree-one group is
  isomorphic to the additive integers and all other degrees are trivial;
- non-contractibility of both the circle and the punctured plane, plus the
  basic Brouwer-degree laws for self-maps of the abstract one-sphere;
- a singular-cycle representation of circle loops, compatibility with
  concatenation and reversal, and the winding-number formula for the actual
  induced first-homology map of every continuous circle self-map.

The AFP entry and Isabelle session are named
`Circle_Torus_Algebraic_Topology`;
`Circle_Torus_Algebraic_Topology.thy` is the stable aggregate theory. The
individual theories remain separate so that later developments can depend
only on the covering, product, retract, Seifert--van Kampen, or homology layer
they need.

## Build

From the monorepo root, the proof-only build is:

    isabelle build \
      -o document=false \
      -d projects/circle-fundamental-group-isabelle \
      -D projects/circle-torus-algebraic-topology-isabelle \
      Circle_Torus_Algebraic_Topology

For the PDF build, replace `-o document=false` with `-o document=pdf`
and add `-o document_output=output` to retain the generated PDF.
Use the published `Fundamental_Group_Circle` entry on `-d` when checking
submission compatibility. `Seifert-Van-Kampen` must also be available from
the AFP installation; `HOL-Homology` is part of Isabelle.

The torus isomorphism is `pi1_torus_iso_integer_product`.
The homology bridge is `circle_homology_action_winding`: under any group
isomorphism from H₁(circle) to the additive integers, the induced map of
`f` is multiplication by `wnd (f ∘ circlepath 0 1)`. There is no basepoint
restriction on `f`. The proof uses singular chains and a winding functional
that vanishes on boundaries, not a newly defined substitute for `hom_induced`.

The SVK interface re-exports established AFP results. The pre-existing
Brouwer-degree laws concern the abstract one-sphere; we do not additionally
identify the library constant `Brouwer_degree2` with this concrete winding
formula. Nor do we claim a general Hurewicz theorem or a homology computation
for the torus.

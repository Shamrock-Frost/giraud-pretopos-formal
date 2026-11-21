# giraud-pretopos-formal

An Isabelle/HOL formalization of a localization theorem for presheaf categories: small
presheaves on a category are its small diagrams, localized at the final reindexings. It follows
Section 3 of a note of mine (Brendan Murphy, *Small presheaves, infinitary pretoposes, and
diagrams up to final reindexing*, in preparation). The repository is named for the other half of
the note, on Giraud's theorem for infinitary pretoposes, which is not formalized.

## The theorem

Let `C` be a locally small category, which may be a proper class.

- `Diag C` is the category of small diagrams in `C`. An object is a pair `⟨J, F⟩` of a small
  category `J` and a functor `F : J → C`. A morphism `⟨J, F⟩ → ⟨K, G⟩` is a functor `p : J → K`
  with a natural transformation `α : F ⇒ G ∘ p`.
- `W0 C` is the class of final reindexings: the morphisms `(q, id) : ⟨J', F ∘ q⟩ → ⟨J, F⟩` with
  `q` a final functor.
- `PSh C` stands for the category of small presheaves on `C`, and `colim_functor C` for the
  functor `Diag C → PSh C` that sends a diagram to its colimit of representables.

Then `colim_functor C` is the localization of `Diag C` at `W0 C`. This is `diagram_localization`
in [`Diag/Diagram_Localization.thy`](Diag/Diagram_Localization.thy):

```isabelle
theorem diagram_localization:
  assumes "category C" and "locally_small C"
  shows "strict_localization (colim_functor C) (W0 C) (Diag C) (PSh C)"
```

`strict_localization A W D E` ([`Cat/Category.thy`](Cat/Category.thy)) says that `A : D → E`
inverts `W` and is universal with that property on the nose: composition with `A` is an
isomorphism from the functors `E → N` to the functors `D → N` that invert `W`, for every `N`.
This implies the usual universal property, where the comparison is only an equivalence.

### How `PSh C` is defined

A small presheaf on a proper class is itself a proper class, so the small presheaves do not
form a class, and `PSh C` cannot be defined in NBG as a category of presheaves. It is defined
([`Diag/Diagrams.thy`](Diag/Diagrams.thy)) as the category with the same objects as `Diag C`,
the diagram `⟨J, F⟩` standing for the presheaf `colim_j y(F j)`, and with morphisms given by

    Hom(colim y F, colim y G) = lim_j colim_k Hom(F j, G k).

So `colim_functor C` is the identity on objects, which is why the localization can be strict.

Three theories tie this category to actual presheaves. None of them is used by the theorem.
[`Diag/Adequacy.thy`](Diag/Adequacy.thy) shows that the arrows of `PSh C` are the natural
transformations between the presheaves the diagrams stand for.
[`Diag/Presheaf_Colimit.thy`](Diag/Presheaf_Colimit.thy) shows that those presheaves are the
colimits of their representables, and that the maps between any two small presheaves are the
arrows of `PSh C` between diagrams that present them (`small_presheaf_hom`).
[`Diag/Yoneda_Check.thy`](Diag/Yoneda_Check.thy) checks that on one-object diagrams `PSh C` is
`C`.

## Foundations

The statement quantifies over categories that are proper classes, so the development works in
von Neumann–Bernays–Gödel set theory, axiomatized inside HOL after Mendelson, *Introduction to
Mathematical Logic*, Chapter 4. This is an attempt to treat size the way mathematicians outside
category theory think of it informally: there are sets, there are classes, and a locally small
category has a class of objects and a set of maps between any two.

[`NBG/Axioms.thy`](NBG/Axioms.thy), 79 lines, is the whole trusted base. It declares one type,
classes, and one constant, membership. Class comprehension is not an axiom scheme: that a
formula whose quantifiers range over sets defines a class is Mendelson's Class Existence
Theorem, proved from the axioms in [`NBG/Class_Existence.thy`](NBG/Class_Existence.thy). There
is no axiom of choice, of infinity or of regularity. Infinity and regularity are stated in
[`NBG/Axioms_Rest.thy`](NBG/Axioms_Rest.thy), which nothing imports. The theories import HOL's
`Main`, so the ambient logic is HOL's; its choice operator `SOME` is never used, and definite
description `THE` is used twice.

Everything else is proved, with no `sorry` and no `oops`.

## Layout

- `NBG/`: the axioms, class existence, and a small library.
- `Cat/`: categories, functors, isomorphisms, final functors, localization.
- `Diag/`: diagrams, `PSh C`, the colimit functor, the theorem, and the comparison with
  presheaves.

27 theories, about 11,800 lines.

## Building

With Isabelle 2025-2:

```sh
isabelle build -D .
```

`flake.nix` pins a nixpkgs revision that provides that Isabelle version (`nix develop`, on
x86_64-linux).

## How it was written

The statement began as a question I asked in 2023. The proof in the note was worked out with
Claude in November 2026, and this development, also written with AI agents under my direction,
is the check of that proof.

I have not found the theorem in the literature, but it may well be known. The functor from
diagrams to small presheaves is studied by Perrone and Tholen, *Kan extensions are partial
colimits* (Appl. Categ. Structures 30, 2022), as a morphism of pseudomonads.

## License

MIT; see `LICENSE`.

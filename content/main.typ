#import "book-style.typ": *
#import "main-defs.typ": editorial-bibliography, source
#import "cover.typ": cover-page
#import "title-page.typ": title-page
#import "imprint.typ": imprint-page
#show: book-style

#counter(page).update(0)
#cover-page()
#counter(page).update(3)
#title-page()
#imprint-page()
#set page(numbering: "1")
#include "00-preface.typ"
#include "01-johnson-introduction.typ"
#include "02-johnson-basic-notions.typ"
#include "03-johnson-quasisymmetries.typ"
#include "04-johnson-anisotropic.typ"
#include "05-johnson-isotropic.typ"
#include "06-johnson-isomorphisms.typ"
#include "07-johnson-automorphisms.typ"
#include "08-johnson-bibliography.typ"
#include "10-cohn-introduction.typ"
#include "11-cohn-summary.typ"
#include "12-cohn-homomorphisms.typ"
#include "13-cohn-isomorphisms.typ"
#include "14-cohn-bibliography.typ"

#set heading(numbering: lecture-heading-numbering)
#include "20-omeara-introduction.typ"
#include "21-omeara-notation.typ"
#include "22-omeara-geometric.typ"
#include "23-omeara-dilatations.typ"
#include "24-omeara-residues.typ"
#include "25-omeara-transvections.typ"
#include "26-omeara-matrices.typ"
#include "27-omeara-projective-transvections.typ"
#include "28-omeara-comments.typ"
#include "29-omeara-generation.typ"
#include "30-omeara-generation-comments.typ"
#include "31-omeara-orders.typ"
#include "32-omeara-centres.typ"
#include "33-omeara-commutators.typ"
#include "34-omeara-simplicity.typ"
#include "35-omeara-simplicity-alternative.typ"
#include "36-omeara-structure-comments.typ"
#include "37-omeara-semilinear.typ"
#include "38-omeara-projective-geometry.typ"
#include "39-omeara-semilinear-groups.typ"
#include "40-omeara-geometric-isomorphisms.typ"
#include "41-omeara-contragredient.typ"
#include "42-omeara-projective-comments.typ"
#include "43-omeara-isomorphism-preliminaries.typ"
#include "44-omeara-rich-transvections.typ"
#include "45-omeara-cdc.typ"
#include "46-omeara-transvection-preservation.typ"
#include "47-omeara-general-isomorphisms.typ"
#include "48-omeara-fields.typ"
#include "49-omeara-integral-domains.typ"
#include "50-omeara-isomorphism-comments.typ"
#include "51-omeara-bibliography.typ"
#set heading(numbering: article-heading-numbering)
#include "52-ojanguren-introduction.typ"
#include "53-ojanguren-projective-spaces.typ"
#include "54-ojanguren-theorem.typ"
#include "55-ojanguren-example.typ"
#include "56-ojanguren-bibliography.typ"
#include "57-pomfret-introduction.typ"
#include "58-pomfret-preliminaries.typ"
#include "59-pomfret-automorphisms.typ"
#include "60-pomfret-bibliography.typ"
#include "62-solazzi-symplectic-introduction.typ"
#include "63-solazzi-symplectic-preliminaries.typ"
#include "64-solazzi-symplectic-projective-groups.typ"
#include "65-solazzi-symplectic-double-centralizers.typ"
#include "66-solazzi-symplectic-automorphisms.typ"
#include "67-solazzi-symplectic-congruence-groups.typ"
#include "68-solazzi-symplectic-bibliography.typ"
#include "69-solazzi-unitary-introduction.typ"
#include "70-solazzi-unitary-preliminaries.typ"
#include "71-solazzi-unitary-double-centralizers.typ"
#include "72-solazzi-unitary-automorphisms.typ"
#include "73-solazzi-unitary-congruence-groups.typ"
#include "74-solazzi-unitary-bibliography.typ"
#include "75-tits-introduction.typ"
#include "76-tits-domains.typ"
#include "77-tits-local-arithmetic.typ"
#include "78-tits-fields.typ"
#include "79-tits-examples.typ"
#include "80-tits-bibliography.typ"
#include "81-yan-introduction.typ"
#include "82-yan-inner-isomorphisms.typ"
#include "83-yan-involutions.typ"
#include "84-yan-elementary-images.typ"
#include "85-yan-main-proof.typ"
#include "86-yan-strengthening.typ"
#include "87-yan-bibliography.typ"
#include "90-editor-overview.typ"
#include "91-editor-bibliography.typ"
#include "98-index.typ"

#source(261)
#source(262)
#frontmatter("contents", [Содержание]) <front:contents>
#outline(title: none, depth: 3)
#editorial-bibliography

# Products

`Products.tex` (compiled: `Products.pdf`, 8 pages) answers Lawvere–Schanuel's first exercise
— *find products in life and in other circumstances* — for the two syllabi of this project:

1. the one test that decides whether something is a product (the universal property);
2. twelve everyday examples, including two that **fail** the test and why;
3. every occurrence of *szorzat* in the `Tárgytematika` of *Kalkulus I* (MBLK37E) and
   *Lineáris algebra I* (MBLK15E), sorted into **product objects** (pairs) and
   **multiplication maps** (arrows out of a pair);
4. an atlas of the products and multiplication maps in `kalkulus_gyakorlo.pdf`;
5. a timed-exam protocol, four worked answers, a time budget, and five traps.

Build with either of:

    tectonic Products.tex
    latexmk -pdf Products.tex

Every mathematical claim of the document is stated and proved in
`RequestProject/ProductOverlap.lean`; the relevant Lean name is printed next to the claim.

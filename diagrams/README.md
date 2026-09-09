# Diagrammatic reasoning notes

`DiagrammaticReasoning.tex` (compiled: `DiagrammaticReasoning.pdf`) is a picture atlas for
the two syllabus overlaps of *Kalkulus I* and *Lineáris algebra I* — the triangle
inequality and the inverse.  It surveys eight diagrammatic languages, says for each what
its legal moves are and whether it is certified, works through the exercises of
`kalkulus_gyakorlo.pdf` that can be settled by drawing, and ends with a playbook for a
timed exam.

The source is split into `part0-intro.tex` … `part8-exam.tex`, all included from
`DiagrammaticReasoning.tex`.

Build with any of:

    tectonic DiagrammaticReasoning.tex
    latexmk -pdf DiagrammaticReasoning.tex

Every mathematical claim illustrated in the document is stated and proved in
`RequestProject/DiagramProofs.lean`; the figure captions name the corresponding theorem.

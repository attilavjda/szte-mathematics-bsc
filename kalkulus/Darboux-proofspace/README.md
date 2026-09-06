This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Darboux : carte de l'espace de preuves

Document : `docs/darboux.tex` → `docs/darboux.pdf` (français, diagrammes TikZ) :
visualisations, lectures catégorique / type-théorique / géométrique, grandes idées, et la
liste des formes de lemmes récoltées.

Modules Lean (tous compilent, sans `sorry`) :

| Fichier | Contenu |
| --- | --- |
| `RequestProject/Darboux/Basic.lean` | la propriété `DarbouxOn`, ses deux sources (continuité, dérivation), stabilités |
| `RequestProject/Darboux/Shapes.lean` | formes `Darboux & X ⇒ Y` : valeur évitée, image dénombrable, injectivité, monotonie, graphe fermé |
| `RequestProject/Darboux/Deriv.lean` | spécialisations aux dérivées ; convexe + dérivable ⇒ `C¹` ; forme « point fixe » ; la fonction signe n'est pas une dérivée |
| `RequestProject/Darboux/Space.lean` | le graphe (nœuds, arêtes, hyper-arêtes), vérifié par la machine |
| `RequestProject/Darboux/Normal.lean` | l'autre Darboux : forme normale d'une densité en dimension 1 |
| `RequestProject/Darboux.lean` | module agrégateur |

Exploration (non vérifiée, prototype) :

```
python3 proofspace.py darboux.space        # rapport : trous, paires ouvertes
python3 proofspace.py darboux.space --dot  # source Graphviz
```

Compilation :

```
lake build RequestProject.Darboux
cd docs && tectonic darboux.tex
```

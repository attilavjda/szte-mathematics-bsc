# Summary of changes for run 9b80c05c-9fb6-4f38-b76a-348ad4dae976
Livré : un document PDF/TeX en français avec TikZ, et un ensemble de petits modules Lean 4 cartographiant l'espace de preuves autour du théorème de Darboux. Tout compile (`lake build`) sans `sorry` ni axiome hors du standard (`propext`, `Classical.choice`, `Quot.sound`).

**Document** — `docs/darboux.tex` → `docs/darboux.pdf` (6 pages, prose minimale) :
- table comparant les deux Darboux (analyse / symplectique) ;
- visualisations TikZ : le saut interdit vs l'oscillation permise, la preuve classique par Fermat, la configuration à trois points de l'argument d'injectivité, le « trou » créé par un saut monotone, l'indénombrabilité d'un intervalle, le graphe de l'espace de preuves (arêtes et hyper-arêtes), le triangle de post-composition, le chemin de Moser, la normalisation d'une densité ;
- lectures catégorique (préservation de π₀ sans fonctorialité ; Darboux n'est pas une catégorie mais un module à gauche sur les continues ; hyper-arêtes = multiflèches), type-théorique (les énoncés comme types Π/Σ, les hyper-arêtes comme règles à deux prémisses, le contenu non constructif du Σ) et géométrique ;
- « grandes idées » en six points, la liste des formes récoltées, et un tableau des trous restants.

**Modules Lean** (`RequestProject/Darboux/`) :
- `Basic.lean` : la propriété `DarbouxOn` isolée de la dérivabilité, sa forme ponctuelle équivalente, ses deux sources (continuité ; dérivation = théorème de Darboux), et la stabilité par post-composition continue.
- `Shapes.lean` : les formes `Darboux & X ⇒ Y` — valeur évitée ⇒ signe constant ; image dénombrable ⇒ constante ; **injective ⇒ strictement monotone** (généralisation sans continuité du résultat correspondant de Mathlib) ; **monotone ⇒ continue** ; **graphe fermé ⇒ continue**.
- `Deriv.lean` : spécialisations aux dérivées (dérivée à valeurs entières constante ; dérivée injective strictement monotone), **convexe + dérivable ⇒ C¹**, la forme « point fixe » `f'(x) ≠ x partout ⇒ signe constant de f' − id` (qui exploite la structure d'espace vectoriel des dérivées, absente pour Darboux en général), et l'obstruction concrète : la fonction signe n'est la dérivée d'aucune fonction.
- `Space.lean` : le graphe lui-même — vocabulaire (9 nœuds), arêtes et hyper-arêtes, chacune un théorème vérifié.
- `Normal.lean` : l'autre Darboux en dimension 1 — toute densité continue strictement positive admet une carte Φ strictement croissante avec Φ′ = ρ, d'image un intervalle et ∫ₐᵇ ρ = Φ(b) − Φ(a).
- `RequestProject/Darboux.lean` : module agrégateur ; `README.md` : mode d'emploi.

**Exploration** : `darboux.space` encode la carte pour le prototype `proofspace.py` fourni (rapport : trous, paires ouvertes, conséquences jointes). Ce script reste exploratoire et ne prouve rien ; seuls les modules Lean font foi.

Point de méthode : les formes 2, 3, 4, 6 et 9 sont exactement des hyper-arêtes que l'on n'écrit pas d'habitude, parce que les théorèmes correspondants sont énoncés avec « continue » là où « Darboux » suffit.
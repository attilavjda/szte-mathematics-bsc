
Nagyon érdekes a számomra, hogy a tantárgyak, habár eleinte szétszórtnak tűntek, sok közös mintát tartalmaznak, és ezeket formalizálni is lehet. Például a háromszögegyenlőtlenség a kalkulus és a lineáris algebra tárgytematikája is, és ez az egyik alapminta a kategórialméletben is.

     explorations/TriangleOverlap.lean formalizálja

A kategóriaelmélettel többekközött ezeket a közös mintákat lehet tanulmányozni, és azthiszem hogy olyan szempontból is hasznos lehet ez, hogy tapasztalatomban érthetőbb és könnyebb a közös mintát megtanulni, mintsem a sok szerteágazó alkalmazását külön-külön, a kapcsolatot nem ismerve tanulni.


A két tankönyv formalizációnak lett egy olyan szuper alkalmazása, hogy így formalizálva be lehet importálni a különböző definíciókat és tételeket, és lehet azokat használni.

például `kalkulus/formalizalt-tankonyv/Analizis/Lawvere_SzorzatObjektum.lean` formalizálva vannak kapcsolatok arról, hogy a `SPACE = PLANE × LINE` szorzat minta a Lawvere-Schanuel Conceptual Mathematics könyvből hol fordul elő a Leindler Analízis könyvben. A Galilei madara aminek a mozgása akkor folytonos, ha a szintjének és a síkjának a mozgása is folytonos, ott van az 5.2.2 definícióban - ami talán egy tök száraz szövegnek tűnhet - és valahogy az ∀ε∃δ-ban például ez az alapvető menő minta!
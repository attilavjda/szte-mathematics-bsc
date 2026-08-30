# SZTE informatika tárgyak — formalizált központi tételek

Ebben a projektben tárgyanként egy-egy Lean 4 fájl található, amely az adott
kurzus néhány központi tételét **teljesen bebizonyítva** tartalmazza (nincs
`sorry` egyik fájlban sem). A dokumentáció magyar, a Lean azonosítók angolok.

Fordítás/ellenőrzés: `lake build`.

## Fájlok és tartalmuk

### `RequestProject/AutomatakEsFormalisNyelvek.lean` — Automaták és formális nyelvek
* `prodDFA`, `accepts_prodDFA` — szorzatautomata; a felismerhető nyelvek zártak
  a **metszetre**.
* `unionDFA`, `accepts_unionDFA` — zártság az **unióra**.
* `complDFA`, `accepts_complDFA` — zártság a **komplementerre**.
* `parityDFA`, `parityDFA_accepts` — konkrét automata: pontosan a páros sok `a`
  betűt tartalmazó szavakat ismeri fel.
* `anbn`, `anbn_not_recognizable` — az `{aⁿbⁿ}` nyelv **nem felismerhető**
  véges determinisztikus automatával (a pumpáló lemma mögötti skatulyaelv
  közvetlen alkalmazásával).

### `RequestProject/Logika.lean` — Logika és informatikai alkalmazásai
* `PFormula`, `PFormula.eval`, `Entails` — az ítéletkalkulus szintaxisa és
  szemantikája.
* `Hilbert` — Hilbert-típusú levezetési rendszer (K, S, `¬¬A → A` axiómasémák,
  modus ponens).
* `Hilbert.id'` — `⊢ A → A`.
* `Hilbert.soundness` — **helyességi tétel**.
* `Hilbert.weaken` — a levezethetőség monotonitása.
* `Hilbert.deduction` — **dedukciótétel** (`Γ ∪ {P} ⊢ Q ⟺ Γ ⊢ P → Q`).
* `Hilbert.consistent` — a kalkulus ellentmondásmentes.

### `RequestProject/SzamitastudomanyAlapjai.lean` — A számítástudomány alapjai
* `words_countable` — `Σ*` megszámlálható.
* `languages_not_countable` — a nyelvek halmaza **nem** megszámlálható
  (Cantor-átló).
* `instFiniteDFA`, `RecognizableLanguages`, `recognizableLanguages_countable` —
  adott állapotszámmal csak véges sok automata van, így a felismerhető nyelvek
  halmaza megszámlálható.
* `exists_not_recognizable` — **létezik nem felismerhető nyelv**.
* `no_universal_decider` — diagonalizáció: nincs olyan `ℕ`-nel indexelt
  felsorolás, amely minden `ℕ → Bool` eldöntő függvényt előállít.

### `RequestProject/Kriptografia.lean` — Kriptográfia és adatbiztonság
* `pow_mod_prime_of_exp_congr` — a kis Fermat-tétel következménye:
  `e·d ≡ 1 (mod p−1)` esetén `m^(e·d) ≡ m (mod p)` **minden** `m`-re.
* `rsa_correct` — az **RSA helyessége**: `p ≠ q` prímek és
  `e·d ≡ 1 (mod lcm(p−1, q−1))` mellett `(mᵉ)ᵈ ≡ m (mod p·q)` minden üzenetre
  (nem csak a modulushoz relatív prímekre).
* `diffie_hellman_correct` — a Diffie–Hellman kulcscsere helyessége.
* `elgamal_correct` — az ElGamal-visszafejtés helyessége.

### `RequestProject/KalkulusI.lean` — Kalkulus I
* `sup_unique` — a felső határ egyértelmű.
* `tendsto_one_div_atTop` — `1/n → 0`.
* `frog_series` — `∑ (1/2)ⁿ⁺¹ = 1` (a "szélesszájú kisbéka" feladat).
* `exists_root_cubic` — Bolzano-tétel: `x³ + x − 1`-nek van gyöke `(0,1)`-ben.
* `strictMono_cube` — `x ↦ x³` szigorúan monoton növő.

### `RequestProject/LinearisAlgebraI.lean` — Lineáris algebra I
* `rank_nullity` — **dimenziótétel**: `dim Im f + dim Ker f = dim V`.
* `det_two_by_two` — a 2×2-es determináns képlete.
* `isUnit_iff_det_ne_zero` — invertálhatóság ⟺ nemnulla determináns.
* `cramer_two` — **Cramer-szabály** 2×2-re, a megoldás egyértelműségével együtt.
* `eigen_example` — sajátvektorok és sajátértékek konkrét mátrixra.

## Tanulási javaslat

1. Olvasd el a tétel *kimondását* Leanben, és fogalmazd meg magyarul, mit
   állít; a fájlok elején lévő doc-kommentek ehhez adnak kapaszkodót.
2. Nézd meg a bizonyítás vázát: hol történik esetszétválasztás, hol indukció,
   melyik lépés a "matematikai mag" (pl. a skatulyaelv az `anbn`-nél, a kis
   Fermat-tétel az RSA-nál, a Cantor-átló a nem felismerhető nyelvnél).
3. Gyakorlásként érdemes a mintákat továbbvinni: pl. a szorzat/unió automata
   mintájára megcsinálni a szimmetrikus differencia automatáját, vagy az
   `anbn` mintájára megmutatni, hogy `{wwᴿ}` sem felismerhető.

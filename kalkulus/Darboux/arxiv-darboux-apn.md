Template (≤8 pp., arXiv math.CO / cs.CR):

Title: The Darboux Pattern in Characteristic Two: Derivative Images of APN and Gold Functions

    Abstract 

    — one claim: the image of a derivative is "convex" in the right sense; over ℝ an interval, over F_2^n an affine coset.

    Introduction 

    — Darboux's classical theorem; 
    APN/Gold/Kasami background;
     what an undergraduate contributes: 
     	the shared pattern + machine-checked proofs.

    Preliminaries
     — F_2^n, discrete derivative D_a f = f(x+a)+f(x), APN, Gold/Kasami exponents, Walsh transform.
    
    The abstract gadget 
    	— convexity structure (closure system); 
    	Darboux property = "range of derivative is convex"; 
    	hull, faithfulness.

    Two instances 
    — (a) Mathlib's real Darboux; 
    (b) quadratic ⇒ derivative image is a coset; 
    size 2^{n−1}.
    
    Transport 
    — coordinate/matrix picture; 
    equivalence proved, not asserted.

    Limits
     — non-quadratic APN:
      counting form survives, affine form fails.
    
    Formalization
    	 — Lean 4 statements, axiom audit, repo link.

    Open questions, refs, appendix with TikZ diagram.

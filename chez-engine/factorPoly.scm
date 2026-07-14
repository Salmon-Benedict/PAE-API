; Polynomial factoring for single-variable polynomials, built on top of
; expandParse.scm's parser and expand() (must be loaded first). Handles:
;   - GCF extraction (integer coefficient GCF and common variable power)
;   - Quadratic trinomials ax^2+bx+c via the discriminant/quadratic
;     formula, which subsumes difference of squares (b=0) and perfect
;     square trinomials (discriminant=0) as special cases automatically
;   - Degree >= 3: searches for a rational root via the rational root
;     theorem and divides it out (Gauss's lemma guarantees an exact
;     integer quotient), recursively re-factoring the quotient. This
;     covers sum/difference of cubes and "biquadratic" x^4 cases as
;     special cases of root-finding, with no dedicated pattern needed
;     for either -- e.g. x^4-5x^2+4 fully factors into 4 linear terms,
;     which the C++ engine's pattern-based factorer cannot do.
;   - Recursively re-factors any resulting sub-factor that is itself
;     still factorable (e.g. pulling a new GCF out after dividing once)
;
; Ported from ../factorPoly.scm (MIT Scheme) to Chez Scheme. Changes:
;   - All 3 `any` calls -> `exists` (MIT's `any` is unbound in Chez).
;   - All 3 `(error "msg" ...)` call sites get an explicit #f who-arg.
;
; Limitations: degree >= 3 polynomials with no rational root (e.g.
; irreducible cubics) are left unfactored -- this matches what's
; mathematically possible without introducing irrational/complex
; coefficients. Multivariable terms aren't supported -- GCF extraction,
; the quadratic formula, and the rational root theorem are genuinely
; single-variable algorithms -- so factor() calls assertSingleVariable
; (below) on its expanded input before running any of this file's logic.

; Returns the variable symbol used by termList (assumes single-variable
; throughout this file), or #f if every term is a constant.
(define (polyVariable termList)
    (cond
        ((null? termList) #f)
        ((var? (var (car termList))) (var (car termList)))
        ('t (polyVariable (cdr termList)))))

; The set of every distinct variable used anywhere in termList (across
; all terms, and within a single multivariable term's own extraVars).
(define (allVariablesIn termList)
    (let ((seen '()))
        (for-each
            (lambda (term)
                (for-each
                    (lambda (v) (if (not (memq v seen)) (set! seen (cons v seen))))
                    (map car (termVarAlist term))))
            termList)
        seen))

; Guards factor()/solve()/differentiateExpr()/integrateExpr() against
; multivariable input. Checking whether any single term has non-empty
; extraVars isn't sufficient -- termList as a whole can be multivariable
; even when every individual term is single-variable, e.g. "x+y" (each
; term uses one variable, but the polynomial uses two) -- so this checks
; the distinct-variable count across the whole list instead. This also
; fixes a latent pre-existing bug: polyVariable/coeffAt only ever look at
; the *first* variable-bearing term, so factor("x+y") used to silently
; drop the y term rather than erroring.
(define (assertSingleVariable termList opName)
    (if (> (length (allVariablesIn termList)) 1)
        (error #f (string-append opName ": multivariable expressions aren't supported yet") termList)))

; Guards factor() (and solveHigherDegree, solvePoly.scm) against a
; fractional coefficient reaching GCF extraction/the rational root
; theorem -- both are integer-coefficient algorithms (findGCF's gcd,
; divisorsOf) that silently ignore a term's cd otherwise, rather than
; erroring: e.g. factor("x^2/2-2") used to come back as "(x-2)(x+2)",
; which is a DIFFERENT polynomial (x^2-4, not x^2/2-2) that just
; happens to share the same roots -- a silently wrong answer, not a
; missing-feature one, found via the division feature's own testing
; since a fractional coefficient reaching factor()/solveHigherDegree was
; never previously reachable (there was no way to construct one without
; '/' support). solveLinear/solveQuadraticFull (solvePoly.scm) are NOT
; guarded by this -- both already work correctly on fractional
; coefficients via coeffAt's exact-rational arithmetic (verified), since
; neither uses gcd/divisorsOf.
(define (assertIntegerCoefficients termList opName)
    (if (exists (lambda (term) (not (= (cd term) 1))) termList)
        (error #f (string-append opName ": a fractional coefficient here isn't supported yet -- only constant-denominator division reaching a whole-number coefficient is") termList)))

; Guards factor()/solveHigherDegree against a negative or fractional
; exponent (e.g. "x^-2" or "x^(1/2)") reaching GCF extraction/the
; rational root theorem -- both assume nonnegative integer degree
; throughout (findGCF's use of gcd, polyDegree's max, divisorsOf), and
; silently produce garbage rather than erroring otherwise: verified live
; that factor("2x^-2+4") currently returns "2(2+1)", not an error and
; not a correct factorization. Checks every variable's exponent across
; the whole term list via termVarAlist (also catches a multivariable
; term's extraVars, not just the primary variable).
(define (assertIntegerExponents termList opName)
    (if (exists (lambda (term)
                 (exists (lambda (p) (not (and (integer? (cdr p)) (>= (cdr p) 0))))
                      (termVarAlist term)))
             termList)
        (error #f (string-append opName ": a negative or fractional exponent here isn't supported yet") termList)))

; Returns the (possibly fractional, e.g. from dividing by a constant --
; see expandParse.scm's foldConstantDenom) coefficient of the term at the
; given degree, as an exact rational, or 0 if no such term exists. Used
; directly in exact-rational arithmetic by solveLinear/solveQuadraticFull
; (solvePoly.scm), which therefore work correctly on fractional
; coefficients for free; factorPoly.scm's own integer-only algorithms
; (GCF/rational-root-theorem) still require integer coefficients and are
; guarded separately -- see assertIntegerCoefficients below.
(define (coeffAt termList degree)
    (cond
        ((null? termList) 0)
        ((and (var? (var (car termList))) (= (varPn (car termList)) degree) (= (varPd (car termList)) 1))
            (/ (cn (car termList)) (cd (car termList))))
        ((and (= degree 0) (not (var? (var (car termList)))))
            (/ (cn (car termList)) (cd (car termList))))
        ('t (coeffAt (cdr termList) degree))))

(define (polyDegree termList)
    (cond
        ((null? termList) 0)
        ('t (apply max (map (lambda (term) (if (var? (var term)) (varPn term) 0)) termList)))))

(define (gcdL aList) (apply gcd aList))

; Greatest common (integer) divisor of all coefficients, and the
; minimum variable power present in EVERY term (0 if any term lacks
; the variable, e.g. a constant term). Returns (coeffGCF . varGCFdeg).
; coeffGCF's sign matches the leading term's sign (even when the gcd
; magnitude is 1) so the quotient left after dividing it out always has
; a positive leading coefficient -- otherwise tryFactorQuadratic's
; Vieta's-formula assumption (A1*A2 = a) silently breaks for a negative
; leading coefficient (e.g. factor("-4x^2+4x+8") used to come out as
; "4(x+1)(x-2)", losing the sign entirely), and a bare negative constant
; like factor("-2") used to crash by rendering as the unparseable "2*-1".
(define (findGCF termList)
    (let* ((coeffs (map (lambda (t) (abs (cn t))) termList))
           (degs (map (lambda (t) (if (var? (var t)) (varPn t) 0)) termList))
           (leadSign (if (< (coeffAt termList (polyDegree termList)) 0) -1 1)))
        (cons (* leadSign (gcdL coeffs)) (apply min degs))))

; Integer square root if n is a perfect square (n >= 0), else #f.
(define (integerSqrt n)
    (if (< n 0)
        #f
        (let ((r (round (sqrt n))))
            (if (= (* r r) n) r #f))))

; Evaluates termList (true-signed) at a numeric (possibly rational) x.
(define (evalPolyAt termList x)
    (apply + (map (lambda (term)
                       (* (/ (cn term) (cd term))
                          (if (var? (var term)) (expt x (varPn term)) 1)))
                   termList)))

; All positive divisors of |n| (or (1) if n=0), ascending.
(define (divisorsOf n)
    (let ((m (abs n)))
        (if (= m 0)
            '(1)
            (let loop ((d 1) (acc '()))
                (cond
                    ((> d m) (reverse acc))
                    ((= 0 (remainder m d)) (loop (+ d 1) (cons d acc)))
                    ('t (loop (+ d 1) acc)))))))

; Searches for a rational root of termList via the rational root
; theorem: any rational root p/q (lowest terms) has p dividing the
; constant term and q dividing the leading coefficient. Returns the
; root as an exact Scheme rational (numerator/denominator give p, q
; directly, already in lowest terms), 0 if the constant term is 0
; (so x is a factor), or #f if no rational root is found. Capped at
; coefficients up to 10000 in magnitude to avoid a pathological search.
(define (findRationalRoot termList)
    (let* ((deg (polyDegree termList))
           (leadCoeff (coeffAt termList deg))
           (constCoeff (coeffAt termList 0)))
        (cond
            ((= constCoeff 0) 0)
            ((or (> (abs constCoeff) 10000) (> (abs leadCoeff) 10000)) #f)
            ('t
                (let ((ps (divisorsOf constCoeff)) (qs (divisorsOf leadCoeff)))
                    (let loopP ((plist ps))
                        (if (null? plist)
                            #f
                            (let loopQ ((qlist qs))
                                (cond
                                    ((null? qlist) (loopP (cdr plist)))
                                    ((= 0 (evalPolyAt termList (/ (car plist) (car qlist))))
                                        (/ (car plist) (car qlist)))
                                    ((= 0 (evalPolyAt termList (/ (- (car plist)) (car qlist))))
                                        (/ (- (car plist)) (car qlist)))
                                    ('t (loopQ (cdr qlist))))))))))))

; Divides termList (degree >= 1, integer coefficients) by the linear
; factor (q*x - p), where p/q (q > 0, lowest terms) is a verified
; rational root. By Gauss's lemma (q and p are coprime, and q divides
; the leading coefficient by construction), this quotient has exact
; integer coefficients -- the standard synthetic-division-by-(qx-p)
; recurrence: b_(n-1) = a_n/q, b_(i-1) = (a_i + p*b_i)/q.
(define (divideByLinearFactor termList p q)
    (let* ((v (polyVariable termList))
           (deg (polyDegree termList))
           (bTop (/ (coeffAt termList deg) q)))
        (let loop ((i (- deg 2)) (bPrev bTop) (terms (list (cons (- deg 1) bTop))))
            (if (< i 0)
                (map (lambda (pr)
                         (if (= (car pr) 0)
                             (makep (cdr pr) 1 1 1 1 1 1 '+)
                             (makep (cdr pr) 1 1 1 v (car pr) 1 '+)))
                     (reverse terms))
                (let ((bNext (/ (+ (coeffAt termList (+ i 1)) (* p bPrev)) q)))
                    (loop (- i 1) bNext (cons (cons i bNext) terms)))))))

; Divides every term's coefficient and (if present) variable degree by
; the GCF found by findGCF. A term whose degree drops to 0 becomes a
; proper constant (var set to the non-variable sentinel 1), matching
; the convention used everywhere else (e.g. parseTerm's bare-number
; case) so stringify doesn't print a spurious "x^0".
(define (divideOutGCF termList gcf)
    (let ((coeffGCF (car gcf)) (varGCFdeg (cdr gcf)))
        (map (lambda (term)
                 (let* ((newDeg (if (var? (var term)) (- (varPn term) varGCFdeg) 0))
                        (newVar (if (and (var? (var term)) (> newDeg 0)) (var term) 1)))
                     (makep (/ (cn term) coeffGCF) (cd term) 1 1 newVar (if (eqv? newVar 1) 1 newDeg) 1 '+)))
             termList)))

; Factors a GCF-free degree-2 true-signed term list ax^2+bx+c into two
; linear true-signed term lists, using the quadratic formula: if the
; discriminant b^2-4ac is a perfect square, the roots are rational, and
; each root R = -B/A (A>0, lowest terms) corresponds to a linear factor
; (A*x + B). A1*A2 = a and B1*B2 = c automatically by Vieta's formulas.
; Returns #f if the discriminant isn't a non-negative perfect square.
(define (tryFactorQuadratic termList)
    (let* ((v (polyVariable termList))
           (a (coeffAt termList 2))
           (b (coeffAt termList 1))
           (c (coeffAt termList 0))
           (disc (- (* b b) (* 4 a c))))
        (let ((sq (integerSqrt disc)))
            (if (not sq)
                #f
                (let* ((r1 (/ (+ (- b) sq) (* 2 a)))
                       (r2 (/ (- (- b) sq) (* 2 a)))
                       (A1 (denominator r1)) (B1 (- (numerator r1)))
                       (A2 (denominator r2)) (B2 (- (numerator r2))))
                    (list
                        (list (makep A1 1 1 1 v 1 1 '+) (makep B1 1 1 1 1 1 1 '+))
                        (list (makep A2 1 1 1 v 1 1 '+) (makep B2 1 1 1 1 1 1 '+))))))))

; Factors a GCF-free degree>=3 true-signed term list by finding one
; rational root via the rational root theorem and dividing it out,
; returning the corresponding linear factor and the (degree-1)
; quotient for the caller to recursively re-factor. This naturally
; subsumes sum/difference of cubes (e.g. x^3-8 has root 2) and even
; "biquadratic" cases the discriminant method alone can't reach (e.g.
; x^4-5x^2+4 has roots ±1, ±2) -- no dedicated pattern needed for
; either. Returns #f if no rational root is found.
(define (tryFactorByRationalRoot termList)
    (let ((root (findRationalRoot termList)))
        (if (not root)
            #f
            (let* ((p (numerator root)) (q (denominator root))
                   (v (polyVariable termList))
                   (linearFactor (list (makep q 1 1 1 v 1 1 '+) (makep (- p) 1 1 1 1 1 1 '+)))
                   (quotient (divideByLinearFactor termList p q)))
                (list linearFactor quotient)))))

; Converts a true-signed term list into its printable boundary-signed
; string, reusing the existing simplify.scm/PolyStoSymbol.scm machinery.
(define (termsToString termList)
    (let* ((noZeros (dropZeros termList))
           (final (if (null? noZeros) (list (makep 0 1 1 1 1 1 1 '+)) noZeros)))
        (recordToString (unapplysigns final))))

; Tries one level of pattern factoring on a GCF-free true-signed term
; list, dispatching on degree. Returns a list of true-signed factor
; term-lists, or #f if no pattern applies (degree <= 1, or no rational
; root/perfect-square discriminant found).
(define (factorReduced termList)
    (let ((deg (polyDegree termList)))
        (cond
            ((= deg 2) (tryFactorQuadratic termList))
            ((>= deg 3) (tryFactorByRationalRoot termList))
            ('t #f))))

; Fully factors a true-signed term list: pull out the GCF, try one
; level of pattern factoring on what's left, and recursively re-factor
; any resulting sub-factor that's itself still factorable (this always
; terminates, since each recursive call is on a strictly smaller-degree
; or otherwise irreducible piece). Returns a flat list of "pieces" to
; print and multiply together -- each piece is a true-signed term list,
; printed bare (no parens) if it's a single term, or parenthesized
; otherwise.
(define (fullyFactorPieces termList)
    (let* ((gcf (findGCF termList))
           (coeffGCF (car gcf)) (varGCFdeg (cdr gcf))
           (hasGCF (or (not (= coeffGCF 1)) (> varGCFdeg 0)))
           (quotient (if hasGCF (divideOutGCF termList gcf) termList))
           (v (polyVariable termList))
           (gcfPiece (if hasGCF (list (list (makep coeffGCF 1 1 1 (if (> varGCFdeg 0) v 1) (if (> varGCFdeg 0) varGCFdeg 1) 1 '+))) '()))
           (subFactors (factorReduced quotient)))
        (cond
            (subFactors (append gcfPiece (apply append (map fullyFactorPieces subFactors))))
            ((and (not (null? gcfPiece)) (= (length quotient) 1) (= (cn (car quotient)) 1) (= (cd (car quotient)) 1) (eqv? (var (car quotient)) 1))
                gcfPiece)  ; quotient is just the constant 1 -- nothing left to print (e.g. factor(x^2) = x^2, not x^2*1)
            ('t (append gcfPiece (list quotient))))))

(define (pieceToString piece)
    (if (= (length piece) 1)
        (termsToString piece)
        (string-append "(" (termsToString piece) ")")))

; Top-level entry point: fully expands then factors a polynomial
; expression (the same syntax parseExpansion/expand accept), e.g.
; "2x^2+6x+4" -> "2(x+1)(x+2)". If nothing factors out at all, returns
; the same plain string expand() would.
(define (factor charL)
    (let* ((addends (parseExpansion charL))
           (expanded (expandSum addends))
           (checked (assertSingleVariable expanded "factor"))
           (checked2 (assertIntegerCoefficients expanded "factor"))
           (checked3 (assertIntegerExponents expanded "factor"))
           (pieces (fullyFactorPieces expanded)))
        (if (null? (cdr pieces))
            (termsToString (car pieces))
            (let loop ((ps pieces) (result "") (first #t))
                (cond
                    ((null? ps) result)
                    ((= (length (car ps)) 1)
                        (loop (cdr ps) (string-append result (if first "" "*") (pieceToString (car ps))) #f))
                    ('t
                        (loop (cdr ps) (string-append result (pieceToString (car ps))) #f)))))))

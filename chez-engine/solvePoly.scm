; Single-variable equation solving, built on top of expandParse.scm and
; factorPoly.scm (both must be loaded first). Handles:
;   - Linear: ax+b=0 -> x = -b/a
;   - Quadratic: ax^2+bx+c=0 via the quadratic formula, covering all
;     three cases: rational roots (discriminant a perfect square),
;     irrational real roots (printed symbolically as p ± q√n, with the
;     largest perfect square factor of the discriminant extracted so n
;     is square-free), and complex roots (printed as p ± qi when the
;     discriminant's magnitude is a perfect square, falling back to a
;     decimal approximation for q otherwise -- same convention as the
;     C++ engine, see note below)
;   - Degree >= 3: repeatedly finds a rational root (factorPoly.scm's
;     findRationalRoot/divideByLinearFactor) and divides it out until
;     the remaining factor is degree <= 2, then solves that with the
;     same quadratic/linear logic. If no rational root exists for the
;     remaining factor while its degree is still >= 3, that factor is
;     reported as unsolved rather than guessed at (true general
;     cubic/quartic radical formulas aren't implemented).
;
; Ported from ../solvePoly.scm (MIT Scheme) to Chez Scheme. Changes: the
; one `(error "msg")` call site gets an explicit #f who-arg.
;
; Output format was matched against the C++ engine's `solve` command
; case by case. Two notable divergences, both deliberate:
;   - The C++ engine has a real bug: for an irrational quadratic root
;     (discriminant positive but not a perfect square), it returns the
;     repeated-root answer -b/2a twice instead of -b/2a ± sqrt(disc)/2a
;     (verified e.g. on x^2+4x-4=0, which should be -2±2√2). This file
;     does NOT replicate that bug -- it returns the correct roots.
;   - The C++ engine also has a real bug with cubics/quartics: passing
;     a degree>=3 equation to its quadratic-only solve path produces
;     nonsense complex output instead of using rational-root division
;     (verified on x^3-6x^2+11x-6=0, which should solve to x=1,2,3).
;     This file's degree>=3 handling is unaffected by that bug.

; Finds the (0-based) index of the first occurrence of ch in charL, or
; #f if absent. Used to split an equation string on '=' before any
; tokenization happens, since '=' isn't part of expandParse's grammar.
(define (findCharPos ch charL idx)
    (cond
        ((null? charL) #f)
        ((eqv? (car charL) ch) idx)
        ('t (findCharPos ch (cdr charL) (+ idx 1)))))

; Parses "LHS = RHS", expands both sides, and moves everything to one
; side (LHS - RHS), returning the combined true-signed term list
; representing "... = 0".
(define (parseEquationToZero charL)
    (let ((eqPos (findCharPos #\= charL 0)))
        (if (not eqPos)
            (error #f "solve: expected an equation containing '='")
            (let* ((lhsChars (if (> eqPos 0) (extract 0 (- eqPos 1) charL) '()))
                   (rhsChars (if (< (+ eqPos 1) (length charL)) (extract (+ eqPos 1) (- (length charL) 1) charL) '()))
                   (lhsExpanded (expandSum (parseExpansion lhsChars)))
                   (rhsExpanded (expandSum (parseExpansion rhsChars))))
                (combineLikeTerms (append lhsExpanded (map negateTerm rhsExpanded)))))))

; Formats an exact rational as "p" or "p/q" (q always positive, since
; Scheme keeps exact rationals in lowest terms with positive denominator).
(define (ratToString r)
    (if (= (denominator r) 1)
        (number->string (numerator r))
        (string-append (number->string (numerator r)) "/" (number->string (denominator r)))))

; Largest exact integer r such that r*r <= n (n >= 0). Avoids floating
; point so extractSquareFactor's divisibility test stays exact.
(define (introot-floor n)
    (let loop ((r 1))
        (if (> (* (+ r 1) (+ r 1)) n) r (loop (+ r 1)))))

; Returns (coeff . radicand) such that coeff^2 * radicand = n and
; radicand is square-free (its largest perfect square factor is 1) --
; i.e. simplifies sqrt(n) to coeff*sqrt(radicand). Searches from the
; largest possible coeff downward so radicand comes out minimal.
(define (extractSquareFactor n)
    (let loop ((f (introot-floor n)))
        (cond
            ((< f 1) (cons 1 n))
            ((= 0 (remainder n (* f f))) (cons f (/ n (* f f))))
            ('t (loop (- f 1))))))

; Formats "x = realPart ± coeff*symbolStr", omitting realPart entirely
; if it's 0 (so "2i" not "0 + 2i") and omitting an explicit "1"
; coefficient UNLESS symbolStr is exactly "i" (matching the C++
; engine's own inconsistent-but-replicated convention: coefficient 1
; is omitted before a radical, e.g. "√2", but kept before i, e.g. "1i").
(define (formatSignedTerm realPart coeff symbolStr)
    (let* ((mag (abs coeff))
           (omitOne (and (= mag 1) (not (string=? symbolStr "i"))))
           (magStr (if omitOne "" (ratToString mag)))
           (term (string-append magStr symbolStr)))
        (cond
            ((= realPart 0) (if (< coeff 0) (string-append "-" term) term))
            ('t (string-append (ratToString realPart) (if (< coeff 0) " - " " + ") term)))))

; Same as formatSignedTerm, but coeff is an inexact (floating-point)
; magnitude, rounded to 5 decimal places -- used for the complex-root
; decimal fallback when the discriminant's magnitude isn't a perfect
; square (see solveQuadraticComplex).
(define (decimalToString x)
    (number->string (/ (round (* x 100000)) 100000.0)))

(define (formatSignedTermDecimal realPart coeff symbolStr)
    (let* ((mag (abs coeff))
           (term (string-append (decimalToString mag) symbolStr)))
        (cond
            ((= realPart 0) (if (< coeff 0) (string-append "-" term) term))
            ('t (string-append (ratToString realPart) (if (< coeff 0) " - " " + ") term)))))

(define (solveDegree0 termList)
    (if (= (coeffAt termList 0) 0)
        (list "All real numbers are solutions")
        (list "No solution")))

; varPrefix builds "v = " from the equation's actual variable symbol
; (found via factorPoly.scm's polyVariable), rather than hardcoding
; "x = " -- a real bug fixed after the worksheet generator's use of
; varied variable names (e.g. solving "2y+3=7" must print "y = 2", not
; "x = 2"; verified this matches the C++ engine's own behavior).
(define (varPrefix v) (string-append (symbol->string v) " = "))

(define (solveLinear termList v)
    (let* ((a (coeffAt termList 1)) (b (coeffAt termList 0))
           (root (/ (- b) a)))
        (list (string-append (varPrefix v) (ratToString root)))))

; Discriminant is a non-negative perfect square: roots are rational.
(define (solveQuadraticRational v negB sq twoA)
    (list (string-append (varPrefix v) (ratToString (/ (+ negB sq) twoA)))
          (string-append (varPrefix v) (ratToString (/ (- negB sq) twoA)))))

; Discriminant is positive but not a perfect square: roots are
; irrational, printed symbolically with the radical simplified.
(define (solveQuadraticIrrational v negB disc twoA)
    (let* ((ext (extractSquareFactor disc))
           (radCoeff (car ext))
           (radicand (cdr ext))
           (realPart (/ negB twoA))
           (coeff1 (/ radCoeff twoA))
           (symbolStr (string-append "√" (number->string radicand))))
        (list (string-append (varPrefix v) (formatSignedTerm realPart coeff1 symbolStr))
              (string-append (varPrefix v) (formatSignedTerm realPart (- coeff1) symbolStr)))))

; Discriminant is negative: roots are complex. If |discriminant| is a
; perfect square the imaginary part is rational and prints
; symbolically; otherwise falls back to a decimal approximation
; (matching the C++ engine's own convention for this sub-case).
(define (solveQuadraticComplex v negB absDisc twoA)
    (let* ((sq (integerSqrt absDisc))
           (realPart (/ negB twoA)))
        (if sq
            (let ((coeff1 (/ sq twoA)))
                (list (string-append (varPrefix v) (formatSignedTerm realPart coeff1 "i"))
                      (string-append (varPrefix v) (formatSignedTerm realPart (- coeff1) "i"))))
            (let ((magnitude (/ (sqrt (exact->inexact absDisc)) (abs twoA))))
                (list (string-append (varPrefix v) (formatSignedTermDecimal realPart magnitude "i"))
                      (string-append (varPrefix v) (formatSignedTermDecimal realPart (- magnitude) "i")))))))

(define (solveQuadraticFull termList v)
    (let* ((a (coeffAt termList 2))
           (b (coeffAt termList 1))
           (c (coeffAt termList 0))
           (disc (- (* b b) (* 4 a c)))
           (twoA (* 2 a))
           (negB (- b)))
        (if (>= disc 0)
            (let ((sq (integerSqrt disc)))
                (if sq
                    (solveQuadraticRational v negB sq twoA)
                    (solveQuadraticIrrational v negB disc twoA)))
            (solveQuadraticComplex v negB (- disc) twoA))))

; Degree >= 3: repeatedly factor out one rational root (reusing
; factorPoly.scm's machinery) until degree drops to <= 2, then finish
; with the linear/quadratic solver. Stops and reports the remainder as
; unsolved if no further rational root exists while degree is still
; >= 3 (no general cubic/quartic radical formula is implemented).
;
; Guarded against a fractional coefficient (assertIntegerCoefficients)
; since findRationalRoot/divideByLinearFactor are integer-only, same
; reasoning as factor()'s own guard -- only checked once at entry, not
; per loop iteration, since divideByLinearFactor's synthetic division is
; only exact (Gauss's lemma) when the input is already integer-
; coefficient, so every subsequent quotient stays integer-coefficient too.
(define (solveHigherDegree termList v)
    (assertIntegerCoefficients termList "solve")
    (let loop ((current termList) (roots '()))
        (let ((deg (polyDegree current)))
            (cond
                ((<= deg 1)
                    (append roots (if (= deg 1) (solveLinear current v) (solveDegree0 current))))
                ((= deg 2)
                    (append roots (solveQuadraticFull current v)))
                ('t
                    (let ((root (findRationalRoot current)))
                        (if (not root)
                            (append roots (list (string-append "(no further rational roots found for: " (termsToString current) ")")))
                            (let* ((p (numerator root)) (q (denominator root))
                                   (quotient (divideByLinearFactor current p q)))
                                (loop quotient (append roots (list (string-append (varPrefix v) (ratToString root)))))))))))))

; Removes duplicate solution strings (exact match), preserving order of
; first occurrence -- a degree>=3 equation with a repeated root (e.g.
; "x^3+3x^2-4=0", which factors to (x-1)(x+2)(x+2)) would otherwise
; list that root once per linear factor it came from (e.g. "x=-2"
; twice). Matches the equivalent fix in the C++ engine's solve(),
; applied for the same reason: a root's multiplicity is a property of
; the factored form, not a second distinct solution to report.
(define (dedupSolutions solutions)
    (let loop ((remaining solutions) (seen '()) (acc '()))
        (cond
            ((null? remaining) (reverse acc))
            ((member (car remaining) seen) (loop (cdr remaining) seen acc))
            ('t (loop (cdr remaining) (cons (car remaining) seen) (cons (car remaining) acc))))))

; Top-level entry point: solves a single-variable equation (e.g.
; "x^2-5x+6=0"), returning a list of "v = ..." solution strings, where
; v is whichever variable the equation actually uses.
(define (solve charL)
    (let* ((combined (parseEquationToZero charL))
           (checked (assertSingleVariable combined "solve"))
           ; Checked here, before polyDegree, not just in solveHigherDegree:
           ; polyDegree/coeffAt look for an EXACT integer degree match, so a
           ; negative-exponent term (e.g. "x^-2+x^2=4") would silently be
           ; dropped from consideration rather than erroring -- degree
           ; classification itself isn't safe with a negative exponent
           ; present, not just the rational-root-theorem path.
           (checked2 (assertIntegerExponents combined "solve"))
           (deg (polyDegree combined))
           (v (or (polyVariable combined) 'x)))
        (dedupSolutions
            (cond
                ((= deg 0) (solveDegree0 combined))
                ((= deg 1) (solveLinear combined v))
                ((= deg 2) (solveQuadraticFull combined v))
                ('t (solveHigherDegree combined v))))))

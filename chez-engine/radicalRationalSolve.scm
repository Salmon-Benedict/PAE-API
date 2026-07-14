; Radical and rational equation solving, built on top of expandParse.scm
; (for expandSumFrac, the fraction-native core) and solvePoly.scm (for
; solve, reused for the actual root-finding after each function reduces
; its equation to an ordinary polynomial one). Requires expandParse.scm,
; factorPoly.scm (evalPolyAt), and solvePoly.scm to be loaded first.
;
; Ported from ../radicalRationalSolve.scm (MIT Scheme) to Chez Scheme.
; Changes: the one (error "msg" left) call site gets an explicit #f
; who-arg. Nothing else -- filter/string->number/substring/remove-all
; and the √( unicode literal all behave identically in Chez (same as
; elsewhere in this port).
;
; Deliberately NOT ported from the C++ engine's solveRadical/
; solveRational -- investigated first and both are narrower/buggier than
; what's built here:
;   - C++'s solveRadical only handles sqrt(LINEAR) [+c] = NUMBER, with a
;     fragile hardcoded-string-pattern re-verification step.
;   - C++'s solveRational only handles poly/poly = NUMBER (explicitly
;     refuses rational=rational), and its extraneous-root check is a
;     documented no-op -- the code literally prints
;     "(Denominator exclusion check: simplified for now)" and does
;     nothing; verified live that "(x^2-4)/(x-2)=4" returns the
;     extraneous x=2 instead of rejecting it.

; Finds the (0-based) index of the first occurrence of ch in a STRING
; (equationVariants.scm has its own copy of this same small helper --
; not shared, to keep this file's dependencies exactly what its header
; comment says: expandParse.scm/factorPoly.scm/solvePoly.scm only).
(define (findStringCharPos ch s idx)
    (cond
        ((>= idx (string-length s)) #f)
        ((eqv? (string-ref s idx) ch) idx)
        ('t (findStringCharPos ch s (+ idx 1)))))

; idx is the position of an opening '(' in s; returns the position of
; its matching ')' by tracking nesting depth (so e.g. the radical
; argument in "√((x+1)*2)=3" is extracted correctly).
(define (findMatchingParen s idx)
    (let loop ((i (+ idx 1)) (depth 1))
        (cond
            ((>= i (string-length s)) #f)
            ((eqv? (string-ref s i) #\() (loop (+ i 1) (+ depth 1)))
            ((eqv? (string-ref s i) #\))
                (if (= depth 1) i (loop (+ i 1) (- depth 1))))
            ('t (loop (+ i 1) depth)))))

; Extracts the numeric value from a "v = ..." solve() solution string,
; or #f if the right side isn't a plain number (an irrational "√n",
; complex "p+qi", or an unsolved-equation message) -- string->number
; already returns #f for any of those, so no separate detection is
; needed. Used to decide which candidate roots the extraneous-root check
; below can actually verify (only rational ones).
(define (safeParseRootValue solutionStr)
    (let ((eqPos (findStringCharPos #\= solutionStr 0)))
        (if (not eqPos)
            #f
            (string->number (substring solutionStr (+ eqPos 2) (string-length solutionStr))))))

; Solves "√(<expr>) [+c|-c] = <rhs>" (or "sqrt(<expr>) ...") for x.
; <expr> and <rhs> can be any single-variable polynomial expression (more
; general than the C++ engine's linear-inside/numeric-RHS-only
; restriction, since squaring the isolated radical and solving the
; result already goes through the general solve()); c, if present, must
; be a plain number. Radicals aren't part of expandParse.scm's grammar
; (matching how equationVariants.scm's solveExponential/solveLogarithm
; already string-preprocess rather than extending the grammar), so this
; locates "√(" or "sqrt(", extracts the argument up to the matching ")",
; any trailing "+c"/"-c", and the right-hand side by hand.
;
; Isolates the radical (inner = (rhs-c)^2) and solves that via solve(),
; then verifies each rational candidate root against the actual domain
; requirement -- rhs-c >= 0 at that root, not just inner >= 0 -- since
; squaring can introduce an extraneous root where the ORIGINAL equation's
; radical (always non-negative) would have to equal a negative number.
; Irrational/complex solve() results (safeParseRootValue returns #f)
; pass through unfiltered, since there's no cheap way to check those.
(define (solveRadical charL)
    (let* ((s (list->string (remove-all #\space charL)))
           (eqPos (findStringCharPos #\= s 0))
           (left (substring s 0 eqPos))
           (rhsStr (substring s (+ eqPos 1) (string-length s)))
           (radicalStart
               (cond
                   ((and (>= (string-length left) 2) (string=? (substring left 0 2) "√(")) 2)
                   ((and (>= (string-length left) 5) (string=? (substring left 0 5) "sqrt(")) 5)
                   ('t (error #f "solveRadical: expected the left side to start with √( or sqrt(" left))))
           (openIdx (- radicalStart 1))
           (closeIdx (findMatchingParen left openIdx))
           (innerStr (substring left radicalStart closeIdx))
           (afterStr (substring left (+ closeIdx 1) (string-length left)))
           (c (if (string=? afterStr "") 0 (string->number afterStr))))
        (let* ((rhsMinusCStr (string-append "(" rhsStr ")-(" (number->string c) ")"))
               (isolatedStr (string-append "(" innerStr ")=(" rhsMinusCStr ")^2"))
               (rhsMinusCTerms (expandSum (parseExpansion (string->list rhsMinusCStr))))
               (solutions (solve (string->list isolatedStr)))
               (filtered (filter
                             (lambda (sol)
                                 (let ((r (safeParseRootValue sol)))
                                     (or (not r) (>= (evalPolyAt rhsMinusCTerms r) 0))))
                             solutions)))
            (if (null? filtered) (list "No real solution") filtered))))

; Solves "<poly>/<poly> = <poly>/<poly>" (a plain polynomial on either
; side is fine too, e.g. "poly = poly/poly") for x -- more general than
; the C++ engine's poly/poly = NUMBER-only restriction, and fixes its
; documented no-op extraneous-root check. Cross-multiplies via
; expandSumFrac directly (NOT the guarded expandSum -- a non-constant
; denominator is exactly what this function exists to handle), solves
; the resulting polynomial equation via solve() (inheriting its single-
; variable/integer-coefficient/integer-exponent guards for free since
; it's just handed a rendered string), then filters out any rational
; candidate root that makes EITHER original denominator zero.
(define (solveRational charL)
    (let* ((s (list->string (remove-all #\space charL)))
           (eqPos (findStringCharPos #\= s 0))
           (lhsStr (substring s 0 eqPos))
           (rhsStr (substring s (+ eqPos 1) (string-length s)))
           (lhsFrac (expandSumFrac (parseExpansion (string->list lhsStr))))
           (rhsFrac (expandSumFrac (parseExpansion (string->list rhsStr))))
           (numerL (car lhsFrac)) (denomL (cdr lhsFrac))
           (numerR (car rhsFrac)) (denomR (cdr rhsFrac))
           (crossed (combineLikeTerms
                        (append (multiplyTermLists numerL denomR)
                                (map negateTerm (multiplyTermLists numerR denomL)))))
           (solutions (solve (string->list (string-append (termsToString crossed) "=0"))))
           (filtered (filter
                         (lambda (sol)
                             (let ((r (safeParseRootValue sol)))
                                 (or (not r)
                                     (and (not (= (evalPolyAt denomL r) 0))
                                          (not (= (evalPolyAt denomR r) 0))))))
                         solutions)))
        (if (null? filtered) (list "No solution (every candidate was extraneous)") filtered)))

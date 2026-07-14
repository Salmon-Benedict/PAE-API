; comprehensiveExpansion.scm -- logarithm and exponential expansion
; rules. Requires helperS.scm, mathHelp.scm, basicmath.scm,
; chemistry.scm (findSubstring), PolyStoSymbol.scm, simplify.scm,
; expandParse.scm (expand), equationVariants.scm (stripSpaces,
; findStringCharPos, matchingParen) to be loaded first.
;
; Ported from ../comprehensiveExpansion.scm (MIT Scheme) to Chez Scheme.
; No MIT-isms found in this file (no #!optional, no error calls, no
; record types, no sort/every/any) -- a direct, unchanged port.
;
; ---- Why this is new math, not a port ----
; This corresponds to the C++ engine's expandComprehensive and its
; helpers (expandLogarithmic, expandExponential, expandTrigonometric,
; simplifyRadicals, finalAlgebraicSimplification). Reading all of them
; directly in vendor/cpp/MathSymbol.cpp found that four of the five are
; complete no-ops -- each is literally `string result = expr; return
; result;` with a comment describing rules it never applies (e.g.
; expandLogarithmic's comment says "log(ab) = log(a) + log(b)..." but
; the function body never does this). The only real step in
; expandComprehensive is calling the existing polynomial-expansion
; pipeline when the input contains parentheses -- already exactly what
; this engine's own expand() does. So there was no existing behavior to
; port or fix here; this file is genuine new simplification logic, not
; verified against a C++ oracle the way every other file in this
; project's gap-closing work has been.
;
; ---- Scope ----
; Logarithm expansion (product/quotient/power rules -- expandLogarithmic
; C++'s comment describes exactly this) is implemented in full: it's a
; standard, well-defined textbook topic with an unambiguous correct
; answer, so it's worth doing properly. Exponential expansion is scoped
; to the power-of-a-product rule ((ab)^c = a^c*b^c) only -- the
; sum-in-the-exponent rule C++'s comment also mentions (a^(b+c)=a^b*a^c)
; is a less standard "expansion" direction (normally you'd combine, not
; split, matching exponents) and was left out as lower-value for the
; added parsing complexity. Trigonometric identity expansion (sum/
; difference formulas, double angle, Pythagorean identity, etc.) is
; deliberately NOT attempted: unlike log/exponential rules, there's no
; single canonical "the" expansion for a general trig expression, and
; getting subtle sign/identity errors wrong with no reference
; implementation to catch them is a real risk -- left as an open gap
; rather than guessed at.
;
; Both expandLogarithmic and expandExponential only handle a BARE
; log(...)/ln(...)/log_N(...) or (...)^N call as the entire input
; expression, not one embedded inside a larger sum -- matching the
; scope of a standalone "expand this logarithmic/exponential
; expression" exercise, not general mixed-expression simplification.

; ---- Shared: top-level (paren-respecting) product/quotient splitting ----

; Splits a product/quotient chain like "x^2*y/z" into
; ((#\* . "x^2") (#\* . "y") (#\/ . "z")) -- the operator paired with
; each chunk is the one that INTRODUCED it (the first chunk is always
; paired with #\*, matching "implicitly multiplied into the product").
(define (splitTopLevelFactors s)
    (let loop ((i 0) (start 0) (depth 0) (pendingOp #\*) (acc '()))
        (cond
            ((>= i (string-length s)) (reverse (cons (cons pendingOp (substring s start (string-length s))) acc)))
            ((eqv? (string-ref s i) #\() (loop (+ i 1) start (+ depth 1) pendingOp acc))
            ((eqv? (string-ref s i) #\)) (loop (+ i 1) start (- depth 1) pendingOp acc))
            ((and (= depth 0) (memv (string-ref s i) (list #\* #\/)))
                (loop (+ i 1) (+ i 1) depth (string-ref s i) (cons (cons pendingOp (substring s start i)) acc)))
            ('t (loop (+ i 1) start depth pendingOp acc)))))

; (cons base exponent) for a top-level '^' in s (respecting parens), or
; #f if there isn't one.
(define (splitTopLevelPower s)
    (let loop ((i 0) (depth 0))
        (cond
            ((>= i (string-length s)) #f)
            ((eqv? (string-ref s i) #\() (loop (+ i 1) (+ depth 1)))
            ((eqv? (string-ref s i) #\)) (loop (+ i 1) (- depth 1)))
            ((and (= depth 0) (eqv? (string-ref s i) #\^))
                (cons (substring s 0 i) (substring s (+ i 1) (string-length s))))
            ('t (loop (+ i 1) depth)))))

(define (stripOuterParens s)
    (if (and (> (string-length s) 1)
             (eqv? (string-ref s 0) #\()
             (eqv? (string-ref s (- (string-length s) 1)) #\))
             (= (matchingParen s 0) (- (string-length s) 1)))
        (substring s 1 (- (string-length s) 1))
        s))

; ---- Logarithm expansion ----

; Locates a bare "ln(", "log_N(", or "log(" call at the start of s,
; returning (list prefixString argStartIdx), or #f if none is found.
(define (findLogCall s)
    (let ((lnIdx (findSubstring s "ln(" 0)))
        (if lnIdx
            (list (substring s lnIdx (+ lnIdx 2)) (+ lnIdx 3))
            (let ((underscoreIdx (findSubstring s "log_" 0)))
                (if underscoreIdx
                    (let ((openIdx (findStringCharPos #\( s underscoreIdx)))
                        (list (substring s underscoreIdx openIdx) (+ openIdx 1)))
                    (let ((logIdx (findSubstring s "log(" 0)))
                        (if logIdx
                            (list (substring s logIdx (+ logIdx 3)) (+ logIdx 4))
                            #f)))))))

; Expands a single factor into "logPrefix(factor)", or "exp*logPrefix
; (base)" if the factor itself is a power (the power rule).
(define (expandLogFactor factor logPrefix)
    (let* ((clean (stripOuterParens factor)) (pw (splitTopLevelPower clean)))
        (if pw
            (string-append (cdr pw) "*" logPrefix "(" (car pw) ")")
            (string-append logPrefix "(" clean ")"))))

; Expands the argument of a single log/ln call using the product rule
; (log(ab)=log(a)+log(b)), quotient rule (log(a/b)=log(a)-log(b)), and
; power rule (log(a^n)=n*log(a)) -- applied per top-level factor, so a
; combination like "x^2*y" expands fully to "2*log(x) + log(y)" in one
; pass (each factor's own power rule fires independently).
(define (expandLogArgument argString logPrefix)
    (let ((factors (splitTopLevelFactors (stripOuterParens argString))))
        (if (= (length factors) 1)
            (expandLogFactor (cdar factors) logPrefix)
            (apply string-append
                (let loop ((fs factors) (first #t) (acc '()))
                    (if (null? fs)
                        (reverse acc)
                        (let* ((op (caar fs)) (term (expandLogFactor (cdar fs) logPrefix))
                               (piece (cond (first term) ((eqv? op #\/) (string-append " - " term)) ('t (string-append " + " term)))))
                            (loop (cdr fs) #f (cons piece acc)))))))))

; Expands a bare logarithmic expression, e.g.
; (expandLogarithmic (string->list "log(x*y)")) -> "log(x) + log(y)"
; (expandLogarithmic (string->list "ln(x^3/y)")) -> "3*ln(x) - ln(y)"
; Returns expr unchanged if it isn't a single bare log/ln/log_N call
; spanning the whole input (see file header for scope).
(define (expandLogarithmic exprChars)
    (let* ((expr (stripSpaces (list->string exprChars)))
           (call (findLogCall expr)))
        (if (not call)
            expr
            (let* ((prefix (car call)) (argStart (cadr call))
                   (openIdx (- argStart 1))
                   (closeIdx (matchingParen expr openIdx))
                   (argument (substring expr argStart closeIdx))
                   (prefixStart (- argStart (string-length prefix) 1))
                   (before (substring expr 0 prefixStart))
                   (after (substring expr (+ closeIdx 1) (string-length expr))))
                (if (or (> (string-length before) 0) (> (string-length after) 0))
                    expr
                    (expandLogArgument argument prefix))))))

; ---- Exponential expansion (power of a product/quotient) ----

; #t if s has a top-level '+' or '-' (after position 0, so a leading
; sign doesn't count) -- used to decide whether a factor needs
; re-wrapping in parens before appending "^exponent" to it.
(define (hasTopLevelSign s)
    (let loop ((i 1) (depth 0))
        (cond
            ((>= i (string-length s)) #f)
            ((eqv? (string-ref s i) #\() (loop (+ i 1) (+ depth 1)))
            ((eqv? (string-ref s i) #\)) (loop (+ i 1) (- depth 1)))
            ((and (= depth 0) (memv (string-ref s i) (list #\+ #\-))) #t)
            ('t (loop (+ i 1) depth)))))

; #t if s has any top-level (paren-respecting) +, -, *, or / -- used to
; verify a "^"-exponent runs to the end of the input with nothing
; trailing, rather than assuming everything after '^' IS the exponent.
(define (containsTopLevelOperator s)
    (let loop ((i 0) (depth 0))
        (cond
            ((>= i (string-length s)) #f)
            ((eqv? (string-ref s i) #\() (loop (+ i 1) (+ depth 1)))
            ((eqv? (string-ref s i) #\)) (loop (+ i 1) (- depth 1)))
            ((and (= depth 0) (memv (string-ref s i) (list #\+ #\- #\* #\/))) #t)
            ('t (loop (+ i 1) depth)))))

(define (raiseFactorToPower factor exponent)
    (let ((f (stripOuterParens factor)))
        (if (hasTopLevelSign f)
            (string-append "(" f ")^" exponent)
            (string-append f "^" exponent))))

; Expands a bare "(a*b)^n"-or-"(a/b)^n" expression via the power-of-a-
; product/quotient rule, e.g.
; (expandExponential (string->list "(2*x)^3")) -> "2^3*x^3"
; (expandExponential (string->list "(x/y)^2")) -> "x^2/y^2"
; Returns expr unchanged if it isn't a single "(...)^N" call spanning
; the whole input, or if the base has no top-level */÷ to distribute
; the exponent across (see file header for scope).
(define (expandExponential exprChars)
    (let ((expr (stripSpaces (list->string exprChars))))
        (if (or (= (string-length expr) 0) (not (eqv? (string-ref expr 0) #\()))
            expr
            (let* ((close (matchingParen expr 0))
                   (after (substring expr (+ close 1) (string-length expr))))
                (if (or (= (string-length after) 0) (not (eqv? (string-ref after 0) #\^)))
                    expr
                    (let* ((exponent (substring after 1 (string-length after)))
                           (base (substring expr 1 close))
                           (factors (splitTopLevelFactors base)))
                        (if (or (= (length factors) 1) (containsTopLevelOperator exponent))
                            expr
                            (apply string-append
                                (let loop ((fs factors) (first #t) (acc '()))
                                    (if (null? fs)
                                        (reverse acc)
                                        (let* ((op (caar fs)) (term (raiseFactorToPower (cdar fs) exponent))
                                               (piece (if first term (string-append (string op) term))))
                                            (loop (cdr fs) #f (cons piece acc)))))))))))))

; ---- Top-level dispatcher ----

; Expands a bare logarithmic call, a bare power-of-a-product/quotient
; call, or (falling through) a genuinely polynomial expression via the
; engine's real expand(). See file header for full scope -- mixed
; expressions combining these (e.g. trig terms inside a polynomial sum)
; are not supported.
(define (expandComprehensive exprChars)
    (let ((expr (stripSpaces (list->string exprChars))))
        (cond
            ((findLogCall expr) (expandLogarithmic exprChars))
            ((and (> (string-length expr) 0) (eqv? (string-ref expr 0) #\()
                  (let ((c (matchingParen expr 0)))
                      (and (< (+ c 1) (string-length expr)) (eqv? (string-ref expr (+ c 1)) #\^))))
                (expandExponential exprChars))
            ((findSubstring expr "(" 0) (expand exprChars))
            ('t expr))))

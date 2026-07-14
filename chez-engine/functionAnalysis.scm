; functionAnalysis.scm -- domain/range analysis and function composition/
; inversion, ported in spirit (not line-by-line) from the C++ engine's
; analyzeDomain/analyzeRange/composeFunction/inverseFunction. Requires
; helperS.scm, mathHelp.scm, basicmath.scm, chemistry.scm (findSubstring,
; range), PolyStoSymbol.scm, simplify.scm, expandParse.scm
; (parseExpansion, expandSum, classifyFrac, expand), factorPoly.scm
; (coeffAt, polyDegree, evalPolyAt), solvePoly.scm, calcPoly.scm,
; equationVariants.scm (stripSpaces, findStringCharPos, matchingParen),
; linearSystems.scm (findFirstAlphaPos, parseFractionOrDecimal) to be
; loaded first.
;
; Ported from ../functionAnalysis.scm (MIT Scheme) to Chez Scheme. Changes:
;   - The two (error "msg" irritant) call sites get an explicit #f who-arg
;     (Chez's error signature is (error who message . irritants)).
;   - Nothing else: no sort/every/any/#!optional/define-record-type usages
;     here, and the Unicode literals (∞, √, ∘, ⁻¹, ≠, ≥, ≤) read fine in
;     Chez's UTF-8 reader (same as chemistry.scm's →).
;
; ---- Why this isn't a line-by-line port ----
; Reading vendor/cpp/MathSymbol.cpp directly turned up two confirmed
; problems worth fixing rather than reproducing:
;   - analyzeRange's quadratic case never actually computes a vertex --
;     for any quadratic beyond the trivial "x^2", it returns the literal
;     placeholder string "[vertex, ∞)" (verified by reading the source:
;     `ranges[0] = "[vertex, ∞)"; // Placeholder for most common case`).
;     This file computes the real vertex via coeffAt/evalPolyAt.
;   - inverseFunction's "general" linear case is mostly hardcoded
;     example answers (`if (expression == "2x+1") inverse_expr =
;     "(x-1)/2"`, four more like it), falling back to "Unable to solve
;     automatically" for anything else. This file derives the inverse
;     algebraically for any linear expression via coeffAt, with no
;     hardcoded cases.
;   - composeFunction "simplifies" through stringsToPollies_2, the same
;     legacy tokenizer path cppBridge.scm's own header already warns
;     produces unreliable, sometimes numeric-looking results. This file
;     substitutes textually (same idea as C++) and then simplifies with
;     the engine's actual, well-tested expand().
;
; ---- Scope ----
; Domain/range analysis handles polynomial, rational (division), radical
; (sqrt/√), logarithmic, and exponential functions, generalizing C++'s
; narrow single-example cases (e.g. its rational-range check only
; special-cases the literal string "1/x") to any linear denominator/
; radicand/log-argument via the engine's real parser -- but doesn't
; attempt full symbolic interval arithmetic for multiple simultaneous
; restrictions (joins them with "and" instead) or non-linear
; denominators/radicands/arguments (falls back to a clear descriptive
; message rather than a wrong or placeholder answer). Composition
; handles any expression expand() can simplify (polynomial and rational,
; matching this engine's own scope elsewhere). Inversion handles any
; linear function fully; quadratic and higher are explicitly declined
; with an explanatory message (matching that a general inverse needs
; domain restriction to even exist) rather than attempted.

; Parses a raw algebraic expression string into its (already-expanded)
; term list.
(define (exprToTermList exprString)
    (expandSum (parseExpansion (string->list exprString))))

; The exact zero of a term list, if it's linear (degree exactly 1) with
; a nonzero x coefficient; #f otherwise.
(define (linearZeroOrFalse termList)
    (if (or (> (polyDegree termList) 1) (= (coeffAt termList 1) 0))
        #f
        (/ (- (coeffAt termList 0)) (coeffAt termList 1))))

; ---- Domain analysis ----

; Restriction records: (kind . boundary) with kind in 'neq/'geq/'leq/
; 'gt/'lt, or ('note . descriptionString) when the relevant sub-
; expression isn't linear (so no exact boundary can be computed).

(define (denominatorTermList func)
    (let ((classified (classifyFrac (parseExpansion (string->list func)))))
        (if (eqv? (car classified) 'whole) #f (cddr classified))))

(define (denominatorRestrictions func)
    (if (not (findSubstring func "/" 0))
        '()
        (let ((denom (denominatorTermList func)))
            (if (not denom)
                '()
                (let ((z (linearZeroOrFalse denom)))
                    (if z (list (cons 'neq z)) '()))))))

; Extracts the argument of "sqrt(" or "√(", or #f if neither is present.
(define (findRadicalArg func)
    (let ((sqrtIdx (findSubstring func "sqrt(" 0)))
        (if sqrtIdx
            (let ((open (+ sqrtIdx 4))) (substring func (+ open 1) (matchingParen func open)))
            (let ((rootIdx (findSubstring func "√(" 0)))
                (if rootIdx
                    (let ((open (+ rootIdx 1))) (substring func (+ open 1) (matchingParen func open)))
                    #f)))))

(define (radicalRestrictions func)
    (let ((arg (findRadicalArg func)))
        (if (not arg)
            '()
            (let* ((tl (exprToTermList arg))
                   (linear (= (polyDegree tl) 1))
                   (a (if linear (coeffAt tl 1) 0))
                   (z (if linear (linearZeroOrFalse tl) #f)))
                (cond
                    ((not z) (list (cons 'note (string-append arg " ≥ 0"))))
                    ((> a 0) (list (cons 'geq z)))
                    ('t (list (cons 'leq z))))))))

; Extracts the argument of "log(" or "ln(", or #f if neither is present.
(define (findLogArg func)
    (let ((logIdx (findSubstring func "log(" 0)))
        (if logIdx
            (let ((open (+ logIdx 3))) (substring func (+ open 1) (matchingParen func open)))
            (let ((lnIdx (findSubstring func "ln(" 0)))
                (if lnIdx
                    (let ((open (+ lnIdx 2))) (substring func (+ open 1) (matchingParen func open)))
                    #f)))))

(define (logRestrictions func)
    (let ((arg (findLogArg func)))
        (if (not arg)
            '()
            (let* ((tl (exprToTermList arg))
                   (linear (= (polyDegree tl) 1))
                   (a (if linear (coeffAt tl 1) 0))
                   (z (if linear (linearZeroOrFalse tl) #f)))
                (cond
                    ((not z) (list (cons 'note (string-append arg " > 0"))))
                    ((> a 0) (list (cons 'gt z)))
                    ('t (list (cons 'lt z))))))))

(define (restrictionToInterval r)
    (case (car r)
        ((neq) (string-append "(-∞, " (number->string (cdr r)) ") ∪ (" (number->string (cdr r)) ", ∞)"))
        ((geq) (string-append "[" (number->string (cdr r)) ", ∞)"))
        ((leq) (string-append "(-∞, " (number->string (cdr r)) "]"))
        ((gt)  (string-append "(" (number->string (cdr r)) ", ∞)"))
        ((lt)  (string-append "(-∞, " (number->string (cdr r)) ")"))
        ((note) (cdr r))))

(define (restrictionDescription r)
    (case (car r)
        ((neq) (string-append "x ≠ " (number->string (cdr r))))
        ((geq) (string-append "x ≥ " (number->string (cdr r))))
        ((leq) (string-append "x ≤ " (number->string (cdr r))))
        ((gt)  (string-append "x > " (number->string (cdr r))))
        ((lt)  (string-append "x < " (number->string (cdr r))))
        ((note) (cdr r))))

(define (joinRestrictionDescriptions restrictions)
    (let loop ((rs restrictions) (acc ""))
        (cond
            ((null? rs) acc)
            ((string=? acc "") (loop (cdr rs) (restrictionDescription (car rs))))
            ('t (loop (cdr rs) (string-append acc " and " (restrictionDescription (car rs))))))))

; Analyzes the domain of a function given as a bare expression (e.g.
; (string->list "1/(x-2)")). Returns a one-element list, e.g.
; (list "(-∞, 2) ∪ (2, ∞)").
(define (analyzeDomain funcChars)
    (let* ((func (stripSpaces (list->string funcChars)))
           (restrictions (append (denominatorRestrictions func) (radicalRestrictions func) (logRestrictions func))))
        (list (cond
            ((null? restrictions) "(-∞, ∞)")
            ((= (length restrictions) 1) (restrictionToInterval (car restrictions)))
            ('t (joinRestrictionDescriptions restrictions))))))

; ---- Range analysis ----

; The real vertex-based range of a quadratic, fixing C++'s
; "[vertex, ∞)"-placeholder bug (see file header).
(define (quadraticRange func)
    (let* ((tl (exprToTermList func))
           (a (coeffAt tl 2)))
        (if (= a 0)
            "(-∞, ∞)"
            (let* ((b (coeffAt tl 1))
                   (x0 (/ (- b) (* 2 a)))
                   (y0 (evalPolyAt tl x0)))
                (if (> a 0)
                    (string-append "[" (number->string y0) ", ∞)")
                    (string-append "(-∞, " (number->string y0) "]"))))))

; Range of sqrt(LINEAR-ARG) with an optional additive shift after the
; closing paren -- either before it (e.g. "3-sqrt(x)") or after it (e.g.
; "sqrt(x-2)+3"), both -> "[3, ∞)" for the negated case, "(-∞, 3]" -- so
; rather than only looking right after the closing paren (which mishandles
; "3-sqrt(x)": the shift there is the leading "3", not the empty string
; after ")"), the whole sqrt(...) call is replaced with the literal "0"
; (valid regardless of any multiplier in front of it, since sqrt is
; exactly 0 at the radicand's own zero either way) and whatever's left
; is evaluated as the shift -- this only needs the rest of the
; expression to be x-free (i.e. no other x usage outside the radical);
; if it isn't, that's caught below rather than guessed at.
(define (sqrtRange func marker)
    (let* ((idx (findSubstring func marker 0))
           (negated (and (> idx 0) (eqv? (string-ref func (- idx 1)) #\-)))
           (open (+ idx (- (string-length marker) 1)))
           (close (matchingParen func open))
           (arg (substring func (+ open 1) close))
           (tl (exprToTermList arg)))
        (if (not (= (polyDegree tl) 1))
            "Range requires further analysis (non-linear radicand)"
            (let* ((withoutSqrt (string-append (substring func 0 idx) "0" (substring func (+ close 1) (string-length func))))
                   (shiftTl (exprToTermList withoutSqrt)))
                (if (> (polyDegree shiftTl) 0)
                    "Range requires further analysis (radical combined with other x terms)"
                    (let ((shift (coeffAt shiftTl 0)))
                        (if negated
                            (string-append "(-∞, " (number->string shift) "]")
                            (string-append "[" (number->string shift) ", ∞)"))))))))

; Range of a constant-over-linear rational function (e.g. "1/(x-2)",
; "3/(2x+1)") is always (-∞,0)∪(0,∞) -- the linear denominator is a
; bijection onto every real, so its reciprocal hits every nonzero real
; too, regardless of the shift. Generalizes C++'s literal "1/x"-only
; special case. Anything with a non-constant numerator or non-linear
; denominator declines rather than guessing (that generalization does
; NOT hold in general, e.g. 1/(x^2+1) has range (0,1], not this).
(define (rationalRange func)
    (let ((classified (classifyFrac (parseExpansion (string->list func)))))
        (if (eqv? (car classified) 'whole)
            "(-∞, ∞)"
            (let ((numer (cadr classified)) (denom (cddr classified)))
                (if (and (= (polyDegree denom) 1) (= (polyDegree numer) 0))
                    "(-∞, 0) ∪ (0, ∞)"
                    "Range requires further analysis (complex rational function)")))))

; Analyzes the range of a function given as a bare expression. Returns a
; one-element list, e.g. (list "[-1, ∞)").
(define (analyzeRange funcChars)
    (let ((func (stripSpaces (list->string funcChars))))
        (list (cond
            ((findSubstring func "x^2" 0) (quadraticRange func))
            ((findSubstring func "sqrt(" 0) (sqrtRange func "sqrt("))
            ((findSubstring func "√(" 0) (sqrtRange func "√("))
            ((or (findSubstring func "log(" 0) (findSubstring func "ln(" 0)) "(-∞, ∞)")
            ((findSubstring func "^x" 0) "(0, ∞)")
            ((findSubstring func "/" 0) (rationalRange func))
            ((not (findFirstAlphaPos func 0)) (string-append "{" func "}"))
            ('t "(-∞, ∞)")))))

; ---- Function composition ----

; "f(x)=2x+1" -> (cons "f" "2x+1").
(define (parseFuncDef defStr)
    (let* ((eqIdx (findStringCharPos #\= defStr 0))
           (left (substring defStr 0 eqIdx))
           (expr (substring defStr (+ eqIdx 1) (string-length defStr)))
           (parenIdx (findStringCharPos #\( left 0)))
        (if (not parenIdx)
            (error #f "parseFuncDef: function must include a variable in parentheses, e.g. f(x)" defStr))
        (cons (substring left 0 parenIdx) expr)))

; Replaces every standalone 'x' in expr with "(" replacement ")" --
; standalone meaning not adjacent to another letter (this engine's
; variables are always single letters, so this is mostly a defensive
; check, matching C++'s equivalent guard against touching 'x' inside a
; longer identifier).
(define (substituteX expr replacement)
    (let loop ((i 0) (acc ""))
        (cond
            ((>= i (string-length expr)) acc)
            ((and (eqv? (string-ref expr i) #\x)
                  (or (= i 0) (not (char-alphabetic? (string-ref expr (- i 1)))))
                  (or (= (+ i 1) (string-length expr)) (not (char-alphabetic? (string-ref expr (+ i 1))))))
                (loop (+ i 1) (string-append acc "(" replacement ")")))
            ('t (loop (+ i 1) (string-append acc (string (string-ref expr i))))))))

; Composes two functions given as "f(x)=EXPR1; g(x)=EXPR2", returning
; both (f∘g)(x) and (g∘f)(x), each simplified via the engine's real
; expand() (see file header for why this differs from C++'s approach).
(define (composeFunction defsChars)
    (let* ((defs (stripSpaces (list->string defsChars)))
           (semiIdx (findStringCharPos #\; defs 0)))
        (if (not semiIdx)
            (list "Error: Need two functions separated by semicolon (e.g., f(x)=2x+1; g(x)=x^2)")
            (let* ((fDef (parseFuncDef (substring defs 0 semiIdx)))
                   (gDef (parseFuncDef (substring defs (+ semiIdx 1) (string-length defs))))
                   (fName (car fDef)) (fExpr (cdr fDef))
                   (gName (car gDef)) (gExpr (cdr gDef))
                   (fOfG (expand (string->list (substituteX fExpr gExpr))))
                   (gOfF (expand (string->list (substituteX gExpr fExpr)))))
                (list
                    (string-append "(" fName "∘" gName ")(x) = " fOfG)
                    (string-append "(" gName "∘" fName ")(x) = " gOfF)
                    (string-append "Domain considerations: Check that " gName "(x) is in domain of " fName " for (" fName "∘" gName ")(x)")
                    (string-append "Domain considerations: Check that " fName "(x) is in domain of " gName " for (" gName "∘" fName ")(x)"))))))

; ---- Function inversion ----

; The inverse of a linear expression in y (e.g. "2y+1" -> "(x-1)/2"),
; derived algebraically via coeffAt -- no hardcoded example cases (see
; file header).
(define (linearInverseExpr yExprString)
    (let* ((tl (exprToTermList yExprString))
           (a (coeffAt tl 1)) (b (coeffAt tl 0)))
        (if (= a 0)
            (error #f "inverseFunction: not invertible (constant function)" yExprString)
            (let* ((bStr (cond ((= b 0) "") ((> b 0) (string-append "-" (number->string b)))
                                ('t (string-append "+" (number->string (- b))))))
                   (numerator (string-append "x" bStr)))
                (if (= a 1) numerator (string-append "(" numerator ")/" (number->string a)))))))

; Finds the inverse of a function given as "f(x)=EXPR" or "y=EXPR".
; Fully general for any linear EXPR; quadratic/higher and non-polynomial
; expressions are explicitly declined (see file header -- a real inverse
; there needs a restricted domain, which this doesn't attempt to infer).
(define (inverseFunction defChars)
    (let* ((def (stripSpaces (list->string defChars)))
           (eqIdx (findStringCharPos #\= def 0)))
        (if (not eqIdx)
            (list "Error: Invalid function format. Use f(x)=expression or y=expression")
            (let* ((left (substring def 0 eqIdx))
                   (expr (substring def (+ eqIdx 1) (string-length def)))
                   (parenIdx (findStringCharPos #\( left 0))
                   (funcName (cond (parenIdx (substring left 0 parenIdx)) ((string=? left "y") "f") ('t left)))
                   (yExpr (substituteX expr "y"))
                   (tl (exprToTermList yExpr))
                   (deg (polyDegree tl)))
                (cond
                    ((= deg 1)
                        (list (string-append funcName "⁻¹(x) = " (linearInverseExpr yExpr))
                              (string-append "Domain of " funcName "⁻¹: (-∞, ∞)")
                              (string-append "Range of " funcName "⁻¹: (-∞, ∞)")))
                    ((= deg 2)
                        (list (string-append "Function is quadratic: " funcName "(x) = " expr)
                              "Quadratic functions require domain restriction to be invertible"
                              (string-append "To find the inverse, solve x = " expr " for the variable")))
                    ('t
                        (list (string-append "Non-linear function: " funcName "(x) = " expr)
                              (string-append "To find the inverse, solve x = " expr " for the variable")
                              "Check whether the function is one-to-one before finding an inverse")))))))

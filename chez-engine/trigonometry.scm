; trigonometry.scm -- trig evaluation and equation solving, ported in
; spirit (not line-by-line) from the C++ engine's evaluateTrig/
; solveTrigEquation/solveTrigonometric (the latter is a pure passthrough
; to solveTrigEquation in C++, so only one function is ported here).
; Requires helperS.scm, mathHelp.scm, basicmath.scm, chemistry.scm (for
; findSubstring, range), equationVariants.scm (for pi-const,
; roundToSigFigs, stripSpaces, findStringCharPos, parseNumeralToRational),
; linearSystems.scm (for splitSignedTerms, parseLinearTerm,
; parseFractionOrDecimal, findFirstAlphaPos -- reused here to parse a
; trig argument like "2x+30" the same way a linear-system term is
; parsed, since "coefficient*x plus/minus a constant" is exactly that
; grammar), mathSymbolClass.scm (for ms-symbol -- see "expression-list
; representation" below), and polyBridge.scm (for expr->engine-str,
; ms-poly-str) to be loaded first.
;
; ---- Expression-list representation ----
; A trig function call is represented as a 2-token expression list:
; (trigExpr 'sin argMs) = (list (ms-symbol 'function 'sin) argMs). This
; needs no changes to mathSymbolClass.scm -- ms-symbol's own header
; comment already lists sin/cos/tan as example function names, and
; polyBridge.scm's expr->engine-str already wraps every ms-fraction in
; parens for engine input, so (trigExpr 'sin (ms-fraction-str "x" "1"))
; round-trips to the string "sin(x)" for free. This is the same token
; kind item 6 (comprehensive/mixed expansion) will need to embed a trig
; call inside a larger polynomial expression, so building on it now
; keeps that door open rather than inventing a second representation.
;
; ---- Scope ----
; Exact special-angle values (degrees only -- radian-mode symbolic input
; like "pi/6" is out of scope) for sin/cos/tan at all 17 standard angles
; 0,30,...,360, covering the full circle. This exceeds C++'s own
; evaluateTrig, which only returns exact fractions for 0-180 degrees and
; silently falls back to a decimal for the recognized angle strings
; 210-360 despite explicitly listing them as inputs it handles (verified
; by reading MathSymbol.cpp directly: its exact-value return block only
; checks angleValue against 0..pi, never the 210-360 range, even though
; the input-parsing block above it accepts those degree strings).
;
; solveTrigEquation supports compound arguments (coefficient*x plus/minus
; an offset, e.g. "sin(2x+30)=1/2"), matching C++'s fuller scope, using
; exact rational arithmetic throughout the base-angle-table case (C++
; uses doubles even for the angles it has exact fractions for). The
; coefficient must be a positive integer -- a clear error is raised
; otherwise, rather than C++'s silent zero-solutions bug when
; (int)coefficient truncates to 0.
;
; Ported from ../trigonometry.scm (MIT Scheme) to Chez Scheme. Changes:
; all 5 (error "msg" ...) call sites get an explicit #f who-arg. Nothing
; else -- assv/assoc/case/memv/sin/cos/tan/asin/acos/atan/rational?/round
; all behave identically in Chez, and range/findSubstring come from the
; already-ported chemistry.scm per this file's own header.

; ---- Special-angle exact-value table ----
; (degree sin cos tan), covering the full circle 0-360 in the standard
; 30/45-degree steps. "undefined" for tan at 90/270.
(define trigSpecialAngles
    (list
        (list 0   "0"     "1"     "0")
        (list 30  "1/2"   "√3/2"  "√3/3")
        (list 45  "√2/2"  "√2/2"  "1")
        (list 60  "√3/2"  "1/2"   "√3")
        (list 90  "1"     "0"     "undefined")
        (list 120 "√3/2"  "-1/2"  "-√3")
        (list 135 "√2/2"  "-√2/2" "-1")
        (list 150 "1/2"   "-√3/2" "-√3/3")
        (list 180 "0"     "-1"    "0")
        (list 210 "-1/2"  "-√3/2" "√3/3")
        (list 225 "-√2/2" "-√2/2" "1")
        (list 240 "-√3/2" "-1/2"  "√3")
        (list 270 "-1"    "0"     "undefined")
        (list 300 "-√3/2" "1/2"   "-√3")
        (list 315 "-√2/2" "√2/2"  "-1")
        (list 330 "-1/2"  "√3/2"  "-√3/3")
        (list 360 "0"     "1"     "0")))

; Evaluates sin/cos/tan at a degree angle (char list, e.g. "30"),
; returning an exact special value string if the angle is one of the 17
; standard angles, else a decimal approximation rounded to 6 significant
; figures.
(define (evaluateTrig funcSym degreeChars)
    (let* ((degValue (parseNumeralToRational (stripSpaces (list->string degreeChars))))
           (row (assv degValue trigSpecialAngles)))
        (if row
            (case funcSym
                ((sin) (cadr row)) ((cos) (caddr row)) ((tan) (cadddr row))
                (else (error #f "evaluateTrig: unsupported function (expected sin, cos, or tan)" funcSym)))
            (let ((rad (/ (* (exact->inexact degValue) pi-const) 180)))
                (roundToSigFigs
                    (case funcSym
                        ((sin) (sin rad)) ((cos) (cos rad)) ((tan) (tan rad))
                        (else (error #f "evaluateTrig: unsupported function (expected sin, cos, or tan)" funcSym)))
                    6)))))

; ---- Base-angle tables for solveTrigEquation ----
; Given a special RHS value, the reference angle(s) within one period
; whose sin/cos/tan equals it -- ported directly from C++'s
; getSineBaseAngles/getCosineBaseAngles/getTangentBaseAngles.
(define sineBaseAngles
    (list (cons "0" (list 0 180)) (cons "1/2" (list 30 150)) (cons "√2/2" (list 45 135))
          (cons "√3/2" (list 60 120)) (cons "1" (list 90)) (cons "-1" (list 270))))
(define cosineBaseAngles
    (list (cons "0" (list 90 270)) (cons "1/2" (list 60 300)) (cons "√2/2" (list 45 315))
          (cons "√3/2" (list 30 330)) (cons "1" (list 0)) (cons "-1" (list 180))))
(define tangentBaseAngles
    (list (cons "0" (list 0)) (cons "1" (list 45)) (cons "√3" (list 60))
          (cons "√3/3" (list 30)) (cons "-1" (list 135))))

(define (periodFor func) (if (eqv? func 'tan) 180 360))
(define (baseAngleTable func)
    (case func ((sin) sineBaseAngles) ((cos) cosineBaseAngles) ((tan) tangentBaseAngles)
               (else (error #f "solveTrigEquation: unsupported function (expected sin, cos, or tan)" func))))

(define (normalizeAngle a period)
    (cond ((< a 0) (normalizeAngle (+ a period) period))
          ((>= a period) (normalizeAngle (- a period) period))
          ('t a)))

; Formats a degree value: bare integer if it's a whole number (always
; true for the base-angle-table case, since that path stays exact
; rational throughout), else rounds to 6 significant figures (the
; numeric-fallback case, which is inherently a decimal approximation).
(define (formatDegreeNumber a)
    (if (and (rational? a) (= a (round a)))
        (number->string (round a))
        (roundToSigFigs (exact->inexact a) 6)))

(define (formatAngleSolution angle period)
    (string-append "x = " (formatDegreeNumber angle) "° + " (formatDegreeNumber period) "°n"))

; Finds which of "sin(", "cos(", "tan(" occurs (searching the whole
; string, matching C++'s find()-based approach) and returns
; (cons funcSymbol indexJustPastTheOpenParen), or #f if none found.
(define (findFuncCall s)
    (let ((sinIdx (findSubstring s "sin(" 0))
          (cosIdx (findSubstring s "cos(" 0))
          (tanIdx (findSubstring s "tan(" 0)))
        (cond
            (sinIdx (cons 'sin (+ sinIdx 4)))
            (cosIdx (cons 'cos (+ cosIdx 4)))
            (tanIdx (cons 'tan (+ tanIdx 4)))
            ('t #f))))

; Parses a trig argument ("x", "2x", "x+30", "2x-45", ...) into
; (cons coefficient offset), reusing linearSystems.scm's term parser --
; the grammar is identical to one side of a linear equation.
(define (parseTrigArgument argument)
    (let loop ((terms (splitSignedTerms argument)) (coefficient 1) (offset 0))
        (cond
            ((null? terms) (cons coefficient offset))
            ((findFirstAlphaPos (car terms) 0)
                (loop (cdr terms) (cdr (parseLinearTerm (car terms))) offset))
            ('t (loop (cdr terms) coefficient (parseFractionOrDecimal (car terms)))))))

; Removes every '(' and ')' from a string -- used to normalize the RHS,
; since ms-poly-str (polyBridge.scm) renders a bare constant fraction
; like 1/2 as "(1) / (2)" (parenthesized so it's safely re-parseable by
; the general engine grammar elsewhere), but a trig equation's RHS is
; always just a bare special-value string ("1/2", "√3/2", "undefined")
; or a bare number here, never an expression that genuinely needs
; grouping -- so stripping parens entirely is safe and normalizes both
; "(1) / (2)" and "1/2" to the same "1/2" before matching/parsing it.
(define (removeParens s) (list->string (remove-all #\) (remove-all #\( (string->list s)))))

; Parses "sin(2x+30)=1/2" (spaces already stripped) into
; (list funcSymbol coefficient offset rhsString).
(define (parseTrigEquation eq)
    (let* ((eqIdx (findStringCharPos #\= eq 0))
           (left (substring eq 0 eqIdx))
           (right (removeParens (substring eq (+ eqIdx 1) (string-length eq))))
           (call (findFuncCall left)))
        (if (not call)
            (error #f "solveTrigEquation: expected sin(...), cos(...), or tan(...) on the left side" eq))
        (let* ((func (car call)) (argStart (cdr call))
               (closeIdx (findStringCharPos #\) left argStart))
               (argument (substring left argStart closeIdx))
               (parsedArg (parseTrigArgument argument)))
            (list func (car parsedArg) (cdr parsedArg) right))))

; All solutions within one period for a known base angle, generalized
; across sin/cos/tan/compound-argument -- C++ special-cases sin, cos,
; and tan into three near-duplicate blocks; this is the one shared path.
(define (solveBaseAngleCase func baseAngles coefficient offset)
    (let ((period (periodFor func)))
        (if (and (= coefficient 1) (= offset 0))
            (map (lambda (ba) (formatAngleSolution ba period)) baseAngles)
            (let ((periodOut (/ period coefficient)))
                (apply append
                    (map (lambda (baseAngle)
                             (map (lambda (k)
                                      (formatAngleSolution
                                          (normalizeAngle (/ (+ (- baseAngle offset) (* period k)) coefficient) period)
                                          periodOut))
                                  (range coefficient)))
                         baseAngles))))))

; Numeric fallback via asin/acos/atan when the RHS isn't one of the
; standard special values.
(define (solveNumericCase func rhsValue coefficient offset)
    (if (and (memv func '(sin cos)) (or (< rhsValue -1) (> rhsValue 1)))
        (list "No real solutions (value out of range [-1, 1])")
        (let* ((angleRad (case func ((sin) (asin rhsValue)) ((cos) (acos rhsValue)) ((tan) (atan rhsValue))))
               (angleDeg0 (/ (* angleRad 180) pi-const))
               (angleDeg (if (and (eqv? func 'tan) (< angleDeg0 0)) (+ angleDeg0 180) angleDeg0))
               (period (periodFor func))
               (periodOut (/ period coefficient))
               (secondAngle (case func ((sin) (- 180 angleDeg)) ((cos) (- 360 angleDeg)) ((tan) #f))))
            (if secondAngle
                (list (formatAngleSolution (/ (- angleDeg offset) coefficient) periodOut)
                      (formatAngleSolution (/ (- secondAngle offset) coefficient) periodOut))
                (list (formatAngleSolution (/ (- angleDeg offset) coefficient) periodOut))))))

; Solves a trig equation, e.g. (string->list "sin(x)=0") ->
; (list "x = 0° + 360°n" "x = 180° + 360°n"). See file header for scope.
(define (solveTrigEquation eqChars)
    (let ((eq (stripSpaces (list->string eqChars))))
        (if (not (findStringCharPos #\= eq 0))
            (list "Error: No equals sign found")
            (let* ((parsed (parseTrigEquation eq))
                   (func (car parsed)) (coefficient (cadr parsed)) (offset (caddr parsed)) (rhs (cadddr parsed)))
                (if (or (not (integer? coefficient)) (<= coefficient 0))
                    (error #f "solveTrigEquation: the coefficient of x must be a positive integer" coefficient)
                    (let ((baseEntry (assoc rhs (baseAngleTable func))))
                        (if baseEntry
                            (solveBaseAngleCase func (cdr baseEntry) coefficient offset)
                            (solveNumericCase func (exact->inexact (parseFractionOrDecimal rhs)) coefficient offset))))))))

; solveTrigonometric is a pure passthrough to solveTrigEquation in C++.
(define (solveTrigonometric eqChars) (solveTrigEquation eqChars))

; ---- ms-symbol / expr-list integration ----

; Builds the two-token expression representing "FUNC(ARG)", e.g.
; (trigExpr 'sin (ms-fraction-str "x" "1")) represents sin(x).
(define (trigExpr funcName argMs) (list (ms-symbol 'function funcName) argMs))

; Solves a trig equation given as an expr-list LHS (built via trigExpr)
; and an ms-fraction RHS, e.g.
; (ms-solve-trig (trigExpr 'sin (ms-fraction-str "x" "1")) (ms-fraction-int 1 2))
; -> ("x = 30° + 360°n" "x = 150° + 360°n").
(define (ms-solve-trig lhsExpr rhsMs)
    (solveTrigEquation (string->list (string-append (expr->engine-str lhsExpr) "=" (ms-poly-str rhsMs)))))

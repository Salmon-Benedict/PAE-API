; String-to-symbol parsing and record-to-string conversion for polynomials.
;
; Ported from ../PolyStoSymbol.scm (MIT Scheme) to Chez Scheme.
; Changes from the original:
;   - mergeDigits's #!optional iList, recordToString's #!optional first?/
;     parseable?, and stringify's #!optional parseable? all rewritten as
;     case-lambda.
;   - stringify's internal (define str "") is rewritten as (let ((str ""))
;     ...) instead -- the original had it appear after an (if ...) form in
;     the body, which MIT tolerates (internal defines anywhere in a body)
;     but is not guaranteed portable; using let sidesteps the question
;     entirely rather than relying on Chez's exact tolerance for it.
;
; Depends on: helperS.scm (remove-all), mathHelp.scm (var?), recordPoly2.scm
; (record accessors/mutators: sgn, xvars, varPd, varPn, var, cd, cn, set-Num!).

; Accumulates consecutive digit integers in aList into whole numbers.
; Helper for PolyStoSymbol.
; Note: named mergeDigits, not AddEm, because MIT Scheme case-folds symbols
; by default and AddEm would collide with addem (simplify.scm).
(define mergeDigits
    (case-lambda
        ((aList) (mergeDigits aList '()))
        ((aList iList)
            (cond
                ((null? aList) aList)
                ((integer? (car aList))
                    (set! iList (cons (car aList) (reverse iList)))
                    (set! iList (reverse iList))
                    (cond
                        ((null? (cdr aList))
                            (cons (toInteger iList) '()))
                        ('t (mergeDigits (cdr aList) iList))))
                ((null? iList) (cons (car aList) (mergeDigits (cdr aList))))
                ('t
                    (cons (toInteger iList) (mergeDigits aList '())))))))

; Converts a list of digit integers into a single integer via string concatenation.
(define (toInteger aList)
    (set! aList (map number->string aList))
    (set! aList (apply string-append aList))
    (string->number aList))

; Converts a polynomial character list into a mixed number/symbol list,
; prepends a leading + sign, and returns the result.
(define (PolyStoSymbol polyL)
    (set! polyL (remove-all #\space polyL))
    (set! polyL (PolyStoSymbolH polyL))
    (set! polyL (mergeDigits polyL))
    (set! polyL (reverse polyL))
    (set! polyL (cons '+ polyL))
    (set! polyL (reverse polyL))
    polyL)

; Converts a character list to a mixed number/symbol list; multi-digit numbers
; remain as separate single-digit integers to be merged by mergeDigits.
; Helper for PolyStoSymbol.
(define (PolyStoSymbolH polyL)
    (cond
        ((null? polyL) polyL)
        ((char-numeric? (car polyL))
            (cons (string->number (string (car polyL))) (PolyStoSymbolH (cdr polyL))))
        ('t (cons (string->symbol (string (car polyL))) (PolyStoSymbolH (cdr polyL))))))

; Converts a list of <poly> records back into a polynomial string.
; The boundary-sign convention (each term's `sign` field is the operator
; before the *next* term) has no slot for a sign before the very first
; term, so if the first term's coefficient is negative -- only possible
; after a sign-aware simplify -- a leading "-" is printed explicitly.
;
; parseable?, if #t, parenthesizes a fractional coefficient attached to a
; variable -- e.g. "(1/2)x" instead of the default "1/2x" -- since the
; latter is ambiguous input under expandParse.scm's division grammar
; ('/' now has meaning): re-parsing "1/2x" reads as "1/(2x)" (implicit
; adjacency binds "2x" into one term before the '/' is applied), not
; "(1/2)*x" as stringify originally intended when producing DISPLAY
; output. Only polyBridge.scm's ms-poly-str (the renderer specifically
; used to build a string that gets FED BACK into the engine, e.g. by
; ms-diff/ms-expand/ms-factor/ms-solve) needs this; expand()/
; differentiateExpr()/integrateExpr()'s own direct-to-user output keeps
; the existing compact convention unchanged (default #f everywhere else).
(define recordToString
    (case-lambda
        ((recordL) (recordToString recordL 't #f))
        ((recordL first?) (recordToString recordL first? #f))
        ((recordL first? parseable?)
            (cond
                ((null? recordL) "")
                ('t
                    (let ((term (car recordL)) (leading ""))
                        (if (and (eqv? first? 't) (negative? (cn term)))
                            (begin
                                (set-Num! term (abs (cn term)))
                                (set! leading "-")))
                        (let ((str (stringify term parseable?)))
                            (if (null? (cdr recordL))
                                (set! str (substring str 0 (- (string-length str) 1))))
                            (string-append leading str (recordToString (cdr recordL) 'f parseable?)))))))))

; Converts a single <poly> record into its string representation.
; Handles: constants, coefficient 1, fractional coefficients/powers.
; See recordToString for what parseable? does.
(define stringify
    (case-lambda
        ((record) (stringify record #f))
        ((record parseable?)
            (let ((str ""))

                (set! str (string-append (symbol->string (sgn record)) str))

                ; Extra variables (multivariable terms, e.g. the "y" in "3x^2y"),
                ; canonically sorted by xvars itself. Iterated in reverse because
                ; each piece is *prepended*, same as every other piece below -- code
                ; executed earlier ends up further right in the final string.
                (for-each
                    (lambda (p)
                        (set! str (string-append (symbol->string (car p))
                                      (if (= (cdr p) 1) "" (string-append "^" (number->string (cdr p))))
                                      str)))
                    (reverse (xvars record)))

                ; Variable power: fractional or greater than 1. A fractional exponent
                ; is always parenthesized ("x^(1/2)", "x^(-3/4)") -- unparenthesized
                ; "x^1/2" is genuinely ambiguous once '/' has grammar meaning (it
                ; re-parses as "(x^1)/2", not "x^(1/2)"), a real round-trip-
                ; corruption bug through polyBridge.scm's ms-poly-str (used by
                ; ms-diff/ms-integrate/etc.), not just a display nitpick. A plain
                ; negative INTEGER exponent (varPd=1) needs no parens -- "x^-2" is
                ; unambiguous (no '/' involved) and matches readTokenPower's ^-<int>
                ; shorthand on the way back in.
                (cond
                    ((not (= (varPd record) 1))
                        (set! str (string-append ")" str))
                        (set! str (string-append (number->string (varPd record)) str))
                        (set! str (string-append (symbol->string '/) str))
                        (set! str (string-append (number->string (varPn record)) str))
                        (set! str (string-append "(" str))
                        (set! str (string-append (symbol->string '^) str)))
                    ((= 1 (varPn record)) '())
                    ('t
                        (set! str (string-append (number->string (varPn record)) str))
                        (set! str (string-append (symbol->string '^) str))))

                (if (var? (var record))
                    (set! str (string-append (symbol->string (var record)) str)))

                ; Coefficient: fractional or plain
                (cond
                    ((not (= (cd record) 1))
                        (if (and parseable? (var? (var record)))
                            (begin
                                (set! str (string-append ")" str))
                                (set! str (string-append (number->string (cd record)) str))
                                (set! str (string-append (symbol->string '/) str))
                                (set! str (string-append (number->string (cn record)) str))
                                (set! str (string-append "(" str)))
                            (begin
                                (set! str (string-append (number->string (cd record)) str))
                                (set! str (string-append (symbol->string '/) str))
                                (set! str (string-append (number->string (cn record)) str)))))
                    ((and (var? (var record)) (= 1 (cn record))) '())
                    ('t (set! str (string-append (number->string (cn record)) str))))

                str))))

; Polynomial record type and list-to-record conversion.
;
; Ported from ../recordPoly2.scm (MIT Scheme) to Chez Scheme.
; Changes from the original:
;   - define-record-type: MIT's syntax is R7RS-style (positional constructor
;     field list). Chez's top-level `define-record-type` binding is actually
;     R6RS's *clause-based* syntax instead -- (name-spec) (fields (mutable
;     field accessor mutator) ...) -- confirmed empirically (a verbatim R7RS
;     define-record-type fails with "invalid define-record-type clause",
;     traced to s/syntax.ss:9900's macro definition). Rewritten below in that
;     clause form; the constructor (makepx), predicate (poly?), and all
;     accessor/mutator names are unchanged so every other file's usage is
;     unaffected.
;   - polys's #!optional sign/rec args rewritten as case-lambda (3 arities,
;     matching the original's two independently-optional trailing args).
;     Note: `sign`'s passed-in value is never actually read in the body (it
;     gets unconditionally reassigned to (sgn rec) before use) -- this was
;     already effectively dead as an input in the original, kept as-is since
;     fixing that isn't in scope for a mechanical port.
;   - `single` (the plain-list-returning sibling of `singleR`) is DROPPED:
;     grepped and confirmed it is never called anywhere in the codebase
;     (only its own definition references itself) -- same dead-code pattern
;     as cTest in mathHelp.scm. `singleR` (which IS used, by polyBridge.scm
;     and expandParse.scm) is kept.
;
; Depends on: helperS.scm (nth, next), mathHelp.scm (var?, sign?, firstsign).

; Record type for a single polynomial term.
; Fields: coefficient (numerator/denominator), coefficient power (numerator/denominator),
;         variable, variable power (numerator/denominator), sign, extra variables.
;
; A term is a single monomial: coefficient * variable^power. `variable`
; holds the term's *primary* variable (or the non-variable sentinel `1`
; for a constant); `extraVars` is an alist of (symbol . exponent-rational)
; for any additional variables beyond the primary one, e.g. the term
; "3x^2y" is primary x^2 plus extraVars=((y . 1)). Every term outside
; expandParse.scm's multiplyTerms is still single-variable and has
; extraVars='() -- see makep below, which every existing call site uses.
(define-record-type (<poly> makepx poly?)
    (fields
        (mutable coNum cn set-Num!)         ; coefficient numerator
        (mutable coDen cd set-Den!)         ; coefficient denominator
        (mutable coPnum pn set-pn!)         ; coefficient power numerator
        (mutable coPden pd set-pd!)         ; coefficient power denominator
        (mutable variable var set-var!)     ; variable symbol
        (mutable varPnum varPn set-varPn!)  ; variable power numerator
        (mutable varPden varPd set-varPd!)  ; variable power denominator
        (mutable sign sgn set-sign!)
        (mutable extraVars xvars set-xvars!))) ; alist of additional (symbol . exponent) pairs

; Plain single-variable constructor -- every pre-existing call site in
; the codebase uses this 8-arg form and always gets extraVars='().
(define (makep coNum coDen coPnum coPden variable varPnum varPden sign)
    (makepx coNum coDen coPnum coPden variable varPnum varPden sign '()))

; Converts a flat polynomial symbol list into a list of <poly> records.
(define polys
    (case-lambda
        ((polyL) (polys polyL '+ (makep 0 0 0 0 0 0 0 '+)))
        ((polyL sign) (polys polyL sign (makep 0 0 0 0 0 0 0 '+)))
        ((polyL sign rec)
            (cond
                ((null? polyL) polyL)
                ('t
                    (set! rec (singleR polyL))
                    (set! sign (sgn rec))
                    (set! polyL (cdr (member sign polyL)))
                    (cons rec (polys polyL)))))))

; Parses the first term from polyL into a <poly> record.
(define (singleR polyL)
    (cond
        ; variable, coefficient 1, power 1: e.g. (x +)
        ((and (var? (car polyL)) (sign? (next polyL)))
            (makep 1 1 1 1 (car polyL) 1 1 (firstsign polyL)))

        ; variable, coefficient 1, power > 1: e.g. (x ^ 5 +)
        ((and (var? (car polyL)) (eqv? '^ (next polyL)))
            (makep 1 1 1 1 (car polyL) (nth 2 polyL) 1 (firstsign polyL)))

        ; constant with no variable: e.g. (5 +)
        ((and (number? (car polyL)) (sign? (next polyL)))
            (makep (car polyL) 1 1 1 1 1 1 (firstsign polyL)))

        ; variable with coefficient > 1 and power > 1: e.g. (3 x ^ 2 +)
        ((and (number? (car polyL)) (eqv? '^ (nth 2 polyL)))
            (makep (car polyL) 1 1 1 (next polyL) (nth 3 polyL) 1 (firstsign polyL)))

        ; default: coefficient and variable, power 1: e.g. (5 x +)
        ('t
            (makep (car polyL) 1 1 1 (next polyL) 1 1 (firstsign polyL)))))

; Polynomial simplification: like-term combining and power resolution.
;
; Ported from ../simplify.scm (MIT Scheme) to Chez Scheme.
; Changes from the original:
;   - applysigns's #!optional precedingSign -> case-lambda (simple default).
;   - addem's #!optional temp -> case-lambda, with care: the ORIGINAL
;     distinguishes "temp not given" (default-object?, always means
;     "initialize/first call") from "temp explicitly '()" (a real,
;     different control-flow branch reached only from a recursive call).
;     A naive case-lambda default of temp='() would collapse these into the
;     SAME branch, which is wrong -- the 1-arg entry point must always hit
;     the "initialize" path regardless of what poly's cdr looks like. Kept
;     as two separate case-lambda clauses with genuinely different bodies
;     (not one clause delegating to the other with a default value) to
;     preserve this distinction exactly.
;   - `test` (a diagnostic loop) DROPPED: grepped and confirmed it is never
;     called anywhere in the codebase -- same dead-code pattern as cTest
;     (mathHelp.scm) and single (recordPoly2.scm).
;
; Depends on: helperS.scm (remove), recordPoly2.scm (record accessors/
; mutators), basicmath.scm (reducefrac).

; Full simplification pipeline: resolve each term's coefficient power,
; reduce the resulting coefficient fraction, bake each term's true sign
; into its coefficient so addem can combine like terms arithmetically,
; drop any term whose coefficient collapsed to zero, then convert back
; to the engine's boundary-sign print convention.
(define (simplify poly)
    (for-each powers poly)
    (for-each reduceTerm poly)
    (applysigns poly)
    (let ((result (dropZeros (addem poly))))
        (if (and (null? result) (not (null? poly)))
            (set! result (list (makep 0 1 1 1 1 1 1 '+))))
        (unapplysigns result)))

; <poly> records store a *boundary* sign -- the operator connecting a
; term to the NEXT one, not the term's own sign -- which is what
; stringify/recordToString expect for printing. addem needs each term's
; own true sign baked into its coefficient to combine correctly, so this
; shifts the boundary signs forward: term i's true sign is whatever
; boundary sign term (i-1) was carrying, defaulting to '+ for the first
; term (which has no predecessor).
(define applysigns
    (case-lambda
        ((poly) (applysigns poly '+))
        ((poly precedingSign)
            (cond
                ((null? poly) 'done)
                ('t
                    (if (eqv? precedingSign '-)
                        (set-Num! (car poly) (- (cn (car poly)))))
                    (applysigns (cdr poly) (sgn (car poly))))))))

; Reverses applysigns after combining: cn goes back to non-negative, and
; each term's `sign` field is set to the boundary operator before the
; NEXT term, based on that next term's (still true-signed) coefficient.
; The first term's own sign is left for recordToString to handle, since
; the boundary convention has no slot for a sign before it.
(define (unapplysigns poly)
    (cond
        ((null? poly) poly)
        ((null? (cdr poly))
            (set-sign! (car poly) '+)
            poly)
        ('t
            (set-sign! (car poly) (if (negative? (cn (cadr poly))) '- '+))
            (set-Num! (cadr poly) (abs (cn (cadr poly))))
            (cons (car poly) (unapplysigns (cdr poly))))))

; Reduces a single term's coefficient fraction in place via reducefrac.
(define (reduceTerm term)
    (let ((r (reducefrac (cn term) (cd term))))
        (set-Num! term (car r))
        (set-Den! term (car (cdr r)))))

; Removes terms whose coefficient numerator is 0.
(define (dropZeros poly)
    (cond
        ((null? poly) poly)
        ((= 0 (cn (car poly))) (dropZeros (cdr poly)))
        ('t (cons (car poly) (dropZeros (cdr poly))))))

; Resolves the power on a coefficient or constant, raising numerator/denominator
; to coPnum and resetting the power to 1.
(define (powers poly)
    (set-Num! poly (power (cn poly) (pn poly)))
    (set-Den! poly (power (cd poly) (pn poly)))
    (set-pn! poly 1))

(define (power n e)
    (cond
        ((= e 0) 1)
        ((= e 1) n)
        ('t (* n (power n (- e 1))))))

; Combines consecutive terms in poly with the same variable/degree by adding
; their coefficients; removes the absorbed term from the list.
; Alters argument (destructive).
(define addem
    (case-lambda
        ((poly)
            (cond
                ((null? poly) poly)
                ((null? (cdr poly)) poly)
                ('t (addem poly (cdr poly))))) ;initialize
        ((poly temp)
            (cond
                ((null? poly) poly)
                ((null? (cdr poly)) poly)
                ((null? temp) (cons (car poly) (addem (cdr poly) (cdr (cdr poly)))))
                ((sameP? (car poly) (car temp))
                    (let ((x (+ (/ (cn (car poly)) (cd (car poly))) (/ (cn (car temp)) (cd (car temp))))))
                        (set-Num! (car poly) (numerator x))
                        (set-Den! (car poly) (denominator x)))
                    (set! poly (remove (car temp) poly))
                    (addem poly (cdr temp)))
                ('t (cons (car poly) (addem (cdr poly) (cdr (cdr poly)))))))))

; #t if power and variable are the same, #f otherwise
(define (sameP? poly1 poly2)
    (and (eqv? (var poly1) (var poly2)) (= (/ (varPn poly1) (varPd poly1)) (/ (varPn poly2) (varPd poly2)))))

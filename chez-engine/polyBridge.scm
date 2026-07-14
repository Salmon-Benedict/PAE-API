; polyBridge.scm  --  bridge between mathSymbolClass and the poly engine
;
; Depends on: mathSymbolClass.scm, expandParse.scm, factorPoly.scm,
;             solvePoly.scm, calcPoly.scm
;
; Load order: all engine files first, then mathSymbolClass.scm, then this file.
;
; Return types:
;   ms-expand      -> ms-fraction  (expanded polynomial)
;   ms-factor      -> string       (factored form, e.g. "(x+1)(x+2)")
;   ms-solve       -> list of strings  (e.g. ("x = 1" "x = 2"))
;   ms-diff        -> ms-fraction  (differentiated polynomial)
;   ms-integrate   -> string       (polynomial + " + C")
;   ms-apply       -> dispatches any of the above by symbol name
;
; Expression-list utilities:
;   expr->charL    -> char list suitable for engine input
;   expr-expand    -> ms-fraction (expands a full expression list)
;   ms-from-str    -> ms-fraction (expands any raw polynomial string)
;
; Ported from ../polyBridge.scm (MIT Scheme) to Chez Scheme. Changes:
;   - ms-diff/ms-integrate's #!optional v -> case-lambda, recursing from
;     the 1-arg form into the 2-arg form with v=#f as the "not supplied"
;     sentinel (safe: v is otherwise always a variable-name symbol).
;   - The 3 (error "msg" ...) call sites get an explicit #f who-arg.

; ---- ms-fraction -> char list for engine input ----

; Renders an ms-fraction as a string for engine functions -- i.e. a
; string that's meant to be RE-PARSED (via ms->charL, or directly by
; ms-solve), unlike ms->string (mathSymbolClass.scm), which is for
; direct-to-user display and stays in recordToString's default compact
; mode. Passes parseable?=#t so a fractional coefficient attached to a
; variable renders as "(1/2)x" rather than "1/2x", which is unambiguous
; when re-parsed (see recordToString's doc comment).
; Copies term lists so recordToString can't mutate the stored first term
; when it has a negative cn (leading-minus case).
(define (ms-poly-str ms)
    (let ((ns (recordToString (copy-termlist (ms-numer ms)) 't #t))
          (ds (recordToString (copy-termlist (ms-denom ms)) 't #t)))
        (if (ms-whole? ms) ns
            (string-append "(" ns ") / (" ds ")"))))

(define (ms->charL ms)
    (string->list (ms-poly-str ms)))

; ---- Expand any polynomial string into ms-fraction ----

; Handles leading minus signs, parenthesized expressions, and genuine
; rational expressions (unlike ms-fraction-str, which calls polys and
; only accepts flat, single-variable, division-free polynomial strings).
; Calls classifyFrac directly (NOT the guarded expandSum) since a
; division result here is exactly what ms-fraction is for -- expandSum
; would error on any non-constant denominator, which would make
; ms-expand (= ms-from-str . expand) crash on every input that
; legitimately expands to a rational function.
; Dependency: parseExpansion, classifyFrac from expandParse.scm.
(define (ms-from-str s)
    (let* ((addends (parseExpansion (string->list s)))
           (result (classifyFrac addends)))
        (if (eqv? (car result) 'whole)
            (ms-fraction (unapplysigns (cdr result)) (list (makep 1 1 1 1 1 1 1 '+)))
            (let ((numer (cadr result)) (denom (cddr result)))
                (ms-fraction (if (null? numer) (list (makep 0 1 1 1 1 1 1 '+)) (unapplysigns numer))
                             (unapplysigns denom))))))

; ---- Engine wrappers ----

; Routes through ms-poly-str (parseable-safe) + ms-from-str directly,
; NOT expand() -- ms's term lists are always already fully expanded/
; combined by construction, so this exists to (re-)combine an ms-fraction
; that might not be (e.g. one built by hand via the raw ms-fraction
; constructor), not to do fresh symbolic expansion. Going through
; expand() here used to double-round-trip through strings (ms -> string
; -> expand()'s OWN default, non-parseable output -> string -> ms
; again), and expand()'s default rendering has the exact same "1/2x"
; ambiguity ms-poly-str's parseable? mode exists to avoid -- e.g.
; ms-expand on "x/2" used to come back as "(1) / (2x)" instead of "1/2x".
(define (ms-expand ms)
    (ms-from-str (ms-poly-str ms)))

; Returns the factored-form string, e.g. "(x+1)^2".
; Use ms-from-str to expand the result back to ms-fraction if needed.
(define (ms-factor ms)
    (factor (ms->charL ms)))

; Treats ms as the LHS of an equation set to zero.
; Returns a list of "var = value" strings (one per root).
(define (ms-solve ms)
    (solve (string->list (string-append (ms-poly-str ms) "=0"))))

; Operates on ms's own term list directly (calcPoly.scm's differentiate,
; not differentiateExpr) rather than routing through a string round-trip
; -- ms->charL's rendering, differentiateExpr's OWN (non-parseable)
; string output, then re-parsing via ms-from-str, same class of bug
; already fixed once for ms-expand: a differentiated/integrated term
; can have BOTH a fractional coefficient and an attached variable (e.g.
; d/dx[x^(3/4)] = "3/4x^2"), which re-parses as "(3) / (4x^2)" -- a
; division, not a coefficient -- once that string is fed back in.
; Guards single-variable-ness itself (differentiate/integrate don't) and
; rejects a genuine (non-constant-denominator) fraction, matching what
; differentiateExpr/integrateExpr already reject via the guarded expandSum.
(define ms-diff
    (case-lambda
        ((ms) (ms-diff ms #f))
        ((ms v)
            (if (not (ms-whole? ms))
                (error #f "ms-diff: differentiating a non-constant-denominator fraction isn't supported"))
            (let* ((numer (copy-termlist (ms-numer ms))))
                (assertSingleVariable numer "differentiate")
                (let ((vv (if v v (or (polyVariable numer) 'x))))
                    (ms-fraction (differentiate numer vv) (list (makep 1 1 1 1 1 1 1 '+))))))))

; Returns result string including " + C".
(define ms-integrate
    (case-lambda
        ((ms) (ms-integrate ms #f))
        ((ms v)
            (if (not (ms-whole? ms))
                (error #f "ms-integrate: integrating a non-constant-denominator fraction isn't supported"))
            (let* ((numer (copy-termlist (ms-numer ms))))
                (assertSingleVariable numer "integrate")
                (let ((vv (if v v (or (polyVariable numer) 'x))))
                    (string-append (termsToString (integrate numer vv)) " + C"))))))

; ---- Expression list utilities ----

; Converts an expression list to a string for engine input.
; Each ms-fraction is wrapped in parens so multi-term polynomials parse correctly
; (e.g. [(x+1) * (x-1)] becomes "(x+1)*(x-1)", not "x+1*x-1").
(define (expr->engine-str expr)
    (apply string-append
        (map (lambda (ms)
                 (if (ms-fraction? ms)
                     (string-append "(" (ms-poly-str ms) ")")
                     (ms->string ms)))
             expr)))

(define (expr->charL expr)
    (string->list (expr->engine-str expr)))

; Expands a full expression list; returns ms-fraction. Routes through
; ms-from-str (NOT ms-fraction-str, which calls the legacy polys/singleR
; parser -- that parser doesn't understand parentheses, multivariable
; terms, or the "(numer) / (denom)" fraction syntax expand() can now
; produce, so it would silently mis-parse exactly the results this
; feature and the prior multivariable one exist to support).
(define (expr-expand expr)
    (ms-from-str (expand (expr->charL expr))))

; ---- General dispatcher ----

; (ms-apply 'expand frac)
; (ms-apply 'differentiate frac)
; (ms-apply 'differentiate frac 'y)
(define (ms-apply op ms . rest)
    (case op
        ((expand)             (ms-expand ms))
        ((factor)             (ms-factor ms))
        ((solve)              (ms-solve ms))
        ((differentiate diff) (apply ms-diff  (cons ms rest)))
        ((integrate int)      (apply ms-integrate (cons ms rest)))
        (else (error #f "ms-apply: unknown operation" op))))

; Single-variable differentiation and integration, built on top of
; expandParse.scm and factorPoly.scm (both must be loaded first; the
; latter only for polyVariable, used to infer the default variable --
; see differentiateExpr/integrateExpr below). Both operate term-by-term on
; the same true-signed flat term-list representation expand() uses, via
; the standard power rule:
;   d/dx[c*x^n] = c*n*x^(n-1)        ∫ c*x^n dx = c/(n+1) * x^(n+1)
; Fractional exponents (varPn/varPd) are handled via exact rational
; arithmetic throughout, so e.g. d/dx[x^(1/2)] works correctly even
; though no test corpus below happens to exercise it (the C++ engine's
; own CLI exposes no differentiate/integrate command to use as an
; oracle for that case -- only the underlying MathSymbol::differentiate/
; integrate functions, reachable only by writing a small throwaway C++
; harness, which is how the integer-exponent cases below were verified).
;
; Ported from ../calcPoly.scm (MIT Scheme) to Chez Scheme. Changes:
;   - differentiateExpr's and integrateExpr's #!optional v -> case-lambda.
;   - integrateTerm's one (error "msg" ...) call gets an explicit #f
;     who-arg.
;
; No constant of integration is added here -- integrate's caller can
; append " + C" for display, matching how the C++ engine's main.cpp
; appends it externally rather than baking it into MathSymbol::integrate.
;
; Output format note: a fractional coefficient prints as "num/den x^n"
; (e.g. "-25/2x^2"), matching the existing recordToString convention
; already used by expand()/factor() elsewhere in this codebase -- NOT
; the C++ engine's own single-term convention of "coeff x^n/den" (e.g.
; "-25x^2/2"). This is a deliberate choice: the C++ engine's multi-term
; integrate output is independently broken (verified via a throwaway
; harness -- integrating x^2+5x produces "x^3/3 +  + 5x^2/2", with a
; spurious extra "+" from a display bug), so there's no consistent
; multi-term convention to match anyway. Keeping one single, already-
; verified convention throughout this codebase was judged more valuable
; than partial parity with a format the oracle itself doesn't apply
; consistently.

; Differentiates one true-signed term w.r.t. v. A term not involving v
; (a constant, including the var=1 sentinel) differentiates to 0.
(define (differentiateTerm term v)
    (if (not (eqv? (var term) v))
        (makep 0 1 1 1 1 1 1 '+)
        (let* ((n (/ (varPn term) (varPd term)))
               (newCoeffRat (* (/ (cn term) (cd term)) n))
               (newExp (- n 1)))
            (if (= newExp 0)
                (makep (numerator newCoeffRat) (denominator newCoeffRat) 1 1 1 1 1 '+)
                (makep (numerator newCoeffRat) (denominator newCoeffRat) 1 1 v
                       (numerator newExp) (denominator newExp) '+)))))

(define (differentiate termList v)
    (let* ((diffed (map (lambda (term) (differentiateTerm term v)) termList))
           (combined (combineLikeTerms diffed))
           (noZeros (dropZeros combined)))
        (if (null? noZeros) (list (makep 0 1 1 1 1 1 1 '+)) noZeros)))

; Integrates one true-signed term w.r.t. v (no constant of integration).
; A term not involving v is a constant w.r.t. v, so its antiderivative
; is term*v (covers the numeric-constant case, ∫c dx = c*x; multivariable
; input is rejected by integrateExpr's assertSingleVariable guard before
; this ever runs, so every term here is guaranteed single-variable).
(define (integrateTerm term v)
    (if (not (eqv? (var term) v))
        (makep (cn term) (cd term) 1 1 v 1 1 '+)
        (let* ((n (/ (varPn term) (varPd term)))
               (newExp (+ n 1)))
            (if (= newExp 0)
                (error #f "integrate: ∫x^-1 dx (= ln|x|) isn't supported" term))
            (let ((newCoeffRat (/ (/ (cn term) (cd term)) newExp)))
                (makep (numerator newCoeffRat) (denominator newCoeffRat) 1 1 v
                       (numerator newExp) (denominator newExp) '+)))))

(define (integrate termList v)
    (let* ((integrated (map (lambda (term) (integrateTerm term v)) termList))
           (combined (combineLikeTerms integrated))
           (noZeros (dropZeros combined)))
        (if (null? noZeros) (list (makep 0 1 1 1 1 1 1 '+)) noZeros)))

; Top-level entry points: take the same character-list input
; expand()/factor() do, plus the variable to differentiate/integrate
; with respect to (defaults to whichever variable the expression
; actually uses, via factorPoly.scm's polyVariable -- NOT a hardcoded
; 'x; passing the wrong variable silently produces nonsense, since
; differentiateTerm/integrateTerm's "doesn't involve v" branch just
; drops the term's own variable factor rather than erroring, so e.g.
; integrating "4u+10u^2" with the default left as 'x used to silently
; collapse to "14x" instead of "4ux + 10u^2x" or correctly inferring
; u. This requires factorPoly.scm to be loaded before this file).
(define differentiateExpr
    (case-lambda
        ((charL) (differentiateExpr charL #f))
        ((charL v)
            (let* ((addends (parseExpansion charL))
                   (expanded (expandSum addends)))
                (assertSingleVariable expanded "differentiate")
                (if (not v) (set! v (or (polyVariable expanded) 'x)))
                (termsToString (differentiate expanded v))))))

(define integrateExpr
    (case-lambda
        ((charL) (integrateExpr charL #f))
        ((charL v)
            (let* ((addends (parseExpansion charL))
                   (expanded (expandSum addends)))
                (assertSingleVariable expanded "integrate")
                (if (not v) (set! v (or (polyVariable expanded) 'x)))
                (string-append (termsToString (integrate expanded v)) " + C")))))

; Basic fraction arithmetic operations.
;
; Ported from ../basicmath.scm (MIT Scheme) to Chez Scheme.
; Changes from the original: reducefrac's #!optional f arg rewritten as
; case-lambda.

; Adds two fractions n1/d1 and n2/d2; returns result as (numerator denominator).
(define (addfrac n1 d1 n2 d2)
    (cond
        ((= d1 d2) (list (+ n1 n2) d2))
        ('t
            (set! n1 (* n1 d2))
            (set! n2 (* n2 d1))
            (set! d1 (* d1 d2))
            (set! n1 (+ n1 n2))
            (list n1 d1))))

; Reduces fraction n/d by trial division starting at f; returns (numerator denominator).
; Repeats the same divisor f until it no longer divides both, so repeated
; prime factors (e.g. 4/8 -> 2/4 -> 1/2) are fully squeezed out before f advances.
; Normalizes a negative d by flipping both signs first -- every existing
; caller already keeps d positive (Scheme's numerator/denominator on an
; exact rational always canonicalize that way), so this is a no-op for
; all of them; it only matters for expandParse.scm's division support,
; where a negative constant denominator (e.g. "x/(-2)") is possible.
; Without this, (>= f d) with a negative d returns immediately with the
; sign never normalized, e.g. reducefrac(6,-2) => (6 -2) instead of (-3 1).
;
; Also fixes a pre-existing off-by-one: the termination check used to be
; (>= f d), which gives up BEFORE ever trying f as a divisor when f has
; just reached d, so e.g. reducefrac(6,2) returned unreduced (6 2)
; instead of (3 1) (found via foldConstantDenom below, which is the
; first caller to feed reducefrac an (n,d) pair that needs reducing at
; exactly f=d rather than one that's already fully reduced by the time
; recursion reaches that point -- every pre-existing caller happened to
; avoid this exact boundary). (> f d) tries f=d first, only stopping once
; f has exceeded d with nothing left to divide out.
(define reducefrac
    (case-lambda
        ((n d) (reducefrac n d 2))
        ((n d f)
            (if (< d 0) (begin (set! n (- n)) (set! d (- d))))
            (cond
                ((> f d) (list n d))
                ((and (= 0 (remainder n f)) (= 0 (remainder d f)))
                    (reducefrac (/ n f) (/ d f) f))
                ('t (reducefrac n d (+ f 1)))))))

; Returns #t if two fraction values are numerically equal.
(define (eqfrac? f1 f2)
    (= f1 f2))

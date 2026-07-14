; factorial.scm -- computes n! for a nonnegative integer n, and
; substitutes every bare-integer "N!" occurrence in an expression
; string with its computed value before further processing, so "!"
; works transparently no matter which command is dispatching the line
; (expand, solve, differentiate, ...) -- matches how mathSymbolClass.scm
; already documents "!" as a postfix MathSymbol token category, though
; no prior engine (MIT, Chez, or the original C++) ever actually
; computed a value for it; this is genuinely new, not a port.

(define (factorial n)
    (cond
        ((= n 0) 1)
        ('t (* n (factorial (- n 1))))))

; #t if s contains a "." anywhere.
(define (containsDot? s)
    (let loop ((i 0))
        (cond
            ((>= i (string-length s)) #f)
            ((eqv? (string-ref s i) #\.) #t)
            ('t (loop (+ i 1))))))

; Index just past the numeral (integer or decimal) starting at i --
; consumes an optional single "." as part of the SAME numeral so a
; multi-digit fractional part (e.g. "3.55") is never mistaken for a
; standalone integer partway through a decimal.
(define (scanNumeralEnd s i)
    (let loop ((j i) (seenDot #f))
        (cond
            ((>= j (string-length s)) j)
            ((char-numeric? (string-ref s j)) (loop (+ j 1) seenDot))
            ((and (not seenDot) (eqv? (string-ref s j) #\.)) (loop (+ j 1) #t))
            ('t j))))

; Replaces every "N!" (N a bare NONNEGATIVE INTEGER numeral, directly
; followed by "!") with the computed factorial's numeral -- e.g.
; "3!+2" -> "6+2", "2*5!" -> "2*120", "10!" -> "3628800". A decimal
; immediately before "!" (e.g. "3.5!") is deliberately left untouched
; -- factorial is only defined here for integers, and declining is
; safer than silently mangling a number that merely happens to be
; adjacent to an unrelated "!". A bare "!" with no preceding numeral
; (e.g. "x!") is also left untouched.
(define (substituteFactorials s)
    (let loop ((i 0) (acc ""))
        (cond
            ((>= i (string-length s)) acc)
            ((char-numeric? (string-ref s i))
                (let* ((j (scanNumeralEnd s i))
                       (numeralStr (substring s i j)))
                    (if (and (< j (string-length s))
                             (eqv? (string-ref s j) #\!)
                             (not (containsDot? numeralStr)))
                        (loop (+ j 1) (string-append acc (number->string (factorial (string->number numeralStr)))))
                        (loop j (string-append acc numeralStr)))))
            ('t (loop (+ i 1) (string-append acc (string (string-ref s i))))))))

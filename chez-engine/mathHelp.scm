; Symbol and variable classification helpers.
;
; Ported from ../mathHelp.scm (MIT Scheme) to Chez Scheme.
; cTest (a diagnostic function) is DROPPED: it is never called anywhere in
; the codebase (verified via grep) and its only real branch called `hw`, a
; function that only ever existed in polyData.scm -- itself already excluded
; from this port as dead scratch code (see project_chez_port_scope memory).
; Dead code depending on dead code; not worth carrying forward.
;
; Depends on: helperS.scm (inlist).

(define variableD '(a b c d e f g h i j k l m n o p q r s t u v w x y z))
(define mathsymbols '(+ - * / #\( #\)))
(define signs '(+ - * /))

; Returns #t if k is a math operator (+, -, *, /).
(define (sign? k)
    (inlist k signs))

; Returns the first math operator found scanning aList from the front.
; Used to find the boundary token immediately after a term, since term
; tokens (numbers, variables, ^, exponents) are never signs themselves.
(define (firstsign aList)
    (cond
        ((null? aList) '())
        ((sign? (car aList)) (car aList))
        ('t (firstsign (cdr aList)))))

; Returns t if n is a math symbol, f otherwise.
(define (mathsymbol? n)
    (cond
        ((inlist n mathsymbols) 't)
        ('t 'f)))

; Returns #t if n is a single-letter variable (a-z).
(define (var? n)
    (inlist n variableD))

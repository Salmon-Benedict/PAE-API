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

; #t if s contains no unmatched parenthesis (depth never goes negative,
; ends at depth 0) -- used by indexedVar? to confirm a "(...)" subscript
; span is one well-formed group, not e.g. "(x+1))(y" masquerading as one.
(define (balancedParens? s)
    (let loop ((i 0) (depth 0))
        (cond
            ((< depth 0) #f)
            ((>= i (string-length s)) (= depth 0))
            ((eqv? (string-ref s i) #\() (loop (+ i 1) (+ depth 1)))
            ((eqv? (string-ref s i) #\)) (loop (+ i 1) (- depth 1)))
            ('t (loop (+ i 1) depth)))))

; Returns #t if n is an indexed-variable symbol of the shape
; groupIndexedVars (PolyStoSymbol.scm) produces: a lowercase letter, an
; underscore, and either a digit-run (x_1, a_23), a single lowercase
; letter (x_n, n_x), or a parenthesized expression (x_(x+1)) whose span
; is paren-balanced. Recognizes the tokenizer's own output shape
; directly rather than trying to enumerate the (unbounded) set of valid
; indexed names up front. The (symbol? n) guard matters: var's
; non-variable sentinel is the plain NUMBER 1 (recordPoly2.scm), and
; symbol->string on a number errors.
(define (indexedVar? n)
    (and (symbol? n)
         (let* ((s (symbol->string n)) (len (string-length s)))
             (and (>= len 3)
                  (inlist (string->symbol (string (string-ref s 0))) variableD)
                  (eqv? (string-ref s 1) #\_)
                  (let ((rest (substring s 2 len)))
                      (or
                          ; digit-run subscript
                          (and (> (string-length rest) 0)
                               (let loop ((i 0))
                                   (or (= i (string-length rest))
                                       (and (char-numeric? (string-ref rest i)) (loop (+ i 1))))))
                          ; single-letter subscript
                          (and (= (string-length rest) 1)
                               (inlist (string->symbol rest) variableD))
                          ; parenthesized-expression subscript -- only
                          ; groupIndexedVars ever produces this shape
                          ; (always from expand()'s own valid output),
                          ; so this just confirms the outer envelope,
                          ; not a full re-validation as an expression.
                          (and (> (string-length rest) 1)
                               (eqv? (string-ref rest 0) #\()
                               (eqv? (string-ref rest (- (string-length rest) 1)) #\))
                               (balancedParens? (substring rest 1 (- (string-length rest) 1))))))))))

; Returns #t if n is a single-letter variable (a-z) or an indexed
; variable (x_1, n_x, x_(x+1)) of the shape indexedVar? recognizes.
(define (var? n)
    (or (inlist n variableD) (indexedVar? n)))

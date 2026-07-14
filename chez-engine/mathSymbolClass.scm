; mathSymbolClass.scm  --  tagged math token type
;
; Depends on: basicmath.scm, recordPoly2.scm, PolyStoSymbol.scm, simplify.scm
;
; Three variants:
;   ms-sign     -- operator or relation (arithmetic or relational)
;   ms-symbol   -- named entity: function, postfix op, notation, unit
;   ms-fraction -- rational expression: polynomial numerator / polynomial denominator
;                  Variables and constants live here as polynomial terms.
;
; A complex expression is a list of <math-symbol> tokens.
;
; Ported from ../mathSymbolClass.scm (MIT Scheme) to Chez Scheme. Changes:
;   - define-record-type rewritten in Chez's R6RS clause-based syntax (see
;     recordPoly2.scm's port notes for why -- Chez's top-level
;     define-record-type binding is R6RS's clause form, not R7RS's
;     positional form).
;   - ms-fraction-int's #!optional d -> case-lambda.
;   - All 5 (error "msg" ...) call sites get an explicit #f who-arg.

(define-record-type (<math-symbol> make-math-symbol math-symbol?)
    (fields
        (immutable ms-kind ms-kind)
        (immutable ms-data ms-data)))

; ===========================================================================
; ms-sign  --  arithmetic operators and relational operators
;
; Arithmetic:  +  -  *  /  ^
; Relational:  =  <  >  <=  >=  !=
; ===========================================================================

(define ms-arithmetic-signs '(+ - * / ^))
(define ms-relational-signs  '(= < > <= >= !=))
(define ms-all-signs (append ms-arithmetic-signs ms-relational-signs))

(define (ms-sign s)
    (if (not (memv s ms-all-signs))
        (error #f "ms-sign: unknown sign" s)
        (make-math-symbol 'sign s)))

(define (ms-sign?            ms) (eqv? (ms-kind ms) 'sign))
(define (ms-sign-arithmetic? ms) (and (ms-sign? ms) (memv (ms-data ms) ms-arithmetic-signs) #t))
(define (ms-sign-relational? ms) (and (ms-sign? ms) (memv (ms-data ms) ms-relational-signs) #t))
(define (ms-sign-value       ms) (ms-data ms))

; ===========================================================================
; ms-symbol  --  named entities that are not values
;
; Categories:
;   function  --  sin  cos  tan  log  ln  sqrt  ...
;   postfix   --  !  (factorial)
;   notation  --  sigma (Σ)  Pi-notation (Π)  integral (∫)  limit (lim)  ...
;   unit      --  degree (°)  radian (rad)  angle (∠)  ...
; ===========================================================================

(define ms-symbol-categories '(function postfix notation unit))

(define (ms-symbol category name)
    (if (not (memv category ms-symbol-categories))
        (error #f "ms-symbol: unknown category" category)
        (make-math-symbol 'symbol (cons category name))))

(define (ms-symbol?   ms) (eqv? (ms-kind ms) 'symbol))
(define (ms-function? ms) (and (ms-symbol? ms) (eqv? (ms-symbol-category ms) 'function)))
(define (ms-postfix?  ms) (and (ms-symbol? ms) (eqv? (ms-symbol-category ms) 'postfix)))
(define (ms-notation? ms) (and (ms-symbol? ms) (eqv? (ms-symbol-category ms) 'notation)))
(define (ms-unit?     ms) (and (ms-symbol? ms) (eqv? (ms-symbol-category ms) 'unit)))

(define (ms-symbol-category ms) (car (ms-data ms)))
(define (ms-symbol-name     ms) (cdr (ms-data ms)))

; ===========================================================================
; ms-fraction  --  rational expression
;
; Numerator and denominator are <poly> term lists (lists of <poly> records).
; Variables and constants are expressed as polynomial terms here.
;
; Constructors:
;   (ms-fraction nL dL)      -- term lists directly
;   (ms-fraction-int n d)    -- integer n/d shorthand (d defaults to 1)
;   (ms-fraction-str sn sd)  -- parse two polynomial strings
; ===========================================================================

(define (ms-fraction numer-terms denom-terms)
    (if (null? denom-terms)
        (error #f "ms-fraction: denominator cannot be empty")
        (make-math-symbol 'fraction (list numer-terms denom-terms))))

(define ms-fraction-int
    (case-lambda
        ((n) (ms-fraction-int n 1))
        ((n d)
            (if (= d 0)
                (error #f "ms-fraction-int: denominator cannot be zero")
                (ms-fraction
                    (list (makep n 1 1 1 1 1 1 '+))
                    (list (makep d 1 1 1 1 1 1 '+)))))))

(define (ms-fraction-str sn sd)
    (ms-fraction
        (polys (PolyStoSymbol (string->list sn)))
        (polys (PolyStoSymbol (string->list sd)))))

(define (ms-fraction? ms) (eqv? (ms-kind ms) 'fraction))
(define (ms-numer     ms) (car  (ms-data ms)))
(define (ms-denom     ms) (cadr (ms-data ms)))

; Returns #t if the denominator is the constant 1 (whole expression, no division).
(define (ms-whole? ms)
    (and (ms-fraction? ms)
         (= (length (ms-denom ms)) 1)
         (= (cn (car (ms-denom ms))) 1)
         (not (var? (var (car (ms-denom ms)))))))

; Reduces by the integer GCF of the leading coefficients.
(define (ms-fraction-reduce ms)
    (let* ((n0 (abs (cn (car (ms-numer ms)))))
           (d0 (abs (cn (car (ms-denom ms)))))
           (g  (gcd n0 d0))
           (div (lambda (t)
               (makepx (/ (cn t) g) (cd t)
                      (pn t) (pd t)
                      (var t) (varPn t) (varPd t)
                      (sgn t) (xvars t)))))
        (ms-fraction (map div (ms-numer ms))
                     (map div (ms-denom ms)))))

; ===========================================================================
; Term-list copy -- prevents unapplysigns mutation from corrupting stored data
; ===========================================================================

(define (copy-term t)
    (makepx (cn t) (cd t) (pn t) (pd t) (var t) (varPn t) (varPd t) (sgn t) (xvars t)))

(define (copy-termlist tl)
    (map copy-term tl))

; ===========================================================================
; ms->string  --  human-readable rendering
; ===========================================================================

(define (ms->string ms)
    (cond
        ((ms-sign? ms)
            (case (ms-data ms)
                ((+)  "+")   ((-) "-")   ((*) "*")
                ((/)  "/")   ((^) "^")
                ((=)  "=")   ((<) "<")   ((>) ">")
                ((<=) "<=")  ((>=) ">=") ((!=) "!=")))

        ((ms-symbol? ms)
            (case (ms-symbol-name ms)
                ((!        ) "!")
                ((sigma    ) "Σ")
                ((Pi       ) "Π")
                ((integral ) "∫")
                ((limit    ) "lim")
                ((degree   ) "°")
                ((radian   ) "rad")
                ((angle    ) "∠")
                (else (symbol->string (ms-symbol-name ms)))))

        ((ms-fraction? ms)
            ; copy-termlist prevents recordToString from mutating the stored first
            ; term's cn when it's negative (leading-minus case).
            (let ((ns (recordToString (copy-termlist (ms-numer ms))))
                  (ds (recordToString (copy-termlist (ms-denom ms)))))
                (if (ms-whole? ms)
                    ns
                    (string-append "(" ns ") / (" ds ")"))))

        ('t (error #f "ms->string: unknown kind" (ms-kind ms)))))

; Renders a full expression (list of <math-symbol>) as a string.
(define (expr->string expr)
    (apply string-append (map ms->string expr)))

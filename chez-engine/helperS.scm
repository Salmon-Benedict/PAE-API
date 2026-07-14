; General-purpose list utility functions.
;
; Ported from ../helperS.scm (MIT Scheme) to Chez Scheme.
; Changes from the original:
;   - splice's #!optional/default-object? arg rewritten as case-lambda
;     (Chez doesn't support #!optional at all -- fails at the reader level).
;   - nth's (error "msg") call gets an explicit #f `who` arg -- Chez's error
;     signature is (error who message . irritants), unlike MIT's
;     (error message . irritants).
;   - take/flatten here are DELIBERATELY NOT the same as any standard-library
;     take/flatten: take is inclusive of index n (off-by-one vs SRFI-1/R7RS
;     take, which is exclusive), and flatten here only flattens ONE level
;     (shallow), not a deep flatten. Kept as top-level defines under their
;     original names (matching the rest of this codebase's call sites) rather
;     than renamed, since Chez's default environment does not bind take or
;     flatten itself (verified empirically) -- only `remove` collides with an
;     existing Chez binding, and redefining it at top level is confirmed safe.
;   - number->string is shadowed (below, after the original is captured as
;     chez-number->string) to reformat flonums MIT-style: MIT's printer omits
;     a leading 0 before "." for |x|<1 (0.5 -> ".5") and any trailing
;     fractional 0 for whole-number flonums (3.0 -> "3.", 0.0 -> "0." --
;     note the intpart's own "0" is NOT stripped in that whole-number case,
;     only when there's an actual nonzero fractional part), while Chez's
;     prints the R6RS-standard "0.5"/"3.0"/"0.0". Confirmed empirically
;     against the real MIT binary across leading/trailing-zero and negative
;     cases. This matters because every already-ported file that formats a
;     flonum via roundToSigFigs (equationVariants.scm, and transitively
;     conicSections.scm/trigonometry.scm's eccentricity/degree/percentage
;     output) would otherwise silently diverge from MIT's textbook-style
;     output. Scientific-notation strings (containing "e"/"E") are passed
;     through unchanged -- Chez switches to scientific notation at a smaller
;     magnitude threshold than MIT (e.g. 0.0001 -> Chez's "1e-4" vs MIT's
;     ".0001"), which isn't fixed here since no call site in this codebase
;     has been observed to produce a flonum that small (roundToSigFigs'
;     inputs are angle/eccentricity/area-scale). Exact numbers (integers,
;     rationals) and the 2-arg (number->string n radix) form are passed
;     through to chez-number->string untouched.

; Returns a list of elements from index 0 through n (inclusive).
(define (take aList n)
    (let loop ((i n) (acc '()))
        (if (< i 0)
            acc
            (loop (- i 1) (cons (nth i aList) acc)))))

; Returns all but the first element, or empty list if singleton.
(define (rest aList)
    (cond
        ((null? (cdr aList)) '())
        ('t (cdr aList))))

; Returns the second element of a list, or empty list if fewer than two elements.
(define (next aList)
    (cond
        ((null? aList) '())
        ((null? (cdr aList)) '())
        ('t (car (cdr aList)))))

; Returns the last element of a list.
(define (last aList)
    (car (reverse aList)))

; Returns #t if var appears anywhere in aList.
(define (inlist var aList)
    (cond
        ((null? aList) #f)
        ((eqv? var (car aList)) #t)
        ('t (inlist var (cdr aList)))))

; Returns the length of the remaining list after the first match from varL in aList.
(define (nextinlist varL aList)
    (cond
        ((null? varL) 1)
        ('t (length (member (car varL) aList)))))

; Removes the first occurrence of e from aList.
; NOTE: shadows Chez's own (remove pred list) -- intentional, matches this
; codebase's element-based (not predicate-based) calling convention.
(define (remove e aList)
    (cond
        ((null? aList) aList)
        ((eqv? e (car aList)) (cdr aList))
        ('t (cons (car aList) (remove e (cdr aList))))))

; Removes all occurrences of e from aList.
(define (remove-all e aList)
    (cond
        ((null? aList) aList)
        ((eqv? e (car aList)) (remove-all e (cdr aList)))
        ('t (cons (car aList) (remove-all e (cdr aList))))))

; Returns a sublist from index start through end (inclusive).
(define (extract start end aList)
    (if (<= start end)
        (cons (nth start aList) (extract (+ start 1) end aList))
        '()))

; Inserts inList into aList after position p.
(define splice
    (case-lambda
        ((p aList inList) (splice p aList inList 0))
        ((p aList inList i)
            (cond
                ((or (null? aList) (null? inList)) '())
                ((>= p i)
                    (cons (car aList) (splice p (cdr aList) inList (+ i 1))))
                ((= p (- i 1))
                    (append (append inList (splice p (cdr aList) inList (+ i 1))) aList))
                ((< p i) '())))))

; Flattens one level of nested lists into a single flat list.
(define (flatten aList)
    (cond
        ((null? aList) aList)
        ((list? (car aList)) (append (car aList) (flatten (cdr aList))))
        ('t (cons (car aList) (flatten (cdr aList))))))

; Consolidates nested integer sublists into a flat list.
(define (consolidateI aList)
    (cond
        ((null? aList) aList)
        ((list? (car aList)) (append (car aList) (consolidateI (cdr aList))))
        ('t (cons (car aList) (consolidateI (cdr aList))))))

; Returns all but the last element of a list.
(define (rcdr aList)
    (reverse (cdr (reverse aList))))

; Returns the element at 0-based index n, or errors if out of bounds.
(define (nth n l)
    (if (or (> n (length l)) (< n 0))
        (error #f "Index out of bounds.")
        (if (eq? n 0)
            (car l)
            (nth (- n 1) (cdr l)))))

; ---- MIT-style number->string shim (see file header) ----

(define chez-number->string number->string)

(define (charIndex s c)
    (let ((len (string-length s)))
        (let loop ((i 0))
            (cond ((>= i len) #f) ((eqv? (string-ref s i) c) i) ('t (loop (+ i 1)))))))

(define (mit-format-flonum-string s)
    (if (or (charIndex s #\e) (charIndex s #\E))
        s
        (let ((dotIdx (charIndex s #\.)))
            (if (not dotIdx)
                s
                (let* ((intPart (substring s 0 dotIdx))
                       (fracPart (substring s (+ dotIdx 1) (string-length s)))
                       (neg? (and (> (string-length intPart) 0) (eqv? (string-ref intPart 0) #\-)))
                       (digitsOnly (if neg? (substring intPart 1 (string-length intPart)) intPart))
                       (newFrac (if (string=? fracPart "0") "" fracPart))
                       (newInt (if (string=? newFrac "")
                                   intPart
                                   (if (string=? digitsOnly "0") (if neg? "-" "") intPart))))
                    (string-append newInt "." newFrac))))))

(define number->string
    (case-lambda
        ((x) (if (and (real? x) (inexact? x)) (mit-format-flonum-string (chez-number->string x)) (chez-number->string x)))
        ((x radix) (chez-number->string x radix))))

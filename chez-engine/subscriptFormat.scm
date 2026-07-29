; subscriptFormat.scm -- converts "base_subscript" notation in an
; already-formatted output string into real Unicode subscript
; characters, mirroring superscriptFormat.scm's toSuperscriptNotation
; exactly (same all-or-nothing-per-occurrence fallback design, same
; "(...)" group vs. bare-run shape). DISPLAY ONLY for now -- this does
; NOT yet make x_1 and x_2 distinct symbols to the tokenizer/engine;
; that's a separate, larger piece.
;
; Unicode's subscript coverage is much sparser than its superscript
; coverage: there is no dedicated subscript character for b, c, d, f,
; g, q, w, y, or z at all. Any "_..." occurrence containing one of
; those (or any other unmapped character) is left as plain "_..." text,
; same fallback policy as toSuperscriptNotation.

(define subscriptCharMap '(
    (#\0 . "₀") (#\1 . "₁") (#\2 . "₂") (#\3 . "₃") (#\4 . "₄")
    (#\5 . "₅") (#\6 . "₆") (#\7 . "₇") (#\8 . "₈") (#\9 . "₉")
    (#\+ . "₊") (#\- . "₋") (#\= . "₌") (#\( . "₍") (#\) . "₎")
    (#\a . "ₐ") (#\e . "ₑ") (#\h . "ₕ") (#\i . "ᵢ") (#\j . "ⱼ")
    (#\k . "ₖ") (#\l . "ₗ") (#\m . "ₘ") (#\n . "ₙ") (#\o . "ₒ")
    (#\p . "ₚ") (#\r . "ᵣ") (#\s . "ₛ") (#\t . "ₜ") (#\u . "ᵤ")
    (#\v . "ᵥ") (#\x . "ₓ")))

; #f if c has no subscript equivalent, else its subscript string.
(define (subscriptChar c)
    (let ((pair (assoc c subscriptCharMap)))
        (if pair (cdr pair) #f)))

; Maps every character of s to its subscript form; #f if ANY character
; in s has no mapping (never a partial result).
(define (subscriptString s)
    (let loop ((i 0) (acc '()))
        (if (>= i (string-length s))
            (apply string-append (reverse acc))
            (let ((mapped (subscriptChar (string-ref s i))))
                (if mapped
                    (loop (+ i 1) (cons mapped acc))
                    #f)))))

; Duplicated per this codebase's own per-file scanning-helper
; convention (see superscriptFormat.scm's own copy).
(define (findMatchingParenForSubscript s idx)
    (let loop ((i (+ idx 1)) (depth 1))
        (cond
            ((>= i (string-length s)) #f)
            ((eqv? (string-ref s i) #\() (loop (+ i 1) (+ depth 1)))
            ((eqv? (string-ref s i) #\))
                (if (= depth 1) i (loop (+ i 1) (- depth 1))))
            ('t (loop (+ i 1) depth)))))

; Converts every "_(...)" or "_<alphanumerics>" occurrence in s into
; Unicode subscript characters. A bare run (no parens) is greedy over
; BOTH letters and digits (unlike toSuperscriptNotation's bare run,
; which is digits-only) -- "x_n" and "x_1" are both valid bare shapes
; here, since a subscript is routinely a single variable, not just a
; numeral.
(define (toSubscriptNotation s)
    (let loop ((i 0) (acc '()))
        (cond
            ((>= i (string-length s)) (apply string-append (reverse acc)))
            ((and (eqv? (string-ref s i) #\_)
                  (< (+ i 1) (string-length s))
                  (eqv? (string-ref s (+ i 1)) #\())
                (let ((closeIdx (findMatchingParenForSubscript s (+ i 1))))
                    (if (not closeIdx)
                        (loop (+ i 1) (cons "_" acc))
                        (let* ((inner (substring s (+ i 2) closeIdx))
                               (mapped (subscriptString inner)))
                            (if mapped
                                (loop (+ closeIdx 1) (cons (string-append "₍" mapped "₎") acc))
                                (loop (+ i 1) (cons "_" acc)))))))
            ((and (eqv? (string-ref s i) #\_)
                  (< (+ i 1) (string-length s))
                  (or (char-numeric? (string-ref s (+ i 1))) (char-alphabetic? (string-ref s (+ i 1)))))
                (let scanRun ((j (+ i 1)))
                    (if (and (< j (string-length s))
                             (or (char-numeric? (string-ref s j)) (char-alphabetic? (string-ref s j))))
                        (scanRun (+ j 1))
                        (let* ((run (substring s (+ i 1) j))
                               (mapped (subscriptString run)))
                            (if mapped
                                (loop j (cons mapped acc))
                                (loop j (cons (string-append "_" run) acc)))))))
            ('t (loop (+ i 1) (cons (string (string-ref s i)) acc))))))

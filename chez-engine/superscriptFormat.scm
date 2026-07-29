; superscriptFormat.scm -- converts "^exponent" notation in an already-
; formatted output string into real Unicode superscript characters, as
; a final display-only pass. Deliberately does NOT touch anything
; upstream -- every internal function (expand, factor, solve, simplify,
; etc.) keeps using plain "^" as its working representation, matching
; every existing golden test unchanged; this file only transforms a
; STRING a caller is about to print/return, the same way factorial.scm's
; substituteFactorials and nextLineTrigger.scm's stripNextLineTrigger
; each operate as a pass over a string rather than rewriting the
; engine's internal term representation.
;
; Per-character mapping is intentionally partial -- there is, for
; instance, no MODIFIER LETTER SMALL Q in Unicode, and no superscript
; "/" either (fractional exponents like "x^(1/2)" are left alone for
; that reason). If ANY character inside one "^..." occurrence has no
; mapping, that whole occurrence is left as plain "^..." text rather
; than producing a partially-converted, visually broken result.

(define superscriptCharMap '(
    (#\0 . "⁰") (#\1 . "¹") (#\2 . "²") (#\3 . "³") (#\4 . "⁴")
    (#\5 . "⁵") (#\6 . "⁶") (#\7 . "⁷") (#\8 . "⁸") (#\9 . "⁹")
    (#\+ . "⁺") (#\- . "⁻") (#\= . "⁼") (#\( . "⁽") (#\) . "⁾")
    (#\a . "ᵃ") (#\b . "ᵇ") (#\c . "ᶜ") (#\d . "ᵈ") (#\e . "ᵉ")
    (#\f . "ᶠ") (#\g . "ᵍ") (#\h . "ʰ") (#\i . "ⁱ") (#\j . "ʲ")
    (#\k . "ᵏ") (#\l . "ˡ") (#\m . "ᵐ") (#\n . "ⁿ") (#\o . "ᵒ")
    (#\p . "ᵖ") (#\r . "ʳ") (#\s . "ˢ") (#\t . "ᵗ") (#\u . "ᵘ")
    (#\v . "ᵛ") (#\w . "ʷ") (#\x . "ˣ") (#\y . "ʸ") (#\z . "ᶻ")))

; #f if c has no superscript equivalent (e.g. #\q), else the (single-
; character-wide) superscript string for c.
(define (superscriptChar c)
    (let ((pair (assoc c superscriptCharMap)))
        (if pair (cdr pair) #f)))

; Maps every character of s to its superscript form; #f (never a
; partial result) if ANY character in s has no mapping.
(define (superscriptString s)
    (let loop ((i 0) (acc '()))
        (if (>= i (string-length s))
            (apply string-append (reverse acc))
            (let ((mapped (superscriptChar (string-ref s i))))
                (if mapped
                    (loop (+ i 1) (cons mapped acc))
                    #f)))))

; Finds the index of the ")" matching the "(" at index idx in s (depth-
; aware, for nested parens inside the exponent) -- #f if unmatched.
; Duplicated from radicalRationalSolve.scm's findMatchingParen rather
; than shared, matching this codebase's established per-file convention
; for small string-scanning helpers.
(define (findMatchingParenForSuperscript s idx)
    (let loop ((i (+ idx 1)) (depth 1))
        (cond
            ((>= i (string-length s)) #f)
            ((eqv? (string-ref s i) #\() (loop (+ i 1) (+ depth 1)))
            ((eqv? (string-ref s i) #\))
                (if (= depth 1) i (loop (+ i 1) (- depth 1))))
            ('t (loop (+ i 1) depth)))))

; Converts every "^(...)" or "^<digits>" occurrence in s into Unicode
; superscript characters. These are the only two shapes "^" is ever
; followed by in this engine's own output conventions: a bare digit run
; for a plain numeral exponent (e.g. "x^2", "(y+2)^10"), or a "(...)"
; group for everything else (variables, multi-term expressions,
; fractional exponents, etc.) -- see expandParse.scm/equationVariants.
; scm's own printing logic. A "^" followed by anything else (shouldn't
; happen given those conventions, but defensive) is left untouched.
(define (toSuperscriptNotation s)
    (let loop ((i 0) (acc '()))
        (cond
            ((>= i (string-length s)) (apply string-append (reverse acc)))
            ((and (eqv? (string-ref s i) #\^)
                  (< (+ i 1) (string-length s))
                  (eqv? (string-ref s (+ i 1)) #\())
                (let ((closeIdx (findMatchingParenForSuperscript s (+ i 1))))
                    (if (not closeIdx)
                        (loop (+ i 1) (cons "^" acc))
                        (let* ((inner (substring s (+ i 2) closeIdx))
                               (mapped (superscriptString inner)))
                            (if mapped
                                (loop (+ closeIdx 1) (cons (string-append "⁽" mapped "⁾") acc))
                                (loop (+ i 1) (cons "^" acc)))))))
            ((and (eqv? (string-ref s i) #\^)
                  (< (+ i 1) (string-length s))
                  (char-numeric? (string-ref s (+ i 1))))
                (let scanDigits ((j (+ i 1)))
                    (if (and (< j (string-length s)) (char-numeric? (string-ref s j)))
                        (scanDigits (+ j 1))
                        (loop j (cons (superscriptString (substring s (+ i 1) j)) acc)))))
            ('t (loop (+ i 1) (cons (string (string-ref s i)) acc))))))

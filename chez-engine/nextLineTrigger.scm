; nextLineTrigger.scm -- detects the "next line/cell" trigger character
; (ç, U+00E7 / 231 -- a Latin-1 "extended ASCII" letter chosen for having
; zero footprint in standard math notation; ~ was ruled out since it's
; already informally used for sample-statistic notation, e.g. n-tilde).
; A prefix or suffix ç on an input expression signals that the computed
; answer should be placed on the next line/cell rather than alongside
; the problem -- every client (Mac App, Excel/Sheets via PAE-API,
; LibreOffice) reacts to the same wire signal the same way: a leading ç
; on the RESULT string dispatcher.scm hands back means "strip this
; marker and render/place the remainder on the next line/cell instead
; of in place," rather than each client needing its own detection logic.
;
; Represented via integer->char rather than a literal ç source character,
; to avoid any risk of source-file encoding mismatches across editors/
; tools.
(define next-line-trigger-char (integer->char 231))

; ---- minimal leading/trailing-whitespace trim, self-contained ----
; (mirrors dispatcher.scm's own trim/ws-char?, which exist there for the
; same reason -- see that file's header comment on chain.scm -- kept
; separate rather than shared, matching this codebase's established
; pattern for small string utilities living alongside whatever needs
; them instead of centralized.)
(define (nlt-ws-char? c) (or (char=? c #\space) (char=? c #\tab) (char=? c #\newline) (char=? c #\return)))

(define (nlt-trim-left s)
    (let ((len (string-length s)))
        (let loop ((i 0))
            (if (and (< i len) (nlt-ws-char? (string-ref s i)))
                (loop (+ i 1))
                (substring s i len)))))

(define (nlt-trim-right s)
    (let ((len (string-length s)))
        (let loop ((i len))
            (if (and (> i 0) (nlt-ws-char? (string-ref s (- i 1))))
                (loop (- i 1))
                (substring s 0 i)))))

(define (nlt-trim s) (nlt-trim-left (nlt-trim-right s)))

; Returns (values strippedLine triggered?). Strips exactly one leading OR
; trailing occurrence of the trigger char (checked after trimming
; whitespace, so both "x=5 ç" and "ç x=5" work, and the stripped result
; is trimmed again to drop the space that was next to the marker) --
; leading is checked first, so a degenerate single-character "ç" input
; strips to an empty (triggered) expression rather than being treated as
; untriggered.
(define (stripNextLineTrigger line)
    (let* ((trimmed (nlt-trim line))
           (len (string-length trimmed)))
        (cond
            ((and (> len 0) (char=? (string-ref trimmed 0) next-line-trigger-char))
                (values (nlt-trim (substring trimmed 1 len)) #t))
            ((and (> len 0) (char=? (string-ref trimmed (- len 1)) next-line-trigger-char))
                (values (nlt-trim (substring trimmed 0 (- len 1))) #t))
            ('t (values line #f)))))

; variableSubstitution.scm -- implements the "@:setval"/"@:clearval"
; feature documented in README_COMMANDS.html as "Planned -- not yet
; implemented": substituting known numeric values for named variables
; in an expression, leaving any variable without an assigned value
; symbolic. Ported in spirit from the C++ engine's real (if apparently
; abandoned) MathSymbol::substituteVariables (Poly-Working/MathSymbol.cpp,
; ~line 11404): for each term, multiply the coefficient by value^degree
; for every variable with an assigned value, checking multivariable
; terms too. Generalized here to exact rationals (not just C++'s int)
; and to indexed-variable symbols (x_1, n_x, x_(x+1)), not just single
; characters.
;
; Requires recordPoly2.scm (record accessors, makep/makepx), mathHelp.scm
; (var?), expandParse.scm (parseExpansion, expandSum, combineLikeTerms),
; simplify.scm (unapplysigns), PolyStoSymbol.scm (recordToString),
; equationVariants.scm or radicalRationalSolve.scm (findStringCharPos),
; linearSystems.scm (parseFractionOrDecimal) to be loaded first.

; Attempts to substitute a numeric value for one (variable . exponent)
; occurrence. Returns (cons #t multiplier) if v has an assigned value in
; varValueAlist AND exponent is a plain integer; (cons #f 1) otherwise
; (either no value assigned, or a fractional exponent -- deliberately
; declined rather than producing an inexact/irrational result this
; engine otherwise keeps symbolic, e.g. via square-root notation).
(define (trySubstituteOne v exponent varValueAlist)
    (let ((assigned (assq v varValueAlist)))
        (if (and assigned (integer? exponent))
            (cons #t (expt (cdr assigned) exponent))
            (cons #f 1))))

; Substitutes known values into one <poly> term, checking both the
; primary `var` field and every entry in `xvars` (multivariable terms,
; e.g. the "y" in "3x^2y" -- xvars entries can themselves be
; indexed-variable symbols, not just plain letters, since var? already
; accepts both). Coefficient power (pn/pd) is unrelated to which
; variables appear and is always carried through unchanged.
;
; If the primary variable substitutes away but xvars still has
; unsubstituted entries, the first remaining xvars entry is promoted to
; primary (this engine's own invariant is that a constant term has an
; empty xvars -- see termVarAlist's '() result for constants). If
; everything substitutes, the term becomes a plain constant (var = 1,
; the existing non-variable sentinel). If the primary variable doesn't
; substitute, it stays primary and only xvars shrinks.
(define (substituteTermValues term varValueAlist)
    (let* ((primaryVar (var term))
           (isVar (var? primaryVar))
           (primaryExp (if isVar (/ (varPn term) (varPd term)) 0))
           (primaryResult (if isVar (trySubstituteOne primaryVar primaryExp varValueAlist) (cons #f 1)))
           (primarySubstituted? (car primaryResult))
           (primaryMultiplier (cdr primaryResult))
           (xvarsResults (map (lambda (p) (list p (trySubstituteOne (car p) (cdr p) varValueAlist))) (xvars term)))
           (xvarsMultiplier (apply * (map (lambda (r) (cdr (cadr r))) (filter (lambda (r) (car (cadr r))) xvarsResults))))
           (remainingXvars (map car (filter (lambda (r) (not (car (cadr r)))) xvarsResults)))
           (newCoeff (* (/ (cn term) (cd term)) primaryMultiplier xvarsMultiplier)))
        (cond
            ((and isVar primarySubstituted? (pair? remainingXvars))
                (let ((newPrimary (car remainingXvars)) (restXvars (cdr remainingXvars)))
                    (makepx (numerator newCoeff) (denominator newCoeff) (pn term) (pd term)
                            (car newPrimary) (numerator (cdr newPrimary)) (denominator (cdr newPrimary))
                            '+ restXvars)))
            ((or (not isVar) (and primarySubstituted? (null? remainingXvars)))
                (makep (numerator newCoeff) (denominator newCoeff) (pn term) (pd term) 1 1 1 '+))
            ('t
                (makepx (numerator newCoeff) (denominator newCoeff) (pn term) (pd term)
                        primaryVar (varPn term) (varPd term) '+ remainingXvars)))))

; Substitutes known values into a whole (true-signed) term list, then
; combines like terms -- confirmed safe: combineLikeTerms keys on
; termVarAlist, which is '() for every constant, so two separate
; constant terms produced by substitution merge into one via the same
; bucketing path multiplication/expandPower already rely on.
(define (substituteVariableValues termList varValueAlist)
    (combineLikeTerms (map (lambda (term) (substituteTermValues term varValueAlist)) termList)))

; Splits s on runs of one or more spaces, dropping empty pieces --
; tolerates multiple spaces and leading/trailing whitespace, unlike a
; naive single-space split.
(define (splitOnSpaces s)
    (let loop ((i 0) (start 0) (acc '()))
        (cond
            ((>= i (string-length s))
                (reverse (if (> i start) (cons (substring s start i) acc) acc)))
            ((eqv? (string-ref s i) #\space)
                (loop (+ i 1) (+ i 1) (if (> i start) (cons (substring s start i) acc) acc)))
            ('t (loop (+ i 1) start acc)))))

; Parses "x=3 y=1/2 x_1=5" (space-separated var=val pairs) into an
; alist of (symbol . exact-number). Deliberate departure from the
; documented C++ "@:setval <vars> <vals>" positional syntax (a
; concatenated string of single characters paired positionally with
; space-separated values) -- that format is physically incapable of
; naming a multi-character indexed variable like x_1. var=val pairs are
; unambiguous and trivially support both. A piece with no "=" is
; silently skipped rather than erroring the whole batch. Values may be
; integers, decimals, or fractions (parseFractionOrDecimal, linearSystems.
; scm, already handles a leading "-" itself).
(define (parseSetvalArg argString)
    (let loop ((pairs (splitOnSpaces argString)) (acc '()))
        (if (null? pairs)
            (reverse acc)
            (let* ((piece (car pairs))
                   (eqIdx (findStringCharPos #\= piece 0)))
                (if (not eqIdx)
                    (loop (cdr pairs) acc)
                    (loop (cdr pairs)
                          (cons (cons (string->symbol (substring piece 0 eqIdx))
                                      (parseFractionOrDecimal (substring piece (+ eqIdx 1) (string-length piece))))
                                acc)))))))

; Substitutes one plain expression piece (no "=") and renders it back
; to a string.
(define (substituteOnePiece piece varValueAlist)
    (recordToString (unapplysigns (substituteVariableValues (expandSum (parseExpansion (string->list piece))) varValueAlist))))

; String-level entry point: substitutes every assigned variable's
; value into line. Splits on the first "=" if present (equations) and
; substitutes each side independently, else treats the whole line as
; one expression. Falls back to the ORIGINAL, unmodified line if
; parsing throws -- e.g. the line contains matrix brackets, "!", or
; chemistry notation, anything parseExpansion doesn't understand -- so
; substitution silently declines rather than corrupting or erroring an
; otherwise-valid line. A no-op (returns line unchanged) whenever
; varValueAlist is empty, to avoid parsing overhead for the common
; no-setval-active case.
(define (substituteKnownValues line varValueAlist)
    (if (null? varValueAlist)
        line
        (guard (c (#t line))
            (let ((eqIdx (findStringCharPos #\= line 0)))
                (if eqIdx
                    (string-append (substituteOnePiece (substring line 0 eqIdx) varValueAlist)
                                   "="
                                   (substituteOnePiece (substring line (+ eqIdx 1) (string-length line)) varValueAlist))
                    (substituteOnePiece line varValueAlist))))))

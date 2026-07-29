; linearSystems.scm -- solves systems of linear equations, ported in
; spirit (not line-by-line) from the C++ engine's solveSystem/
; solveSystemMulti. Requires helperS.scm, mathHelp.scm, basicmath.scm,
; chemistry.scm (for the generic rref/matrix helpers -- getEntry,
; numRows, numCols, range, rowSwap, rowScale, rowSub, splitOnChar), and
; equationVariants.scm (for stripSpaces, findStringCharPos,
; parseNumeralToRational) to be loaded first.
;
; Ported from ../linearSystems.scm (MIT Scheme) to Chez Scheme. Changes:
;   - The one `sort` call gets its arguments swapped: Chez's sort is
;     (pred list), the reverse of MIT's (list pred).
;   - Both `(error "msg" ...)` call sites get an explicit #f who-arg.
;
; Unlike C++'s solveSystem/solveSystemMulti split (2-variable Cramer's
; rule vs. a separate 2-4-variable path, both hand-rolling numerator/
; denominator fraction arithmetic), this is a single function that
; builds the augmented coefficient matrix and reduces it with chemistry
; .scm's exact-rational rref -- which naturally handles any number of
; equations/variables, not just 2-4. Solution values are exact rationals
; printed directly via number->string (e.g. 7/2), no manual fraction
; bookkeeping needed.
;
; Nonlinear equations (a variable's exponent, or a product of two
; variables in one term) are rejected with a clear error rather than
; silently mishandled -- matching factorPoly.scm's
; assertSingleVariable/assertIntegerCoefficients pattern. C++'s
; solveSystemPoly (substitution-based nonlinear system solving) has no
; Scheme equivalent yet; this file only covers the linear case.
;
; Input format: equations separated by ';', e.g. "x+y=5;x-y=1". Each
; equation's left side is a sum of signed coefficient*variable terms
; (coefficient optional, defaulting to 1/-1); its right side is a single
; constant (integer, decimal, or "num/den" fraction). The set of
; variables is inferred from every letter appearing anywhere in the
; input; there must be exactly as many distinct variables as equations.

; Index of the ")" matching the "(" at idx in s, or #f if unmatched.
; Same depth-counting idiom as this codebase's other paren matchers
; (e.g. radicalRationalSolve.scm's findMatchingParen), duplicated here
; per this codebase's own convention of not centralizing small
; scanning helpers.
(define (varTokenMatchingParen s idx)
    (let loop ((i (+ idx 1)) (depth 1))
        (cond
            ((>= i (string-length s)) #f)
            ((eqv? (string-ref s i) #\() (loop (+ i 1) (+ depth 1)))
            ((eqv? (string-ref s i) #\))
                (if (= depth 1) i (loop (+ i 1) (- depth 1))))
            ('t (loop (+ i 1) depth)))))

; Index just past the variable token starting at idx in s (s[idx] must
; be alphabetic) -- either idx+1 for a bare single-letter variable, or
; past a "_"+digit-run, "_"+single-letter, or "_(...)" (paren-balanced)
; subscript suffix. Mirrors PolyStoSymbol.scm's groupIndexedVars
; recognition shape.
(define (varTokenEnd s idx)
    (let ((afterLetter (+ idx 1)))
        (if (and (< afterLetter (string-length s)) (eqv? (string-ref s afterLetter) #\_)
                 (< (+ afterLetter 1) (string-length s)))
            (let ((afterUS (+ afterLetter 1)))
                (cond
                    ((char-numeric? (string-ref s afterUS))
                        (let loop ((j (+ afterUS 1)))
                            (if (and (< j (string-length s)) (char-numeric? (string-ref s j)))
                                (loop (+ j 1)) j)))
                    ((and (char-alphabetic? (string-ref s afterUS))
                          (or (= (+ afterUS 1) (string-length s))
                              (not (or (char-alphabetic? (string-ref s (+ afterUS 1)))
                                       (char-numeric? (string-ref s (+ afterUS 1)))))))
                        (+ afterUS 1))
                    ((eqv? (string-ref s afterUS) #\()
                        (let ((close (varTokenMatchingParen s afterUS)))
                            (if close (+ close 1) afterLetter)))
                    ('t afterLetter)))
            afterLetter)))

; Every distinct variable TOKEN in s (single letters or indexed
; variables like x_1/n_x/x_(x+1)), in first-appearance order.
(define (uniqueVarTokens s)
    (let loop ((i 0) (acc '()))
        (cond
            ((>= i (string-length s)) (reverse acc))
            ((char-alphabetic? (string-ref s i))
                (let* ((end (varTokenEnd s i)) (tok (substring s i end)))
                    (loop end (if (member tok acc) acc (cons tok acc)))))
            ('t (loop (+ i 1) acc)))))

; Index of the first alphabetic character in s at or after idx, or #f.
(define (findFirstAlphaPos s idx)
    (cond
        ((>= idx (string-length s)) #f)
        ((char-alphabetic? (string-ref s idx)) idx)
        ('t (findFirstAlphaPos s (+ idx 1)))))

; Splits a signed sum like "2x+3y-5" into ("2x" "+3y" "-5") -- every
; term after the first keeps the operator that introduced it; the first
; term keeps its sign only if negative.
(define (splitSignedTerms s)
    (let loop ((i 1) (start 0) (acc '()))
        (cond
            ((>= i (string-length s)) (reverse (cons (substring s start (string-length s)) acc)))
            ((or (eqv? (string-ref s i) #\+) (eqv? (string-ref s i) #\-))
                (loop (+ i 1) i (cons (substring s start i) acc)))
            ('t (loop (+ i 1) start acc)))))

; Parses "3/4" or "3.5" or "3" into an exact rational.
(define (parseFractionOrDecimal s)
    (let ((slashIdx (findStringCharPos #\/ s 0)))
        (if slashIdx
            (/ (parseNumeralToRational (substring s 0 slashIdx))
               (parseNumeralToRational (substring s (+ slashIdx 1) (string-length s))))
            (parseNumeralToRational s))))

; Raises a clear error if body (a term with its sign already stripped)
; isn't a valid linear term -- either a bare exponent (e.g. "x^2") or a
; product of two variables (e.g. "xy") makes the whole system nonlinear,
; which this file doesn't attempt to solve.
(define (assertLinearTerm body)
    (if (findStringCharPos #\^ body 0)
        (error #f "solveSystem: nonlinear term (contains an exponent) is not supported" body))
    (let ((firstAlpha (findFirstAlphaPos body 0)))
        (if firstAlpha
            (if (findFirstAlphaPos body (varTokenEnd body firstAlpha))
                (error #f "solveSystem: nonlinear term (product of variables) is not supported" body)))))

; Parses one signed term (e.g. "+3y", "-x", "x/2", "3/4z", "x_1/2") into
; (cons variableToken exactCoefficient). Supports a leading coefficient
; ("3y", "3/4y") and a trailing divisor on the variable itself ("y/2",
; meaning coefficient 1/2). variableToken is a string, not a character,
; since it may be an indexed variable (x_1, n_x, x_(x+1)).
(define (parseLinearTerm rawTerm)
    (let* ((negative (and (> (string-length rawTerm) 0) (eqv? (string-ref rawTerm 0) #\-)))
           (body (if (and (> (string-length rawTerm) 0)
                          (or (eqv? (string-ref rawTerm 0) #\+) (eqv? (string-ref rawTerm 0) #\-)))
                     (substring rawTerm 1 (string-length rawTerm))
                     rawTerm)))
        (assertLinearTerm body)
        (let* ((varIdx (findFirstAlphaPos body 0))
               (varEnd (varTokenEnd body varIdx))
               (variable (substring body varIdx varEnd))
               (before (substring body 0 varIdx))
               (after (substring body varEnd (string-length body)))
               (magnitude
                   (cond
                       ((> (string-length after) 0)
                           (/ 1 (parseNumeralToRational (substring after 1 (string-length after)))))
                       ((= (string-length before) 0) 1)
                       ('t (parseFractionOrDecimal before)))))
            (cons variable (if negative (- magnitude) magnitude)))))

; Parses one equation string (spaces already stripped) into
; (cons coefficientRow constant), coefficientRow in the given variable
; order (0 for any variable this equation doesn't mention). variables
; is a list of variable-token strings (see uniqueVarTokens); lookup
; uses assoc/equal? rather than assv/eqv? since a token may be a
; multi-character string.
(define (parseLinearEquation eq variables)
    (let* ((eqIdx (findStringCharPos #\= eq 0))
           (left (substring eq 0 eqIdx))
           (right (substring eq (+ eqIdx 1) (string-length eq)))
           (parsedTerms (map parseLinearTerm (splitSignedTerms left)))
           (row (map (lambda (v) (let ((p (assoc v parsedTerms))) (if p (cdr p) 0))) variables))
           (constant (parseFractionOrDecimal right)))
        (cons row constant)))

(define (buildAugmentedMatrix eqStrings variables)
    (map (lambda (eq)
             (let* ((parsed (parseLinearEquation (stripSpaces eq) variables))
                    (row (car parsed)) (const (cdr parsed)))
                 (append row (list const))))
         eqStrings))

; #t if every one of the first n entries of row r in mat is zero -- a
; row like this represents "0 = k" once RREF'd, useful for detecting
; both inconsistency (k != 0) and dependency (k = 0, one fewer pivot
; than variables).
(define (rowIsZeroCoeffs mat r n)
    (let loop ((c 0))
        (cond
            ((>= c n) #t)
            ((not (= 0 (getEntry mat r c))) #f)
            ('t (loop (+ c 1))))))

; Classifies an RREF'd n-variable augmented system and, if uniquely
; solvable, returns (cons 'unique (list x1 x2 ... xn)) in variable
; order. A full-rank n x n coefficient block RREFs to the identity
; matrix with pivotCols exactly (0 1 ... n-1) in order (rref scans
; columns strictly left to right, so its pivotCols are always
; increasing) -- in that case row i's augmented-column entry directly
; is x_i. Otherwise checks every row for the "0 = nonzero" pattern to
; tell an inconsistent system from a dependent (infinite-solutions) one.
(define (classifyAndSolve rrefMat pivotCols n)
    (if (equal? pivotCols (range n))
        (cons 'unique (map (lambda (r) (getEntry rrefMat r n)) (range n)))
        (if (let loop ((r 0))
                (cond
                    ((>= r n) #f)
                    ((and (rowIsZeroCoeffs rrefMat r n) (not (= 0 (getEntry rrefMat r n)))) #t)
                    ('t (loop (+ r 1)))))
            (cons 'inconsistent #f)
            (cons 'dependent #f))))

; Solves a system of linear equations, e.g. (string->list "x+y=5;x-y=1")
; -> (list "x = 3" "y = 2"). See file header for input format and scope.
(define (solveSystem systemChars)
    (let* ((s (stripSpaces (list->string systemChars)))
           (eqStrings (splitOnChar s #\;))
           (variables (sort string<? (uniqueVarTokens s)))
           (n (length eqStrings)))
        (cond
            ((< n 2) (list "Error: System must have at least two equations"))
            ((not (= (length variables) n))
                (list (string-append "Error: Number of variables (" (number->string (length variables))
                                      ") doesn't match number of equations (" (number->string n) ")")))
            ('t
                (let* ((matrix (buildAugmentedMatrix eqStrings variables))
                       (rrefResult (rref matrix))
                       (rrefMat (car rrefResult)) (pivotCols (cdr rrefResult))
                       (result (classifyAndSolve rrefMat pivotCols n)))
                    (cond
                        ((eq? (car result) 'inconsistent) (list "No solution (inconsistent system)"))
                        ((eq? (car result) 'dependent) (list "Infinite solutions (dependent equations)"))
                        ('t (map (lambda (v val) (string-append v " = " (number->string val)))
                                 variables (cdr result)))))))))

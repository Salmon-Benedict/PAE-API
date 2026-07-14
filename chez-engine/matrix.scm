; matrix.scm -- matrix arithmetic (add, subtract, scalar multiply,
; multiply, transpose, determinant, inverse, rref), bracket-notation
; ("[[1,2],[3,4]]") parsing/formatting, and CSV interop. Requires
; helperS.scm, mathHelp.scm, basicmath.scm, chemistry.scm (row-op
; primitives + rref), equationVariants.scm + linearSystems.scm
; (parseFractionOrDecimal, stripSpaces), and solvePoly.scm (ratToString)
; to be loaded first.
;
; Ported from ../matrix.scm (MIT Scheme) to Chez Scheme. Differences,
; matching every other ported file in this directory:
;   - Both `(error "msg" ...)` call sites in findMatchingBracket/
;     parseMatrixRow/validateRectangular/parseMatrixBracket get an
;     explicit #f who-arg.
;   - validateRectangular's `every` (MIT) is unbound in Chez; replaced
;     with `for-all`, the R6RS/Chez name for the same operation (see
;     chez/chemistry.scm's oxStatesBalance? for the identical swap).
;
; Representation: plain list-of-lists of exact rationals, row-major --
; identical to chemistry.scm's own convention, so its primitives
; (numRows, numCols, getRow, getEntry, setRow, rowSwap, rowScale,
; rowSub, range, splitOnChar, rref) are reused directly rather than
; duplicated. rref itself is never modified here -- linearSystems.scm
; and chemistry.scm's own equation-balancing depend on its exact
; current behavior (every pivot normalized to 1, pivot columns
; returned).
;
; Two error conventions, matching existing precedent elsewhere in this
; codebase (see e.g. linearSystems.scm's assertLinearTerm vs.
; solveSystem's own returned error strings):
;   - Malformed SYNTAX (bad bracket notation, ragged rows) raises via
;     `error`, to be caught by the caller (a test's `safely`, or the
;     Chez dispatcher's per-line guard).
;   - Semantically-invalid but well-formed input (dimension mismatches,
;     non-square/singular matrices) returns an "Error: ..." string
;     directly as a normal value, matching solveSystem's own tone.

; ---- Bracket-notation parsing ----

; idx is the position of an opening '[' in s; returns the position of
; its matching ']' by tracking nesting depth (same structure as
; radicalRationalSolve.scm's findMatchingParen, [ / ] instead of ( / )).
(define (findMatchingBracket s idx)
    (let loop ((i (+ idx 1)) (depth 1))
        (cond
            ((>= i (string-length s)) (error #f "findMatchingBracket: unmatched [" s))
            ((eqv? (string-ref s i) #\[) (loop (+ i 1) (+ depth 1)))
            ((eqv? (string-ref s i) #\])
                (if (= depth 1) i (loop (+ i 1) (- depth 1))))
            ('t (loop (+ i 1) depth)))))

; Splits s at depth-0 commas only, tracking [ / ] nesting -- used both
; for the outer row-split (so the comma between rows, not the commas
; inside them, is the split point) and, trivially since no nesting
; occurs there, each row's own cell-split.
(define (splitTopLevelOnComma s)
    (let loop ((i 0) (start 0) (depth 0) (acc '()))
        (cond
            ((>= i (string-length s)) (reverse (cons (substring s start i) acc)))
            ((eqv? (string-ref s i) #\[) (loop (+ i 1) start (+ depth 1) acc))
            ((eqv? (string-ref s i) #\]) (loop (+ i 1) start (- depth 1) acc))
            ((and (eqv? (string-ref s i) #\,) (= depth 0))
                (loop (+ i 1) (+ i 1) depth (cons (substring s start i) acc)))
            ('t (loop (+ i 1) start depth acc)))))

; Parses one bracketed row, e.g. "[1,2]" -> (1 2), cells via
; parseFractionOrDecimal (linearSystems.scm) so "3/4"/"3.5"/"-2" all work.
(define (parseMatrixRow rowStr)
    (if (or (< (string-length rowStr) 2)
            (not (eqv? (string-ref rowStr 0) #\[))
            (not (eqv? (string-ref rowStr (- (string-length rowStr) 1)) #\])))
        (error #f "parseMatrixRow: expected a bracketed row, e.g. [1,2]" rowStr)
        (let ((inner (substring rowStr 1 (- (string-length rowStr) 1))))
            (if (string=? inner "")
                (error #f "parseMatrixRow: empty row" rowStr)
                (map parseFractionOrDecimal (splitTopLevelOnComma inner))))))

; Errors (rather than silently accepting) a ragged or empty row list --
; every downstream matrix op assumes a genuine rectangular list-of-lists.
(define (validateRectangular rows)
    (let ((lens (map length rows)))
        (if (or (null? lens) (not (for-all (lambda (l) (= l (car lens))) lens)))
            (error #f "Matrix rows have inconsistent lengths" rows)
            rows)))

; Top-level bracket-notation parser, e.g. "[[1,2],[3,4]]" -> ((1 2) (3 4)).
(define (parseMatrixBracket s)
    (let ((stripped (stripSpaces s)))
        (if (or (= (string-length stripped) 0) (not (eqv? (string-ref stripped 0) #\[)))
            (error #f "parseMatrixBracket: expected a matrix starting with [" stripped)
            (let ((closeIdx (findMatchingBracket stripped 0)))
                (if (not (= closeIdx (- (string-length stripped) 1)))
                    (error #f "parseMatrixBracket: unexpected characters after the closing ]" stripped)
                    (validateRectangular
                        (map parseMatrixRow
                             (splitTopLevelOnComma (substring stripped 1 closeIdx)))))))))

; Small local string-joiner -- not shared with dispatcher.scm's own
; join-strings, since this file must load standalone (no dispatcher.scm)
; via load-engine.scm.
(define (joinWith sep strs)
    (cond
        ((null? strs) "")
        ((null? (cdr strs)) (car strs))
        ('t (string-append (car strs) sep (joinWith sep (cdr strs))))))

(define (matrixRowToBracketString row)
    (string-append "[" (joinWith "," (map ratToString row)) "]"))

(define (matrixToBracketString m)
    (string-append "[" (joinWith "," (map matrixRowToBracketString m)) "]"))

; ---- CSV -- dedicated matrix-file grid (real newlines) ----
;
; For importing a matrix a user actually typed into a spreadsheet as a
; normal-looking grid: select just the matrix's cells and export/copy
; that selection as its own small CSV file (standard spreadsheet
; operation), giving a real multi-row, comma-separated numeric block
; with nothing else in it.

(define (parseMatrixCSVRow rowStr) (map parseFractionOrDecimal (splitOnChar rowStr #\,)))

(define (parseMatrixCSV s)
    (let* ((rawRows (splitOnChar s #\newline))
           (rows (filter (lambda (r) (not (string=? r ""))) rawRows)))
        (validateRectangular (map parseMatrixCSVRow rows))))

(define (matrixRowToCSVString row) (joinWith "," (map ratToString row)))
(define (matrixToCSVString m) (joinWith "\n" (map matrixRowToCSVString m)))

(define (csvToBracketString s) (matrixToBracketString (parseMatrixCSV s)))
(define (bracketToCSVString s) (matrixToCSVString (parseMatrixBracket s)))

; ---- CSV -- single-cell embedding ----
;
; For saving/embedding a bracket-notation matrix (e.g. a computed
; result) as one field inside a larger, mixed CSV -- a worksheet row
; that also has other equations/solutions in other columns. Bracket
; notation never contains a literal '"' or a real newline, so only the
; enclosing quotes standard CSV requires for a comma-bearing field are
; ever needed -- no internal escaping.
(define (matrixToCSVField bracketStr) (string-append "\"" bracketStr "\""))

(define (csvFieldToMatrix fieldStr)
    (let* ((len (string-length fieldStr))
           (quoted (and (>= len 2)
                        (eqv? (string-ref fieldStr 0) #\")
                        (eqv? (string-ref fieldStr (- len 1)) #\"))))
        (if quoted (substring fieldStr 1 (- len 1)) fieldStr)))

; ---- Arithmetic ----

(define (dimStr m) (string-append (number->string (numRows m)) "x" (number->string (numCols m))))

(define (matrixAdd a b)
    (if (or (not (= (numRows a) (numRows b))) (not (= (numCols a) (numCols b))))
        (string-append "Error: Matrix dimensions don't match for addition (" (dimStr a) " vs " (dimStr b) ")")
        (map (lambda (ra rb) (map + ra rb)) a b)))

(define (matrixSubtract a b)
    (if (or (not (= (numRows a) (numRows b))) (not (= (numCols a) (numCols b))))
        (string-append "Error: Matrix dimensions don't match for subtraction (" (dimStr a) " vs " (dimStr b) ")")
        (map (lambda (ra rb) (map - ra rb)) a b)))

(define (matrixScalarMultiply k m) (map (lambda (row) (rowScale row k)) m))

(define (matrixMultiply a b)
    (if (not (= (numCols a) (numRows b)))
        (string-append "Error: Matrix dimensions don't match for multiplication (" (dimStr a) " vs " (dimStr b) ")")
        (map (lambda (i)
                 (map (lambda (j)
                          (apply + (map (lambda (k) (* (getEntry a i k) (getEntry b k j))) (range (numCols a)))))
                      (range (numCols b))))
             (range (numRows a)))))

(define (matrixTranspose m)
    (map (lambda (j) (map (lambda (row) (list-ref row j)) m)) (range (numCols m))))

; ---- Determinant ----
;
; Its own elimination pass, NOT chemistry.scm's rref (rref normalizes
; every pivot to 1 and discards exactly the raw pivot values/swap-count
; a determinant needs). Partial-pivoting forward elimination (same
; pivot-selection rule as rref's own), tracking the running
; UNNORMALIZED pivot product and a sign flip per row swap, eliminating
; only below the pivot row (row-echelon, not full reduction -- cheaper
; than rref since determinant doesn't need it). A fully-zero column
; at/below the current pivot row means singular -> returns 0
; immediately. A 0x0 matrix falls out as 1 with no special-casing.
(define (detEliminate m)
    (let ((n (numRows m)))
        (let loop ((mat m) (row 0) (sign 1) (product 1))
            (if (>= row n)
                (* sign product)
                (let ((sel (let findNonzero ((r row))
                               (cond
                                   ((>= r n) #f)
                                   ((not (= 0 (getEntry mat r row))) r)
                                   ('t (findNonzero (+ r 1)))))))
                    (if (not sel)
                        0
                        (let* ((mat (if (= sel row) mat (rowSwap mat row sel)))
                               (sign (if (= sel row) sign (- sign)))
                               (pivotVal (getEntry mat row row))
                               (mat (let elimLoop ((r (+ row 1)) (mat mat))
                                        (if (>= r n)
                                            mat
                                            (let ((factor (getEntry mat r row)))
                                                (if (= factor 0)
                                                    (elimLoop (+ r 1) mat)
                                                    (elimLoop (+ r 1)
                                                        (setRow mat r (rowSub (getRow mat r) (rowScale (getRow mat row) (/ factor pivotVal)))))))))))
                            (loop mat (+ row 1) sign (* product pivotVal)))))))))

(define (matrixDeterminant m)
    (if (not (= (numRows m) (numCols m)))
        (string-append "Error: Determinant requires a square matrix (got " (dimStr m) ")")
        (detEliminate m)))

; ---- Inverse and rref ----
;
; Both reuse chemistry.scm's rref directly, unmodified.

(define (identityMatrix n)
    (map (lambda (i) (map (lambda (j) (if (= i j) 1 0)) (range n))) (range n)))

(define (matrixInverse m)
    (if (not (= (numRows m) (numCols m)))
        (string-append "Error: Inverse requires a square matrix (got " (dimStr m) ")")
        (let* ((n (numRows m))
               (augmented (map (lambda (row idRow) (append row idRow)) m (identityMatrix n)))
               (rrefResult (rref augmented))
               (rrefMat (car rrefResult)) (pivotCols (cdr rrefResult)))
            (if (not (equal? pivotCols (range n)))
                "Error: Matrix is singular, no inverse exists"
                (map (lambda (row) (list-tail row n)) rrefMat)))))

(define (matrixRref m) (car (rref m)))

; ---- Implicit recognition ----
;
; Matrix operations are recognized directly from bracket notation in
; the input text, rather than needing an explicit mode switch -- the
; same design as factorial.scm's substituteFactorials, which resolves
; every bare "N!" before any command ever sees the line, so "!" works
; transparently no matter which command is active. substituteMatrixExpressions
; does the same thing for "[...]": it scans a line, reduces every
; recognized matrix (sub)expression to its result's text in place, and
; hands back a plain string -- the caller (dispatcher.scm) doesn't need
; to know anything about matrix syntax at all.
;
; Three recognized shapes, tried in this order at each scan position:
;   1. Unary function-call syntax -- det(...)/transpose(...)/inverse(...)/
;      rref(...) -- mirrors this engine's existing sqrt(.../log(...
;      convention (functionAnalysis.scm, radicalRationalSolve.scm): its
;      own literal-prefix scan, then findMatchingBracket for the argument.
;   2. Binary arithmetic -- matrixA+matrixB, matrixA-matrixB, matrixA*matrixB,
;      k*matrix, matrix*k -- the operator character itself (+/-/*) selects
;      add/subtract/multiply/scalarmultiply directly, no separate mode
;      needed, since that's exactly how ordinary arithmetic already reads.
;   3. A bare bracket-matrix with nothing recognized around it --
;      reformatted/validated in place (parse then re-format), the same
;      "no-op but canonicalized" treatment a bare numeral gets under expand.
;
; One necessary departure from factorial's model: factorial's result is
; always a plain number, automatically compatible with whatever grammar
; the active command expects. A matrix-shaped result generally isn't (no
; other command understands bracket notation), and neither is one of
; this file's own "Error: ..." strings (dimension mismatch, non-square,
; singular). So: matrixDeterminant's numeric result is spliced in and
; scanning continues normally (exactly like "3!" -> "6" composing into
; "6+2"), but the moment ANY error string is produced, scanning stops
; immediately and that error string alone is returned -- there's no
; sensible way to keep splicing text around an error. isMatrixResultLine?
; (below) is how the caller tells "this line IS the final answer, don't
; hand it to any command" from "this is still ordinary composable text".

; #t if s starts with prefix at position i (bounds-checked).
(define (stringPrefixAt? s i prefix)
    (let ((plen (string-length prefix)))
        (and (<= (+ i plen) (string-length s))
             (string=? (substring s i (+ i plen)) prefix))))

; (name . function) pairs, checked in order -- longer/more-specific
; names aren't a concern here since none of these four share a prefix.
(define matrixUnaryOps
    (list (cons "det(" matrixDeterminant)
          (cons "transpose(" matrixTranspose)
          (cons "inverse(" matrixInverse)
          (cons "rref(" matrixRref)))

; Returns (cons function afterPrefixIndex) for the first unary-op name
; matching at position i, or #f if none do.
(define (matchUnaryOpAt s i)
    (let loop ((ops matrixUnaryOps))
        (cond
            ((null? ops) #f)
            ((stringPrefixAt? s i (caar ops)) (cons (cdar ops) (+ i (string-length (caar ops)))))
            ('t (loop (cdr ops))))))

; A result is either a matrix (list of lists), a plain number (det), or
; an "Error: ..." string (dimension mismatch/non-square/singular) --
; formats each back to wire-text the same way, matching the exact
; 3-way check the old @:matrix dispatcher command used to do.
(define (formatMatrixOpResult result)
    (cond
        ((string? result) result)
        ((number? result) (ratToString result))
        ('t (matrixToBracketString result))))

; Scans the end of a numeral (scalar operand) starting at i -- integer,
; decimal, or a "p/q" fraction, optionally negative, mirroring
; parseFractionOrDecimal's own supported shapes (linearSystems.scm).
; Returns i unchanged if s doesn't start with a numeral there at all.
(define (scanScalarNumeralEnd s i)
    (let* ((len (string-length s))
           (start (if (and (< i len) (eqv? (string-ref s i) #\-)) (+ i 1) i)))
        (if (or (>= start len) (not (char-numeric? (string-ref s start))))
            i
            (let* ((scanDigits (lambda (j)
                                    (let loop ((j j))
                                        (cond
                                            ((>= j len) j)
                                            ((char-numeric? (string-ref s j)) (loop (+ j 1)))
                                            ('t j)))))
                   (afterInt (scanDigits start))
                   (afterDecimal (if (and (< afterInt len) (eqv? (string-ref s afterInt) #\.))
                                      (scanDigits (+ afterInt 1))
                                      afterInt))
                   (afterFrac (if (and (< afterDecimal len) (eqv? (string-ref s afterDecimal) #\/)
                                        (< (+ afterDecimal 1) len) (char-numeric? (string-ref s (+ afterDecimal 1))))
                                   (scanDigits (+ afterDecimal 1))
                                   afterDecimal)))
                afterFrac))))

(define (scalarNumeralStartsAt? s i) (> (scanScalarNumeralEnd s i) i))

; Tries det(/transpose(/inverse(/rref( at position i. #f if the prefix
; doesn't match, isn't immediately followed by a bracket matrix, or
; that matrix isn't immediately followed by the closing ")".
(define (tryUnaryOpAt s i)
    (let ((match (matchUnaryOpAt s i)))
        (if (not match)
            #f
            (let* ((opFunc (car match)) (matStart (cdr match)))
                (if (or (>= matStart (string-length s)) (not (eqv? (string-ref s matStart) #\[)))
                    #f
                    (let ((closeB (findMatchingBracket s matStart)))
                        (if (or (>= (+ closeB 1) (string-length s)) (not (eqv? (string-ref s (+ closeB 1)) #\))))
                            #f
                            (let* ((m (parseMatrixBracket (substring s matStart (+ closeB 1))))
                                   (result (opFunc m)))
                                (list (formatMatrixOpResult result) (+ closeB 2) (string? result))))))))))

; matrixA OP matrixB, or matrixA * number -- s[i] is already known to be "[".
(define (tryMatrixFirstBinaryAt s i)
    (let* ((closeB (findMatchingBracket s i))
           (afterFirst (+ closeB 1)))
        (if (>= afterFirst (string-length s))
            #f
            (let ((opChar (string-ref s afterFirst)) (secondStart (+ afterFirst 1)))
                (cond
                    ((not (memv opChar '(#\+ #\- #\*))) #f)
                    ((and (< secondStart (string-length s)) (eqv? (string-ref s secondStart) #\[))
                        (let* ((closeB2 (findMatchingBracket s secondStart))
                               (a (parseMatrixBracket (substring s i (+ closeB 1))))
                               (b (parseMatrixBracket (substring s secondStart (+ closeB2 1))))
                               (result (cond
                                           ((eqv? opChar #\+) (matrixAdd a b))
                                           ((eqv? opChar #\-) (matrixSubtract a b))
                                           ('t (matrixMultiply a b)))))
                            (list (formatMatrixOpResult result) (+ closeB2 1) (string? result))))
                    ((and (eqv? opChar #\*) (scalarNumeralStartsAt? s secondStart))
                        (let* ((numEnd (scanScalarNumeralEnd s secondStart))
                               (a (parseMatrixBracket (substring s i (+ closeB 1))))
                               (k (parseFractionOrDecimal (substring s secondStart numEnd)))
                               (result (matrixScalarMultiply k a)))
                            (list (formatMatrixOpResult result) numEnd #f)))
                    ('t #f))))))

; number * matrixB -- s[i] is already known to start a scalar numeral.
(define (tryScalarFirstBinaryAt s i)
    (let ((numEnd (scanScalarNumeralEnd s i)))
        (if (or (>= numEnd (string-length s)) (not (eqv? (string-ref s numEnd) #\*)))
            #f
            (let ((matStart (+ numEnd 1)))
                (if (or (>= matStart (string-length s)) (not (eqv? (string-ref s matStart) #\[)))
                    #f
                    (let* ((closeB (findMatchingBracket s matStart))
                           (k (parseFractionOrDecimal (substring s i numEnd)))
                           (m (parseMatrixBracket (substring s matStart (+ closeB 1))))
                           (result (matrixScalarMultiply k m)))
                        (list (formatMatrixOpResult result) (+ closeB 1) #f)))))))

(define (tryBinaryOpAt s i)
    (cond
        ((and (< i (string-length s)) (eqv? (string-ref s i) #\[)) (tryMatrixFirstBinaryAt s i))
        ((scalarNumeralStartsAt? s i) (tryScalarFirstBinaryAt s i))
        ('t #f)))

; A bare "[...]" with nothing recognized around it -- reformatted (not
; just passed through) so e.g. stray internal spaces/decimal cells still
; come out canonical, the same "no-op but validated" treatment a bare
; numeral gets under expand.
(define (tryBareMatrixAt s i)
    (if (or (>= i (string-length s)) (not (eqv? (string-ref s i) #\[)))
        #f
        (let* ((closeB (findMatchingBracket s i))
               (m (parseMatrixBracket (substring s i (+ closeB 1)))))
            (list (matrixToBracketString m) (+ closeB 1) #f))))

(define (tryMatrixMatchAt s i)
    (or (tryUnaryOpAt s i) (tryBinaryOpAt s i) (tryBareMatrixAt s i)))

; Top-level entry point: scans s left to right, splicing every
; recognized matrix (sub)expression's result-text in place of its
; source text. Stops immediately and returns just that text the moment
; an "Error: ..." result is produced -- see the file-header comment on
; why splicing can't sensibly continue past an error.
(define (substituteMatrixExpressions s)
    (let loop ((i 0) (acc ""))
        (if (>= i (string-length s))
            acc
            (let ((m (tryMatrixMatchAt s i)))
                (if (not m)
                    (loop (+ i 1) (string-append acc (string (string-ref s i))))
                    (let ((resultText (car m)) (nextIdx (cadr m)) (isError (caddr m)))
                        (if isError
                            resultText
                            (loop nextIdx (string-append acc resultText)))))))))

; #t if a substituteMatrixExpressions result IS the final answer for its
; whole line (a matrix literal, or one of this file's own "Error: ..."
; strings) rather than ordinary text a command should still process --
; e.g. distinguishes the "[[6,8],[10,12]]" left over from
; "[[1,2],[3,4]]+[[5,6],[7,8]]" (return directly -- no command
; understands bracket notation) from the "-2+5" left over from
; "det([[1,2],[3,4]])+5" (a plain number embedded in more text, which
; should still reach whatever command is active, exactly like factorial).
(define (isMatrixResultLine? s)
    (or (and (> (string-length s) 0)
             (eqv? (string-ref s 0) #\[)
             (eqv? (string-ref s (- (string-length s) 1)) #\]))
        (and (>= (string-length s) 7) (string=? (substring s 0 7) "Error: "))))

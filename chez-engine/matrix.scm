; matrix.scm -- matrix arithmetic (add, subtract, scalar multiply,
; multiply, transpose, determinant, inverse, rref), bracket-notation
; ("[[1,2],[3,4]]") parsing/formatting, and CSV interop. Requires
; helperS.scm, mathHelp.scm, basicmath.scm, chemistry.scm (row-op
; primitives), equationVariants.scm + linearSystems.scm (stripSpaces),
; solvePoly.scm (ratToString), and expandParse.scm (parseExpansion,
; expandCellFrac, fracAddScalar/fracMultiplyScalar/fracNegateScalar/
; fracReciprocalScalar, renderFracCell, identityFracRows, dropZeros) to
; be loaded first.
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
; Cell representation: each entry is a scalar fraction-pair cell
; (numerTermList . denomTermList) -- the exact same shape expandParse.scm
; already produces for an ordinary scalar expression, reused directly
; rather than a second cell type -- so a matrix cell can be "x+1",
; "1/(x-2)", or a plain rational, all through the same machinery. This
; replaces the ORIGINAL plain-rational-number cell representation (see
; math-edu-scheme/matrices.md for the full rationale: reusing
; expandParse.scm's existing fraction arithmetic, which already handles
; "divide by a variable" for ordinary scalars, is what makes symbolic
; matrix cells and symbolic determinant/inverse/rref tractable here
; without inventing a second engine).
;
; Structural helpers (numRows, numCols, getRow, getEntry, setRow,
; rowSwap, splitOnChar, range) are still reused from chemistry.scm --
; those never do arithmetic themselves, just list manipulation, so they
; work identically regardless of cell type. chemistry.scm's own
; rowScale/rowSub and rref, however, do raw +/-/*// on cells and are
; NOT reused here anymore for anything symbolic-capable: fracRowScale/
; fracRowSub/fracRref below are this file's own cell-type-aware
; replacements, used by matrixDeterminant/matrixInverse/matrixRref.
; chemistry.scm's own rref is untouched and still used exactly as
; before by linearSystems.scm and chemistry.scm's own equation-
; balancing, neither of which this change affects.
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
;
; Determinant/inverse/rref on a matrix with variable entries: a pivot
; (or, for determinant, nothing -- cofactor expansion needs no pivot at
; all) cell is treated as "zero" only if it's the LITERAL zero term-list
; (i.e. zero for every value of its variables) -- a cell like "x-2"
; (zero only at one specific point) is treated as usable/nonzero. This
; is the standard "generic point" convention first-course linear-
; algebra-with-parameters problems use; deciding whether a symbolic
; cell is zero in general is undecidable, so this is a deliberate,
; documented simplification, not an oversight.

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

; #t if cellStr is a bare numeral (digits, an optional leading '-', an
; optional '.', an optional '/') with no variable letters at all --
; expandParse.scm's general grammar has no notion of a decimal point (it
; only understands integers and explicit int/int division), so a plain
; decimal cell like "4.5" needs linearSystems.scm's parseFractionOrDecimal
; specifically; anything else (variables, nested expressions) goes
; through the general grammar instead.
(define (pureNumeralCell? cellStr)
    (let loop ((i 0))
        (cond
            ((>= i (string-length cellStr)) #t)
            ((memv (string-ref cellStr i) '(#\- #\. #\/ #\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)) (loop (+ i 1)))
            ('t #f))))

; Parses one cell string ("3/4", "3.5", "-2", but now also "x+1",
; "1/(x-2)", ...) into a scalar fraction-pair cell. Pure numerals route
; through parseFractionOrDecimal (preserving decimal-point support
; exactly as before); everything else goes through expandParse.scm's own
; parseExpansion/expandCellFrac -- the exact same pipeline expand()
; itself uses for a matrix literal's cells, invoked directly on a
; standalone cell string here since bracket-notation parsing is entirely
; string-driven in this file, not token-list-driven.
(define (cellFracFromString cellStr)
    (if (pureNumeralCell? cellStr)
        (numberToFracCell (parseFractionOrDecimal cellStr))
        (expandCellFrac (parseExpansion (string->list cellStr)))))

; Parses one bracketed row, e.g. "[1,2]" -> a list of fraction-pair cells.
(define (parseMatrixRow rowStr)
    (if (or (< (string-length rowStr) 2)
            (not (eqv? (string-ref rowStr 0) #\[))
            (not (eqv? (string-ref rowStr (- (string-length rowStr) 1)) #\])))
        (error #f "parseMatrixRow: expected a bracketed row, e.g. [1,2]" rowStr)
        (let ((inner (substring rowStr 1 (- (string-length rowStr) 1))))
            (if (string=? inner "")
                (error #f "parseMatrixRow: empty row" rowStr)
                (map cellFracFromString (splitTopLevelOnComma inner))))))

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
    (string-append "[" (joinWith "," (map renderFracCell row)) "]"))

(define (matrixToBracketString m)
    (string-append "[" (joinWith "," (map matrixRowToBracketString m)) "]"))

; ---- CSV -- dedicated matrix-file grid (real newlines) ----
;
; For importing a matrix a user actually typed into a spreadsheet as a
; normal-looking grid: select just the matrix's cells and export/copy
; that selection as its own small CSV file (standard spreadsheet
; operation), giving a real multi-row, comma-separated numeric block
; with nothing else in it.

(define (parseMatrixCSVRow rowStr) (map cellFracFromString (splitOnChar rowStr #\,)))

(define (parseMatrixCSV s)
    (let* ((rawRows (splitOnChar s #\newline))
           (rows (filter (lambda (r) (not (string=? r ""))) rawRows)))
        (validateRectangular (map parseMatrixCSVRow rows))))

(define (matrixRowToCSVString row) (joinWith "," (map renderFracCell row)))
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
        (map (lambda (ra rb) (map fracAddScalar ra rb)) a b)))

(define (matrixSubtract a b)
    (if (or (not (= (numRows a) (numRows b))) (not (= (numCols a) (numCols b))))
        (string-append "Error: Matrix dimensions don't match for subtraction (" (dimStr a) " vs " (dimStr b) ")")
        (map (lambda (ra rb) (map (lambda (ca cb) (fracAddScalar ca (fracNegateScalar cb))) ra rb)) a b)))

; k is a plain rational NUMBER (every existing caller -- the golden
; tests and this file's own implicit-recognition scanner below -- passes
; one directly); converted to a fraction-pair cell once here so the
; actual per-entry work is the same fracMultiplyScalar every other
; operation uses. A general polynomial scalar (e.g. "3x") times a matrix
; is handled by expandParse.scm's own matrix-aware fracMultiply instead
; -- that's the new capability this whole change exists for, and it
; doesn't need this file's help.
(define (numberToFracCell k)
    (cons (list (makep (numerator k) 1 1 1 1 1 1 '+))
          (list (makep (denominator k) 1 1 1 1 1 1 '+))))

(define (matrixScalarMultiply k m)
    (let ((kCell (numberToFracCell k)))
        (map (lambda (row) (map (lambda (cell) (fracMultiplyScalar kCell cell)) row)) m)))

(define (matrixMultiply a b)
    (if (not (= (numCols a) (numRows b)))
        (string-append "Error: Matrix dimensions don't match for multiplication (" (dimStr a) " vs " (dimStr b) ")")
        (map (lambda (i)
                 (map (lambda (j)
                          (let loop ((k 0) (acc (zeroFracCell)))
                              (if (>= k (numCols a))
                                  acc
                                  (loop (+ k 1) (fracAddScalar acc (fracMultiplyScalar (getEntry a i k) (getEntry b k j)))))))
                      (range (numCols b))))
             (range (numRows a)))))

(define (matrixTranspose m)
    (map (lambda (j) (map (lambda (row) (list-ref row j)) m)) (range (numCols m))))

; ---- Determinant ----
;
; Cofactor (Laplace) expansion along row 0, built entirely from
; fracMultiplyScalar/fracAddScalar/fracNegateScalar -- needs no division
; at all, so it generalizes to symbolic entries for free and never hits
; a "is this pivot nonzero" question (unlike the ORIGINAL raw-number
; partial-pivoting elimination this replaces, which relied on dividing
; by a chosen pivot -- not meaningful in general for a symbolic pivot).
; More expensive than elimination for large matrices, but this engine's
; matrices are worksheet-sized, not performance-critical. A 0x0 matrix's
; determinant is 1 by the standard (empty-product) convention.
(define (dropIndex lst i)
    (let loop ((lst lst) (idx 0) (acc '()))
        (cond
            ((null? lst) (reverse acc))
            ((= idx i) (loop (cdr lst) (+ idx 1) acc))
            ('t (loop (cdr lst) (+ idx 1) (cons (car lst) acc))))))

(define (fracMinorRows rows i j)
    (map (lambda (row) (dropIndex row j)) (dropIndex rows i)))

(define (cofactorDet rows)
    (let ((n (numRows rows)))
        (cond
            ((= n 0) (oneFracCell))
            ((= n 1) (getEntry rows 0 0))
            ('t
                (let loop ((j 0) (acc (zeroFracCell)))
                    (if (>= j n)
                        acc
                        (let* ((cellJ (getEntry rows 0 j))
                               (minorDet (cofactorDet (fracMinorRows rows 0 j)))
                               (term (fracMultiplyScalar cellJ minorDet))
                               (signedTerm (if (even? j) term (fracNegateScalar term))))
                            (loop (+ j 1) (fracAddScalar acc signedTerm)))))))))

; Renders a fraction-pair cell as a plain rational NUMBER if it has no
; variable content at all (matching matrixDeterminant's pre-existing
; numeric-only test contract exactly), otherwise as a rendered string
; (reusing expandParse.scm's renderFracCell) for a genuine symbolic
; result -- e.g. det([[x,1],[2,y]]) = "xy-2".
(define (fracCellIsNumeric? cell)
    (let ((numer (dropZeros (car cell))) (denom (dropZeros (cdr cell))))
        (and (= (length denom) 1) (not (var? (var (car denom))))
             (or (null? numer) (and (= (length numer) 1) (not (var? (var (car numer)))))))))

(define (fracCellToNumber cell)
    (let* ((numer (dropZeros (car cell))) (denom (dropZeros (cdr cell)))
           (folded (foldConstantDenom numer (car denom))))
        (/ (cn (car folded)) (cd (car folded)))))

(define (fracCellToValue cell)
    (if (fracCellIsNumeric? cell) (fracCellToNumber cell) (renderFracCell cell)))

(define (matrixDeterminant m)
    (if (not (= (numRows m) (numCols m)))
        (string-append "Error: Determinant requires a square matrix (got " (dimStr m) ")")
        (fracCellToValue (cofactorDet m))))

; ---- Inverse and rref ----
;
; NEITHER reuses chemistry.scm's shared rref anymore -- that one does
; raw +/-/*// on cells (needed unchanged by linearSystems.scm and
; chemistry.scm's own equation-balancing, neither touched here). This
; file's own fracRref below is cell-type-aware: identical row-reduction
; structure, but pivot-normalize/row-eliminate go through
; fracReciprocalScalar/fracMultiplyScalar/fracNegateScalar/fracAddScalar,
; and the pivot/zero test is fracCellIsZero? (the "generic point"
; convention documented in this file's header) instead of (= 0 ...).

(define (fracCellIsZero? cell) (null? (dropZeros (car cell))))
(define (fracRowScale row k) (map (lambda (cell) (fracMultiplyScalar cell k)) row))
(define (fracRowSub row1 row2) (map (lambda (c1 c2) (fracAddScalar c1 (fracNegateScalar c2))) row1 row2))

; Row-reduces a fraction-cell matrix to reduced row-echelon form.
; Returns (cons rrefRows pivotCols), mirroring chemistry.scm's own rref
; return shape.
(define (fracRref rows)
    (let ((n (numRows rows)) (totalCols (matNumCols rows)))
        (let loop ((mat rows) (row 0) (col 0) (pivots '()))
            (cond
                ((or (>= row n) (>= col totalCols)) (cons mat (reverse pivots)))
                ('t
                    (let ((sel (let findNonzero ((r row))
                                   (cond
                                       ((>= r n) #f)
                                       ((not (fracCellIsZero? (getEntry mat r col))) r)
                                       ('t (findNonzero (+ r 1)))))))
                        (if (not sel)
                            (loop mat row (+ col 1) pivots)
                            (let* ((mat (if (= sel row) mat (rowSwap mat row sel)))
                                   (pivotRecip (fracReciprocalScalar (getEntry mat row col)))
                                   (mat (setRow mat row (fracRowScale (getRow mat row) pivotRecip)))
                                   (mat (let elimLoop ((r 0) (mat mat))
                                            (cond
                                                ((>= r n) mat)
                                                ((= r row) (elimLoop (+ r 1) mat))
                                                ('t
                                                    (let ((factor (getEntry mat r col)))
                                                        (if (fracCellIsZero? factor)
                                                            (elimLoop (+ r 1) mat)
                                                            (elimLoop (+ r 1)
                                                                (setRow mat r (fracRowSub (getRow mat r) (fracRowScale (getRow mat row) factor)))))))))))
                                (loop mat (+ row 1) (+ col 1) (cons col pivots))))))))))

(define (matrixInverse m)
    (if (not (= (numRows m) (numCols m)))
        (string-append "Error: Inverse requires a square matrix (got " (dimStr m) ")")
        (let* ((n (numRows m))
               (augmented (map (lambda (row idRow) (append row idRow)) m (identityFracRows n)))
               (rrefResult (fracRref augmented))
               (rrefMat (car rrefResult)) (pivotCols (cdr rrefResult)))
            (if (not (equal? pivotCols (range n)))
                "Error: Matrix is singular, no inverse exists"
                (map (lambda (row) (list-tail row n)) rrefMat)))))

(define (matrixRref m) (car (fracRref m)))

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

; dispatcher.scm -- CLI entry point for the PAE Bird native bridge
; (see /Users/rat/Documents/CS/C++/Poly/PolySwift/PAEBird-Chez/
; CHEZ-ENGINE-SWAP-PLAN.md for full context). Loads the engine (this
; directory's load-engine.scm file list minus cppBridge.scm -- see
; note below) and implements the small subset of the old C++ engine's
; batch protocol that the Swift app actually uses, confirmed
; empirically by reading AppState.swift/WorksheetView.swift directly:
; a batch of lines, optionally headed by one "@:<command>[ <arg>]"
; line setting the command for every subsequent line (default command
; is expand), one output line per input line, joined with newlines.
;
; Usage:
;   petite -q -b petite.boot --script dispatcher.scm process <inputFile> <outputFile>
;   petite -q -b petite.boot --script dispatcher.scm worksheet <type> <difficulty> <count> <baseFilename>
;
; NOTE: cppBridge.scm is deliberately NOT loaded (and not bundled into
; the app) -- its only job was shelling out to the OLD C++ engine this
; whole file exists to replace; nothing in the app's command
; vocabulary needs it once the engine is Chez-native.

(for-each load
    '("helperS.scm" "mathHelp.scm" "recordPoly2.scm" "basicmath.scm"
      "chemistry.scm" "PolyStoSymbol.scm" "simplify.scm" "expandParse.scm"
      "factorPoly.scm" "solvePoly.scm" "calcPoly.scm" "equationVariants.scm"
      "comprehensiveExpansion.scm" "linearSystems.scm" "functionAnalysis.scm"
      "conicSections.scm" "worksheetGenerator.scm" "radicalRationalSolve.scm"
      "mathSymbolClass.scm" "polyBridge.scm" "trigonometry.scm" "factorial.scm"
      "matrix.scm" "nextLineTrigger.scm"))

; ---- string utilities (copied from chain.scm, not loaded wholesale --
; chain.scm implements a different, richer protocol Swift never sends;
; only these small MIT-compat/string-splitting helpers are needed here.
; See chain.scm's own header for why string-trim/string-search-forward
; need shims at all in Chez.) ----

(define (ws-char? c) (or (char=? c #\space) (char=? c #\tab) (char=? c #\newline) (char=? c #\return)))

(define (string-trim-left s)
    (let ((len (string-length s)))
        (let loop ((i 0))
            (if (and (< i len) (ws-char? (string-ref s i)))
                (loop (+ i 1))
                (substring s i len)))))

(define (string-trim-right s)
    (let ((len (string-length s)))
        (let loop ((i len))
            (if (and (> i 0) (ws-char? (string-ref s (- i 1))))
                (loop (- i 1))
                (substring s 0 i)))))

(define (trim s) (string-trim-left (string-trim-right s)))

(define (starts-with? s prefix)
    (and (>= (string-length s) (string-length prefix))
         (string=? (substring s 0 (string-length prefix)) prefix)))

(define (string-search-forward pattern str start)
    (let ((plen (string-length pattern)) (slen (string-length str)))
        (let loop ((i start))
            (cond
                ((> (+ i plen) slen) #f)
                ((string=? (substring str i (+ i plen)) pattern) i)
                ('t (loop (+ i 1)))))))

; Splits s on its first space; returns (before . after-trimmed).
; If no space, returns (s . "").
(define (split-first-space s)
    (let ((i (string-search-forward " " s 0)))
        (if i
            (cons (substring s 0 i)
                  (trim (substring s (+ i 1) (string-length s))))
            (cons s ""))))

(define (join-strings strs sep)
    (cond
        ((null? strs) "")
        ((null? (cdr strs)) (car strs))
        ('t (string-append (car strs) sep (join-strings (cdr strs) sep)))))

; Splits a newline-separated string into a list of line strings
; (unlike split-lines elsewhere in this codebase, this keeps blank
; lines as empty strings rather than dropping them, since the
; protocol's own invariant -- one output line per input line -- means
; the dispatcher can't silently drop or merge lines).
(define (splitOnNewline s)
    (let loop ((chars (string->list s)) (cur '()) (result '()))
        (cond
            ((null? chars) (reverse (cons (list->string (reverse cur)) result)))
            ((char=? (car chars) #\newline)
                (loop (cdr chars) '() (cons (list->string (reverse cur)) result)))
            ('t (loop (cdr chars) (cons (car chars) cur) result)))))

; ---- command dispatch ----

; #t if s (already space-stripped, optional leading "-") is nothing
; but digits and at most one ".". toScientificNotation (equationVariants.scm)
; assumes exactly this shape and does NOT validate it -- fed anything
; else (e.g. "6/2") it doesn't error, it silently produces garbage
; (confirmed empirically: toScientificNotation("6/2") -> "6./2 × 10^2",
; no exception at all), so a guard/try-catch fallback can't detect the
; bad case. This explicit check is what sciCommand uses instead.
(define (bareNumeralString? s)
    (let* ((body (if (and (> (string-length s) 0) (eqv? (string-ref s 0) #\-))
                      (substring s 1 (string-length s))
                      s))
           (len (string-length body)))
        (and (> len 0)
             (let loop ((i 0) (seenDot #f))
                 (cond
                     ((>= i len) #t)
                     ((char-numeric? (string-ref body i)) (loop (+ i 1) seenDot))
                     ((and (eqv? (string-ref body i) #\.) (not seenDot)) (loop (+ i 1) #t))
                     ('t #f))))))

; Converts line to scientific notation. A bare decimal/integer numeral
; (the common case, and the only shape toScientificNotation itself is
; actually built to parse -- see its own golden tests: "12345",
; "123456789", "0.001", "-45.6", "0") is converted directly. Anything
; else is expand()ed first (covers integer-arithmetic expressions like
; "6/2" -> "3"), which only works because THIS engine's expand() itself
; has no decimal-literal support at all (a separate, pre-existing
; scope limit of parseTerm/expandParse.scm, not something introduced
; here) -- so a decimal combined with another operator (e.g. "6.5/2")
; remains genuinely unsupported and reports an error via
; safeApplyCommand's guard, rather than silently mishandling it.
(define (sciCommand line)
    (let ((stripped (stripSpaces line)))
        (if (bareNumeralString? stripped)
            (toScientificNotation (string->list stripped))
            (toScientificNotation (string->list (expand (string->list line)))))))

; Applies command `cmd` (with optional trailing argument `arg`, e.g.
; differentiate's optional variable name) to one input line, returning
; a single output string. List-valued engine results (solve and
; friends) are joined with ", " -- matches chain.scm's own established
; convention for the identical situation (its "solve" case).
; "!" and "[...]" are both resolved BEFORE dispatching to any specific
; command (rather than being commands themselves) so they work
; transparently everywhere -- "3!+2" under @:expand becomes "6+2"
; before expand() ever sees it, "3!=x" under @:solve becomes "6=x"
; before solve() ever sees it, etc. Matrix expressions (matrix.scm's
; substituteMatrixExpressions) work the same way: "[[1,2],[3,4]]+
; [[5,6],[7,8]]" reduces to "[[6,8],[10,12]]" regardless of the active
; command -- and since no command besides a matrix one understands
; bracket notation, isMatrixResultLine? short-circuits straight to that
; result rather than handing it to whatever @: mode happens to be set,
; the one place this doesn't mirror factorial exactly (see matrix.scm's
; own header comment on why a matrix-shaped or "Error: ..." result
; can't keep composing the way a plain number always can).
;
; csv2bracket/bracket2csv are exempted from that implicit recognition
; entirely (checked first, before substituteMatrixExpressions ever
; runs): bracket2csv's own input IS a bare bracket-matrix, which is
; exactly the shape isMatrixResultLine? treats as "already a final
; result" -- without this exemption, that check would swallow
; bracket2csv's input and return the reformatted matrix directly,
; never reaching bracket2csv at all.
(define (applyCommand cmd arg rawLine)
    (let ((afterFactorial (substituteFactorials rawLine)))
        (cond
            ((string=? cmd "csv2bracket") (csvFieldToMatrix afterFactorial))
            ((string=? cmd "bracket2csv") (matrixToCSVField afterFactorial))
            ('t
                (let ((line (substituteMatrixExpressions afterFactorial)))
                    (if (isMatrixResultLine? line)
                        line
                        (let ((charL (string->list line)))
                            (cond
                                ((string=? cmd "expand") (expand charL))
                                ((string=? cmd "factor") (factor charL))
                                ((string=? cmd "solve") (join-strings (solve charL) ", "))
                                ((string=? cmd "solveexp") (join-strings (solveExponential charL) ", "))
                                ((string=? cmd "solvelog") (join-strings (solveLogarithm charL) ", "))
                                ((string=? cmd "radical") (join-strings (solveRadical charL) ", "))
                                ((string=? cmd "rational") (join-strings (solveRational charL) ", "))
                                ((or (string=? cmd "trig") (string=? cmd "trigonometric")) (join-strings (solveTrigEquation charL) ", "))
                                ((or (string=? cmd "conic") (string=? cmd "conics")) (join-strings (analyzeConic charL) ", "))
                                ((string=? cmd "domain") (join-strings (analyzeDomain charL) ", "))
                                ((string=? cmd "range") (join-strings (analyzeRange charL) ", "))
                                ((string=? cmd "compose") (join-strings (composeFunction charL) ", "))
                                ((string=? cmd "inverse") (join-strings (inverseFunction charL) ", "))
                                ((string=? cmd "system") (join-strings (solveSystem charL) ", "))
                                ((string=? cmd "inequality") (solveInequality charL))
                                ((or (string=? cmd "expandc") (string=? cmd "expandC")) (expandComprehensive charL))
                                ((string=? cmd "logtoexp") (logToExp charL))
                                ((string=? cmd "exptolog") (expToLog charL))
                                ((string=? cmd "rotate") (rotateEq charL))
                                ((string=? cmd "flip") (flipEq charL))
                                ((string=? cmd "degtorad") (degToRad charL))
                                ((string=? cmd "radtodeg") (radToDeg charL))
                                ((string=? cmd "sqrt") (simplifySquareRootCmd charL))
                                ; sci -- see sciCommand below for why this isn't a direct
                                ; one-line call to toScientificNotation.
                                ((string=? cmd "sci") (sciCommand line))
                                ; balance/oxstate take a plain string, not a char list --
                                ; the only two commands in this table that do (confirmed
                                ; from chemistry.scm's own function signatures).
                                ((string=? cmd "balance") (balanceEquation line))
                                ((string=? cmd "oxstate") (oxidationStates line))
                                ((string=? cmd "differentiate")
                                    (if (string=? arg "") (differentiateExpr charL) (differentiateExpr charL (string->symbol arg))))
                                ((string=? cmd "integrate")
                                    (if (string=? arg "") (integrateExpr charL) (integrateExpr charL (string->symbol arg))))
                                ((string=? cmd "canon") (canonicalize charL))
                                ('t (string-append "[unknown command: " cmd "]"))))))))))

; Runs applyCommand, catching any engine exception and turning it into
; an "Error: ..." string instead -- see runProcess's own comment for
; why this per-line isolation matters (one malformed line must not
; abort the whole batch). Mirrors framework.scm's `safely` pattern
; (guard IS Chez/R7RS's direct equivalent of MIT's ignore-errors, no
; separate condition-catching step needed), not loaded here since
; framework.scm is test-only infrastructure, not part of the app's
; bundled engine.
;
; Also handles the "next line/cell" trigger (nextLineTrigger.scm): a
; leading or trailing ç on `line` is stripped BEFORE applyCommand ever
; sees it (so it never has to know about this concept at all -- same
; reasoning as factorial/matrix substitution happening ahead of command
; dispatch), and if present, the same ç is re-prepended to the final
; result string. This is the one wire signal every downstream client
; (Mac App, Excel/Sheets via PAE-API, LibreOffice) checks for to decide
; whether to render/place the answer on the next line/cell instead of
; in place -- deliberately not a separate structured field, so it works
; identically for both `process` (batch) and `compute` (single-shot)
; modes without needing two different response formats, and without any
; risk to runProcess's one-line-per-input-line invariant (the marker is
; a single leading character, never an embedded newline).
(define (safeApplyCommand cmd arg line)
    (call-with-values
        (lambda () (stripNextLineTrigger line))
        (lambda (strippedLine triggered?)
            (let ((result (guard (c (#t (string-append "Error: " (with-output-to-string (lambda () (display-condition c))))))
                              (applyCommand cmd arg strippedLine))))
                (if triggered?
                    (string-append (string next-line-trigger-char) result)
                    result)))))

; Reads the whole content of a file as one string.
(define (readWholeFile path)
    (call-with-input-file path
        (lambda (port)
            (let loop ((acc '()))
                (let ((c (read-char port)))
                    (if (eof-object? c)
                        (list->string (reverse acc))
                        (loop (cons c acc))))))))

(define (writeWholeFile path content)
    (call-with-output-file path
        (lambda (port) (display content port))
        'replace))

; Reads inputPath, peels off an optional "@:<command>[ <arg>]" header
; line, applies that command (default "expand") to every remaining
; line, and writes one output line per input line (joined with
; newlines, matching Swift's own `components(separatedBy: "\n")`
; expectation) to outputPath.
(define (runProcess inputPath outputPath)
    (let* ((rawLines (splitOnNewline (readWholeFile inputPath)))
           (firstLine (if (null? rawLines) "" (trim (car rawLines))))
           (hasHeader (starts-with? firstLine "@:"))
           (headerRest (if hasHeader (trim (substring firstLine 2 (string-length firstLine))) ""))
           (headerParts (split-first-space headerRest))
           (cmd (if hasHeader (car headerParts) "expand"))
           (arg (if hasHeader (cdr headerParts) ""))
           (dataLines (if hasHeader (cdr rawLines) rawLines))
           ; Blank/whitespace-only lines (including the trailing empty
           ; "line" that a final newline in the input always produces)
           ; get an empty-string result rather than being run through
           ; the engine, which would crash on empty input for most
           ; commands -- matches the old C++ engine's own handling of
           ; blank rows (skip processing, but still emit one output
           ; line so the line-count invariant holds).
           ;
           ; Every other line goes through safeApplyCommand, which
           ; catches any engine exception (e.g. a malformed/
           ; out-of-grammar input for the selected command) and turns
           ; it into an "Error: ..." string for THAT line only --
           ; without this, one bad line in an otherwise-valid batch
           ; would abort the whole process call via an uncaught
           ; exception, losing every other line's result and leaving
           ; outputPath never written at all. Matches the old C++
           ; engine's own per-problem try/catch (main.cpp) rather than
           ; a per-batch all-or-nothing failure.
           (results (map (lambda (line)
                             (if (string=? (trim line) "") "" (safeApplyCommand cmd arg line)))
                         dataLines)))
        (writeWholeFile outputPath (join-strings results "\n"))))

; Runs generateWorksheet (worksheetGenerator.scm) directly -- it
; already writes <baseFilename>_STUDENT.csv/_TEACHER.csv/_STUDENT.html/
; _TEACHER.html/.tex itself; the caller (PolyProcessor.mm) reads back
; whichever 2 of those 5 files match its requested format.
; Swift's own WorksheetView.swift sends "calculus"/"integration" as the
; literal type strings (confirmed directly from its `types` array),
; which don't match worksheetGenerator.scm's own vocabulary ('diff/
; 'integ) -- translated here rather than in the native bridge, since
; this is easier to test/adjust from the CLI than from Xcode.
(define (mapWorksheetType type)
    (cond
        ((string=? type "calculus") "diff")
        ((string=? type "integration") "integ")
        ('t type)))

(define (runWorksheet type difficulty count baseFilename)
    (generateWorksheet (string->symbol (mapWorksheetType type)) (string->symbol difficulty) count baseFilename)
    (display "ok") (newline))

; File-based matrix<->CSV modes (mirrors runWorksheet's own file-based
; precedent, not the line-oriented process protocol) -- for a dedicated
; matrix-only CSV file a user exported from a spreadsheet selection (see
; matrix.scm's own header comment on parseMatrixCSV for why this needs
; to be a real, whole-file multi-line grid rather than the one-line
; wire format process uses).
(define (runMatrixLoad csvFile outFile)
    (writeWholeFile outFile (csvToBracketString (readWholeFile csvFile))))

(define (runMatrixSave bracketLine csvFile)
    (writeWholeFile csvFile (bracketToCSVString bracketLine)))

; ---- XLSX (real Excel files) via the xlsxtool subprocess ----
;
; Neither MIT nor Chez Scheme has a ZIP/DEFLATE library, so real .xlsx
; reading/writing is done by a small first-party Swift CLI (XLSXKit's
; xlsxtool executable target -- see /Users/rat/Documents/CS/C++/Poly/
; PolySwift/Poly/XLSXKit/) built specifically for this bridge, using
; Apple's own Compression framework for the actual DEFLATE work. Its
; contract is deliberately just "XLSX <-> CSV text" over stdin/stdout,
; so matrix.scm's already-built csvToBracketString/bracketToCSVString
; handle everything past that -- no XLSX-specific logic needed here.
;
; Copied from cppBridge.scm's own shell-quote (that file is not loaded
; here -- see this file's own header -- so this is duplicated, not
; shared, matching this file's existing pattern for small self-
; contained string utilities). This matters because a matrix's bracket
; notation or a file path could in principle contain shell-special
; characters; shell-quote's POSIX single-quote-wrapping (escaping any
; embedded "'" as '\'') makes every argument passed to `process`
; (which runs its string through /bin/sh -c) inert as plain text.
(define (shell-quote s)
    (let loop ((i 0) (acc "'"))
        (if (>= i (string-length s))
            (string-append acc "'")
            (let ((c (string-ref s i)))
                (if (eqv? c #\')
                    (loop (+ i 1) (string-append acc "'\\''"))
                    (loop (+ i 1) (string-append acc (string c))))))))

; $XLSXTOOL env var override, else a known absolute path on this
; machine -- mirrors chez/run-tests.sh's own $CHEZ-or-fallback-path
; pattern for locating the Chez binary itself. Unlike that case, there
; is no useful *relative* fallback here: XLSXKit lives in a completely
; separate project tree (PAE Bird's Xcode project), not a sibling
; directory of this repo.
(define (resolve-xlsxtool-path)
    (or (getenv "XLSXTOOL")
        "/Users/rat/Documents/CS/C++/Poly/PolySwift/Poly/XLSXKit/.build/release/xlsxtool"))

; xlsxtool prefixes every error it reports with this exact marker (see
; its own main.swift for why: this Chez build's `process` merges a
; subprocess's stderr into the same stream read back as stdout, so an
; error can otherwise arrive silently mixed into what looks like valid
; CSV output). Checked BEFORE ever handing output to csvToBracketString
; -- without this, an xlsxtool failure surfaces as a confusing crash
; deep inside matrix.scm's numeral parsing instead of a clear error.
(define xlsxtool-error-prefix "XLSXTOOL_ERROR: ")

; get-string-all returns the eof-object (not "") when the port produced
; zero bytes -- confirmed empirically, hits every successful
; xlsxtool-write call, whose stdout is normally empty. Normalized here
; before the prefix check, since (string-length #!eof) errors.
(define (check-xlsxtool-output raw)
    (let ((s (if (eof-object? raw) "" raw)))
        (if (and (>= (string-length s) (string-length xlsxtool-error-prefix))
                 (string=? (substring s 0 (string-length xlsxtool-error-prefix)) xlsxtool-error-prefix))
            (error #f (string-append "xlsxtool: " (substring s (string-length xlsxtool-error-prefix) (string-length s))))
            s)))

; Runs `xlsxtool read <xlsxFile> [sheet]`, returning its stdout (the
; CSV text) as a string. No stdin needed for this direction.
(define (xlsxtool-read xlsxFile sheet)
    (let* ((cmdline (string-append (shell-quote (resolve-xlsxtool-path)) " read " (shell-quote xlsxFile)
                                   (if sheet (string-append " " (shell-quote sheet)) "")))
           (result (process cmdline))
           (from-out (car result))
           (to-in (cadr result)))
        (close-port to-in)
        (let ((s (get-string-all from-out)))
            (close-port from-out)
            (check-xlsxtool-output s))))

; Runs `xlsxtool write <sheetName> <xlsxFile>`, writing csvText to its
; stdin before closing it -- xlsxtool's contract is CSV on stdin, only
; the file path/sheet name go through argv (shell-quoted regardless).
(define (xlsxtool-write sheetName xlsxFile csvText)
    (let* ((cmdline (string-append (shell-quote (resolve-xlsxtool-path)) " write "
                                   (shell-quote sheetName) " " (shell-quote xlsxFile)))
           (result (process cmdline))
           (from-out (car result))
           (to-in (cadr result)))
        (display csvText to-in)
        (close-port to-in)
        (let ((s (get-string-all from-out)))
            (close-port from-out)
            (check-xlsxtool-output s))))

(define (runMatrixLoadXLSX xlsxFile outFile)
    (writeWholeFile outFile (csvToBracketString (xlsxtool-read xlsxFile #f))))

(define (runMatrixSaveXLSX bracketLine xlsxFile)
    (xlsxtool-write "Matrix" xlsxFile (bracketToCSVString bracketLine)))

; ---- entry point ----

(let ((args (command-line-arguments)))
    (cond
        ((and (>= (length args) 3) (string=? (car args) "process"))
            (runProcess (cadr args) (caddr args)))
        ((and (>= (length args) 5) (string=? (car args) "worksheet"))
            (runWorksheet (cadr args) (caddr args) (string->number (cadddr args)) (car (cddddr args))))
        ((and (>= (length args) 3) (string=? (car args) "matrixload"))
            (runMatrixLoad (cadr args) (caddr args)))
        ((and (>= (length args) 3) (string=? (car args) "matrixsave"))
            (runMatrixSave (cadr args) (caddr args)))
        ((and (>= (length args) 3) (string=? (car args) "matrixloadxlsx"))
            (runMatrixLoadXLSX (cadr args) (caddr args)))
        ((and (>= (length args) 3) (string=? (car args) "matrixsavexlsx"))
            (runMatrixSaveXLSX (cadr args) (caddr args)))
        ; Single-computation mode, for the compute-API server (PAE-API):
        ; one line of output, reusing safeApplyCommand directly (same
        ; error-string convention as the batch `process` mode) -- no new
        ; dispatch logic, this is exactly applyCommand's own cmd/arg/line
        ; parameters taken straight from argv instead of a batch file's
        ; "@:<command>" header. arg may be an empty string ("") when the
        ; command (e.g. differentiate/integrate) has no explicit variable.
        ((and (>= (length args) 4) (string=? (car args) "compute"))
            (display (safeApplyCommand (cadr args) (caddr args) (cadddr args)))
            (newline))
        ('t
            (display "Usage: dispatcher.scm process <in> <out> | worksheet <type> <difficulty> <count> <baseFilename> | matrixload <csvFile> <outFile> | matrixsave <bracketLine> <csvFile> | matrixloadxlsx <xlsxFile> <outFile> | matrixsavexlsx <bracketLine> <xlsxFile> | compute <cmd> <arg> <expression>")
            (newline)
            (exit 1))))

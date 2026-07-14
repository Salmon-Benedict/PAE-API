; Worksheet generation, ported from the C++ engine's WorksheetGenerator
; (Poly-Working/WorksheetGenerator.cpp -- not vendored into this repo's
; vendor/cpp/, which only has MathSymbol; read directly from the
; sibling Poly-Working checkout instead). Requires expandParse.scm,
; factorPoly.scm, solvePoly.scm, calcPoly.scm, equationVariants.scm
; (for solveExponential/solveLogarithm), and conicSections.scm (for
; analyzeConic, used by the conic-section worksheet type) to be loaded
; first.
;
; Ported from ../worksheetGenerator.scm (MIT Scheme) to Chez Scheme.
; Changes:
;   - Both (error "msg" type) call sites get an explicit #f who-arg.
;   - get-universal-time/universal-time->string are MIT-only (confirmed
;     unbound in Chez); currentTimestamp uses Chez's own (date-and-time),
;     which already returns a formatted string directly (e.g. "Sat Jul 11
;     22:53:23 2026") -- not textually identical to MIT's format, but
;     nothing golden-tests this (it's a generated-file timestamp, not
;     reproducible across runs either way).
;   - All 5 open-output-file call sites get an explicit 'replace second
;     arg: Chez's open-output-file errors ("file exists") if the target
;     already exists, unlike MIT's, which silently overwrites (confirmed
;     empirically against both binaries) -- 'replace restores MIT's
;     overwrite behavior.
;   - random, list-ref, assoc, filter, open-output-file/close-port (given
;     'replace, above) all verified present in Chez with matching
;     MIT-compatible signatures -- no changes needed for those.
;
; Unlike expand/factor/solve/calc (each checked against the C++ engine
; as an oracle), this file's solution generation does NOT replicate the
; C++ WorksheetGenerator's own logic -- it reuses this codebase's
; already-verified expand/factor/solve/differentiate/integrate/
; analyzeConic functions directly. This was a deliberate choice:
; inspecting actual past output from the C++ generator (committed CSVs
; in the Poly-Working tree) showed its calculus solutions are seriously
; broken, e.g. differentiating "-3b-3b+5b^4+4b^4" gives "-3 - 3 + 20b^3
; + 16b^3" (the terms are never combined, neither in the restated
; problem nor the answer), and integrating "5z^4+4z+2z^2" gives "5z *
; z^5/5 + + 4z * z^2/2 + + 2z * z^3/3 + C" (a display bug -- "5z *
; z^5/5" should just be "z^5" -- with the same spurious double "+" bug
; documented in calcPoly.scm). Since this codebase's own calculus
; functions are independently verified against 1000 closed-form cases,
; building the worksheet generator on top of them sidesteps this
; entire class of bug rather than reproducing it.
;
; Problems are generated so a clean answer is *guaranteed* (e.g.
; factoring problems are built by expanding chosen integer roots,
; rather than picking random coefficients and hoping they factor).
;
; ---- Remaining gaps closed here ----
; Three of the four originally-missing pieces (cpp-vs-scheme-gaps.md):
; conic-section worksheets (below, reusing analyzeConic), a MIXED
; *difficulty* mode (distinct from the 'mixed *type* mode already
; above -- C++ has both: a WorksheetType::MIXED_PRACTICE that varies
; the problem TYPE per problem, matching this file's existing 'mixed,
; and a separate DifficultyLevel::MIXED that varies EASY/MEDIUM/HARD
; per problem, which this file didn't have until now), and HTML export
; (MathJax) -- all pure output-formatting/generation logic with a
; C++ reference to check against, so ported directly. PDF export is
; scoped down: C++'s exportToPDF shells out to an installed `pdflatex`
; binary (`system("pdflatex ...")`) to compile a temp .tex file --
; that's an external-tool dependency, not math-engine logic, so this
; file generates the LaTeX *source* (the portable, testable part,
; verified structurally) but doesn't attempt to invoke a PDF compiler.

; Note: helperS.scm defines its OWN `remove`, with signature (remove
; element list) -- it removes one occurrence of a literal value, NOT
; SRFI-1's (remove predicate list). Passing a predicate lambda to it
; silently removes nothing (no list element is ever eqv? to a lambda),
; which doesn't error -- it just silently fails. This bit the first
; draft of genCalculusPolynomial below (its degree-without-replacement
; picker looked correct but always failed to shrink its candidate
; pool, occasionally producing uncombined duplicate-degree terms like
; "3z^2+z^2"); fixed by calling (remove pick avail) directly.

(define variablePool '(a b c m n p q r s t u v w y z))
(define (randomVariable) (list-ref variablePool (random (length variablePool))))

; Random nonzero integer in [-mag, mag] (excludes 0).
(define (randomNonzero mag)
    (let ((n (- (random (+ (* 2 mag) 1)) mag)))
        (if (= n 0) 1 n)))

(define (randomInt mag) (- (random (+ (* 2 mag) 1)) mag))

(define (difficultyRange difficulty)
    (cond
        ((eqv? difficulty 'easy) 5)
        ((eqv? difficulty 'medium) 10)
        ((eqv? difficulty 'hard) 15)
        ('t 10)))

(define (range n) (let loop ((i 0) (acc '())) (if (>= i n) (reverse acc) (loop (+ i 1) (cons i acc)))))

; Formats a single "coeff*var^deg" term as a signed string piece
; suitable for direct concatenation (e.g. "+3x^2", "-x", "+5"),
; omitting a coefficient of 1 (but not -1, which prints as "-var").
(define (termPiece coeff v deg)
    (let* ((sign (if (< coeff 0) "-" "+"))
           (mag (abs coeff))
           (magStr (if (and (= mag 1) (> deg 0)) "" (number->string mag)))
           (varStr (cond ((= deg 0) "") ((= deg 1) (symbol->string v)) ('t (string-append (symbol->string v) "^" (number->string deg))))))
        (string-append sign magStr varStr)))

; Concatenates termPiece strings into one expression, dropping any
; zero terms and stripping the leading "+" (or returning "0" if
; everything cancelled).
(define (joinTermPieces pieces)
    (let* ((nonZero (filter (lambda (p) (not (string=? p "+0"))) pieces))
           (s (apply string-append nonZero)))
        (cond
            ((= (string-length s) 0) "0")
            ((eqv? (string-ref s 0) #\+) (substring s 1 (string-length s)))
            ('t s))))

; ---- Problem generators ----
;
; Each returns a bare problem string (no "factor "/"solve "/etc.
; prefix -- generateWorksheet adds the appropriate display wrapper).

; Expansion: "(ax+b)(cx+d)" or "(ax+b)^2".
(define (genExpansionProblem difficulty)
    (let* ((v (randomVariable))
           (mag (difficultyRange difficulty))
           (coeffMag (if (eqv? difficulty 'easy) 3 5))
           (a (randomNonzero coeffMag)) (b (randomInt mag))
           (c (randomNonzero coeffMag)) (d (randomInt mag))
           (factor1 (string-append "(" (joinTermPieces (list (termPiece a v 1) (termPiece b v 0))) ")"))
           (useSquare (and (not (eqv? difficulty 'hard)) (= (random 2) 0))))
        (if useSquare
            (string-append factor1 "^2")
            (string-append factor1 "(" (joinTermPieces (list (termPiece c v 1) (termPiece d v 0))) ")"))))

; Factoring: picks 2 (easy/medium) or 3 (hard) small integer roots and
; builds the EXPANDED polynomial from them, guaranteeing it factors.
(define (genFactoringProblem difficulty)
    (let* ((v (randomVariable))
           (numRoots (if (eqv? difficulty 'hard) 3 2))
           (mag (if (eqv? difficulty 'easy) 6 10))
           (roots (let loop ((n numRoots) (acc '())) (if (= n 0) acc (loop (- n 1) (cons (randomNonzero mag) acc)))))
           (factorStrs (map (lambda (r) (string-append "(" (joinTermPieces (list (termPiece 1 v 1) (termPiece (- r) v 0))) ")")) roots))
           (factoredForm (apply string-append factorStrs)))
        (expand (string->list factoredForm))))

; Algebraic solving: linear "ax+b=c" (easy/medium), or a quadratic
; "ax^2+bx+c=0" built from two integer roots (hard), so it's always
; rational-root solvable.
(define (genSolvingProblem difficulty)
    (let ((v (randomVariable)) (mag (difficultyRange difficulty)))
        (if (eqv? difficulty 'hard)
            (let* ((r1 (randomNonzero 8)) (r2 (randomNonzero 8)) (a (randomNonzero 3))
                   (factor1 (string-append "(" (joinTermPieces (list (termPiece a v 1) (termPiece (- r1) v 0))) ")"))
                   (factor2 (string-append "(" (joinTermPieces (list (termPiece 1 v 1) (termPiece (- r2) v 0))) ")"))
                   (expanded (expand (string->list (string-append factor1 factor2)))))
                (string-append expanded "=0"))
            (let ((a (randomNonzero 9)) (b (randomInt mag)) (c (randomInt mag)))
                (string-append (joinTermPieces (list (termPiece a v 1) (termPiece b v 0))) "=" (number->string c))))))

; Exponential solving: "base^(ax+b)=value", where value is
; pre-computed as base^k for a chosen integer k, guaranteeing an exact
; rational solution.
(define (genExponentialProblem difficulty)
    (let* ((v (randomVariable))
           (base (+ 2 (random 4)))
           (a (randomNonzero (if (eqv? difficulty 'easy) 2 3)))
           (b (randomInt (if (eqv? difficulty 'easy) 3 6)))
           (k (randomInt (if (eqv? difficulty 'hard) 5 4)))
           (value (expt base k))
           (expChars (joinTermPieces (list (termPiece a v 1) (termPiece b v 0)))))
        (string-append (number->string base) "^(" expChars ")=" (number->string value))))

; Logarithmic solving: "log_base(x+offset)=k", guaranteeing the
; argument evaluates to the exact integer base^k.
(define (genLogarithmProblem difficulty)
    (let* ((v (randomVariable))
           (base (+ 2 (random 4)))
           (k (+ 1 (random (if (eqv? difficulty 'hard) 4 3))))
           (offset (randomInt (if (eqv? difficulty 'easy) 3 6)))
           (argStr (joinTermPieces (list (termPiece 1 v 1) (termPiece offset v 0)))))
        (string-append "log_" (number->string base) "(" argStr ")=" (number->string k))))

; Calculus: a random already-simplified polynomial (2-3 distinct-
; degree terms) for differentiation or integration practice.
(define (genCalculusPolynomial difficulty)
    (let* ((v (randomVariable))
           (maxDeg (cond ((eqv? difficulty 'easy) 3) ((eqv? difficulty 'hard) 5) ('t 4)))
           (mag (difficultyRange difficulty))
           (numTerms (+ 2 (random 2)))
           (degsUsed (let loop ((n numTerms) (acc '()) (avail (range (+ maxDeg 1))))
                         (if (or (= n 0) (null? avail))
                             acc
                             (let ((pick (list-ref avail (random (length avail)))))
                                 (loop (- n 1) (cons pick acc) (remove pick avail))))))
           (pieces (map (lambda (d) (termPiece (randomNonzero mag) v d)) degsUsed)))
        (joinTermPieces pieces)))

; Signed constant piece for direct concatenation, e.g. 3 -> "+3",
; -2 -> "-2", 0 -> "".
(define (signedOffset n)
    (cond ((= n 0) "")
          ((> n 0) (string-append "+" (number->string n)))
          ('t (string-append "-" (number->string (- n))))))

; Conic section: circle, parabola, ellipse, or hyperbola in standard
; form, chosen at random -- matching C++'s generateConicSectionProblems'
; 4 patterns. Doesn't vary by difficulty (neither does C++'s version).
; Parabola is generated as "y=a(x-h)^2+k" (fully on the right side)
; rather than C++'s own "y-k=a(x-h)^2" -- mathematically identical, but
; matches analyzeConic's accepted standard-form shape directly rather
; than requiring it to also recognize a shifted-left-hand-side variant.
(define (genConicProblem difficulty)
    (let ((type (random 4)))
        (cond
            ((= type 0)
                (let ((h (randomInt 5)) (k (randomInt 5)) (r (+ 2 (random 7))))
                    (string-append "(x" (signedOffset (- h)) ")^2+(y" (signedOffset (- k)) ")^2=" (number->string (* r r)))))
            ((= type 1)
                (let ((h (randomInt 3)) (k (randomInt 3)) (a (+ 1 (random 4))))
                    (string-append "y=" (number->string a) "(x" (signedOffset (- h)) ")^2" (signedOffset k))))
            ((= type 2)
                (let* ((a (+ 3 (random 6))) (b0 (+ 2 (random 5))) (b (if (>= b0 a) (max 1 (- a 1)) b0)))
                    (string-append "x^2/" (number->string (* a a)) "+y^2/" (number->string (* b b)) "=1")))
            ('t
                (let ((a (+ 2 (random 5))) (b (+ 2 (random 5))))
                    (string-append "x^2/" (number->string (* a a)) "-y^2/" (number->string (* b b)) "=1"))))))

; ---- Worksheet types and per-type problem/solution generation ----

(define worksheetTypes '(expand factor solve solveexp solvelog diff integ conic))

(define (genProblemOfType type difficulty)
    (cond
        ((eqv? type 'expand) (genExpansionProblem difficulty))
        ((eqv? type 'factor) (genFactoringProblem difficulty))
        ((eqv? type 'solve) (genSolvingProblem difficulty))
        ((eqv? type 'solveexp) (genExponentialProblem difficulty))
        ((eqv? type 'conic) (genConicProblem difficulty))
        ((eqv? type 'solvelog) (genLogarithmProblem difficulty))
        ((eqv? type 'diff) (genCalculusPolynomial difficulty))
        ((eqv? type 'integ) (genCalculusPolynomial difficulty))
        ('t (error #f "genProblemOfType: unknown type" type))))

(define (joinSolutionList lst)
    (let loop ((l lst) (acc ""))
        (cond
            ((null? l) acc)
            ((string=? acc "") (loop (cdr l) (car l)))
            ('t (loop (cdr l) (string-append acc ", " (car l)))))))

; Returns (cons displayProblemString solutionString) for one problem
; of the given type, using this codebase's own verified solvers.
(define (genProblemAndSolution type difficulty)
    (let ((p (genProblemOfType type difficulty)))
        (cond
            ((eqv? type 'expand) (cons (string-append "Expand: " p) (expand (string->list p))))
            ((eqv? type 'factor) (cons (string-append "Factor: " p) (factor (string->list p))))
            ((eqv? type 'solve) (cons (string-append "Solve: " p) (joinSolutionList (solve (string->list p)))))
            ((eqv? type 'solveexp) (cons (string-append "Solve: " p) (joinSolutionList (solveExponential (string->list p)))))
            ((eqv? type 'solvelog) (cons (string-append "Solve: " p) (joinSolutionList (solveLogarithm (string->list p)))))
            ((eqv? type 'diff) (cons (string-append "Differentiate: " p) (differentiateExpr (string->list p))))
            ((eqv? type 'integ) (cons (string-append "Integrate: " p) (integrateExpr (string->list p))))
            ((eqv? type 'conic) (cons (string-append "Analyze: " p) (joinSolutionList (analyzeConic (string->list p)))))
            ('t (error #f "genProblemAndSolution: unknown type" type)))))

; "mixed" picks a random type per problem instead of a fixed one.
(define (genMixedProblemAndSolution difficulty)
    (genProblemAndSolution (list-ref worksheetTypes (random (length worksheetTypes))) difficulty))

; ---- Top-level worksheet data generation ----

(define typeDisplayNames '(
    (expand . "Polynomial Expansion")
    (factor . "Polynomial Factoring")
    (solve . "Algebraic Solving")
    (solveexp . "Exponential Equation Solving")
    (solvelog . "Logarithmic Equation Solving")
    (diff . "Calculus - Differentiation")
    (integ . "Calculus - Integration")
    (conic . "Conic Sections")
    (mixed . "Mixed Practice")))

(define (typeDisplayName type) (cdr (assoc type typeDisplayNames)))

; 'mixed here is a DIFFERENT axis than the 'mixed worksheet TYPE above
; -- C++ has both a WorksheetType::MIXED_PRACTICE (varies the problem
; type per problem, matching this file's existing genMixedProblemAndSolution)
; and a separate DifficultyLevel::MIXED (varies easy/medium/hard per
; problem, independent of which type is being generated) -- resolved
; per-problem in generateProblemSet below via resolveDifficulty.
(define difficultyDisplayNames '((easy . "Easy") (medium . "Medium") (hard . "Hard") (mixed . "Mixed")))
(define (difficultyDisplayName difficulty) (cdr (assoc difficulty difficultyDisplayNames)))

(define (resolveDifficulty difficulty)
    (if (eqv? difficulty 'mixed)
        (list-ref '(easy medium hard) (random 3))
        difficulty))

; Generates count (problem . solution) pairs for the given worksheet
; type and difficulty (type 'mixed randomly varies the type per
; problem; difficulty 'mixed randomly varies easy/medium/hard per
; problem -- the two are independent and can be combined).
(define (generateProblemSet type difficulty count)
    (let loop ((n count) (acc '()))
        (if (= n 0)
            (reverse acc)
            (let ((d (resolveDifficulty difficulty)))
                (loop (- n 1)
                      (cons (if (eqv? type 'mixed)
                                (genMixedProblemAndSolution d)
                                (genProblemAndSolution type d))
                            acc))))))

; ---- CSV output ----

(define (currentTimestamp) (date-and-time))

; Writes the teacher version (problems + solutions) to filename.
(define (writeTeacherCSV problemSet type difficulty filename)
    (let ((port (open-output-file filename 'replace)))
        (display (string-append "# Mathematical Practice Worksheet - " (typeDisplayName type)) port) (newline port)
        (display (string-append "# Generated on: " (currentTimestamp)) port) (newline port)
        (display (string-append "# Problem Type: " (typeDisplayName type)) port) (newline port)
        (display (string-append "# Difficulty: " (difficultyDisplayName difficulty)) port) (newline port)
        (newline port)
        (display "Problem Number,Problem,Solution" port) (newline port)
        (let loop ((items problemSet) (n 1))
            (if (not (null? items))
                (begin
                    (display n port) (display ",\"" port) (display (car (car items)) port) (display "\",\"" port)
                    (display (cdr (car items)) port) (display "\"" port) (newline port)
                    (loop (cdr items) (+ n 1)))))
        (close-port port)))

; Writes the student version (problems only) to filename.
(define (writeStudentCSV problemSet type difficulty filename)
    (let ((port (open-output-file filename 'replace)))
        (display (string-append "# STUDENT WORKSHEET - " (typeDisplayName type)) port) (newline port)
        (display (string-append "# Generated on: " (currentTimestamp)) port) (newline port)
        (display (string-append "# Difficulty: " (difficultyDisplayName difficulty)) port) (newline port)
        (display "# Instructions: Solve each problem. Show your work." port) (newline port)
        (newline port)
        (display "Problem Number,Problem" port) (newline port)
        (let loop ((items problemSet) (n 1))
            (if (not (null? items))
                (begin
                    (display n port) (display ",\"" port) (display (car (car items)) port) (display "\"" port) (newline port)
                    (loop (cdr items) (+ n 1)))))
        (close-port port)))

; ---- HTML output (MathJax) ----
; Matches C++'s writeHTML/writeHTMLStudentVersion: a self-contained HTML
; page with the MathJax CDN script tags, rendering each problem/solution
; as inline TeX (\(...\)).

(define (htmlHead title styleBlock)
    (string-append
        "<!DOCTYPE html>\n<html>\n<head>\n"
        "<title>" title "</title>\n"
        "<script src='https://polyfill.io/v3/polyfill.min.js?features=es6'></script>\n"
        "<script id='MathJax-script' async src='https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js'></script>\n"
        "<style>\nbody { font-family: Arial, sans-serif; margin: 40px; }\n"
        styleBlock "</style>\n"
        "</head>\n<body>\n"))

(define teacherStyleBlock ".problem { margin: 20px 0; }\n.solution { color: blue; margin-top: 5px; }\n")
(define studentStyleBlock
    (string-append
        ".problem { margin: 20px 0; padding: 10px; border: 1px solid #ddd; }\n"
        ".answer-space { margin-top: 10px; padding: 20px; border: 1px dashed #ccc; background: #f9f9f9; }\n"
        "h1 { color: #333; }\n"))

; Writes the teacher version (problems + solutions) to filename.
(define (writeTeacherHTML problemSet type difficulty filename)
    (let ((port (open-output-file filename 'replace)) (title (typeDisplayName type)))
        (display (htmlHead title teacherStyleBlock) port)
        (display (string-append "<h1>" title "</h1>\n") port)
        (display (string-append "<p>Generated on: " (currentTimestamp) "</p>\n") port)
        (display (string-append "<p>Difficulty: " (difficultyDisplayName difficulty) "</p>\n\n") port)
        (let loop ((items problemSet) (n 1))
            (if (not (null? items))
                (begin
                    (display "<div class='problem'>\n" port)
                    (display (string-append "<strong>" (number->string n) ".</strong> \\(" (car (car items)) "\\)\n") port)
                    (display (string-append "<div class='solution'><em>Solution:</em> \\(" (cdr (car items)) "\\)</div>\n") port)
                    (display "</div>\n" port)
                    (loop (cdr items) (+ n 1)))))
        (display "</body>\n</html>" port)
        (close-port port)))

; Writes the student version (problems only) to filename.
(define (writeStudentHTML problemSet type difficulty filename)
    (let ((port (open-output-file filename 'replace)) (title (typeDisplayName type)))
        (display (htmlHead (string-append "STUDENT WORKSHEET - " title) studentStyleBlock) port)
        (display "<h1>STUDENT WORKSHEET</h1>\n" port)
        (display (string-append "<h2>" title "</h2>\n") port)
        (display "<p><em>Instructions: Solve each problem and show your work in the space provided.</em></p>\n" port)
        (let loop ((items problemSet) (n 1))
            (if (not (null? items))
                (begin
                    (display "<div class='problem'>\n" port)
                    (display (string-append "<strong>" (number->string n) ".</strong> \\(" (car (car items)) "\\)\n") port)
                    (display "<div class='answer-space'>Your work and answer:</div>\n" port)
                    (display "</div>\n" port)
                    (loop (cdr items) (+ n 1)))))
        (display "</body>\n</html>" port)
        (close-port port)))

; ---- LaTeX output ----
; Matches C++'s generateLaTeXDocument: produces the .tex SOURCE only.
; C++'s exportToPDF additionally shells out to an installed `pdflatex`
; binary to compile it -- an external-tool dependency outside this
; engine's scope (see file header) -- so this stops at writing the .tex
; file, the portable and testable part.

(define (writeLaTeXDocument problemSet type filename)
    (let ((port (open-output-file filename 'replace)) (title (typeDisplayName type)))
        (display "\\documentclass{article}\n" port)
        (display "\\usepackage{amsmath}\n\\usepackage{amsfonts}\n\\usepackage{geometry}\n" port)
        (display "\\geometry{margin=1in}\n\n" port)
        (display "\\begin{document}\n\n" port)
        (display (string-append "\\title{" title "}\n") port)
        (display (string-append "\\date{" (currentTimestamp) "}\n") port)
        (display "\\maketitle\n\n" port)
        (let loop ((items problemSet) (n 1))
            (if (not (null? items))
                (begin
                    (display (string-append "\\textbf{" (number->string n) ".} $" (car (car items)) "$\n\n") port)
                    (display (string-append "\\textit{Solution:} $" (cdr (car items)) "$\n\n") port)
                    (display "\\vspace{0.5cm}\n\n" port)
                    (loop (cdr items) (+ n 1)))))
        (display "\\end{document}" port)
        (close-port port)))

; Top-level entry point: generates a worksheet of the given type
; ('expand/'factor/'solve/'solveexp/'solvelog/'diff/'integ/'conic/'mixed),
; difficulty ('easy/'medium/'hard/'mixed), and problem count, writing a
; STUDENT (problems only) and TEACHER (problems + solutions) file in
; CSV, HTML, and LaTeX (.tex source only -- see above) using baseFilename
; as a shared prefix. Returns the problemSet itself (a list of
; (problem . solution) pairs) in case the caller wants it without
; re-parsing an output file.
(define (generateWorksheet type difficulty count baseFilename)
    (let ((problemSet (generateProblemSet type difficulty count)))
        (writeStudentCSV problemSet type difficulty (string-append baseFilename "_STUDENT.csv"))
        (writeTeacherCSV problemSet type difficulty (string-append baseFilename "_TEACHER.csv"))
        (writeStudentHTML problemSet type difficulty (string-append baseFilename "_STUDENT.html"))
        (writeTeacherHTML problemSet type difficulty (string-append baseFilename "_TEACHER.html"))
        (writeLaTeXDocument problemSet type (string-append baseFilename ".tex"))
        problemSet))

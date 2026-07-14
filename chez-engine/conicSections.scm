; conicSections.scm -- conic section detection and analysis, ported in
; spirit (not line-by-line) from the C++ engine's analyzeConic and its
; isCircleEquation/analyzeCircle, isParabolaEquation/analyzeParabola,
; isEllipseEquation/analyzeEllipse, isHyperbolaEquation/analyzeHyperbola
; helpers. Requires helperS.scm, mathHelp.scm, basicmath.scm,
; chemistry.scm, PolyStoSymbol.scm, simplify.scm, expandParse.scm,
; factorPoly.scm (coeffAt, polyDegree), solvePoly.scm
; (extractSquareFactor), equationVariants.scm (stripSpaces,
; findStringCharPos, matchingParen, pi-const, roundToSigFigs),
; linearSystems.scm (findFirstAlphaPos, parseFractionOrDecimal),
; functionAnalysis.scm (exprToTermList, linearZeroOrFalse) to be loaded
; first.
;
; Ported from ../conicSections.scm (MIT Scheme) to Chez Scheme.
; Changes: none -- this file uses no MIT-specific forms (no error/sort/
; every/any/#!optional/define-record-type), and numerator/denominator/
; exact->inexact/memv all behave identically in Chez. Verbatim copy
; except this note.
;
; ---- Why this isn't a line-by-line port ----
; C++ detects each conic type via 3-6 separate hand-written regexes per
; shape (one per standard-form variant: origin-centered, shifted,
; general Ax²+By²=C), and extracts h/k/a²/b² via more regex captures.
; This file instead splits the equation into its (at most two) top-level
; signed squared terms once and parses each uniformly (parseSquaredTerm
; below) regardless of which standard-form variant it's written in --
; one code path instead of ~20 regexes across four shapes. It also fixes
; a confirmed bug: C++'s analyzeParabola coefficient extraction
; literally assumes the linear (b) coefficient is always zero ("For
; simple analysis, assume b=0, c=0 for basic forms" -- verified in the
; source), so it gives a wrong vertex for anything like "y=x^2+2x+3".
; This file parses the full quadratic via the engine's real polynomial
; parser (coeffAt), so b is never dropped.
;
; ---- Scope ----
; Standard-form input only, matching C++'s own scope (neither engine
; completes the square from general form, e.g. "x^2+y^2-4x+6y-3=0" is
; not recognized as a circle by either). Radius/semi-axes/linear
; eccentricity are rendered as exact numbers or symbolic radicals
; (e.g. "2√3") rather than C++'s decimal approximations, via
; solvePoly.scm's extractSquareFactor; eccentricity, area, and
; circumference/perimeter are inherently irrational (they involve π or,
; for the ellipse perimeter, an approximation formula even in exact
; math) and stay decimal, matching C++'s own treatment of those.

; ---- Symbolic square root formatting ----

; sqrt(rat) = coeff*sqrt(radicand)/denom, rat a nonnegative exact
; rational. Rationalizes the denominator first (sqrt(p/q) = sqrt(p*q)/q)
; so extractSquareFactor (which needs a nonnegative integer) always has
; valid input.
(define (sqrtParts rat)
    (if (= rat 0)
        (list 0 1 1)
        (let* ((p (numerator rat)) (q (denominator rat))
               (ext (extractSquareFactor (* p q))))
            (list (car ext) (cdr ext) q))))

(define (formatRadicalFraction coeff radicand q)
    (cond
        ((= coeff 0) "0")
        ((= radicand 1) (number->string (/ coeff q)))
        ((= q 1) (string-append (if (= coeff 1) "" (number->string coeff)) "√" (number->string radicand)))
        ('t (string-append (if (= coeff 1) "" (number->string coeff)) "√" (number->string radicand) "/" (number->string q)))))

(define (symbolicSqrtString rat)
    (let ((parts (sqrtParts rat)))
        (formatRadicalFraction (car parts) (cadr parts) (caddr parts))))

; Formats "base ± sqrt(offsetSquared)" (sign = -1 or 1) -- an exact
; number if offsetSquared is a perfect square (possibly after clearing
; a denominator), else a combined "base ± c√radicand" expression string.
; Used for vertex/focus/co-vertex coordinates.
(define (offsetPoint base offsetSquared sign)
    (let* ((parts (sqrtParts offsetSquared)) (coeff (car parts)) (radicand (cadr parts)) (q (caddr parts)))
        (cond
            ((= radicand 1) (number->string (+ base (* sign (/ coeff q)))))
            ((= base 0) (string-append (if (> sign 0) "" "-") (formatRadicalFraction coeff radicand q)))
            ('t (string-append (number->string base) (if (> sign 0) " + " " - ") (formatRadicalFraction coeff radicand q))))))

; ---- Shared squared-term parsing (circle/ellipse/hyperbola) ----

; Splits a signed sum like "(x-2)^2/9+(y+1)^2/4" into ("(x-2)^2/9"
; "+(y+1)^2/4"), respecting parens (unlike linearSystems.scm's
; splitSignedTerms, which isn't paren-aware and would incorrectly split
; inside "(x-2)" too).
(define (splitTopLevelSignedTerms s)
    (let loop ((i 0) (start 0) (depth 0) (acc '()))
        (cond
            ((>= i (string-length s)) (reverse (cons (substring s start (string-length s)) acc)))
            ((eqv? (string-ref s i) #\() (loop (+ i 1) start (+ depth 1) acc))
            ((eqv? (string-ref s i) #\)) (loop (+ i 1) start (- depth 1) acc))
            ((and (> i start) (= depth 0) (or (eqv? (string-ref s i) #\+) (eqv? (string-ref s i) #\-)))
                (loop (+ i 1) i depth (cons (substring s start i) acc)))
            ('t (loop (+ i 1) start depth acc)))))

; Parses one signed squared term -- "(x-2)^2/9", "-(y+1)^2/4", "x^2",
; "4y^2", "y^2/9" -- into (list variableChar h coefficient), where the
; term equals coefficient*(variable-h)^2 (coefficient carries the
; term's sign, e.g. negative for a hyperbola's subtracted term).
(define (parseSquaredTerm term)
    (let* ((negative (and (> (string-length term) 0) (eqv? (string-ref term 0) #\-)))
           (body (if (and (> (string-length term) 0) (memv (string-ref term 0) (list #\+ #\-)))
                     (substring term 1 (string-length term))
                     term)))
        (if (eqv? (string-ref body 0) #\()
            (let* ((close (matchingParen body 0))
                   (inner (substring body 1 close))
                   (after (substring body (+ close 1) (string-length body))))
                (if (or (< (string-length after) 2) (not (string=? (substring after 0 2) "^2")))
                    #f
                    (let* ((variable (string-ref inner 0))
                           (h (if (= (string-length inner) 1) 0 (linearZeroOrFalse (exprToTermList inner))))
                           (slashIdx (findStringCharPos #\/ after 0))
                           (coeff (if slashIdx (/ 1 (parseFractionOrDecimal (substring after (+ slashIdx 1) (string-length after)))) 1)))
                        (list variable h (if negative (- coeff) coeff)))))
            (let ((varIdx (findFirstAlphaPos body 0)))
                (if (or (not varIdx)
                        (< (string-length body) (+ varIdx 3))
                        (not (string=? (substring body (+ varIdx 1) (+ varIdx 3)) "^2")))
                    #f
                    (let* ((variable (string-ref body varIdx))
                           (before (substring body 0 varIdx))
                           (after (substring body (+ varIdx 3) (string-length body)))
                           (slashIdx (findStringCharPos #\/ after 0))
                           (coeff (if slashIdx
                                      (/ 1 (parseFractionOrDecimal (substring after (+ slashIdx 1) (string-length after))))
                                      (if (= (string-length before) 0) 1 (parseFractionOrDecimal before)))))
                        (list variable 0 (if negative (- coeff) coeff))))))))

; Classifies the LHS as a two-squared-term conic (circle/ellipse/
; hyperbola), returning (list h k aSqRaw bSqRaw) -- aSqRaw/bSqRaw are
; RHS/coefficient, signed (negative for a hyperbola's subtracted term,
; both positive and equal for a circle, both positive and unequal for
; an ellipse) -- or #f if the LHS isn't exactly two squared terms, one
; each in x and y.
(define (classifyTwoSquareConic lhs rhs)
    (let ((terms (splitTopLevelSignedTerms lhs)))
        (if (not (= (length terms) 2))
            #f
            (let* ((p1 (parseSquaredTerm (car terms))) (p2 (parseSquaredTerm (cadr terms))))
                (if (not (and p1 p2 (memv (car p1) (list #\x #\y)) (memv (car p2) (list #\x #\y)) (not (eqv? (car p1) (car p2)))))
                    #f
                    (let* ((xp (if (eqv? (car p1) #\x) p1 p2)) (yp (if (eqv? (car p1) #\y) p1 p2))
                           (rhsVal (parseFractionOrDecimal rhs)))
                        (list (cadr xp) (cadr yp) (/ rhsVal (caddr xp)) (/ rhsVal (caddr yp)))))))))

; ---- Circle ----

(define (circleGeometry h k rSq)
    (let* ((parts (sqrtParts rSq)) (coeff (car parts)) (radicand (cadr parts)) (q (caddr parts)))
        (list "Type: Circle"
              (string-append "Center: (" (number->string h) ", " (number->string k) ")")
              (string-append "Radius: " (formatRadicalFraction coeff radicand q))
              (string-append "Area: " (number->string rSq) "π")
              (string-append "Circumference: " (formatRadicalFraction (* 2 coeff) radicand q) "π"))))

; ---- Ellipse ----

(define (ellipseGeometry h k aSqRaw bSqRaw)
    (let* ((majorHorizontal (> aSqRaw bSqRaw))
           (majorSq (max aSqRaw bSqRaw)) (minorSq (min aSqRaw bSqRaw))
           (cSq (- majorSq minorSq))
           (aStr (symbolicSqrtString majorSq)) (bStr (symbolicSqrtString minorSq)) (cStr (symbolicSqrtString cSq))
           (eccentricity (roundToSigFigs (/ (sqrt (exact->inexact cSq)) (sqrt (exact->inexact majorSq))) 5))
           (area (roundToSigFigs (* pi-const (sqrt (exact->inexact majorSq)) (sqrt (exact->inexact minorSq))) 5)))
        (append
            (list "Type: Ellipse"
                  (string-append "Center: (" (number->string h) ", " (number->string k) ")"))
            (if majorHorizontal
                (list (string-append "Semi-major axis (horizontal): a = " aStr)
                      (string-append "Semi-minor axis (vertical): b = " bStr)
                      (string-append "Vertices: (" (offsetPoint h majorSq -1) ", " (number->string k) "), ("
                                                    (offsetPoint h majorSq 1) ", " (number->string k) ")")
                      (string-append "Co-vertices: (" (number->string h) ", " (offsetPoint k minorSq -1) "), ("
                                                        (number->string h) ", " (offsetPoint k minorSq 1) ")")
                      (string-append "Foci: (" (offsetPoint h cSq -1) ", " (number->string k) "), ("
                                                (offsetPoint h cSq 1) ", " (number->string k) ")"))
                (list (string-append "Semi-major axis (vertical): a = " aStr)
                      (string-append "Semi-minor axis (horizontal): b = " bStr)
                      (string-append "Vertices: (" (number->string h) ", " (offsetPoint k majorSq -1) "), ("
                                                    (number->string h) ", " (offsetPoint k majorSq 1) ")")
                      (string-append "Co-vertices: (" (offsetPoint h minorSq -1) ", " (number->string k) "), ("
                                                        (offsetPoint h minorSq 1) ", " (number->string k) ")")
                      (string-append "Foci: (" (number->string h) ", " (offsetPoint k cSq -1) "), ("
                                                (number->string h) ", " (offsetPoint k cSq 1) ")")))
            (list (string-append "Eccentricity: e ≈ " eccentricity)
                  (string-append "Linear eccentricity: c = " cStr)
                  (string-append "Area: π·a·b ≈ " area)))))

; ---- Hyperbola ----

(define (hyperbolaGeometry h k aSq bSq isHorizontal)
    (let* ((cSq (+ aSq bSq))
           (aStr (symbolicSqrtString aSq)) (bStr (symbolicSqrtString bSq)) (cStr (symbolicSqrtString cSq))
           (eccentricity (roundToSigFigs (/ (sqrt (exact->inexact cSq)) (sqrt (exact->inexact aSq))) 5))
           (slope (roundToSigFigs (/ (sqrt (exact->inexact bSq)) (sqrt (exact->inexact aSq))) 5)))
        (append
            (list "Type: Hyperbola"
                  (string-append "Orientation: " (if isHorizontal "Horizontal" "Vertical"))
                  (string-append "Center: (" (number->string h) ", " (number->string k) ")"))
            (if isHorizontal
                (list (string-append "Semi-transverse axis (horizontal): a = " aStr)
                      (string-append "Semi-conjugate axis (vertical): b = " bStr)
                      (string-append "Vertices: (" (offsetPoint h aSq -1) ", " (number->string k) "), ("
                                                    (offsetPoint h aSq 1) ", " (number->string k) ")")
                      (string-append "Foci: (" (offsetPoint h cSq -1) ", " (number->string k) "), ("
                                                (offsetPoint h cSq 1) ", " (number->string k) ")")
                      "Asymptotes:"
                      (string-append "  y - " (number->string k) " = " slope "(x - " (number->string h) ")")
                      (string-append "  y - " (number->string k) " = -" slope "(x - " (number->string h) ")"))
                (list (string-append "Semi-transverse axis (vertical): a = " aStr)
                      (string-append "Semi-conjugate axis (horizontal): b = " bStr)
                      (string-append "Vertices: (" (number->string h) ", " (offsetPoint k aSq -1) "), ("
                                                    (number->string h) ", " (offsetPoint k aSq 1) ")")
                      (string-append "Foci: (" (number->string h) ", " (offsetPoint k cSq -1) "), ("
                                                (number->string h) ", " (offsetPoint k cSq 1) ")")
                      "Asymptotes:"
                      (string-append "  x - " (number->string h) " = " slope "(y - " (number->string k) ")")
                      (string-append "  x - " (number->string h) " = -" slope "(y - " (number->string k) ")")))
            (list (string-append "Eccentricity: e ≈ " eccentricity)))))

(define (dispatchTwoSquareConic h k aSqRaw bSqRaw)
    (cond
        ((and (> aSqRaw 0) (> bSqRaw 0) (= aSqRaw bSqRaw)) (circleGeometry h k aSqRaw))
        ((and (> aSqRaw 0) (> bSqRaw 0)) (ellipseGeometry h k aSqRaw bSqRaw))
        ((and (> aSqRaw 0) (< bSqRaw 0)) (hyperbolaGeometry h k aSqRaw (- bSqRaw) #t))
        ((and (< aSqRaw 0) (> bSqRaw 0)) (hyperbolaGeometry h k bSqRaw (- aSqRaw) #f))
        ('t (list "Conic type not yet supported or equation format not recognized"
                  "Currently supported: Circle, Parabola, Ellipse, and Hyperbola equations"))))

; ---- Parabola ----

; Parses the full quadratic via the engine's real polynomial parser
; (coeffAt), so the linear (b) coefficient is never dropped -- unlike
; C++, which literally assumes b=0 for "simple forms" (see file header).
(define (parabolaFromQuadratic quadraticSide isVertical)
    (let ((tl (exprToTermList quadraticSide)))
        (if (not (= (polyDegree tl) 2))
            (list "Error: Not a valid parabola (coefficient 'a' cannot be zero)")
            (let* ((a (coeffAt tl 2)) (b (coeffAt tl 1)) (c (coeffAt tl 0))
                   (hVal (/ (- b) (* 2 a))) (kVal (- c (/ (* b b) (* 4 a))))
                   (p (/ 1 (* 4 a))))
                (append
                    (list "Type: Parabola"
                          (string-append "Orientation: " (if isVertical "Vertical" "Horizontal"))
                          (string-append "Standard form: " (if isVertical "y = " "x = ") quadraticSide))
                    (if isVertical
                        ; y = ax^2+bx+c: hVal/kVal are the vertex's own (x, y).
                        (list (string-append "Vertex: (" (number->string hVal) ", " (number->string kVal) ")")
                              (string-append "Focus: (" (number->string hVal) ", " (number->string (+ kVal p)) ")")
                              (string-append "Directrix: y = " (number->string (- kVal p)))
                              (string-append "Axis of Symmetry: x = " (number->string hVal))
                              (string-append "Opens: " (if (> a 0) "Upward" "Downward")))
                        ; x = ay^2+by+c: the quadratic's input variable is y, so
                        ; hVal is the vertex's y-coordinate and kVal is its
                        ; x-coordinate -- the reverse of the vertical case.
                        (list (string-append "Vertex: (" (number->string kVal) ", " (number->string hVal) ")")
                              (string-append "Focus: (" (number->string (+ kVal p)) ", " (number->string hVal) ")")
                              (string-append "Directrix: x = " (number->string (- kVal p)))
                              (string-append "Axis of Symmetry: y = " (number->string hVal))
                              (string-append "Opens: " (if (> a 0) "Rightward" "Leftward"))))
                    (list (string-append "Coefficient 'a': " (number->string a) " (controls width and direction)")))))))

; ---- Top-level dispatcher ----

; Analyzes a conic section equation, e.g. (string->list "x^2+y^2=25")
; -> ("Type: Circle" "Center: (0, 0)" "Radius: 5" ...). See file header
; for scope (standard-form input only).
(define (analyzeConic eqChars)
    (let* ((eq (stripSpaces (list->string eqChars)))
           (eqIdx (findStringCharPos #\= eq 0)))
        (if (not eqIdx)
            (list "Error: No equals sign found in equation")
            (let ((left (substring eq 0 eqIdx)) (right (substring eq (+ eqIdx 1) (string-length eq))))
                (cond
                    ((or (string=? left "y") (string=? right "y"))
                        (parabolaFromQuadratic (if (string=? left "y") right left) #t))
                    ((or (string=? left "x") (string=? right "x"))
                        (parabolaFromQuadratic (if (string=? left "x") right left) #f))
                    ('t
                        (let ((classified (classifyTwoSquareConic left right)))
                            (if (not classified)
                                (list "Conic type not yet supported or equation format not recognized"
                                      "Currently supported: Circle, Parabola, Ellipse, and Hyperbola equations")
                                (apply dispatchTwoSquareConic classified)))))))))

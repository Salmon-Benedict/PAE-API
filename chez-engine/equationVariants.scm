; Small equation-transformation and numeric-display utilities, ported
; from the C++ engine's rotate/flip/degToRad/radToDeg/
; simplifySquareRootCmd/toScientificNotation/logToExp/expToLog/
; solveExponential/solveLogarithm commands. Requires expandParse.scm,
; factorPoly.scm (for extractSquareFactor), and solvePoly.scm (for
; solve, reused by solveExponential/solveLogarithm) to be loaded first.
;
; Ported from ../equationVariants.scm (MIT Scheme) to Chez Scheme.
; Changes: the one `(error "msg")` call site (findInequalityOp) gets an
; explicit #f who-arg.

; Finds the (0-based) index of the first occurrence of ch in a STRING
; (as opposed to findCharPos in solvePoly.scm, which operates on a char
; list) -- needed for parsing decimal numerals in toScientificNotation.
(define (findStringCharPos ch s idx)
    (cond
        ((>= idx (string-length s)) #f)
        ((eqv? (string-ref s idx) ch) idx)
        ('t (findStringCharPos ch s (+ idx 1)))))

; Swaps the two sides of an equation (raw substrings, no expansion --
; matches the C++ engine's `rotate` exactly, e.g. "x+2=3y-1" -> "3y-1 = x+2").
(define (rotateEq charL)
    (let* ((noSpaces (remove-all #\space charL))
           (eqPos (findCharPos #\= noSpaces 0))
           (lhsChars (if (> eqPos 0) (extract 0 (- eqPos 1) noSpaces) '()))
           (rhsChars (if (< (+ eqPos 1) (length noSpaces)) (extract (+ eqPos 1) (- (length noSpaces) 1) noSpaces) '())))
        (string-append (list->string rhsChars) " = " (list->string lhsChars))))

; Negates every term on one side of an equation. Unlike termsToString's
; normal convention (omit a leading "+"), flip always shows an explicit
; sign on the leading term -- matches the C++ engine's `flip`, e.g.
; "-2x-3=-7" -> "+2x+3 = +7" (verified directly against it).
(define (flipSide chars)
    (let* ((addends (parseExpansion chars))
           (expanded (expandSum addends))
           (negated (map negateTerm expanded))
           (noZeros (dropZeros negated))
           (final (if (null? noZeros) (list (makep 0 1 1 1 1 1 1 '+)) noZeros))
           (str (termsToString final)))
        (if (or (string=? str "0") (eqv? (string-ref str 0) #\-))
            str
            (string-append "+" str))))

(define (flipEq charL)
    (let* ((eqPos (findCharPos #\= charL 0))
           (lhsChars (extract 0 (- eqPos 1) charL))
           (rhsChars (extract (+ eqPos 1) (- (length charL) 1) charL)))
        (string-append (flipSide lhsChars) " = " (flipSide rhsChars))))

; Converts a degree value to radians, expressed symbolically as a
; reduced fraction of π (e.g. 90 -> "π/2 radians", 360 -> "2π radians",
; -90 -> "-π/2 radians") -- matches the C++ engine's `degtorad` exactly.
(define (degToRad degChars)
    (let* ((deg (string->number (list->string (remove-all #\space degChars))))
           (deg (if (exact? deg) deg (inexact->exact deg))))
        (if (= deg 0)
            "0 radians"
            (let* ((frac (/ deg 180))
                   (p (numerator frac))
                   (q (denominator frac))
                   (piStr (cond ((= p 1) "π") ((= p -1) "-π") ('t (string-append (number->string p) "π")))))
                (string-append piStr (if (= q 1) "" (string-append "/" (number->string q))) " radians")))))

; Rounds a nonzero flonum to n significant figures, returning it as a
; plain decimal string.
(define (roundToSigFigs x n)
    (if (= x 0)
        "0"
        (let* ((mag (floor (/ (log (abs x)) (log 10))))
               (scale (expt 10.0 (- n 1 mag)))
               (rounded (/ (round (* x scale)) scale)))
            (number->string rounded))))

(define pi-const (* 4 (atan 1)))

; Converts a radian value to degrees: value*180/π, rounded to 10
; significant figures -- a purely numeric (non-symbolic) decimal
; conversion, matching the C++ engine's `radtodeg` exactly (confirmed
; it does NOT recognize e.g. 3.14159265 as π and stay symbolic; it
; always gives a decimal approximation, and the 10-significant-figure
; rounding was reverse-engineered from its actual output).
(define (radToDeg radChars)
    (let* ((rad (exact->inexact (string->number (list->string (remove-all #\space radChars)))))
           (deg (/ (* rad 180) pi-const)))
        (string-append (roundToSigFigs deg 10) " degrees")))

; Simplifies √n by extracting its largest perfect-square factor (reuses
; extractSquareFactor/integerSqrt from factorPoly.scm) -- matches the
; C++ engine's `sqrt` command exactly, e.g. "12" -> "2√3", "9" -> "3".
; Also accepts an outer coefficient before a literal "√", e.g. "2√12"
; -> "4√3" (2 * the 2√3 that "12" alone simplifies to), matching C++'s
; simplifySquareRootCmd (MathSymbol.cpp), which parses that same form.
(define (simplifySquareRootCmd numChars)
    (let* ((s (stripSpaces (list->string numChars)))
           (sqrtIdx (findStringCharPos #\√ s 0))
           (outerCoeff (if (and sqrtIdx (> sqrtIdx 0))
                           (string->number (substring s 0 sqrtIdx))
                           1))
           (radicandStr (if sqrtIdx (substring s (+ sqrtIdx 1) (string-length s)) s))
           (n (string->number radicandStr))
           (sq (integerSqrt n)))
        (if sq
            (number->string (* outerCoeff sq))
            (let* ((ext (extractSquareFactor n))
                   (coeff (* outerCoeff (car ext)))
                   (radicand (cdr ext)))
                (if (= coeff 1)
                    (string-append "√" (number->string radicand))
                    (string-append (number->string coeff) "√" (number->string radicand)))))))

(define (stripLeadingZeros s)
    (let loop ((i 0))
        (cond
            ((>= i (string-length s)) "")
            ((eqv? (string-ref s i) #\0) (loop (+ i 1)))
            ('t (substring s i (string-length s))))))

(define (stripTrailingZeros s)
    (let loop ((i (string-length s)))
        (cond
            ((= i 0) "")
            ((eqv? (string-ref s (- i 1)) #\0) (loop (- i 1)))
            ('t (substring s 0 i)))))

; Shared formatting core for scientific notation: given a digit string
; with no separators (concatenated integer+fractional digits), how many
; of its trailing digits are fractional (decimalPlaces), and the
; number's sign, builds the normalized "m × 10^e" string (1 <= |m| < 10,
; or just "m" when e=0). Used by both toScientificNotation (digits taken
; straight from a user-typed numeral) and rationalToScientificNotation
; (digits taken from an exact rational computed by
; addScientificNotation/subtractScientificNotation/
; multiplyScientificNotation) so both paths share one exact,
; floating-point-free path to the final string.
(define (digitsToScientific allDigits decimalPlaces negative)
    (let ((stripped (stripLeadingZeros allDigits)))
        (if (= (string-length stripped) 0)
            "0"
            (let* ((firstDigit (substring stripped 0 1))
                   (restRaw (substring stripped 1 (string-length stripped)))
                   (restDigits (stripTrailingZeros restRaw))
                   (mantissa (if (= (string-length restDigits) 0) firstDigit (string-append firstDigit "." restDigits)))
                   (numLeadingZerosStripped (- (string-length allDigits) (string-length stripped)))
                   (intPartLen (- (string-length allDigits) decimalPlaces))
                   (e (- (- intPartLen numLeadingZerosStripped) 1)))
                (string-append (if negative "-" "") mantissa
                               (if (= e 0) "" (string-append " × 10^" (number->string e))))))))

; Converts a plain decimal numeral to scientific notation "m × 10^e"
; with 1 <= |m| < 10 (or just "m" when e=0), working entirely on the
; numeral's digit string (no floating-point arithmetic) so every
; significant digit of the input is preserved exactly.
;
; This intentionally does NOT match the C++ engine's own
; toScientificNotation, which has two confirmed bugs: (1) it truncates
; the mantissa to 4 significant figures regardless of how many the
; input actually has (e.g. 12345 -> "1.234 × 10^4", dropping the final
; "5"; 123450 gives the identical truncated "1.234 × 10^5" despite a
; different actual value), and (2) it loses the exponent entirely for
; |value| < 1 instead of using a negative exponent (e.g. 0.001 -> "1"
; with no "× 10^-3" at all; 0.5 -> "5" instead of "5 × 10^-1"). Both
; verified directly against the running C++ binary. This file returns
; the mathematically correct result instead.
(define (toScientificNotation numChars)
    (let* ((s (list->string (remove-all #\space numChars)))
           (negative (and (> (string-length s) 0) (eqv? (string-ref s 0) #\-)))
           (body (if negative (substring s 1 (string-length s)) s))
           (dotIdx (findStringCharPos #\. body 0))
           (intPart (if dotIdx (substring body 0 dotIdx) body))
           (fracPart (if dotIdx (substring body (+ dotIdx 1) (string-length body)) ""))
           (allDigits (string-append intPart fracPart))
           (decimalPlaces (string-length fracPart)))
        (digitsToScientific allDigits decimalPlaces negative)))

; Removes every space from a string.
(define (stripSpaces s) (list->string (remove-all #\space (string->list s))))

; Parses a plain decimal numeral string (e.g. "12345.6789", "-0.5", or
; "1 234" with incidental spaces) into an exact rational -- same
; digit-string approach as toScientificNotation, so no significant digit
; is ever lost to floating-point rounding.
(define (parseNumeralToRational rawS)
    (let* ((s (stripSpaces rawS))
           (negative (and (> (string-length s) 0) (eqv? (string-ref s 0) #\-)))
           (body (if negative (substring s 1 (string-length s)) s))
           (dotIdx (findStringCharPos #\. body 0))
           (intPart (if dotIdx (substring body 0 dotIdx) body))
           (fracPart (if dotIdx (substring body (+ dotIdx 1) (string-length body)) ""))
           (allDigits (string-append intPart fracPart))
           (decimalPlaces (string-length fracPart))
           (magnitude (/ (string->number allDigits) (expt 10 decimalPlaces))))
        (if negative (- magnitude) magnitude)))

; Parses either a plain decimal numeral or an already-formatted
; scientific-notation string ("m × 10^e", as produced by
; toScientificNotation/digitsToScientific) into an exact rational.
; Locates the mantissa/exponent split via the '×' character itself
; (rather than assuming a fixed offset from '^') so this works whether
; or not the surrounding spaces survived upstream processing -- e.g. an
; input already run through remove-all #\space, like "1.5×10^4".
(define (parseScientificToRational rawS)
    (let* ((s (stripSpaces rawS))
           (timesIdx (findStringCharPos #\× s 0)))
        (if timesIdx
            (let* ((mantissa (substring s 0 timesIdx))
                   (caretIdx (findStringCharPos #\^ s timesIdx))
                   (exponent (string->number (substring s (+ caretIdx 1) (string-length s)))))
                (* (parseNumeralToRational mantissa) (expt 10 exponent)))
            (parseNumeralToRational s))))

; Left-pads a digit string with zeros until it's at least minLen long
; (needed when an exact rational's magnitude is smaller than its own
; decimal-place count, e.g. 0.005 -> integer part "5", 3 decimal places
; -> needs padding to "005" before digitsToScientific can split it).
(define (padLeftZeros s minLen)
    (if (>= (string-length s) minLen)
        s
        (padLeftZeros (string-append "0" s) minLen)))

; Smallest k >= 0 such that r * 10^k is an integer. Always terminates
; for any r built purely from add/subtract/multiply starting from
; decimal numerals (the property this file's scientific-notation
; arithmetic relies on): such an r's reduced denominator only ever has 2
; and 5 as prime factors, so some power of 10 always clears it -- unlike
; division, which this file's arithmetic functions deliberately don't
; support, since a quotient like 1/3 has no terminating decimal form.
(define (decimalPlacesNeeded r)
    (let loop ((k 0))
        (if (integer? (* r (expt 10 k)))
            k
            (loop (+ k 1)))))

; Converts an exact rational into a normalized "m × 10^e" scientific
; string via the same exact digit-string path as toScientificNotation.
; Unlike the C++ engine's addScientific/subtractScientific/
; multiplyScientific (which operate on doubles and lose precision once
; the two operands' exponents are far apart, e.g. summing 1×10^20 and
; 1×10^-20 silently drops the smaller term entirely), this stays exact
; regardless of exponent spread, because r itself was computed with
; exact rational arithmetic by the caller.
(define (rationalToScientificNotation r)
    (let* ((negative (< r 0))
           (magnitude (abs r))
           (k (decimalPlacesNeeded magnitude))
           (digits (number->string (* magnitude (expt 10 k))))
           (allDigits (padLeftZeros digits k)))
        (digitsToScientific allDigits k negative)))

; Adds/subtracts/multiplies two numbers, each given as either a plain
; decimal numeral or an already-formatted "m × 10^e" scientific string,
; returning their exact result re-normalized to scientific notation.
; Mirror the C++ engine's addScientific/subtractScientific/
; multiplyScientific in purpose (arithmetic on values already in
; scientific form) but are exact rather than double-based -- see
; rationalToScientificNotation.
(define (addScientificNotation aChars bChars)
    (rationalToScientificNotation
        (+ (parseScientificToRational (list->string aChars))
           (parseScientificToRational (list->string bChars)))))

(define (subtractScientificNotation aChars bChars)
    (rationalToScientificNotation
        (- (parseScientificToRational (list->string aChars))
           (parseScientificToRational (list->string bChars)))))

(define (multiplyScientificNotation aChars bChars)
    (rationalToScientificNotation
        (* (parseScientificToRational (list->string aChars))
           (parseScientificToRational (list->string bChars)))))

; Finds the index of the ')' matching the '(' at openIdx in s.
(define (matchingParen s openIdx)
    (let loop ((i (+ openIdx 1)) (depth 1))
        (cond
            ((eqv? (string-ref s i) #\() (loop (+ i 1) (+ depth 1)))
            ((eqv? (string-ref s i) #\))
                (if (= depth 1) i (loop (+ i 1) (- depth 1))))
            ('t (loop (+ i 1) depth)))))

; Parses "log_BASE(ARG)=Y" into (list BASE ARG Y) as raw substrings
; (no further parsing of BASE/ARG/Y themselves at this stage).
(define (parseLogEq charL)
    (let* ((s (list->string (remove-all #\space charL)))
           (underscoreIdx (findStringCharPos #\_ s 0))
           (openParenIdx (findStringCharPos #\( s 0))
           (base (substring s (+ underscoreIdx 1) openParenIdx))
           (closeParenIdx (matchingParen s openParenIdx))
           (arg (substring s (+ openParenIdx 1) closeParenIdx))
           (eqIdx (findStringCharPos #\= s closeParenIdx))
           (y (substring s (+ eqIdx 1) (string-length s))))
        (list base arg y)))

; Converts "log_BASE(ARG)=Y" to "BASE^Y = ARG" -- matches the C++
; engine's `logtoexp` exactly.
(define (logToExp charL)
    (let* ((parsed (parseLogEq charL))
           (base (car parsed)) (arg (cadr parsed)) (y (caddr parsed)))
        (string-append base "^" y " = " arg)))

; Parses "BASE^EXPONENT=ARG" into (list BASE EXPONENT ARG), stripping
; one layer of parens from EXPONENT if present (e.g. "2^(x+1)=8" gives
; exponent "x+1", not "(x+1)").
(define (parseExpEq charL)
    (let* ((s (list->string (remove-all #\space charL)))
           (caretIdx (findStringCharPos #\^ s 0))
           (base (substring s 0 caretIdx))
           (eqIdx (findStringCharPos #\= s 0))
           (expRaw (substring s (+ caretIdx 1) eqIdx))
           (exp (if (and (> (string-length expRaw) 0)
                         (eqv? (string-ref expRaw 0) #\()
                         (eqv? (string-ref expRaw (- (string-length expRaw) 1)) #\)))
                     (substring expRaw 1 (- (string-length expRaw) 1))
                     expRaw))
           (arg (substring s (+ eqIdx 1) (string-length s))))
        (list base exp arg)))

; Converts "BASE^EXPONENT=ARG" to "log_BASE(ARG) = EXPONENT" -- matches
; the C++ engine's `exptolog` exactly.
(define (expToLog charL)
    (let* ((parsed (parseExpEq charL))
           (base (car parsed)) (exp (cadr parsed)) (arg (caddr parsed)))
        (string-append "log_" base "(" arg ") = " exp)))

; Finds an integer k (searched over -20..20, sufficient for textbook-
; level problems) such that base^k = value exactly.
(define (findExponentForValue base value)
    (let loop ((k -20))
        (cond
            ((> k 20) #f)
            ((= (expt base k) value) k)
            ('t (loop (+ k 1))))))

; Finds the position of the LAST top-level (paren-depth 0) occurrence of
; ch in s at or after startIdx, or #f if none found. "Top-level" means
; not nested inside the parens of, say, an exponent like "2^(x+1)" --
; the "+" in there must NOT match when looking for a constant added
; to/subtracted from the exponential term itself.
(define (findTopLevelCharPos ch s startIdx)
    (let loop ((i startIdx) (depth 0) (found #f))
        (cond
            ((>= i (string-length s)) found)
            ((eqv? (string-ref s i) #\() (loop (+ i 1) (+ depth 1) found))
            ((eqv? (string-ref s i) #\)) (loop (+ i 1) (- depth 1) found))
            ((and (= depth 0) (> i 0) (eqv? (string-ref s i) ch)) (loop (+ i 1) depth i))
            ('t (loop (+ i 1) depth found)))))

; Reduces an exponential equation string to the clean "base^exp=value"
; form parseExpEq/solveExponential expect, by stripping away an outer
; coefficient (parenthesized "coeff(base^exp [+-] const)" or bare
; "coeff*base^exp") and/or a trailing "+const"/"-const". Mirrors the
; equivalent C++ MathSymbol::solveExponential fix -- the original port
; here called parseExpEq directly, which finds the FIRST '^' and treats
; everything up to the next '=' as the WHOLE exponent. That silently
; misread "2^x+1=9" as "2^(x+1)=9" (giving the wrong answer x=2 instead
; of the correct x=3), and crashed outright on a leading coefficient
; like "5(2^x-3)=5" or "3*2^x=24" (parseExpEq's "base" substring would
; include the coefficient prefix, e.g. "5(2" or "3*2", neither a valid
; number, which (string->number ...) turns into #f and propagates into
; an arithmetic type error deep inside findExponentForValue).
(define (preprocessExpEq s)
    (let* ((eqPos (findStringCharPos #\= s 0))
           (left (substring s 0 eqPos))
           (right (substring s (+ eqPos 1) (string-length s)))
           (leftOpenParen (findStringCharPos #\( left 0)))
        (cond
            ; "coeff(inner)" where inner contains '^' and the paren spans
            ; to the very end of left -- divide right by coeff, recurse
            ; on the unwrapped inner expression.
            ((and (> (string-length left) 0) (char-numeric? (string-ref left 0))
                  leftOpenParen
                  (= (matchingParen left leftOpenParen) (- (string-length left) 1))
                  (findStringCharPos #\^ left leftOpenParen))
                (let* ((coeffStr (substring left 0 leftOpenParen))
                       (inner (substring left (+ leftOpenParen 1) (- (string-length left) 1)))
                       (coeff (string->number coeffStr))
                       (rightVal (string->number right)))
                    (preprocessExpEq (string-append inner "=" (number->string (/ rightVal coeff))))))
            ('t
                (let ((caretIdx (findStringCharPos #\^ left 0)))
                    (if (not caretIdx)
                        (string-append left "=" right)
                        (let ((multIdx (findTopLevelCharPos #\* left 0)))
                            (cond
                                ; "coeff*base^exp" -- if coeff is itself an
                                ; exact power of base, fold it into the
                                ; exponent; otherwise just divide both
                                ; sides by it (the far more common case).
                                ((and multIdx (< multIdx caretIdx))
                                    (let* ((coeffStr (substring left 0 multIdx))
                                           (rest (substring left (+ multIdx 1) (string-length left)))
                                           (coeff (string->number coeffStr))
                                           (caretInRest (findStringCharPos #\^ rest 0))
                                           (baseStr (substring rest 0 caretInRest))
                                           (expStr (substring rest (+ caretInRest 1) (string-length rest)))
                                           (base (string->number baseStr))
                                           (rightVal (string->number right))
                                           (k (findExponentForValue base coeff)))
                                        (if k
                                            (string-append baseStr "^(" expStr "+" (number->string k) ")=" (number->string rightVal))
                                            (string-append baseStr "^" expStr "=" (number->string (/ rightVal coeff))))))
                                ('t
                                    ; "base^exp +/- const" -- move the
                                    ; constant to the right side.
                                    (let ((plusIdx (findTopLevelCharPos #\+ left (+ caretIdx 1)))
                                          (minusIdx (findTopLevelCharPos #\- left (+ caretIdx 1))))
                                        (cond
                                            ((and plusIdx (or (not minusIdx) (> plusIdx minusIdx)))
                                                (let* ((expPart (substring left 0 plusIdx))
                                                       (constVal (string->number (substring left (+ plusIdx 1) (string-length left))))
                                                       (rightVal (string->number right)))
                                                    (string-append expPart "=" (number->string (- rightVal constVal)))))
                                            (minusIdx
                                                (let* ((expPart (substring left 0 minusIdx))
                                                       (constVal (string->number (substring left (+ minusIdx 1) (string-length left))))
                                                       (rightVal (string->number right)))
                                                    (string-append expPart "=" (number->string (+ rightVal constVal)))))
                                            ('t (string-append left "=" right)))))))))))))

; Solves "BASE^EXPONENT(x)=VALUE" by finding the integer k with
; base^k=value, then solving "EXPONENT(x) = k" for x via solvePoly.scm's
; solve (the exponent is itself an ordinary polynomial in x, e.g.
; "2x" or "x+1" -- this is what reduces an exponential equation to a
; linear one). Matches the C++ engine's `solveexp` exactly (after the
; preprocessExpEq normalization above, which both engines now need for
; the same reason -- see its comment).
(define (solveExponential charL)
    (let* ((rawStr (list->string (remove-all #\space charL)))
           (normalized (preprocessExpEq rawStr))
           (parsed (parseExpEq (string->list normalized)))
           (base (string->number (car parsed)))
           (expChars (string->list (cadr parsed)))
           (value (string->number (caddr parsed)))
           (k (findExponentForValue base value)))
        (if (not k)
            (list (string-append "No solution found (target value " (caddr parsed) " is not an integer power of " (car parsed) ")"))
            (solve (append expChars (string->list (string-append "=" (number->string k))))))))

; Solves "log_BASE(ARG(x))=Y" by computing VALUE=base^y, then solving
; "ARG(x) = VALUE" for x via solvePoly.scm's solve. Matches the C++
; engine's `solvelog` exactly.
(define (solveLogarithm charL)
    (let* ((parsed (parseLogEq charL))
           (base (string->number (car parsed)))
           (argChars (string->list (cadr parsed)))
           (y (string->number (caddr parsed)))
           (rhsValue (expt base y)))
        (solve (append argChars (string->list (string-append "=" (number->string rhsValue)))))))

; ---- Linear inequality solving ----
;
; The C++ engine's MathSymbol::solveInequality has confirmed real bugs
; (no CLI command exposes it; verified via a throwaway harness calling
; it directly): it does not flip the inequality direction when dividing
; by a negative coefficient (e.g. "-2x+3>7" should give x<-2, i.e.
; "(-∞, -2)", but it returns "(-2, ∞)"), and it doesn't distinguish
; strict from non-strict comparisons in its bracket notation (e.g.
; "3x>=9" should give the closed bracket "[3, ∞)" but it returns the
; open "(3, ∞)"). This file implements the mathematically correct
; version instead. Only linear (degree <= 1) inequalities are
; supported -- quadratic+ inequalities need interval sign analysis,
; which isn't implemented here.

; Finds the comparison operator (<, >, <=, or >=) in s, returning
; (list opSymbol startIdx endIdx).
(define (findInequalityOp s)
    (let loop ((i 0))
        (cond
            ((>= i (string-length s)) (error #f "solveInequality: no comparison operator found"))
            ((eqv? (string-ref s i) #\<)
                (if (and (< (+ i 1) (string-length s)) (eqv? (string-ref s (+ i 1)) #\=))
                    (list '<= i (+ i 2))
                    (list '< i (+ i 1))))
            ((eqv? (string-ref s i) #\>)
                (if (and (< (+ i 1) (string-length s)) (eqv? (string-ref s (+ i 1)) #\=))
                    (list '>= i (+ i 2))
                    (list '> i (+ i 1))))
            ('t (loop (+ i 1))))))

(define (flipIneqOp op)
    (cond ((eqv? op '<) '>) ((eqv? op '>) '<) ((eqv? op '<=) '>=) ((eqv? op '>=) '<=)))

(define (formatInterval op k)
    (let ((kStr (ratToString k)))
        (cond
            ((eqv? op '<) (string-append "(-∞, " kStr ")"))
            ((eqv? op '<=) (string-append "(-∞, " kStr "]"))
            ((eqv? op '>) (string-append "(" kStr ", ∞)"))
            ((eqv? op '>=) (string-append "[" kStr ", ∞)")))))

(define (boolOpHolds op lhs rhs)
    (cond
        ((eqv? op '<) (< lhs rhs))
        ((eqv? op '>) (> lhs rhs))
        ((eqv? op '<=) (<= lhs rhs))
        ((eqv? op '>=) (>= lhs rhs))))

; Top-level entry point: solves a linear inequality (e.g. "2x+3>7"),
; returning an interval-notation string.
(define (solveInequality charL)
    (let* ((s (list->string (remove-all #\space charL)))
           (opInfo (findInequalityOp s))
           (op (car opInfo)) (opStart (cadr opInfo)) (opEnd (caddr opInfo))
           (lhsChars (string->list (substring s 0 opStart)))
           (rhsChars (string->list (substring s opEnd (string-length s))))
           (lhsExpanded (expandSum (parseExpansion lhsChars)))
           (rhsExpanded (expandSum (parseExpansion rhsChars)))
           (combined (combineLikeTerms (append lhsExpanded (map negateTerm rhsExpanded))))
           (deg (polyDegree combined)))
        (if (> deg 1)
            (string-append "(inequality solving for degree " (number->string deg) " not yet supported)")
            (let* ((a (coeffAt combined 1)) (b (coeffAt combined 0)))
                (if (= a 0)
                    (if (boolOpHolds op b 0) "All real numbers" "No solution")
                    (let* ((k (/ (- b) a))
                           (effectiveOp (if (< a 0) (flipIneqOp op) op)))
                        (formatInterval effectiveOp k)))))))

; ---- canon (raw, unexpanded term canonicalization) ----
; canonicalize sorts a raw (unexpanded) sum's top-level terms by
; descending "raw degree" (computed WITHOUT multiplying anything out --
; see canonTermDegree below) then alphabetically by the term's own
; variable letters, and reprints each term's ORIGINAL substring
; unchanged -- unlike expand(), which always fully multiplies through
; and combines like terms first. Ported from the C++ engine's
; MathSymbol::canonicalize/calculateTermDegree (MathSymbol.cpp), a
; genuinely different command from `expand` with no prior Scheme port
; (confirmed absent from both the original MIT-Scheme source and this
; Chez port before now).
;
; Faithfully replicates one real quirk of C++'s calculateTermDegree
; rather than "fixing" it, since this is a display/sort heuristic, not
; a correctness-critical answer: it sums every variable's own exponent
; contribution found anywhere in a term (including inside nested
; parens), REGARDLESS of whether that variable is connected by
; multiplication or a '+'/'-' inside a parenthesized group -- e.g. the
; unexpanded content "(x+x^2)" is treated as degree 1+2=3, not the
; mathematically correct max(1,2)=2, because C++'s token scanner simply
; ignores +/- operators when summing degree contributions. This only
; affects degree-based SORT ORDER for terms with a sum inside an
; unexpanded parenthesized factor -- it never changes the reprinted
; text of any term, and normal implicit-multiplication cases (e.g.
; "(x+1)(x-2)", correctly degree 1+1=2, or "x^2y", correctly degree
; 2+1=3) are computed exactly right by the same summing rule, since
; degree of a product IS additive.
;
; The alphabetical tie-break is simplified relative to C++'s own
; multi-variable-token internals: this just collects every variable
; letter appearing anywhere in the term (sorted, duplicates allowed),
; which matches C++ for the single/dual-variable cases this engine's
; scope otherwise covers, without chasing its exact internal tie-break
; behavior for exotic multi-variable ties (a cosmetic, same-degree-only
; corner case).

; Splits s into raw (unexpanded) top-level +/- terms, each substring
; keeping its own leading sign character (except the very first term,
; which has none unless s itself starts with "-") -- same paren-depth-
; aware scanning approach as conicSections.scm's splitTopLevelSignedTerms,
; duplicated here rather than shared across files (matches this
; codebase's existing convention of small per-file helper copies, e.g.
; radicalRationalSolve.scm's own findStringCharPos).
(define (canonSplitTerms s)
    (let loop ((i 0) (start 0) (depth 0) (acc '()))
        (cond
            ((>= i (string-length s)) (reverse (cons (substring s start (string-length s)) acc)))
            ((eqv? (string-ref s i) #\() (loop (+ i 1) start (+ depth 1) acc))
            ((eqv? (string-ref s i) #\)) (loop (+ i 1) start (- depth 1) acc))
            ((and (> i start) (= depth 0) (or (eqv? (string-ref s i) #\+) (eqv? (string-ref s i) #\-)))
                (loop (+ i 1) i depth (cons (substring s start i) acc)))
            ('t (loop (+ i 1) start depth acc)))))

; Splits a term into (cons sign body), where sign is #\+, #\-, or #f
; (no baked-in sign -- only the term canonSplitTerms captured first,
; when the whole input didn't start with "-", has this) and body is
; the term with any sign stripped. Needed for reassembly, not just
; degree/variable analysis: a term's position after sorting generally
; differs from where canonSplitTerms found it, and this codebase's
; convention (like every other stringifier in this port) never shows
; an explicit leading "+" at position 0, but DOES require an explicit
; sign at every later position -- so the sign has to be re-derived
; from scratch at output time, not reused verbatim from the input.
(define (canonSignAndBody term)
    (if (and (> (string-length term) 0) (memv (string-ref term 0) (list #\+ #\-)))
        (cons (string-ref term 0) (substring term 1 (string-length term)))
        (cons #f term)))

; Reads an integer (possibly negative, if s(i) is "-") starting at
; index i; returns (cons value indexJustPastIt), or (cons 1 i) if
; there's no digit there at all (so callers can treat a bare
; variable/closing-paren with no explicit exponent as an implicit ^1).
(define (canonReadExponent s i)
    (let* ((neg (and (< i (string-length s)) (eqv? (string-ref s i) #\-)))
           (start (if neg (+ i 1) i)))
        (let loop ((j start))
            (if (and (< j (string-length s)) (char-numeric? (string-ref s j)))
                (loop (+ j 1))
                (if (= j start)
                    (cons 1 i)
                    (cons (* (if neg -1 1) (string->number (substring s start j))) j))))))

; Sums every variable's own exponent contribution anywhere in term
; (top-level or nested inside parens), ignoring +/-/* and bare
; coefficient digits -- see the section header above for why this
; intentionally does NOT distinguish addition from multiplication when
; degree-counting inside a paren group (faithfully matches C++).
(define (canonTermDegree term)
    (let loop ((i 0) (deg 0))
        (cond
            ((>= i (string-length term)) deg)
            ((eqv? (string-ref term i) #\()
                (let* ((close (matchingParen term i))
                       (insideDeg (canonTermDegree (substring term (+ i 1) close)))
                       (expAfter (if (and (< (+ close 1) (string-length term)) (eqv? (string-ref term (+ close 1)) #\^))
                                     (canonReadExponent term (+ close 2))
                                     (cons 1 (+ close 1)))))
                    (loop (cdr expAfter) (+ deg (* insideDeg (car expAfter))))))
            ((char-alphabetic? (string-ref term i))
                (let* ((afterVar (+ i 1))
                       (expAfter (if (and (< afterVar (string-length term)) (eqv? (string-ref term afterVar) #\^))
                                     (canonReadExponent term (+ afterVar 1))
                                     (cons 1 afterVar))))
                    (loop (cdr expAfter) (+ deg (car expAfter)))))
            ('t (loop (+ i 1) deg)))))

; Sorted (with duplicates) list of variable characters appearing
; anywhere in term (top-level or nested inside parens) -- used only to
; alphabetically tie-break terms of equal canonTermDegree.
(define (canonTermVarChars term)
    (let loop ((i 0) (vars '()))
        (cond
            ((>= i (string-length term)) vars)
            ((eqv? (string-ref term i) #\()
                (let ((close (matchingParen term i)))
                    (loop (+ close 1) (append (canonTermVarChars (substring term (+ i 1) close)) vars))))
            ((char-alphabetic? (string-ref term i))
                (loop (+ i 1) (cons (string-ref term i) vars)))
            ('t (loop (+ i 1) vars)))))

(define (canonTermVarString term)
    (list->string (sort char<? (canonTermVarChars term))))

; Sorts a raw (unexpanded) sum's top-level terms by descending degree,
; then alphabetically by variable letters, reprinting each term's
; original substring unchanged -- see section header for full scope/
; rationale. Matches the C++ engine's `canon` command.
(define (canonicalize charL)
    (let* ((s (stripSpaces (list->string charL)))
           (rawTerms (canonSplitTerms s))
           (annotated (map (lambda (term)
                                (let* ((sb (canonSignAndBody term))
                                       (sign (car sb)) (body (cdr sb)))
                                    (list sign body (canonTermDegree body) (canonTermVarString body))))
                            rawTerms))
           (sorted (sort (lambda (a b)
                             (cond
                                 ((> (caddr a) (caddr b)) #t)
                                 ((< (caddr a) (caddr b)) #f)
                                 ('t (string<? (cadddr a) (cadddr b)))))
                         annotated)))
        (let loop ((entries sorted) (first? 't) (acc ""))
            (cond
                ((null? entries) acc)
                ('t
                    (let* ((entry (car entries)) (sign (car entry)) (body (cadr entry))
                           (piece (if (eqv? first? 't)
                                      (if (eqv? sign #\-) (string-append "-" body) body)
                                      (string-append (if (eqv? sign #\-) "-" "+") body))))
                        (loop (cdr entries) 'f (string-append acc piece))))))))

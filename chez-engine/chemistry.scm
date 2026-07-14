; Chemical equation balancing, ported from the C++ engine's
; ChemicalReaction::balanceEquation. Requires only helperS.scm,
; mathHelp.scm, and basicmath.scm (for gcd/lcm) to be loaded first --
; entirely independent of the polynomial machinery elsewhere in this
; codebase.
;
; Ported from ../chemistry.scm (MIT Scheme) to Chez Scheme. Changes:
;   - Both (error "msg" irritant) call sites get an explicit #f who-arg
;     (Chez's error signature is (error who message . irritants)).
;   - sortByAtomicNumber: Chez's `sort` takes (pred list), the REVERSE of
;     MIT's (list pred) -- confirmed empirically by probing both orders
;     against the real binary (only (pred list) returned a sorted result).
;   - oxStatesBalance?: MIT's `every` is unbound in Chez; replaced with
;     `for-all`, which is Chez's/R6RS's name for the same operation
;     (verified identical behavior).
;   - list-head, list-tail, set-cdr!, gcd, lcm, denominator, quotient,
;     filter, char-upper-case? all verified present in Chez with matching
;     MIT-compatible signatures -- no changes needed for those.
;
; Approach: parse each compound's formula into an element->count map,
; build the element-by-compound matrix (reactant columns positive,
; product columns negated), and find a positive-integer vector in its
; null space via exact-rational Gaussian elimination -- this is the
; standard linear-algebra method for balancing equations, and is more
; robust than a small-integer brute-force search.
;
; This only balances equations with explicit products given (e.g.
; "C3H8 + O2 -> CO2 + H2O") -- it does NOT predict products from
; reactants alone (the C++ engine's reaction-type classifier --
; combustion/synthesis/decomposition/replacement/acid-base detection --
; is a separate, much fuzzier heuristic system not ported here).

; ---- Chemical formula parsing ----

; Merges count n for element sym into an (element . count) alist,
; adding to any existing entry for that element.
(define (addToCounts counts sym n)
    (let ((existing (assoc sym counts)))
        (if existing
            (begin (set-cdr! existing (+ (cdr existing) n)) counts)
            (append counts (list (cons sym n))))))

(define (scaleCounts counts mult)
    (map (lambda (p) (cons (car p) (* (cdr p) mult))) counts))

(define (mergeCounts counts newCounts)
    (let loop ((nc newCounts) (acc counts))
        (if (null? nc)
            acc
            (loop (cdr nc) (addToCounts acc (caar nc) (cdar nc))))))

; Parses the formula substring s[i..end) into an (element . count)
; alist, returning (cons countsAlist indexAfterFormula) -- stops at an
; unmatched ')' without consuming it, so the caller (recursing into a
; parenthesized group) can read the multiplier that follows.
(define (parseFormulaHelper s i end)
    (let loop ((i i) (counts '()))
        (cond
            ((>= i end) (cons counts i))
            ((eqv? (string-ref s i) #\()
                (let* ((innerResult (parseFormulaHelper s (+ i 1) end))
                       (innerCounts (car innerResult))
                       (afterInner (cdr innerResult))
                       (numEnd (let scanDigits ((j (+ afterInner 1)))
                                   (if (and (< j end) (char-numeric? (string-ref s j))) (scanDigits (+ j 1)) j)))
                       (mult (if (= numEnd (+ afterInner 1)) 1 (string->number (substring s (+ afterInner 1) numEnd)))))
                    (loop numEnd (mergeCounts counts (scaleCounts innerCounts mult)))))
            ((eqv? (string-ref s i) #\))
                (cons counts i))
            ((char-upper-case? (string-ref s i))
                (let* ((symEnd (if (and (< (+ i 1) end) (char-lower-case? (string-ref s (+ i 1)))) (+ i 2) (+ i 1)))
                       (sym (substring s i symEnd))
                       (numEnd (let scanDigits ((j symEnd)) (if (and (< j end) (char-numeric? (string-ref s j))) (scanDigits (+ j 1)) j)))
                       (count (if (= numEnd symEnd) 1 (string->number (substring s symEnd numEnd)))))
                    (loop numEnd (addToCounts counts sym count))))
            ('t (error #f "parseFormula: unexpected character" (string-ref s i))))))

; Top-level formula parser, e.g. "Al2(SO4)3" -> (("Al" . 2) ("S" . 3) ("O" . 12)).
(define (parseFormula s) (car (parseFormulaHelper s 0 (string-length s))))

; ---- Equation string splitting ----

(define (trimSpaces s)
    (let* ((len (string-length s))
           (start (let loop ((i 0)) (if (and (< i len) (eqv? (string-ref s i) #\space)) (loop (+ i 1)) i)))
           (end (let loop ((i len)) (if (and (> i start) (eqv? (string-ref s (- i 1)) #\space)) (loop (- i 1)) i))))
        (substring s start end)))

(define (splitOnChar s ch)
    (let loop ((i 0) (start 0) (acc '()))
        (cond
            ((>= i (string-length s)) (reverse (cons (trimSpaces (substring s start i)) acc)))
            ((eqv? (string-ref s i) ch) (loop (+ i 1) (+ i 1) (cons (trimSpaces (substring s start i)) acc)))
            ('t (loop (+ i 1) start acc)))))

(define (findSubstring s sub idx)
    (let ((slen (string-length s)) (sublen (string-length sub)))
        (let loop ((i idx))
            (cond
                ((> (+ i sublen) slen) #f)
                ((string=? (substring s i (+ i sublen)) sub) i)
                ('t (loop (+ i 1)))))))

; Splits "A + B -> C + D" into (list (A B) (C D)) -- accepts either
; "->" or the unicode "→" as the arrow, and "+" to separate compounds
; on each side. If no arrow is found, returns (list (A B ...) '())
; (no products given).
(define (splitEquation s)
    (let* ((arrowIdx (or (findSubstring s "->" 0) (findSubstring s "→" 0))))
        (if (not arrowIdx)
            (list (splitOnChar s #\+) '())
            (let* ((arrowLen (if (findSubstring s "->" 0) 2 1))
                   (lhs (substring s 0 arrowIdx))
                   (rhs (substring s (+ arrowIdx arrowLen) (string-length s))))
                (list (splitOnChar lhs #\+) (splitOnChar rhs #\+))))))

; ---- Element-by-compound matrix and Gaussian elimination ----

; All unique element symbols appearing across a list of formula
; strings, in first-appearance order.
(define (allElements formulas)
    (let loop ((fs formulas) (acc '()))
        (if (null? fs)
            acc
            (loop (cdr fs)
                  (let elloop ((els (parseFormula (car fs))) (acc acc))
                      (if (null? els)
                          acc
                          (elloop (cdr els) (if (member (caar els) acc) acc (append acc (list (caar els)))))))))))

; Element x compound matrix: one row per element, one column per
; compound (reactants then products), reactant entries positive,
; product entries negated -- a balanced equation is exactly a positive
; integer vector x with matrix*x = 0.
(define (buildMatrix reactantFormulas productFormulas elements)
    (let* ((reactantCounts (map parseFormula reactantFormulas))
           (productCounts (map parseFormula productFormulas)))
        (map (lambda (el)
                 (append
                     (map (lambda (counts) (let ((p (assoc el counts))) (if p (cdr p) 0))) reactantCounts)
                     (map (lambda (counts) (let ((p (assoc el counts))) (- (if p (cdr p) 0)))) productCounts)))
             elements)))

(define (numRows m) (length m))
(define (numCols m) (if (null? m) 0 (length (car m))))
(define (getRow m i) (list-ref m i))
(define (getEntry m i j) (list-ref (list-ref m i) j))
(define (setRow m i newRow)
    (let ((v (list->vector m))) (vector-set! v i newRow) (vector->list v)))
(define (rowSwap m i j)
    (let ((v (list->vector m)) (tmp #f))
        (set! tmp (vector-ref v i))
        (vector-set! v i (vector-ref v j))
        (vector-set! v j tmp)
        (vector->list v)))
(define (rowScale row factor) (map (lambda (x) (* x factor)) row))
(define (rowSub row1 row2) (map - row1 row2))
(define (range n) (let loop ((i 0) (acc '())) (if (>= i n) (reverse acc) (loop (+ i 1) (cons i acc)))))

; Reduces matrix m to reduced row echelon form using exact rational
; arithmetic. Returns (cons rrefMatrix pivotColumnsInRowOrder).
(define (rref m)
    (let ((rows (numRows m)) (cols (numCols m)))
        (let loop ((mat m) (pivotRow 0) (col 0) (pivotCols '()))
            (cond
                ((or (>= pivotRow rows) (>= col cols)) (cons mat (reverse pivotCols)))
                ('t
                    (let ((sel (let findNonzero ((r pivotRow))
                                   (cond
                                       ((>= r rows) #f)
                                       ((not (= 0 (getEntry mat r col))) r)
                                       ('t (findNonzero (+ r 1)))))))
                        (if (not sel)
                            (loop mat pivotRow (+ col 1) pivotCols)
                            (let* ((mat (if (= sel pivotRow) mat (rowSwap mat pivotRow sel)))
                                   (pivotVal (getEntry mat pivotRow col))
                                   (mat (setRow mat pivotRow (rowScale (getRow mat pivotRow) (/ 1 pivotVal))))
                                   (mat (let elimLoop ((r 0) (mat mat))
                                            (if (>= r rows)
                                                mat
                                                (if (= r pivotRow)
                                                    (elimLoop (+ r 1) mat)
                                                    (let ((factor (getEntry mat r col)))
                                                        (if (= factor 0)
                                                            (elimLoop (+ r 1) mat)
                                                            (elimLoop (+ r 1) (setRow mat r (rowSub (getRow mat r) (rowScale (getRow mat pivotRow) factor)))))))))))
                                (loop mat (+ pivotRow 1) (+ col 1) (cons col pivotCols))))))))))

; Extracts the null-space vector from an RREF'd matrix, assuming
; exactly one free (non-pivot) column -- the typical case for a
; well-posed, uniquely-balanceable equation. Sets the free variable to
; 1 and back-substitutes the pivot variables from the RREF rows.
(define (nullSpaceVector rrefMat pivotCols totalCols)
    (let* ((freeCols (filter (lambda (c) (not (member c pivotCols))) (range totalCols))))
        (if (not (= (length freeCols) 1))
            (error #f "balanceEquation: equation is underdetermined or inconsistent (expected exactly one degree of freedom, found)" (length freeCols))
            (let* ((freeCol (car freeCols))
                   (solution (make-vector totalCols 0)))
                (vector-set! solution freeCol 1)
                (for-each
                    (lambda (pc rowIdx) (vector-set! solution pc (- (getEntry rrefMat rowIdx freeCol))))
                    pivotCols (range (length pivotCols)))
                (vector->list solution)))))

(define (lcmL lst) (apply lcm lst))

; Scales an exact-rational null-space vector to the smallest positive
; integer solution: clear denominators via their LCM, then divide by
; the GCD of the resulting integers, flipping sign if needed.
(define (normalizeToIntegers vec)
    (let* ((denoms (map denominator vec))
           (commonDenom (lcmL denoms))
           (scaled (map (lambda (x) (* x commonDenom)) vec))
           (g (apply gcd (map abs scaled)))
           (result (map (lambda (x) (/ x g)) scaled)))
        (if (< (car result) 0) (map - result) result)))

; Finds the balancing coefficients for the given reactant and product
; formula lists, in that combined order.
(define (balanceFormulas reactantFormulas productFormulas)
    (let* ((elements (allElements (append reactantFormulas productFormulas)))
           (matrix (buildMatrix reactantFormulas productFormulas elements))
           (rrefResult (rref matrix))
           (rrefMat (car rrefResult)) (pivotCols (cdr rrefResult))
           (totalCols (+ (length reactantFormulas) (length productFormulas)))
           (nullVec (nullSpaceVector rrefMat pivotCols totalCols)))
        (normalizeToIntegers nullVec)))

; ---- Formatting and top-level entry point ----

(define (formatCompound coeff formula)
    (if (= coeff 1) formula (string-append (number->string coeff) formula)))

(define (joinWithPlus formulaList coeffs)
    (let loop ((fs formulaList) (cs coeffs) (acc ""))
        (cond
            ((null? fs) acc)
            ((string=? acc "") (loop (cdr fs) (cdr cs) (formatCompound (car cs) (car fs))))
            ('t (loop (cdr fs) (cdr cs) (string-append acc " + " (formatCompound (car cs) (car fs))))))))

; Top-level entry point: balances a chemical equation given as a
; string with explicit products, e.g. "C3H8 + O2 -> CO2 + H2O" ->
; "C3H8 + 5O2 → 3CO2 + 4H2O".
(define (balanceEquation eqStr)
    (let* ((parts (splitEquation eqStr))
           (reactants (car parts)) (products (cadr parts)))
        (if (null? products)
            "Error: balanceEquation requires explicit products (e.g. \"A + B -> C + D\"); product prediction is not supported"
            (let* ((coeffs (balanceFormulas reactants products))
                   (rCoeffs (list-head coeffs (length reactants)))
                   (pCoeffs (list-tail coeffs (length reactants))))
                (string-append (joinWithPlus reactants rCoeffs) " → " (joinWithPlus products pCoeffs))))))

; ---- Oxidation state calculation ----
;
; Ported from ChemicalReaction::getKnownOxidationState/
; calculateOxidationStates/formatOxidationStates. Element symbol ->
; atomic number table copied directly from the C++ source's
; ELEMENT_TO_NUMBER map, needed only to match its output ordering
; (elements are listed by atomic number, e.g. "KMnO4" prints
; "O4: -2, K: +1, Mn: +7" -- O(8) before K(19) before Mn(25) -- not
; formula order or alphabetical order).

(define atomicNumbers '(
    ("H" . 1) ("He" . 2) ("Li" . 3) ("Be" . 4) ("B" . 5) ("C" . 6) ("N" . 7) ("O" . 8) ("F" . 9) ("Ne" . 10)
    ("Na" . 11) ("Mg" . 12) ("Al" . 13) ("Si" . 14) ("P" . 15) ("S" . 16) ("Cl" . 17) ("Ar" . 18) ("K" . 19) ("Ca" . 20)
    ("Sc" . 21) ("Ti" . 22) ("V" . 23) ("Cr" . 24) ("Mn" . 25) ("Fe" . 26) ("Co" . 27) ("Ni" . 28) ("Cu" . 29) ("Zn" . 30)
    ("Ga" . 31) ("Ge" . 32) ("As" . 33) ("Se" . 34) ("Br" . 35) ("Kr" . 36) ("Rb" . 37) ("Sr" . 38) ("Y" . 39) ("Zr" . 40)
    ("Nb" . 41) ("Mo" . 42) ("Tc" . 43) ("Ru" . 44) ("Rh" . 45) ("Pd" . 46) ("Ag" . 47) ("Cd" . 48) ("In" . 49) ("Sn" . 50)
    ("Sb" . 51) ("Te" . 52) ("I" . 53) ("Xe" . 54) ("Cs" . 55) ("Ba" . 56) ("La" . 57) ("Ce" . 58) ("Pr" . 59) ("Nd" . 60)
    ("Pm" . 61) ("Sm" . 62) ("Eu" . 63) ("Gd" . 64) ("Tb" . 65) ("Dy" . 66) ("Ho" . 67) ("Er" . 68) ("Tm" . 69) ("Yb" . 70)
    ("Lu" . 71) ("Hf" . 72) ("Ta" . 73) ("W" . 74) ("Re" . 75) ("Os" . 76) ("Ir" . 77) ("Pt" . 78) ("Au" . 79) ("Hg" . 80)
    ("Tl" . 81) ("Pb" . 82) ("Bi" . 83) ("Po" . 84) ("At" . 85) ("Rn" . 86) ("Fr" . 87) ("Ra" . 88) ("Ac" . 89) ("Th" . 90)
    ("Pa" . 91) ("U" . 92) ("Np" . 93) ("Pu" . 94) ("Am" . 95) ("Cm" . 96) ("Bk" . 97) ("Cf" . 98) ("Es" . 99) ("Fm" . 100)
    ("Md" . 101) ("No" . 102) ("Lr" . 103) ("Rf" . 104) ("Db" . 105) ("Sg" . 106) ("Bh" . 107) ("Hs" . 108) ("Mt" . 109) ("Ds" . 110)
    ("Rg" . 111) ("Cn" . 112) ("Nh" . 113) ("Fl" . 114) ("Mc" . 115) ("Lv" . 116) ("Ts" . 117) ("Og" . 118)))

(define (atomicNumberOf sym) (let ((p (assoc sym atomicNumbers))) (if p (cdr p) 999)))

(define nonmetalSymbols '("H" "C" "N" "O" "P" "S" "Se" "F" "Cl" "Br" "I" "He" "Ne" "Ar" "Kr" "Xe" "Rn"))
(define (isMetalSym sym) (not (member sym nonmetalSymbols)))
(define halogenSymbols '("F" "Cl" "Br" "I" "At"))
(define (isHalogenSym sym) (and (member sym halogenSymbols) 't))
(define alkaliMetalSymbols '("Li" "Na" "K" "Rb" "Cs" "Fr"))
(define alkalineEarthSymbols '("Be" "Mg" "Ca" "Sr" "Ba" "Ra"))

(define (existsInList pred lst)
    (cond ((null? lst) #f) ((pred (car lst)) #t) ('t (existsInList pred (cdr lst)))))

; Returns the fixed/known oxidation state for element sym within
; compoundCounts (an (element . count) alist), or #f if it must be
; calculated via the charge-balance rule instead.
(define (knownOxidationState sym compoundCounts)
    (cond
        ((string=? sym "F") -1)
        ((string=? sym "O") (if (assoc "F" compoundCounts) 2 -2))
        ((string=? sym "H")
            (let* ((others (filter (lambda (p) (not (string=? (car p) "H"))) compoundCounts))
                   (onlyMetal (and (= (length others) 1) (isMetalSym (car (car others))))))
                (if (and onlyMetal (= (length compoundCounts) 2)) -1 1)))
        ((member sym alkaliMetalSymbols) 1)
        ((member sym alkalineEarthSymbols) 2)
        ((and (isHalogenSym sym) (not (string=? sym "F")))
            (if (existsInList (lambda (p) (isMetalSym (car p))) compoundCounts) -1 #f))
        ((string=? sym "Al") 3)
        ((string=? sym "Zn") 2)
        ('t #f)))

; Runs the known/unknown-balancing pass once. forceUnknownSym, if given
; (not #f), is a symbol whose otherwise-fixed rule (from
; knownOxidationState) is ignored, so it gets re-derived from the
; charge-balance equation instead -- used to correct oxygen's default
; -2 rule for peroxides/superoxides (see calculateOxidationStates).
(define (oxidationPass compoundCounts totalCharge forceUnknownSym)
    (let loop ((items compoundCounts) (known '()) (knownSum 0) (unknowns '()))
        (if (null? items)
            (cond
                ((= (length unknowns) 1)
                    (let* ((u (car unknowns)) (sym (car u)) (cnt (cdr u))
                           (neededSum (- totalCharge knownSum))
                           (oxState (quotient neededSum cnt)))
                        (append known (list (cons sym oxState)))))
                ((null? unknowns) known)
                ('t
                    (append known
                        (map (lambda (u) (cons (car u) (if (isMetalSym (car u)) 1 -1))) unknowns))))
            (let* ((sym (caar items)) (cnt (cdar items))
                   (ox (if (and forceUnknownSym (string=? sym forceUnknownSym))
                           #f
                           (knownOxidationState sym compoundCounts))))
                (if ox
                    (loop (cdr items) (append known (list (cons sym ox))) (+ knownSum (* ox cnt)) unknowns)
                    (loop (cdr items) known knownSum (append unknowns (list (cons sym cnt)))))))))

(define (oxStatesBalance? compoundCounts oxStates totalCharge)
    (and (for-all (lambda (item) (assoc (car item) oxStates)) compoundCounts)
         (= totalCharge (apply + (map (lambda (item) (* (cdr (assoc (car item) oxStates)) (cdr item))) compoundCounts)))))

; Assigns oxidation states to every element in compoundCounts (see
; oxidationPass for the core known/unknown-balancing algorithm). If the
; default fixed-rule pass doesn't actually balance to totalCharge --
; this happens for peroxides/superoxides like H2O2 or KO2, where
; oxygen's normal -2 default rule conflicts with the other elements'
; own fixed rules -- retries with oxygen forced to be derived from the
; balance equation instead of its default.
(define (calculateOxidationStates compoundCounts totalCharge)
    (if (= (length compoundCounts) 1)
        (list (cons (caar compoundCounts) 0))
        (let ((firstPass (oxidationPass compoundCounts totalCharge #f)))
            (if (and (assoc "O" compoundCounts) (not (oxStatesBalance? compoundCounts firstPass totalCharge)))
                (oxidationPass compoundCounts totalCharge "O")
                firstPass))))

; NOTE: Chez's sort takes (pred list) -- the REVERSE of MIT's (list pred).
(define (sortByAtomicNumber counts)
    (sort (lambda (a b) (< (atomicNumberOf (car a)) (atomicNumberOf (car b)))) counts))

(define (formatOxidationStates orderedCounts oxStates)
    (let loop ((items orderedCounts) (acc "") (first #t))
        (if (null? items)
            acc
            (let* ((sym (caar items)) (cnt (cdar items))
                   (ox (cdr (assoc sym oxStates)))
                   (piece (string-append sym (if (> cnt 1) (number->string cnt) "") ": " (if (> ox 0) "+" "") (number->string ox))))
                (loop (cdr items) (string-append acc (if first "" ", ") piece) #f)))))

; Top-level entry point: shows oxidation states for a (neutral, charge
; 0) compound formula, e.g. "H2SO4" -> "H2SO4: H2: +1, O4: -2, S: +6".
(define (oxidationStates formula)
    (let* ((counts (parseFormula formula))
           (ordered (sortByAtomicNumber counts))
           (oxStates (calculateOxidationStates counts 0)))
        (string-append formula ": " (formatOxidationStates ordered oxStates))))

; ---- Net ionic equations ----
;
; Ported from ChemicalReaction::netIonicEquation. Supports the two
; common double-replacement cases: precipitation (one product is
; insoluble, becomes the net ionic reaction; the other product's ions
; are spectators and dropped) and acid-base neutralization (H+ + OH-
; -> H2O). Does not predict combustion/synthesis/single-replacement
; products -- only double-replacement and acid-base, which is what
; netIonicEquation is actually for.

(define polyatomicIons '(
    ("C2H3O2" . -1)
    ("NO3" . -1)
    ("SO4" . -2)
    ("CO3" . -2)
    ("PO4" . -3)
    ("NH4" . 1)
    ("OH" . -1)))

(define (detectPolyatomicIon formula)
    (let loop ((ions polyatomicIons))
        (cond
            ((null? ions) #f)
            ((findSubstring formula (caar ions) 0) (cons (caar ions) (findSubstring formula (caar ions) 0)))
            ('t (loop (cdr ions))))))

(define (findFirst pred lst)
    (cond ((null? lst) #f) ((pred (car lst)) (car lst)) ('t (findFirst pred (cdr lst)))))

; Parses a leading element-symbol+count substring, e.g. "Ba" -> ("Ba" 1), "Na2" -> ("Na" 2).
(define (parseLeadingElement s)
    (let* ((symEnd (if (and (> (string-length s) 1) (char-lower-case? (string-ref s 1))) 2 1))
           (sym (substring s 0 symEnd))
           (numEnd (let scanDigits ((j symEnd)) (if (and (< j (string-length s)) (char-numeric? (string-ref s j))) (scanDigits (+ j 1)) j)))
           (count (if (= numEnd symEnd) 1 (string->number (substring s symEnd numEnd)))))
        (list sym count)))

; Splits a non-acid ionic compound formula into (list cationSym
; cationCount anionSym anionCount), where anionSym/cationSym may be a
; polyatomic ion name or a single element symbol. Acids (formulas
; starting with H, handled by splitAcidFormula below) go through a
; separate path since H isn't a metal and so isn't found by
; splitBinaryIonic's plain isMetalSym scan.
(define (splitIonicCompound formula)
    (let ((poly (detectPolyatomicIon formula)))
        (if poly
            (splitWithPolyatomic formula poly)
            (splitBinaryIonic formula))))

(define (splitWithPolyatomic formula poly)
    (let* ((ionName (car poly))
           (startIdx (cdr poly))
           (precededByParen (and (> startIdx 0) (eqv? (string-ref formula (- startIdx 1)) #\( )))
           (cationEnd (if precededByParen (- startIdx 1) startIdx))
           (cationStr (substring formula 0 cationEnd))
           (afterIon (+ startIdx (string-length ionName)))
           (followedByCloseParen (and (< afterIon (string-length formula)) (eqv? (string-ref formula afterIon) #\) )))
           (countStart (if followedByCloseParen (+ afterIon 1) afterIon))
           (numEnd (let scanDigits ((j countStart)) (if (and (< j (string-length formula)) (char-numeric? (string-ref formula j))) (scanDigits (+ j 1)) j)))
           (anionCount (if (= numEnd countStart) 1 (string->number (substring formula countStart numEnd))))
           (cation (parseLeadingElement cationStr)))
        (list (car cation) (cadr cation) ionName anionCount)))

(define (splitBinaryIonic formula)
    (let* ((counts (parseFormula formula))
           (cationPair (findFirst (lambda (p) (isMetalSym (car p))) counts))
           (anionPair (findFirst (lambda (p) (not (isMetalSym (car p)))) counts)))
        (list (car cationPair) (cdr cationPair) (car anionPair) (cdr anionPair))))

; Splits an acid formula like "HCl" or "H2SO4" into (list "H" hCount anionSym anionCount).
(define (splitAcidFormula formula)
    (let* ((rest (substring formula 1 (string-length formula)))
           (numEnd (let scanDigits ((j 0)) (if (and (< j (string-length rest)) (char-numeric? (string-ref rest j))) (scanDigits (+ j 1)) j)))
           (hCount (if (= numEnd 0) 1 (string->number (substring rest 0 numEnd))))
           (anionStr (substring rest numEnd (string-length rest)))
           (poly (detectPolyatomicIon anionStr)))
        (if poly
            (list "H" hCount (car poly) 1)
            (let ((counts (parseFormula anionStr)))
                (list "H" hCount (caar counts) (cdar counts))))))

(define fixedCationCharges '(("Ag" . 1) ("Zn" . 2) ("Al" . 3) ("Pb" . 2) ("Cd" . 2)))

(define (anionChargeOf anionSym)
    (cond
        ((assoc anionSym polyatomicIons) (cdr (assoc anionSym polyatomicIons)))
        ((string=? anionSym "O") -2)
        ((string=? anionSym "S") -2)
        ((member anionSym halogenSymbols) -1)
        ('t -1)))

; Most cation charges are fixed by element/group; anything else is
; inferred from charge balance with the (already-known) anion charge,
; the same approach knownOxidationState/calculateOxidationStates use.
(define (cationChargeOf cationSym cationCount anionSym anionCount)
    (cond
        ((string=? cationSym "H") 1)
        ((string=? cationSym "NH4") 1)
        ((member cationSym alkaliMetalSymbols) 1)
        ((member cationSym alkalineEarthSymbols) 2)
        ((assoc cationSym fixedCationCharges) (cdr (assoc cationSym fixedCationCharges)))
        ('t (quotient (- (* anionCount (anionChargeOf anionSym))) cationCount))))

; Full ion-split including inferred charges: returns (list cationSym
; cationCount anionSym anionCount cationCharge anionCharge).
(define (splitIonicCompoundFull formula)
    (let* ((base (if (and (>= (string-length formula) 1) (eqv? (string-ref formula 0) #\H) (not (string=? formula "H2O")))
                      (splitAcidFormula formula)
                      (splitIonicCompound formula)))
           (cationSym (car base)) (cationCount (cadr base)) (anionSym (caddr base)) (anionCount (cadddr base))
           (anionCh (anionChargeOf anionSym))
           (cationCh (cationChargeOf cationSym cationCount anionSym anionCount)))
        (list cationSym cationCount anionSym anionCount cationCh anionCh)))

(define insolubleHalideCations '("Ag" "Pb" "Hg"))
(define insolubleSulfateCations '("Ba" "Pb" "Ca" "Sr"))
(define solubleHydroxideCations '("Li" "Na" "K" "Rb" "Cs" "Ba" "Sr"))

; Standard solubility rules, applied uniformly regardless of whether
; the anion is a polyatomic ion or a single atom (see the file header
; comment about the C++ engine's inconsistency here for sulfide).
(define (isSolubleCompound cationSym anionSym)
    (cond
        ((member cationSym alkaliMetalSymbols) #t)
        ((string=? cationSym "NH4") #t)
        ((string=? anionSym "NO3") #t)
        ((string=? anionSym "C2H3O2") #t)
        ((member anionSym halogenSymbols) (not (member cationSym insolubleHalideCations)))
        ((string=? anionSym "SO4") (not (member cationSym insolubleSulfateCations)))
        ((string=? anionSym "CO3") #f)
        ((string=? anionSym "PO4") #f)
        ((string=? anionSym "OH") (and (member cationSym solubleHydroxideCations) #t))
        ((string=? anionSym "S") (or (member cationSym alkaliMetalSymbols) (member cationSym alkalineEarthSymbols)))
        ('t #t)))

(define superscriptDigits '((1 . "") (2 . "²") (3 . "³") (4 . "⁴")))
(define (chargeSuperscript charge)
    (let* ((mag (abs charge))
           (digitStr (cdr (assoc mag superscriptDigits)))
           (sign (if (> charge 0) "⁺" "⁻")))
        (string-append digitStr sign)))

; Builds the simplest charge-balanced neutral formula string for
; cation+anion (e.g. Pb 2+ & S 2- -> "PbS"; Fe 3+ & OH 1- -> "Fe(OH)3";
; Ag 1+ & PO4 3- -> "Ag3PO4"). Returns (list formulaStr cationCount anionCount).
(define (buildNeutralFormula cationSym cationCharge anionSym anionCharge)
    (let* ((a (abs cationCharge)) (b (abs anionCharge)) (g (gcd a b))
           (cCount (/ b g)) (aCount (/ a g))
           (anionNeedsParen (and (> aCount 1) (assoc anionSym polyatomicIons)))
           (cationPart (string-append cationSym (if (> cCount 1) (number->string cCount) "")))
           (anionPart (if anionNeedsParen
                           (string-append "(" anionSym ")" (number->string aCount))
                           (string-append anionSym (if (> aCount 1) (number->string aCount) "")))))
        (list (string-append cationPart anionPart) cCount aCount)))

(define (formatAqIon coeff sym charge)
    (string-append (if (= coeff 1) "" (number->string coeff)) sym (chargeSuperscript charge) "(aq)"))

(define (formatPrecipitateNetIonic cationSym cationCharge anionSym anionCharge)
    (let* ((built (buildNeutralFormula cationSym cationCharge anionSym anionCharge))
           (formulaStr (car built)) (cCount (cadr built)) (aCount (caddr built)))
        (string-append
            (formatAqIon cCount cationSym cationCharge) " + " (formatAqIon aCount anionSym anionCharge)
            " → " formulaStr "(s)")))

; H+ + OH- -> H2O, scaled to the smallest whole-number coefficients
; that balance H+ against OH- (their LCM): e.g. for KOH+H2SO4 (1 OH
; per KOH, 2 H per H2SO4), n=lcm(1,2)=2, giving "2OH- + 2H+ -> 2H2O".
(define (formatAcidBase hPerUnit ohPerUnit)
    (let ((n (lcm hPerUnit ohPerUnit)))
        (string-append
            (formatAqIon n "OH" -1) " + " (formatAqIon n "H" 1)
            " → " (if (= n 1) "" (number->string n)) "H2O(l)")))

; Top-level entry point: derives the net ionic equation for a
; double-replacement (precipitation) or acid-base reaction between two
; reactant formulas, e.g. "AgNO3 + NaCl" -> "Ag⁺(aq) + Cl⁻(aq) →
; AgCl(s)". Returns " → " (no reaction) if neither possible product is
; insoluble and it isn't an acid-base pair.
(define (netIonicEquation eqStr)
    (let* ((parts (splitEquation eqStr))
           (reactants (car parts)))
        (if (not (= (length reactants) 2))
            "Error: netIonicEquation expects exactly two reactants"
            (let* ((s1 (splitIonicCompoundFull (car reactants)))
                   (s2 (splitIonicCompoundFull (cadr reactants)))
                   (cat1 (list-ref s1 0)) (catCount1 (list-ref s1 1)) (an1 (list-ref s1 2)) (anCount1 (list-ref s1 3)) (catCh1 (list-ref s1 4)) (anCh1 (list-ref s1 5))
                   (cat2 (list-ref s2 0)) (catCount2 (list-ref s2 1)) (an2 (list-ref s2 2)) (anCount2 (list-ref s2 3)) (catCh2 (list-ref s2 4)) (anCh2 (list-ref s2 5)))
                (cond
                    ((and (string=? cat1 "H") (string=? an2 "OH")) (formatAcidBase (* catCount1 anCount1) (* catCount2 anCount2)))
                    ((and (string=? cat2 "H") (string=? an1 "OH")) (formatAcidBase (* catCount2 anCount2) (* catCount1 anCount1)))
                    ('t
                        (let ((prod1Soluble (isSolubleCompound cat1 an2))
                              (prod2Soluble (isSolubleCompound cat2 an1)))
                            (cond
                                ((not prod1Soluble) (formatPrecipitateNetIonic cat1 catCh1 an2 anCh2))
                                ((not prod2Soluble) (formatPrecipitateNetIonic cat2 catCh2 an1 anCh1))
                                ('t " → ")))))))))

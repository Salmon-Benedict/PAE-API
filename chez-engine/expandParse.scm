; Parsing AND expansion for general polynomial *expansion* expressions
; -- the same breadth of input the C++ Poly engine's tokenizer/parser
; accepts: sums and products of terms and arbitrarily nested
; parenthesized groups, with implicit or explicit multiplication and
; integer exponents on any group. E.g.:
;   (x+1)(x+2)         (x+1)*(x+2)         (x+1)^2
;   ((x+1)+2)           (x+(y+1))           (x*(y+1))
;   (2*(x+1))           ((2x+1)+(3x+2))
;   ((x+1)^2)*((x+2)^2)   (((x+y)+(a+b))^2)
;
; Grammar (structuring only, see below for the actual expansion):
;   Sum     ::= ['+'|'-'] Product (('+'|'-') Product)*
;   Product ::= Factor (['*'|'/'] Factor)*   ; implicit/explicit multiply, explicit divide
;   Factor  ::= '(' Sum ')' ['^' nonNegInt]  |  Term
;   Term    ::= [coefficient] [variable ['^' exponent]]   ; same shapes as singleR
;   exponent ::= [nonNegInt] | '-' nonNegInt | '(' <constant expr> ')'
;
; Ported from ../expandParse.scm (MIT Scheme) to Chez Scheme. Changes:
;   - Both define-record-type forms (<group>, <addend>) rewritten in
;     Chez's R6RS clause-based syntax (see recordPoly2.scm's port notes for
;     why -- Chez's top-level define-record-type binding is R6RS's clause
;     form, not R7RS's positional form).
;   - sumToString's #!optional first -> case-lambda.
;   - All 6 (error "msg" ...) call sites get an explicit #f who-arg.
;   - Both `sort` calls get their arguments swapped: Chez's sort is
;     (pred list), the reverse of MIT's (list pred) -- see chemistry.scm's
;     port notes, same fix.
;   - `any` (readParenPower) -> `exists`, Chez's/R6RS's name for the same
;     operation (any is unbound in Chez, confirmed empirically, same
;     pattern as every/for-all in chemistry.scm).
;
; A variable's own exponent (not a group's) can be negative and/or
; fractional -- x^-2, x^(1/2), x^(-3/4) -- via readTokenPower below,
; which evaluates a parenthesized exponent expression down to a plain
; rational at parse time. A group's exponent stays a plain nonnegative
; integer (expandPower raises it via literal repeated self-
; multiplication, which can't extend to fractional/negative -- see
; parseFactor's own comment).
; Division IS part of this grammar (see the fraction-native expand*Frac
; functions below): every expanded value is a numerator/denominator pair
; of term lists, with '/' implemented as reciprocal-then-multiply. There
; are no precedence tiers within Product beyond left-to-right -- implicit
; adjacency after a '/' still binds like '*', not like a second '/', so
; "x/yz" parses as "(x/y)*z", NOT "x/(y*z)" (matching this grammar's
; existing philosophy that implicit adjacency and explicit '*' are
; already equal-precedence). No polynomial factor cancellation is
; performed (e.g. "(x+1)/(x+1)" stays "(x+1) / (x+1)", not "1") --
; matches the C++ engine's own scope, which doesn't cancel either.
; Multivariable terms ARE supported here (e.g. the cross term in
; (x+y)^2 -- see multiplyTerms/termVarAlist below); factorPoly.scm,
; solvePoly.scm, and calcPoly.scm still guard against multivariable
; input themselves, since GCF/quadratic-formula/rational-root factoring,
; equation solving, and power-rule calculus are genuinely single-variable
; algorithms that don't generalize just because expand() now does. The
; same three files also guard against a non-constant denominator (a
; genuine rational expression) via expandSum -- see classifyFrac below.

; A parenthesized group: its contents (a Sum, i.e. a list of <addend>
; records) and the integer exponent the whole group is raised to.
(define-record-type (<group> makegrp group?)
    (fields
        (mutable groupSum gs set-gs!)
        (mutable groupPow gp set-gp!)))

; One signed summand of a Sum: its own sign ('+ or '-), and the list of
; factors combined to form it. Each factor is stored as (op . factor),
; where op is '* (multiply into the product -- the first factor and any
; implicit-adjacency continuation always get '*) or '/ (divide by this
; factor, only after an explicit '/' token). factor itself is either a
; bare <poly> term (its `sign` field is unused/ignored here -- a term
; being multiplied has no boundary-sign role) or a nested <group>.
(define-record-type (<addend> makeadd addend?)
    (fields
        (mutable addSign asn set-asn!)
        (mutable addFactors afac set-afac!)))

; A matrix literal: its rows (a list of rows, each row a list of cell
; Sums -- i.e. exactly what parseSum returns per cell, deliberately left
; UNEXPANDED here, same deferred-expansion discipline <group> already
; uses for its own contents) and the integer power the whole matrix is
; raised to (mirrors <group>'s groupPow -- see expandFactorFrac's
; matrixLit branch for where expansion and squaring actually happen).
(define-record-type (<matrixLit> makematlit matrixLit?)
    (fields
        (mutable mlRows mlRows set-mlRows!)
        (mutable mlPow  mlPow  set-mlPow!)))

(define (lparen? k) (eqv? k (string->symbol "(")))
(define (rparen? k) (eqv? k (string->symbol ")")))
(define (addOp? k) (or (eqv? k '+) (eqv? k '-)))

; Matrix-literal tokens ('[', ']', ',') -- same string->symbol tokenization
; lparen?/rparen? already rely on. None of these three characters had any
; prior meaning in this grammar (a bare comma or bracket previously fell
; through to parseTerm's "expected a term" error), so treating them as
; additional Sum/Product terminators below is purely additive: it only
; changes behavior for input that used to error.
(define (lbracket? k) (eqv? k (string->symbol "[")))
(define (rbracket? k) (eqv? k (string->symbol "]")))
(define (comma? k) (eqv? k (string->symbol ",")))
; A Sum/Product must stop at a matrix row/cell boundary the same way it
; already stops at a top-level ')' -- a matrix cell's own Sum is parsed via
; the ordinary parseSum/parseProduct recursion (see parseMatrixRow below),
; so ',' and ']' need to be recognized terminators there too.
(define (sumStop? k) (or (rparen? k) (rbracket? k) (comma? k)))

; Top-level entry point: parses a character list into a Sum (a list of
; <addend> records).
(define (parseExpansion charL)
    (car (parseSum (mergeDigits (PolyStoSymbolH (groupIndexedVars (remove-all #\space charL)))))))

; Parses a sum of signed products. Stops at a top-level ')' or end of
; input -- nested parens are fully consumed by parseFactor's own
; recursive call to parseSum, so this never needs to track depth itself.
(define (parseSum tokL)
    (let* ((hasSign (and (not (null? tokL)) (addOp? (car tokL))))
           (sgn (if hasSign (car tokL) '+))
           (afterSign (if hasSign (cdr tokL) tokL))
           (prodResult (parseProduct afterSign))
           (addend (makeadd sgn (car prodResult)))
           (tail (cdr prodResult)))
        (if (or (null? tail) (sumStop? (car tail)))
            (cons (list addend) tail)
            (let ((sumResult (parseSum tail)))
                (cons (cons addend (car sumResult)) (cdr sumResult))))))

; Parses one or more factors combined by multiplication (implicit or via
; '*') or division (via '/'), stopping at '+', '-', ')', or end of input.
; Returns a list of (op . factor) pairs -- see <addend>'s doc comment for
; what op means. parseProductH threads through the operator that
; introduced the factor currently being parsed (defaulting to '* for the
; very first factor, since there's nothing before it to divide by).
(define (parseProduct tokL) (parseProductH tokL '*))

(define (parseProductH tokL op)
    (let* ((factorResult (parseFactor tokL))
           (tagged (cons op (car factorResult)))
           (tail (cdr factorResult)))
        (cond
            ((null? tail) (cons (list tagged) tail))
            ((eqv? (car tail) '*)
                (let ((next (parseProductH (cdr tail) '*)))
                    (cons (cons tagged (car next)) (cdr next))))
            ((eqv? (car tail) '/)
                (let ((next (parseProductH (cdr tail) '/)))
                    (cons (cons tagged (car next)) (cdr next))))
            ((or (addOp? (car tail)) (sumStop? (car tail)))
                (cons (list tagged) tail))
            ('t
                (let ((next (parseProductH tail '*)))
                    (cons (cons tagged (car next)) (cdr next)))))))

; Parses one factor: a parenthesized group (optionally raised to a
; power) or a bare term. A group's own power must be a nonnegative
; integer, unlike a bare variable's (see readTokenPower) -- expandPower
; (below) raises a group to its power via literal repeated self-
; multiplication, which can't extend to a fractional power (the square
; root of a general polynomial isn't a polynomial) and would recurse
; forever on a negative one (verified: it hangs until MIT Scheme's
; recursion-depth abort, since expandPower's recursion only terminates
; by counting DOWN to 0 or 1). Reject here with a clear parse error
; instead of letting that happen.
(define (parseFactor tokL)
    (cond
        ((lparen? (car tokL))
            (let* ((sumResult (parseSum (cdr tokL)))
                   (afterSum (cdr sumResult))      ; (car afterSum) is the matching ')'
                   (afterParen (cdr afterSum))
                   (powResult (readTokenPower afterParen))
                   (pow (car powResult)))
                (if (not (and (integer? pow) (>= pow 0)))
                    (error #f "parseFactor: a parenthesized group's exponent must be a nonnegative integer -- fractional/negative exponents are only supported directly on a variable, not a group" pow))
                (cons (makegrp (car sumResult) pow) (cdr powResult))))
        ((lbracket? (car tokL)) (parseMatrixLiteral tokL))
        ('t (parseTerm tokL))))

; ---- Matrix-literal parsing: '[' Row (',' Row)* ']' ['^' nonNegInt] ----
; Row ::= '[' Sum (',' Sum)* ']'
;
; Each cell is a full recursive parseSum call -- a cell can be "x+1",
; "1/(x-2)", a nested paren group, anything the grammar already accepts --
; left UNEXPANDED (a list of addends) until expandFactorFrac's matrixLit
; branch actually expands it, matching <group>'s own deferred-expansion
; discipline (see the file's grammar comment at the top: "structuring
; only... expansion" happens in a later pass).

; tokL starts right after this row's own '['. Returns (cons cellSumList
; afterRowClose) -- cellSumList is a list of (unexpanded) cell Sums,
; afterRowClose skips the row's own closing ']'.
;
; Named parseMatrixCellRow, NOT parseMatrixRow, to avoid colliding with
; matrix.scm's own pre-existing (string-based) parseMatrixRow -- matrix.scm
; loads AFTER this file, so a same-named definition there would silently
; win at the top level and shadow this one entirely (confirmed empirically:
; this is exactly what happened before this function was renamed).
(define (parseMatrixCellRow tokL)
    (let loop ((tokL tokL) (cells '()))
        (let* ((sumResult (parseSum tokL))
               (cellSum (car sumResult))
               (rest (cdr sumResult))
               (cells (cons cellSum cells)))
            (cond
                ((and (pair? rest) (comma? (car rest))) (loop (cdr rest) cells))
                ((and (pair? rest) (rbracket? (car rest))) (cons (reverse cells) (cdr rest)))
                ('t (error #f "parseMatrixCellRow: expected ',' or ']' in matrix row" rest))))))

; tokL starts at a row's own '[' (the matrix's outer '[' already consumed
; by the caller). Returns (cons rowList afterLastRow) -- rowList is a list
; of rows (each a list of cell Sums, per parseMatrixRow), afterLastRow is
; everything after the last row, up to and including the matrix's own
; closing ']' (parseMatrixLiteral checks for that itself).
(define (parseMatrixRows tokL)
    (if (not (and (pair? tokL) (lbracket? (car tokL))))
        (error #f "parseMatrixRows: expected '[' to start a matrix row" tokL)
        (let* ((rowResult (parseMatrixCellRow (cdr tokL)))
               (row (car rowResult))
               (rest (cdr rowResult)))
            (cond
                ((and (pair? rest) (comma? (car rest)))
                    (let ((next (parseMatrixRows (cdr rest))))
                        (cons (cons row (car next)) (cdr next))))
                ('t (cons (list row) rest))))))

; tokL starts with the matrix literal's own outer '['. A matrix's own
; exponent, like a parenthesized group's, must be a nonnegative integer
; (matrixPow -- see below -- raises it via repeated self-multiplication,
; and only a square matrix has a meaningful power at all).
(define (parseMatrixLiteral tokL)
    (let* ((rowsResult (parseMatrixRows (cdr tokL)))
           (rows (car rowsResult))
           (afterRows (cdr rowsResult)))
        (if (not (and (pair? afterRows) (rbracket? (car afterRows))))
            (error #f "parseMatrixLiteral: expected closing ']'" afterRows)
            (let ((rowLens (map length rows)))
                (if (or (null? rowLens) (not (for-all (lambda (l) (= l (car rowLens))) rowLens)))
                    (error #f "parseMatrixLiteral: matrix rows have inconsistent lengths" rows)
                    (let* ((afterClose (cdr afterRows))
                           (powResult (readTokenPower afterClose))
                           (pow (car powResult)))
                        (if (not (and (integer? pow) (>= pow 0)))
                            (error #f "parseMatrixLiteral: a matrix's exponent must be a nonnegative integer" pow)
                            (cons (makematlit rows pow) (cdr powResult)))))))))

; Parses one bare term (the same shapes singleR recognizes), without
; requiring or consuming a trailing sign -- a term factor inside a
; product can be followed by '*', '(', another term, '+', '-', ')', or
; end of input. A bare number is NOT allowed a trailing exponent here
; (Term ::= [coefficient] [variable ['^' exponent]] -- an exponent only
; ever attaches to a variable, not a lone number); write "(2)^-1" via
; the group path in parseFactor for that.
(define (parseTerm tokL)
    (cond
        ((var? (car tokL))
            (let ((powResult (readTokenPower (cdr tokL))))
                (cons (makep 1 1 1 1 (car tokL)
                             (numerator (car powResult)) (denominator (car powResult)) '+)
                      (cdr powResult))))
        ((and (number? (car tokL)) (not (null? (cdr tokL))) (var? (cadr tokL)))
            (let ((powResult (readTokenPower (cddr tokL))))
                (cons (makep (car tokL) 1 1 1 (cadr tokL)
                             (numerator (car powResult)) (denominator (car powResult)) '+)
                      (cdr powResult))))
        ((number? (car tokL))
            (cons (makep (car tokL) 1 1 1 1 1 1 '+) (cdr tokL)))
        ('t (error #f "parseTerm: expected a term" tokL))))

; If tokL starts with '^', reads the exponent as one of:
;   ^<int>     -- plain non-negative integer literal (the original case)
;   ^-<int>    -- bare negative integer, a convenience shorthand for ^(-<int>)
;   ^(<expr>)  -- a parenthesized sub-expression, parsed via parseSum and
;                 fully evaluated to a single exact rational via
;                 classifyFrac (readParenPower below) -- this is how
;                 fractional and/or negative exponents are written, e.g.
;                 x^(1/2), x^(-3/4). Errors if the expression doesn't
;                 reduce to a plain number (e.g. still has a variable in
;                 it -- variable exponents like x^y are out of scope).
; Returns (cons exponent restOfList); (cons 1 tokL) unchanged if no '^'.
; Shared by parseTerm (a variable's own exponent) and parseFactor (a
; parenthesized group's exponent, which parseFactor further restricts to
; a nonnegative integer -- see its own comment for why).
(define (readTokenPower tokL)
    (cond
        ((or (null? tokL) (not (eqv? (car tokL) '^))) (cons 1 tokL))
        ((and (not (null? (cdr tokL))) (lparen? (cadr tokL))) (readParenPower (cddr tokL)))
        ((and (not (null? (cdr tokL))) (eqv? (cadr tokL) '-)
              (not (null? (cddr tokL))) (number? (caddr tokL)))
            (cons (- (caddr tokL)) (cdddr tokL)))
        ((and (not (null? (cdr tokL))) (number? (cadr tokL))) (cons (cadr tokL) (cddr tokL)))
        ('t (error #f "readTokenPower: exponent must be a number or (expression)" tokL))))

; tokL is positioned just after the '(' that follows '^'. Parses the
; parenthesized exponent expression and evaluates it down to a single
; exact rational via classifyFrac -- the SAME fraction-native machinery
; expand() itself uses, so e.g. ^(1/2) or ^(-3/4) work via ordinary
; division, no separate exponent-arithmetic path needed.
(define (readParenPower tokL)
    (let* ((sumResult (parseSum tokL))
           (afterParen (cdr (cdr sumResult)))   ; skip the matching ')'
           (classified (classifyFrac (car sumResult))))
        (if (or (not (eqv? (car classified) 'whole))
                (exists (lambda (term) (var? (var term))) (cdr classified)))
            (error #f "readTokenPower: exponent expression must evaluate to a plain number" (car sumResult)))
        (cons (apply + (map (lambda (term) (/ (cn term) (cd term))) (cdr classified))) afterParen)))

; ---- String reconstruction, for testing/inspection only ----

(define sumToString
    (case-lambda
        ((addends) (sumToString addends 't))
        ((addends first)
            (cond
                ((null? addends) "")
                ('t
                    (let* ((a (car addends))
                           (sgnStr (cond
                                        ((and (eqv? first 't) (eqv? (asn a) '+)) "")
                                        ((eqv? (asn a) '+) "+")
                                        ('t "-"))))
                        (string-append sgnStr (productToString (afac a)) (sumToString (cdr addends) 'f))))))))

; factorL is a list of (op . factor) pairs (see <addend>'s doc comment).
; The separator before each factor is that factor's OWN op ('* or '/),
; since op describes how a factor combines with the product built so far.
(define (productToString factorL)
    (cond
        ((null? factorL) "")
        ('t
            (let* ((factor (cdar factorL))
                   (piece (if (group? factor) (groupToString factor) (termToString factor))))
                (string-append piece
                               (if (null? (cdr factorL)) "" (if (eqv? (caadr factorL) '/) "/" "*"))
                               (productToString (cdr factorL)))))))

(define (groupToString g)
    (let ((s (string-append "(" (sumToString (gs g)) ")")))
        (if (= (gp g) 1) s (string-append s "^" (number->string (gp g))))))

; Renders a single bare <poly> term as a plain magnitude string (no
; sign, since a term factor's sign field is unused in this grammar).
(define (termToString term)
    (let ((s ""))
        (cond
            ((not (= (varPd term) 1))
                (set! s (string-append "^(" (number->string (varPn term)) "/" (number->string (varPd term)) ")")))
            ((= 1 (varPn term)) '())
            ('t (set! s (string-append "^" (number->string (varPn term))))))
        (if (var? (var term))
            (set! s (string-append (symbol->string (var term)) s)))
        (cond
            ((not (= (cd term) 1))
                (set! s (string-append (number->string (cn term)) "/" (number->string (cd term)) s)))
            ((and (var? (var term)) (= 1 (cn term))) '())
            ('t (set! s (string-append (number->string (cn term)) s))))
        s))

; ---- Real expansion: multiplication and distribution ----
;
; Everything above only structures an expression into a Sum of
; <addend>s (each a sign and a list of factors). The functions below
; actually multiply it out into a single flat, fully-combined list of
; <poly> terms. Throughout, "true-signed" means each term's own sign is
; baked into its coefficient (as opposed to the <poly> record's normal
; *boundary*-sign convention used for printing -- see simplify.scm).

; Negates a term's coefficient (used when an addend's sign is '-). Must
; carry extraVars through -- this runs on the primary expand path itself
; (expandSum negates every term of a '-'-signed addend), so dropping it
; here would silently truncate a negated multivariable term.
(define (negateTerm term)
    (makepx (- (cn term)) (cd term) 1 1 (var term) (varPn term) (varPd term) '+ (xvars term)))

; A term's full (variable . exponent) list: its primary var/exponent (if
; var? holds) consed onto extraVars; '() for a constant.
(define (termVarAlist term)
    (if (var? (var term))
        (cons (cons (var term) (/ (varPn term) (varPd term))) (xvars term))
        (xvars term)))

; Merges two var-alists, summing exponents for variables shared by both
; (Scheme's exact rationals add directly -- no separate num/den bookkeeping
; needed the way the legacy varPn/varPd split requires), then sorts the
; result canonically by variable name so any two structurally-equal
; multivariable terms always produce `equal?` results (combineLikeTerms's
; assoc-based bucketing below depends on this).
; NOTE: Chez's sort takes (pred list) -- the REVERSE of MIT's (list pred).
(define (mergeVarAlists a1 a2)
    ; Drops a variable entirely if its summed exponent lands on exactly 0
    ; (e.g. x^2 * x^-2 -> the constant 1; x*y*x^-1 -> just y) -- now that
    ; negative exponents exist, "cancels out" is a real, reachable case,
    ; not just a variable that happens to have exponent 1.
    (define (addOne alist v e)
        (let ((existing (assq v alist)))
            (if existing
                (let ((newExp (+ (cdr existing) e))
                      (removed (filter (lambda (p) (not (eq? (car p) v))) alist)))
                    (if (= newExp 0) removed (cons (cons v newExp) removed)))
                (cons (cons v e) alist))))
    (define (foldIn alist pairs)
        (if (null? pairs) alist (foldIn (addOne alist (caar pairs) (cdar pairs)) (cdr pairs))))
    (sort (lambda (x y) (string<? (symbol->string (car x)) (symbol->string (car y)))) (foldIn a1 a2)))

; Multiplies two true-signed <poly> terms, of any number of variables
; each. Merging via termVarAlist/mergeVarAlists means this naturally
; covers the constant/constant, constant/variable, same-variable, and
; multivariable-cross-term (e.g. an x-term times a y-term, as in
; expanding (x+y)^2's cross term) cases in one path -- if the merged
; result has only one variable, the term is built via the plain 8-arg
; makep, so genuinely single-variable results (the overwhelming majority
; of usage) get byte-for-byte the same term shape as before this existed.
(define (multiplyTerms t1 t2)
    (let* ((rawN (* (cn t1) (cn t2)))
           (rawD (* (cd t1) (cd t2)))
           (reduced (reducefrac rawN rawD))
           (merged (mergeVarAlists (termVarAlist t1) (termVarAlist t2))))
        (cond
            ((null? merged)
                (makep (car reduced) (cadr reduced) 1 1 1 1 1 '+))
            ((null? (cdr merged))
                (let ((v (caar merged)) (e (cdar merged)))
                    (makep (car reduced) (cadr reduced) 1 1 v (numerator e) (denominator e) '+)))
            ('t
                (let ((v (caar merged)) (e (cdar merged)))
                    (makepx (car reduced) (cadr reduced) 1 1 v (numerator e) (denominator e) '+ (cdr merged)))))))

; FOIL: multiplies every term in list1 by every term in list2,
; producing the (not yet like-term-combined) list of all products.
(define (multiplyTermLists list1 list2)
    (apply append
        (map (lambda (t1) (map (lambda (t2) (multiplyTerms t1 t2)) list2))
             list1)))

; A term's total degree for sorting purposes: the sum of every variable's
; exponent (termVarAlist), or 0 for a constant. For single-variable terms
; this is identical to just that one exponent.
(define (termTotalDegree term) (apply + (map cdr (termVarAlist term))))

; Combines every term in termList sharing the same full variable-alist
; key (termVarAlist -- already canonically sorted by mergeVarAlists, so
; it's safe as an equal?-comparable assoc key), regardless of position --
; unlike addem (simplify.scm), which only merges *adjacent* terms and is
; therefore insufficient once multiplication has scrambled term order.
; Mutates and reuses the first term seen for each key as the accumulator,
; then sorts the result by descending total degree -- multiplying 3+
; factors otherwise leaves terms in whatever order FOIL-by-pairs happened
; to produce them, not the canonical descending-degree convention
; expand()'s output always uses elsewhere (e.g. "x(2x-7)(x^2+1)" would
; print as "2x^4+2x^2-7x^3-7x" instead of "2x^4-7x^3+2x^2-7x").
; NOTE: Chez's sort takes (pred list) -- the REVERSE of MIT's (list pred).
(define (combineLikeTerms termList)
    (define (termKey term) (termVarAlist term))
    (let ((buckets '()))
        (for-each
            (lambda (term)
                (let* ((k (termKey term))
                       (existing (assoc k buckets)))
                    (if existing
                        (let* ((acc (cdr existing))
                               (sum (addfrac (cn acc) (cd acc) (cn term) (cd term)))
                               (reduced (reducefrac (car sum) (cadr sum))))
                            (set-Num! acc (car reduced))
                            (set-Den! acc (cadr reduced)))
                        (set! buckets (append buckets (list (cons k term)))))))
            termList)
        (sort (lambda (a b) (> (termTotalDegree a) (termTotalDegree b))) (map cdr buckets))))

; Raises a true-signed term list to integer power n via repeated
; self-multiplication, combining like terms after each step to keep
; intermediate lists from growing combinatorially.
(define (expandPower termList n)
    (cond
        ((= n 0) (list (makep 1 1 1 1 1 1 1 '+)))
        ((= n 1) termList)
        ('t (combineLikeTerms (multiplyTermLists termList (expandPower termList (- n 1)))))))

; ---- Fractions: every expanded "value" is (numer . denom), both flat
; true-signed term lists, denom defaulting to a fresh constant-1 list
; when no division is involved (the overwhelming common case). '/' is
; implemented as reciprocal-then-multiply, per the standard identity
; a/(b/c) = a*(c/b) -- since a nested group's own fraction is a genuine
; (numer . denom) pair (not assumed to have denom=1), dividing by it
; just swaps that pair before multiplying, with no special-casing needed
; for "dividing by something that's itself a fraction".

; A fresh constant-1 singleton term list. Deliberately a niladic
; procedure, called fresh every time, rather than a single hoisted list
; -- combineLikeTerms mutates its first-seen term in place when merging
; a duplicate key, so a shared/hoisted "1" could eventually be corrupted
; by an unrelated merge elsewhere (the same aliasing hazard already fixed
; once this session in mathSymbolClass.scm's copy-term/ms->string path).
(define (oneTermList) (list (makep 1 1 1 1 1 1 1 '+)))

; ---- Scalar fraction arithmetic (the ORIGINAL fracMultiply/fracReciprocal/
; fracNegate/fracAdd bodies, renamed *Scalar) -- unchanged from before
; matrix values existed. The public fracMultiply/fracReciprocal/
; fracNegate/fracAdd below dispatch to these whenever neither operand is
; a matrix value, so the all-scalar path every existing caller (expand,
; factor, solve, differentiate/integrate, ...) exercises is byte-identical
; to before this file supported matrices at all.

(define (fracMultiplyScalar f1 f2)
    (cons (combineLikeTerms (multiplyTermLists (car f1) (car f2)))
          (combineLikeTerms (multiplyTermLists (cdr f1) (cdr f2)))))

(define (fracReciprocalScalar f) (cons (cdr f) (car f)))

(define (fracNegateScalar f) (cons (map negateTerm (car f)) (cdr f)))

; Adds two fractions via cross-multiplication: n1/d1 + n2/d2 = (n1*d2 + n2*d1)/(d1*d2).
(define (fracAddScalar f1 f2)
    (cons (combineLikeTerms (append (multiplyTermLists (car f1) (cdr f2))
                                     (multiplyTermLists (car f2) (cdr f1))))
          (combineLikeTerms (multiplyTermLists (cdr f1) (cdr f2)))))

; ---- Matrix-aware dispatch ----
;
; fracAdd/fracNegate/fracReciprocal/fracMultiply are the names every
; other function in this file (expandFactorFrac, expandProductFrac,
; expandSumFrac) already calls -- those three needed NO changes at all to
; support matrices, since they're already generic over whatever these
; four return. Type/dimension violations (adding a matrix to a scalar,
; dividing by a matrix, mismatched dimensions) raise via `error`, exactly
; like this file's pre-existing "expand: division by zero" -- caught by
; the same safety net (a test's `safely`, or dispatcher.scm's per-line
; guard) that already turns a raised error into an "Error: ..." string,
; no new plumbing needed.

; Renders "RxC" for an error message, the same shape matrix.scm's own
; dimension-mismatch strings already use (e.g. "(1x2 vs 1x3)") -- kept
; here as plain text baked into the message itself, NOT as a separate
; error irritant: an irritant holding raw matrix rows (fraction-pair
; cells wrapping <poly> records) would render as an unreadable object
; dump wherever this error surfaces (e.g. dispatcher.scm's safeApplyCommand,
; which formats any caught error via display-condition, irritants and
; all) -- exactly the same reasoning this file's pre-existing
; "expand: division by zero" already follows by passing no irritant at all.
(define (matDimStr rows) (string-append (number->string (matNumRows rows)) "x" (number->string (matNumCols rows))))

(define (fracAdd f1 f2)
    (cond
        ((and (fracMatrix? f1) (fracMatrix? f2))
            (if (not (matDimsMatch? (matRows f1) (matRows f2)))
                (error #f (string-append "expand: matrix dimensions don't match for addition (" (matDimStr (matRows f1)) " vs " (matDimStr (matRows f2)) ")"))
                (makeMatrixVal (map (lambda (row1 row2) (map fracAddScalar row1 row2)) (matRows f1) (matRows f2)))))
        ((or (fracMatrix? f1) (fracMatrix? f2))
            (error #f "expand: can't add a matrix and a scalar"))
        ('t (fracAddScalar f1 f2))))

(define (fracNegate f)
    (if (fracMatrix? f)
        (makeMatrixVal (map (lambda (row) (map fracNegateScalar row)) (matRows f)))
        (fracNegateScalar f)))

(define (fracReciprocal f)
    (if (fracMatrix? f)
        (error #f "expand: can't divide by a matrix")
        (fracReciprocalScalar f)))

(define (fracMultiply f1 f2)
    (cond
        ((and (fracMatrix? f1) (fracMatrix? f2))
            (if (not (= (matNumCols (matRows f1)) (matNumRows (matRows f2))))
                (error #f (string-append "expand: matrix dimensions don't match for multiplication (" (matDimStr (matRows f1)) " vs " (matDimStr (matRows f2)) ")"))
                (makeMatrixVal (matMatrixProductRows (matRows f1) (matRows f2)))))
        ((fracMatrix? f1)
            (makeMatrixVal (map (lambda (row) (map (lambda (cell) (fracMultiplyScalar f2 cell)) row)) (matRows f1))))
        ((fracMatrix? f2)
            (makeMatrixVal (map (lambda (row) (map (lambda (cell) (fracMultiplyScalar f1 cell)) row)) (matRows f2))))
        ('t (fracMultiplyScalar f1 f2))))

; ---- Matrix values: tagging and cellwise/whole-matrix helpers ----
;
; A matrix value is (cons 'matrix rows) -- rows is a list of rows, each
; row a list of scalar fraction-pair cells, i.e. exactly the same
; (numerTermList . denomTermList) shape expandFactorFrac already produces
; for an ordinary scalar. A scalar value's own car is always a (possibly
; empty) plain list of <poly> records, never the bare symbol 'matrix, so
; this tag is unambiguous, and (car v) is always safe to call: every value
; this file produces is a cons cell (a scalar fraction pair or a freshly
; tagged matrix pair), never anything else.
(define (fracMatrix? v) (eq? (car v) 'matrix))
(define (matRows v) (cdr v))
(define (makeMatrixVal rows) (cons 'matrix rows))

(define (matNumRows rows) (length rows))
(define (matNumCols rows) (if (null? rows) 0 (length (car rows))))
(define (matDimsMatch? r1 r2)
    (and (= (matNumRows r1) (matNumRows r2)) (= (matNumCols r1) (matNumCols r2))))
(define (matColumn rows j) (map (lambda (row) (list-ref row j)) rows))

; Zero/one as scalar fraction-pair cells, matching calcPoly.scm's own
; makep-based zero/one term convention elsewhere in this codebase.
(define (zeroFracCell) (cons (list (makep 0 1 1 1 1 1 1 '+)) (oneTermList)))
(define (oneFracCell)  (cons (list (makep 1 1 1 1 1 1 1 '+)) (oneTermList)))

(define (identityFracRows n)
    (map (lambda (i) (map (lambda (j) (if (= i j) (oneFracCell) (zeroFracCell))) (range n)))
         (range n)))

; Sums a list of scalar fraction-pair cells via repeated fracAddScalar --
; the row.column contraction matrix multiplication needs.
(define (sumFracCells cells)
    (if (null? cells) (zeroFracCell) (fracAddScalar (car cells) (sumFracCells (cdr cells)))))

(define (dotProductFrac rowCells colCells)
    (sumFracCells (map fracMultiplyScalar rowCells colCells)))

(define (matMatrixProductRows rows1 rows2)
    (map (lambda (row1) (map (lambda (j) (dotProductFrac row1 (matColumn rows2 j)))
                              (range (matNumCols rows2))))
         rows1))

; Raises a scalar-or-matrix value to a nonnegative integer power -- the
; generalization of expandPower (which only ever raised a plain scalar
; fraction pair) to also cover a matrix value, since a parenthesized
; group's contents (expandFactorFrac's group branch) or a bare matrix
; literal (its own matrixLit branch) can now be either.
(define (fracPow v n)
    (if (fracMatrix? v)
        (matrixPow v n)
        (cons (expandPower (car v) n) (expandPower (cdr v) n))))

; n=1 (the default when a matrix literal has no explicit '^', i.e. every
; ordinary matrix expression) is checked FIRST and unconditionally passed
; through -- it needs no square-dimension check at all, since M^1 = M
; regardless of shape. Squareness only matters for n=0 (identity) or
; n>=2 (repeated self-multiplication, which matMatrixProductRows itself
; would otherwise reject via its own dimension check anyway, but the
; clearer square-specific message is worth raising directly here).
(define (matrixPow mval n)
    (if (= n 1)
        mval
        (let ((rows (matRows mval)))
            (if (not (= (matNumRows rows) (matNumCols rows)))
                (error #f (string-append "expand: a matrix power requires a square matrix (got " (matDimStr rows) ")"))
                (cond
                    ((= n 0) (makeMatrixVal (identityFracRows (matNumRows rows))))
                    ('t (fracMultiply mval (matrixPow mval (- n 1)))))))))

; Expands one factor (a bare <poly> term, or a grp) into a fraction. A
; bare term has an implicit denominator of 1 (parseTerm always gives it
; sign '+' and the grammar doesn't use a term factor's sign field); a grp
; expands its inner Sum to a fraction and raises BOTH sides to the
; group's power independently, e.g. (1/x)^2 = 1/x^2. expandPower never
; evaluates its base for n=0 (returns [1] unconditionally), so something
; like (1/(x-x))^0 silently gives 1 rather than erroring on the
; zero-denominator base -- this matches expandPower's own pre-existing
; never-checked 0^0 convention for plain (non-fraction) values too, so
; it's not a new gap, just worth calling out here.
; Expands one matrix cell's (unexpanded) Sum into a scalar fraction pair
; -- errors if the cell itself turns out to be matrix-valued (a matrix
; can't contain another matrix as one of its own cells).
(define (expandCellFrac cellSum)
    (let ((v (expandSumFrac cellSum)))
        (if (fracMatrix? v)
            (error #f "expand: a matrix cell can't itself be a matrix")
            v)))

(define (expandFactorFrac factor)
    (cond
        ((group? factor)
            (fracPow (expandSumFrac (gs factor)) (gp factor)))
        ((matrixLit? factor)
            (fracPow (makeMatrixVal (map (lambda (row) (map expandCellFrac row)) (mlRows factor)))
                     (mlPow factor)))
        ('t (cons (list factor) (oneTermList)))))

; Expands and combines every factor in a Product (the (op . factor) list
; of one <addend>) left to right, multiplying or dividing per each
; factor's own op (see <addend>'s doc comment).
(define (expandProductFrac factors)
    (cond
        ((null? factors) (cons (list (makep 1 1 1 1 1 1 1 '+)) (oneTermList)))
        ((null? (cdr factors))
            (let ((f (expandFactorFrac (cdar factors))))
                (if (eqv? (caar factors) '/) (fracReciprocal f) f)))
        ('t
            (let* ((f (expandFactorFrac (cdar factors)))
                   (f (if (eqv? (caar factors) '/) (fracReciprocal f) f)))
                (fracMultiply f (expandProductFrac (cdr factors)))))))

; Expands a full Sum (list of <addend>s) into one combined fraction:
; expand each addend's product, negate its numerator if the addend's
; sign is '-', then fold all addends together via fraction addition
; (cross-multiplication) -- addends can have different denominators,
; e.g. "1/x + 1/y".
(define (expandSumFrac addends)
    (cond
        ((null? (cdr addends))
            (let ((f (expandProductFrac (afac (car addends)))))
                (if (eqv? (asn (car addends)) '-) (fracNegate f) f)))
        ('t
            (let* ((a (car addends))
                   (f1 (expandProductFrac (afac a)))
                   (f1 (if (eqv? (asn a) '-) (fracNegate f1) f1)))
                (fracAdd f1 (expandSumFrac (cdr addends)))))))

; Runs the fraction-native core and classifies the (dropZeros'd) result
; the same way for every external consumer (expandSum, expand, and
; polyBridge.scm's ms-from-str):
;   ('whole . flatTermList)            -- denom was a plain constant,
;                                          folded into numer's coefficients
;   ('fraction numerList . denomList)  -- denom has a real variable, a
;                                          genuine rational expression
; "Division by zero" has exactly one meaning regardless of caller, so
; it's errored here rather than by each consumer separately.
(define (classifyFrac addends)
    (let ((raw (expandSumFrac addends)))
        (if (fracMatrix? raw)
            (cons 'matrix (matRows raw))
            (let* ((numer (dropZeros (car raw)))
                   (denom (dropZeros (cdr raw))))
                (cond
                    ((null? denom) (error #f "expand: division by zero"))
                    ((and (= (length denom) 1) (not (var? (var (car denom)))))
                        (cons 'whole (foldConstantDenom numer (car denom))))
                    ('t (cons 'fraction (cons numer denom))))))))

; Divides every term in numerList's coefficient by the single constant
; denomTerm, via ordinary fraction division (reducefrac handles sign
; normalization for a negative denomTerm, e.g. "x/(-2)" -- see the fix in
; basicmath.scm). Substitutes the zero-constant sentinel if the result is
; empty (e.g. "0/2"), matching dropZeros's usual empty-list convention.
(define (foldConstantDenom numerList denomTerm)
    (let ((folded (map (lambda (t)
                            (let ((r (reducefrac (* (cn t) (cd denomTerm)) (* (cd t) (cn denomTerm)))))
                                (makepx (car r) (cadr r) 1 1 (var t) (varPn t) (varPd t) '+ (xvars t))))
                        numerList)))
        (if (null? folded) (list (makep 0 1 1 1 1 1 1 '+)) folded)))

; Expands a full Sum (list of <addend>s) into one combined, true-signed
; flat term list -- the contract every existing external caller (factor,
; solve, differentiate/integrate, flipSide, solveInequality, ...) already
; relies on. A plain constant denominator (e.g. "6x/3") folds
; transparently into the result, same as always; a genuine rational
; expression (a variable in the denominator) raises a clear error rather
; than silently discarding the denominator, since none of those callers
; are equipped to handle one -- only expand() (via expandSumFrac/
; classifyFrac directly) and polyBridge.scm's ms-from-str render true
; fractions.
(define (expandSum addends)
    (let ((result (classifyFrac addends)))
        (cond
            ((eqv? (car result) 'matrix)
                (error #f "expand: matrix input isn't supported here -- use expand() for matrix expressions"))
            ((eqv? (car result) 'whole) (cdr result))
            ('t (error #f "expand: division by a non-constant isn't supported here -- use expand() for rational expressions" (cddr result))))))

; Top-level entry point: fully expands a polynomial expansion
; expression (the same syntax parseExpansion accepts) into its
; simplified polynomial string, e.g. "(x+1)*(x+2)" -> "x^2+3x+2", or,
; for a genuine rational expression, "(numerator) / (denominator)" (no
; factor cancellation -- see the grammar comment at the top of this file).
; Renders one scalar fraction-pair cell of a matrix -- mirrors classifyFrac/
; expand's own whole-vs-fraction logic, just applied to a single cell and
; producing a string directly rather than a further-classified tag (a
; matrix cell is always a leaf as far as rendering goes).
(define (renderFracCell cell)
    (let ((numer (dropZeros (car cell))) (denom (dropZeros (cdr cell))))
        (cond
            ((null? denom) (error #f "expand: division by zero"))
            ((and (= (length denom) 1) (not (var? (var (car denom)))))
                (recordToString (unapplysigns (foldConstantDenom numer (car denom)))))
            ('t (if (null? numer)
                    "0"
                    (string-append "(" (recordToString (unapplysigns numer))
                                   ") / (" (recordToString (unapplysigns denom)) ")"))))))

(define (joinCommaStrings strs)
    (cond
        ((null? strs) "")
        ((null? (cdr strs)) (car strs))
        ('t (string-append (car strs) "," (joinCommaStrings (cdr strs))))))

(define (renderMatrixRow row) (string-append "[" (joinCommaStrings (map renderFracCell row)) "]"))
(define (renderMatrixRows rows) (string-append "[" (joinCommaStrings (map renderMatrixRow rows)) "]"))

(define (expand charL)
    (let* ((addends (parseExpansion charL))
           (result (classifyFrac addends)))
        (cond
            ((eqv? (car result) 'matrix) (renderMatrixRows (cdr result)))
            ((eqv? (car result) 'whole) (recordToString (unapplysigns (cdr result))))
            ('t
                (let ((numer (cadr result)) (denom (cddr result)))
                    (if (null? numer)
                        "0"
                        (string-append "(" (recordToString (unapplysigns numer))
                                       ") / (" (recordToString (unapplysigns denom)) ")")))))))

; #t if s is non-empty and every character is a digit.
(define (bareDigitRun? s)
    (and (> (string-length s) 0)
         (let loop ((i 0))
             (or (= i (string-length s))
                 (and (char-numeric? (string-ref s i)) (loop (+ i 1)))))))

; Given lst starting immediately AFTER an opening "(" (one level of
; nesting already "owed"), returns (cons innerChars afterClose) --
; innerChars is everything up to (not including) the matching ")",
; afterClose is everything after it. #f if lst has no matching ")" at
; all (unbalanced input). Same depth-counting idiom as this codebase's
; other paren-matching helpers (e.g. radicalRationalSolve.scm's
; findMatchingParen), adapted to a character LIST instead of a
; string+index since groupIndexedVars already works on lists.
(define (splitAtMatchingParenIndexed lst)
    (let loop ((l lst) (depth 1) (acc '()))
        (cond
            ((null? l) #f)
            ((eqv? (car l) #\() (loop (cdr l) (+ depth 1) (cons (car l) acc)))
            ((eqv? (car l) #\))
                (if (= depth 1)
                    (cons (reverse acc) (cdr l))
                    (loop (cdr l) (- depth 1) (cons (car l) acc))))
            ('t (loop (cdr l) depth (cons (car l) acc))))))

; Scans polyL (already space-stripped) for "letter_subscript" runs and
; collapses each into one pre-formed symbol token (e.g. 'x_1, 'n_x,
; 'x_(x+1)), left in place of the characters it consumed. Everything
; else -- any run not matching one of the three recognized shapes --
; passes through completely unchanged, one character at a time, to be
; tokenized as today by PolyStoSymbolH (PolyStoSymbol.scm). Must run
; BEFORE PolyStoSymbolH, which has one pass-through clause to leave
; these pre-formed symbols alone instead of trying to (string->symbol
; (string ...)) a symbol, which errors.
;
; Deliberately defined HERE (in expandParse.scm, loaded after
; PolyStoSymbol.scm) rather than alongside PolyStoSymbolH -- this
; function calls expand() (below), and expand's name collides with a
; pre-existing Chez built-in (its own macro-expansion utility, already
; bound before any engine file loads); a function referencing `expand`
; from an EARLIER-loaded file captures that built-in instead of this
; codebase's redefinition (confirmed empirically -- every other caller
; of expand() already happens to live in a later-loaded file, so
; nothing had hit this before). Wired in from parseExpansion (above)
; and PolyStoSymbol.scm's PolyStoSymbol -- both are fine referencing a
; function defined later in load order, same as e.g. dispatcher.scm's
; join-strings, since groupIndexedVars itself is a genuinely fresh name
; with no prior Chez binding to accidentally capture.
;
; Subscript shapes recognized:
;   - digit-run:                x_1, a_23
;   - single letter:             x_n, n_x
;   - parenthesized expression:  x_(1+x) -- the inner text is run
;     through expand() and the symbol is built from the EXPANDED
;     result (e.g. 'x_(x+1) regardless of whether the input was
;     "x_(1+x)" or "x_(x+1)"), so identity/combining is always based
;     on canonical form -- there is no separate "evaluate" mode to
;     toggle.
;
; Base letter and single-letter subscript content are restricted to
; lowercase a-z, matching mathHelp.scm's existing 26-letter variableD
; domain exactly. A run that doesn't match one of the three shapes
; (e.g. "x_ab", multi-letter subscript; "_1" not preceded by a letter;
; unbalanced parens) falls through completely unrecognized -- this is
; deliberately conservative: no input lacking an underscore, and no
; underscore-shape outside the three supported forms, changes behavior
; at all.
(define (groupIndexedVars polyL)
    (cond
        ((null? polyL) polyL)
        ((and (char-alphabetic? (car polyL)) (char-lower-case? (car polyL))
              (pair? (cdr polyL)) (eqv? (cadr polyL) #\_)
              (pair? (cddr polyL)))
            (let ((baseChar (car polyL)) (suffix (cddr polyL)))
                (cond
                    ; digit-run subscript: x_1, x_10, a_23
                    ((char-numeric? (car suffix))
                        (let loop ((rest (cdr suffix)) (digits (list (car suffix))))
                            (if (and (pair? rest) (char-numeric? (car rest)))
                                (loop (cdr rest) (cons (car rest) digits))
                                (cons (string->symbol
                                          (list->string (cons baseChar (cons #\_ (reverse digits)))))
                                      (groupIndexedVars rest)))))
                    ; single-letter subscript: n_x, x_n -- must not itself
                    ; be immediately followed by another alnum, else it's
                    ; a multi-letter subscript (unsupported) -- fall through.
                    ((and (char-alphabetic? (car suffix)) (char-lower-case? (car suffix))
                          (or (null? (cdr suffix))
                              (not (or (char-alphabetic? (cadr suffix)) (char-numeric? (cadr suffix))))))
                        (cons (string->symbol (string baseChar #\_ (car suffix)))
                              (groupIndexedVars (cdr suffix))))
                    ; parenthesized-expression subscript: x_(1+x)
                    ((eqv? (car suffix) #\()
                        (let ((split (splitAtMatchingParenIndexed (cdr suffix))))
                            (if (not split)
                                (cons (car polyL) (groupIndexedVars (cdr polyL)))
                                (let ((expanded (expand (car split))))
                                    (cons (string->symbol
                                              (cond
                                                  ; Unify with the digit-run/single-letter shapes when the
                                                  ; normalized subscript collapses to one of those -- e.g.
                                                  ; "x_(1)" and plain "x_1" must be the SAME symbol, not
                                                  ; just look alike, since expand()'s whole point here is
                                                  ; that two spellings of the same subscript are one
                                                  ; variable. Without this, "x_1" and "x_(1)" would combine
                                                  ; incorrectly (confirmed empirically: they didn't, before
                                                  ; this fix).
                                                  ((bareDigitRun? expanded)
                                                      (string-append (string baseChar) "_" expanded))
                                                  ((and (= (string-length expanded) 1)
                                                        (char-alphabetic? (string-ref expanded 0))
                                                        (char-lower-case? (string-ref expanded 0)))
                                                      (string-append (string baseChar) "_" expanded))
                                                  ('t (string-append (string baseChar) "_(" expanded ")"))))
                                          (groupIndexedVars (cdr split)))))))
                    ; anything else: not a recognized shape, fall through
                    ; unchanged, one char at a time.
                    ('t (cons (car polyL) (groupIndexedVars (cdr polyL)))))))
        ('t (cons (car polyL) (groupIndexedVars (cdr polyL))))))

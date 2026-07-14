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

(define (lparen? k) (eqv? k (string->symbol "(")))
(define (rparen? k) (eqv? k (string->symbol ")")))
(define (addOp? k) (or (eqv? k '+) (eqv? k '-)))

; Top-level entry point: parses a character list into a Sum (a list of
; <addend> records).
(define (parseExpansion charL)
    (car (parseSum (mergeDigits (PolyStoSymbolH (remove-all #\space charL))))))

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
        (if (or (null? tail) (rparen? (car tail)))
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
            ((or (addOp? (car tail)) (rparen? (car tail)))
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
    (if (lparen? (car tokL))
        (let* ((sumResult (parseSum (cdr tokL)))
               (afterSum (cdr sumResult))      ; (car afterSum) is the matching ')'
               (afterParen (cdr afterSum))
               (powResult (readTokenPower afterParen))
               (pow (car powResult)))
            (if (not (and (integer? pow) (>= pow 0)))
                (error #f "parseFactor: a parenthesized group's exponent must be a nonnegative integer -- fractional/negative exponents are only supported directly on a variable, not a group" pow))
            (cons (makegrp (car sumResult) pow) (cdr powResult)))
        (parseTerm tokL)))

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

(define (fracMultiply f1 f2)
    (cons (combineLikeTerms (multiplyTermLists (car f1) (car f2)))
          (combineLikeTerms (multiplyTermLists (cdr f1) (cdr f2)))))

(define (fracReciprocal f) (cons (cdr f) (car f)))

(define (fracNegate f) (cons (map negateTerm (car f)) (cdr f)))

; Adds two fractions via cross-multiplication: n1/d1 + n2/d2 = (n1*d2 + n2*d1)/(d1*d2).
(define (fracAdd f1 f2)
    (cons (combineLikeTerms (append (multiplyTermLists (car f1) (cdr f2))
                                     (multiplyTermLists (car f2) (cdr f1))))
          (combineLikeTerms (multiplyTermLists (cdr f1) (cdr f2)))))

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
(define (expandFactorFrac factor)
    (cond
        ((group? factor)
            (let ((inner (expandSumFrac (gs factor))) (n (gp factor)))
                (cons (expandPower (car inner) n) (expandPower (cdr inner) n))))
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
    (let* ((raw (expandSumFrac addends))
           (numer (dropZeros (car raw)))
           (denom (dropZeros (cdr raw))))
        (cond
            ((null? denom) (error #f "expand: division by zero"))
            ((and (= (length denom) 1) (not (var? (var (car denom)))))
                (cons 'whole (foldConstantDenom numer (car denom))))
            ('t (cons 'fraction (cons numer denom))))))

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
        (if (eqv? (car result) 'whole)
            (cdr result)
            (error #f "expand: division by a non-constant isn't supported here -- use expand() for rational expressions" (cddr result)))))

; Top-level entry point: fully expands a polynomial expansion
; expression (the same syntax parseExpansion accepts) into its
; simplified polynomial string, e.g. "(x+1)*(x+2)" -> "x^2+3x+2", or,
; for a genuine rational expression, "(numerator) / (denominator)" (no
; factor cancellation -- see the grammar comment at the top of this file).
(define (expand charL)
    (let* ((addends (parseExpansion charL))
           (result (classifyFrac addends)))
        (if (eqv? (car result) 'whole)
            (recordToString (unapplysigns (cdr result)))
            (let ((numer (cadr result)) (denom (cddr result)))
                (if (null? numer)
                    "0"
                    (string-append "(" (recordToString (unapplysigns numer))
                                   ") / (" (recordToString (unapplysigns denom)) ")"))))))

#lang eopl


;; Takes input in the form of a list of lists where each 'inner list' represents
;; a propsitional logic staement and the last statement is the conclusion.

;; ****GOD****
;; (tree-method '((E => OP) (E => ON) (E => B) (P => (K => (!Z => !B))) (!P => !OP) (ON => (X => K)) (K => !X) (X) (!E)))


;; EXAMPLES FROM SLIDES
;; (tree-method '((S => G) (!S => E) (!G => !E) (G)))          == valid
;; (tree-method '((S) (S => M) (M)))                           == valid
;; (tree-method '((B => I) (M => !D) (I => D) (B => !M)))      == valid

;; (tree-method '((A ^ B) (!A => B) (C => !D) (A => C)))       == invalid
;; (tree-method '((A ^ (B ^ Z)) (!A => B) (C => !D) (A => C))) == invalid
;; (tree-method '(((A V !Z) ^ (B ^ Z)) (!A => B) (C => !D) (A => C))) == invalid


;; Rules Of Inference (****ALL ARE VALID****)
;; (tree-method '((p) (p => q) (q)))           == modus ponens
;; (tree-method '((!q) (p => q) (!p)))         == modus tollens
;; (tree-method '((p) (p V q)))                == addition
;; (tree-method '((p ^ q) (p)))                == simplification
;; (tree-method '((p) (q) (p ^ q)))            == conjunction
;; (tree-method '((p => q) (q => r) (p => r))) == hypothetical syllogism
;; (tree-method '((p V q) (!p) (q)))           == disjunctive syllogism
;; (tree-method '((p V q) (!p V r) (q V r)))   == resolution



(define (tree-method input)
  (tree-method-helper input '() #f))

(define (tree-method-helper input output-tree conclusion-negated)
  (if (null? input)
      ;;(re-eval output-tree)
      (evaluate output-tree)
      ;;output-tree
      (if conclusion-negated
          (tree-method-helper (cdr input) (add-to-tree (car input) output-tree) conclusion-negated)
          (tree-method-helper (cdr (reverse input)) (begin-tree (apply-negation (car (reverse input)))) #t))))


(define (begin-tree conc)
  (if (>= (length conc) 3)
      (case (get-op conc)
        ('^ (list (list (car conc) (car (reverse conc)))))
        ('V (list (list (car conc)) (list (car (reverse conc))))))
      (list conc)))




;; (add-to-tree '(r ^ v) '((t y))) == '((t y r v))
(define (add-to-tree layer current-tree)
  ;;(display "adding...\n")
  (if (>= (length layer) 3)
      (case (get-op layer)
        ('^  (add-new-and (car layer) (car (reverse layer)) current-tree))
        ('V  (add-new-or  (car layer) (car (reverse layer)) current-tree))
        ('=> (add-new-imp (car layer) (car (reverse layer)) current-tree))
        (else "ERROR: INVALID OPERATOR"))
      (add-new-individual (car layer) current-tree)))

;;(apply-negation '(r ^ v)) == '(!r V !v)
(define (apply-negation conclusion)
  ;;(display "negating...\n")
  (if (>= (length conclusion) 3)
      (case (get-op conclusion)
        ('^  (apply-negation-helper conclusion 'V))
        ('V  (apply-negation-helper conclusion '^))
        ('=> (apply-negation-helper (list (negate (car conclusion)) (car (reverse conclusion))) '^)))
      (list (negate (car conclusion)))))

(define (apply-negation-helper conclusion op)
  (list (negate (car conclusion)) op (negate (car (reverse conclusion)))))




;; Adds new values to the logic tree if there is an 'and'
(define (add-new-and oper1 oper2 current-tree)
  ;;(display "adding-and...\n")
  (add-new-and-helper oper1 oper2 current-tree '()))

(define (add-new-and-helper oper1 oper2 old-tree new-tree)
  ;;(if (or (list? oper1) (list? oper2))
    ;;  (cond
      ;;  ((and (list? oper1) (list? oper2)) (add-new-and-helper)
        ;;((list? oper1))
      (if (null? old-tree)
          new-tree
          (add-new-and-helper oper1 oper2 (cdr old-tree) (cons (cons oper1 (cons oper2 (car old-tree))) new-tree))))





;; Adds new values to the logic tree if there is an 'or'
(define (add-new-or oper1 oper2 current-tree)
  ;;(display "adding-or...\n")
  (add-new-or-helper (list oper1 oper2) (list oper1 oper2) current-tree '()))

(define (add-new-or-helper opers opers-iter old-tree new-tree)
  (if (null? old-tree)
      new-tree
      (if (null? opers-iter)
          (add-new-or-helper opers opers (cdr old-tree) new-tree)
          (add-new-or-helper opers (cdr opers-iter) old-tree (cons (cons (car opers-iter) (car old-tree)) new-tree)))))




;; Adds new values to the logic tree if there is an 'implies'
(define (add-new-imp oper1 oper2 current-tree)
  ;;(display "adding-imp...\n")
  (add-new-or (negate oper1) oper2 current-tree))




;; Adds an individual statement to the tree (eg. A )
(define (add-new-individual oper current-tree)
  (add-new-individual-helper oper current-tree '()))

(define (add-new-individual-helper oper old-tree new-tree)
  (if (null? old-tree)
      new-tree
      (add-new-individual-helper oper (cdr old-tree) (cons (cons oper (car old-tree)) new-tree)))) 



;; Evaluates the tree
;; Checks for nested statements and evaluates them 
(define (evaluate tree)
  (eval-helper (car tree) (car tree) (cdr tree)))

(define (eval-helper branch branch-iter old-tree)
  (if (and (null? old-tree) (element? (negate (car branch-iter)) branch))
      ;;(display "Valid")
      '()
      (cond
        ((null? branch-iter) (make-set branch)) ;; branch didnt die, contradiction was found
        ((list? (car branch-iter)) (eval-helper (car (add-to-tree (car branch-iter) (list (remove (car branch-iter) branch)))) (cdr branch-iter) old-tree))
        ((element? (negate (car branch-iter)) branch) (eval-helper (car old-tree) (car old-tree) (cdr old-tree)))  ;; branch dies
        (else (eval-helper branch (cdr branch-iter) old-tree))  ;; continue searching the branch
        )))



(define (negate val)
  (if (list? val)
      (apply-negation val)
      (if (equal? (car (string->list (symbol->string val))) (car (string->list (symbol->string '!))))
          (string->symbol (list->string (cdr (string->list (symbol->string val)))))
          (string->symbol (string-append "!" (symbol->string val))))))

;; (get-op '(1 ^ 3)) => 2
(define (get-op list)
  (cadr list))


(define (element? item list-of-items)
  (if (null? list-of-items)
      #f
      (if (equal? item (car list-of-items))
          #t
          (element? item (cdr list-of-items)))))

(define (make-set list-of-items)
  (cond
    [(null? list-of-items)
     '()] ; Empty lists never have duplicates
    [(element? (car list-of-items) (cdr list-of-items))
     (make-set (cdr list-of-items))]
    [else
     (cons (car list-of-items) (make-set (cdr list-of-items)))]))

(define (remove element set)
  (set-difference set (list element)))

(define (set-difference setA setB)
  (make-set (Set-Difference setA setB)))

(define (Set-Difference setA setB)
  (if (null? setA)
      '()
      (if (element? (car setA) setB)
          (Set-Difference (cdr setA) setB)
          (cons (car setA) (Set-Difference (cdr setA) setB)))))

;; (begin-tree (apply-negation (car (reverse '((B => I) (M => !D) (I => D) (B => !M))))))
;; (add-to-tree (car (make-set '((B ^ Z) A !D A !C))) (remove '(B ^ Z) '(A (B ^ Z) A !D A !C)))

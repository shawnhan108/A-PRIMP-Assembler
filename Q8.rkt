#lang racket
;Collaboration with Yunkai Xiao (20776848), CS146, Winter 2019.
;Compiler from SIMP to A-PRIMP
(define memsize 10000)
(define memory (make-vector memsize 0))
(define SP 0)
(define temcounter 1)
(define labelcounter 1)
(define dataset (mutable-set))

(define dispatchtable
  (hash
   '+ 'add
   '- 'sub
   '* 'mul
   'div 'div
   'mod 'mod
   '= 'equal
   '> 'gt
   '< 'lt
   '>= 'ge
   '<= 'le
   'not 'lnot
   'and 'land
   'or 'lor
   ))

(define (solve-op target op) ;;e.g: y, (* 2 (+ 2 3)) returns a list of aprimp instructions
  (define (solveand target op out) ; if of the form (exp1 exp2 exp3 ,...)    
    (define localtemp (string->symbol(string-append* "TMP" (list (number->string temcounter)))))
    (define localtemp1 (string->symbol(string-append* "TMP" (list (number->string (add1 temcounter))))))
    (set-add! dataset (list 'data localtemp 0))
    (set-add! dataset (list 'data localtemp1 0))
    (if (= 2 (length op))
        (begin
          (set! temcounter (+ 2 temcounter))
          (append (solve-op localtemp (car op)) (solve-op localtemp1 (second op))
                  (list (list 'land target localtemp localtemp1))
                  out))
        (begin          
          (set! temcounter (+ 2 temcounter))
          (solveand localtemp (cdr op) (append (solve-op localtemp1 (car op)) (list(list 'land target localtemp1 localtemp)) out)))))  
  (define (solveor target op out) ; if of the form (exp1 exp2 exp3 ,...)    
    (define localtemp (string->symbol(string-append* "TMP" (list (number->string temcounter)))))
    (define localtemp1 (string->symbol(string-append* "TMP" (list (number->string (add1 temcounter))))))
    (set-add! dataset (list 'data localtemp 0))
    (set-add! dataset (list 'data localtemp1 0))
    (if (= 2 (length op))
        (begin
          (set! temcounter (+ 2 temcounter))
          (append (solve-op localtemp (car op)) (solve-op localtemp1 (second op))
                  (list (list 'lor target localtemp localtemp1))
                  out))
        (begin          
          (set! temcounter (+ 2 temcounter))
          (solveor localtemp (cdr op) (append (solve-op localtemp1 (car op)) (list(list 'lor target localtemp1 localtemp)) out))))) 
  (cond
    [(boolean? op)(if (equal? #t op)
                       (list(list 'move target #t))
                       (list(list 'move target #f)))]
    [(not (list? op)) (cond
                        [(and (symbol? op) (symbol=? 'true op)) (list(list 'move target #t))]
                        [(and (symbol? op) (symbol=? 'false op)) (list(list 'move target #f))]
                        [true (list(list 'move target op))]
                        )]
    [(and (= (length op) 2) (symbol? (first op)) (or (symbol=? (first op) 'and) (symbol=? (first op) 'or)))
     (if (symbol=? (first op) 'and)
         (solveand target (list (second op) #t) empty)
         (solveor target (list  (second op) #f) empty))]
    [(= 2 (length op))
     (begin
       (define localtemp1 (string->symbol(string-append* "TMP" (list (number->string temcounter)))))
       (set! temcounter (add1 temcounter))
       (append (list(list 'lnot target localtemp1)) (solve-op localtemp1 (list '* 1 (second op)))))]
    [(> (length op) 3);; op = (and/or bexp1 bexp2 bexp3 bexp4...)
     (if (symbol=? (car op) 'and) (solveand target (cdr op) empty)
         (solveor target (cdr op) empty))]
    [(and (list? (second op))(list? (third op))) ;(and (> 10 (+ x y))(< y (+ x y)))
     (define localtemp (string->symbol(string-append* "TMP" (list (number->string temcounter)))))
     (define localtemp1 (string->symbol(string-append* "TMP" (list (number->string (add1 temcounter))))))
     (begin       
       (set! temcounter (+ 2 temcounter))
       (set-add! dataset (list 'data localtemp 0))
       (set-add! dataset (list 'data localtemp1 0))
       (append (solve-op localtemp (second op))
               (solve-op localtemp1 (third op))
               (list (list (hash-ref dispatchtable (first op)) target localtemp localtemp1))))]
    [(list? (second op))
     (define localtemp (string->symbol(string-append* "TMP" (list (number->string temcounter)))))
     (begin
       (set! temcounter (+ 1 temcounter))
       (set-add! dataset (list 'data localtemp 0))
       (append (solve-op localtemp (second op))
               (list (list (hash-ref dispatchtable (first op)) target localtemp
                           (cond
                             [(symbol? (third op)) (cond
                                                     [(symbol=? (third op) 'true) #t]
                                                     [(symbol=? (third op) 'false) #f]
                                                     [true (third op)])]
                             [true (third op)])))
               ))]
    [(list? (third op))
     (define localtemp (string->symbol(string-append* "TMP" (list (number->string temcounter)))))
     (begin
       (set! temcounter (+ 1 temcounter))
       (set-add! dataset (list 'data localtemp 0))
       (append (solve-op localtemp (third op))
               (list (list (hash-ref dispatchtable (first op)) target
                           (cond
                             [(symbol? (second op)) (cond
                                                     [(symbol=? (second op) 'true) #t]
                                                     [(symbol=? (second op) 'false) #f]
                                                     [true (second op)])]
                             [true (second op)])
                           localtemp))
               ))]
    [true (list (list (hash-ref dispatchtable (first op)) target
                      (cond
                             [(symbol? (second op)) (cond
                                                     [(symbol=? (second op) 'true) #t]
                                                     [(symbol=? (second op) 'false) #f]
                                                     [true (second op)])]
                             [true (second op)])
                      (cond
                             [(symbol? (third op)) (cond
                                                     [(symbol=? (third op) 'true) #t]
                                                     [(symbol=? (third op) 'false) #f]
                                                     [true (third op)])]
                             [true (third op)])))]  
    ))


(define (compile-simp explst)
  (define (solvevar varlst) ;a void function
    (if (empty? varlst) empty
        (begin
          (set-add! dataset (list 'data (first (car varlst)) (second (car varlst))))
          (solvevar (cdr varlst)))))
  (define (solveif con stmt1 stmt2);correct
    (begin
      (set! temcounter (add1 temcounter))
      (define templabel1 (string->symbol(string-append* "label" (list (number->string labelcounter)))))
      (define templabel2 (string->symbol(string-append* "label" (list (number->string (+ 1 labelcounter))))))
      (define templabel3 (string->symbol(string-append* "label" (list (number->string (+ 2 labelcounter))))))
      (define localtemp (string->symbol(string-append* "TMP" (list (number->string (- temcounter 1))))))
      (set-add! dataset (list 'data localtemp 0))
      (define lst1 (solve-op localtemp con))
      (define lst2 (list 'branch localtemp templabel1))      
      (define lst3 (list 'jump templabel2))
      (define lst4 (list 'label templabel1))
      (set! labelcounter (+ 3 labelcounter))
      (define stmt1-code (solveseq stmt1 empty))
      (define lst5 (list 'jump templabel3))
      (define lst6 (list 'label templabel2))
      (define stmt2-code (solveseq stmt2 empty))
      (define lst7 (list 'label templabel3))
      (append lst1 (list lst2 lst3 lst4) stmt1-code (list lst5 lst6) stmt2-code (list lst7))
      ))
  (define (solvewhile con stmts);a list of statements to be executed in the while loop.
    (begin
      (set! temcounter (add1 temcounter))
      (define templabel1 (string->symbol(string-append* "label" (list (number->string labelcounter)))))
      (define templabel2 (string->symbol(string-append* "label" (list (number->string (+ 1 labelcounter))))))
      (define templabel3 (string->symbol(string-append* "label" (list (number->string (+ 2 labelcounter))))))
      (define lst0 (list 'label templabel1))
      (set! labelcounter (+ 3 labelcounter))
      (define localtemp (string->symbol(string-append* "TMP" (list (number->string (- temcounter 1))))))
      (set-add! dataset (list 'data localtemp 0))
      (define lst1 (solve-op localtemp con))
      (define lst2 (list 'branch localtemp templabel2))
      (define lst3 (list 'jump templabel3))
      (define lst4 (list 'label templabel2))
      (define lst5 (list 'jump templabel1))
      (define lst6 (list 'label templabel3))      
      (append (list lst0) lst1 (list lst2 lst3 lst4)(solveseq stmts empty)(list lst5 lst6))))
  (define (solveseq lst acc)
    (cond
      [(empty? lst) acc]
      [(symbol? (car lst)) (cs-h lst empty)]
      [true (solveseq (cdr lst) (append acc (cs-h (car lst) empty)))]))
  (define (solveprint a)
    (define localtemp (string->symbol(string-append* "TMP" (list (number->string temcounter)))))
    (begin
      (set! temcounter (add1 temcounter))
      (set-add! dataset (list 'data localtemp 0))
      (append (solve-op localtemp a) (list(list 'print-val localtemp)) )))
  (define (cs-h explst aprimplst)
    (if (empty? explst) true
        (match explst
          [`(vars ,a ,b) (cs-h b (solvevar a))]
          [`(vars ,a ,stmts ___) (cs-h (cons 'seq stmts) (solvevar a))]
          [`(set ,a ,b) (append aprimplst (solve-op a b))]
          [`(while ,con ,stmts ...)(append aprimplst (solvewhile con stmts))]
          [`(seq ,val ___) (append aprimplst (solveseq val empty))]
          [`(print ,a) (cond
                         [(number? a) (append aprimplst (list (list 'print-string a)))]
                         [(string? a) (append aprimplst (list (list 'print-string a)))]
                         [(symbol? a) (cond
                                        [(symbol=? a 'true) (append aprimplst (list (list 'print-string #t)))]
                                        [(symbol=? a 'false) (append aprimplst (list (list 'print-string #f)))]
                                        [true (append aprimplst (list (list 'print-val a)))])]
                         [(list? a) (append aprimplst (solveprint a))])]
          [`(skip) aprimplst]
          [`(iif ,con ,stmt1 ,stmt2) (append aprimplst (solveif con stmt1 stmt2))]
          ))) 
  (append (cs-h explst empty)(set->list dataset)))

(define test7 '(vars [(x 10) (y 10) (z 10)]
                     (set x (and (and (> 10 (+ x y)) (< y (+ x y)))
                               (< 9 z)))
                     (print x)))
; Original Sugar
(define-syntax-rule
  (named-let-1 proc-id ([arg-id init-expr] ...) body)
  (letrec ([proc-id (lambda (arg-id ...) body)])
    (proc-id init-expr ...)))

; Refined Sugar
(define-syntax-rule
  (named-let-2 proc-id ([arg-id init-expr] ...) body)
  (letrec ([f (lambda (arg-id ...) (let ([proc-id f]) body))])
    (f init-expr ...)))


; This desugaring has the correct binding structure,
; but all of the generated temporaries are a mess.
(define-syntax named-let-3
  (lambda (stx)
    (syntax-case stx ()
      [(named-let-3 tag [[name val] ...] body ...)
       (with-syntax (((x ...) (generate-temporaries (syntax (name ...)))))
                    (syntax ((letrec [[f (lambda [x ...]
                                           (let [[tag f] [name x] ...] body ...))]]
                               f)
                             val ...)))])))

(define (rev-1 lst)
  (named-let-1 rev
      [[unreversed lst]
       [reversed empty]]
    (if (empty? unreversed)
        reversed
        (rev (cdr unreversed)
             (cons (car unreversed) reversed)))))

(define (rev-2 lst)
  (named-let-2
   rev [[unreversed lst]
        [reversed empty]]
   (if (empty? unreversed)
       reversed
       (rev (cdr unreversed)
            (cons (car unreversed) reversed)))))

(define (rev-3 lst)
  (named-let-3
   rev [[unreversed lst]
        [reversed empty]]
   (if (empty? unreversed)
       reversed
       (rev (cdr unreversed)
            (cons (car unreversed) reversed)))))

(print (rev-1 (list 1 2 3)))
(newline)
(print (rev-2 (list 1 2 3)))
(newline)
(print (rev-3 (list 1 2 3)))
(newline)
(print 'ok)
(newline)

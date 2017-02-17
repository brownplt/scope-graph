(define-syntax named-let-1
  (syntax-rules ()
    [(named-let-1 tag [[name val] ...] body)
     ((letrec [[tag (lambda [name ...] body)]]
        tag)
      val ...)]))

(define-syntax named-let-2
  (syntax-rules ()
    [(named-let-2 tag [[name val] ...] body)
     ((letrec [[f (lambda [name ...] (let [[tag f]] body))]]
        f)
      val ...)]))

; This desugaring has the correct binding structure,
; but all of the generated temporaries are a mess.
(define-syntax named-let-3
  (lambda (stx)
    (syntax-case stx ()
      [(named-let-3 tag [[name val] ...] body)
       (with-syntax (((x ...) (generate-temporaries (syntax (name ...)))))
                    (syntax ((letrec [[f (lambda [x ...]
                                           (let [[tag f] [name x] ...] body))]]
                               f)
                             val ...)))])))

(define (rev-1 lst)
  (named-let-1
   rev [[forward lst]
        [backward (list)]]
   (if (empty? forward)
       backward
       (rev (cdr forward)
            (cons (car forward) backward)))))

(define (rev-2 lst)
  (named-let-2
   rev [[forward lst]
        [backward (list)]]
   (if (empty? forward)
       backward
       (rev (cdr forward)
            (cons (car forward) backward)))))

(define (rev-3 lst)
  (named-let-3
   rev [[forward lst]
        [backward (list)]]
   (if (empty? forward)
       backward
       (rev (cdr forward)
            (cons (car forward) backward)))))

(print (rev-1 (list 1 2 3)))
(newline)
(print (rev-2 (list 1 2 3)))
(newline)
(print (rev-3 (list 1 2 3)))
(newline)
(print 'ok)
(newline)

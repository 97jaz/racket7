(library (schemify)
  (export schemify-linklet
          lift-in-schemified-linklet
          prim-knowns
          a-known-procedure
          a-known-constant)
  (import (chezpart)
          (rename (core)
                  [correlated? core:correlated?]
                  [correlated-e core:correlated-e])
          (regexp)
          (io)
          (known-primitive))

  ;; Bridge for flattened "schemify/wrap.rkt"
  ;; and "schemify/wrap-annotation.rkt"
  (define (primitive-table name)
    (case name
      [(|#%kernel|)
       (hash 'syntax? core:correlated?
             'syntax-e core:correlated-e)]
      [(|#%annotation|)
       (hash 'annotation? annotation?
             'annotation-expression annotation-expression)]
      [else #f]))

  (include "compiled/schemify.scm")

  (define (add-known ht syms extract known)
    (let loop ([ht ht] [syms syms])
      (cond
       [(null? syms) ht]
       [else (loop (hash-set ht
                             (extract (car syms))
                             (if (procedure? known)
                                 (known (car syms))
                                 known))
                   (cdr syms))])))

  (define prim-knowns
    (add-known
     (add-known
      (add-known
       (add-known (hasheq) known-procedures (lambda (s) s) a-known-procedure)
       known-struct-type-property/immediate-guards (lambda (s) s)
       a-known-struct-type-property/immediate-guard)
      known-constructors car
      (lambda (s) (known-constructor (car s) (cadr s))))
     known-constants (lambda (x) x)
     a-known-constant)))
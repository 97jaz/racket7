#lang racket/base
(require (for-syntax racket/base
                     syntax/kerncase
                     racket/syntax
                     "private/stxparamkey.rkt")
         (for-meta 2  ; for wrap-et-param
                   racket/base
                   syntax/kerncase)
         "private/stxparam.rkt"
         "private/local.rkt")

(provide splicing-let-syntax
         splicing-let-syntaxes
         splicing-letrec-syntax
         splicing-letrec-syntaxes
         splicing-let
         splicing-let-values
         splicing-letrec
         splicing-letrec-values
         splicing-letrec-syntaxes+values
         splicing-local
         splicing-syntax-parameterize)

(module syntax/loc/props racket/base
  (require (for-syntax racket/base))
  (provide syntax/loc/props quasisyntax/loc/props)

  (define-syntaxes [syntax/loc/props quasisyntax/loc/props]
    (let ()
      (define (mk-syntax/loc/props syntax-id)
        (λ (stx)
          (syntax-case stx ()
            [(_ src-expr template)
             #`(let ([src src-expr])
                 (datum->syntax (quote-syntax #,stx) (syntax-e (#,syntax-id template)) src src))])))
      (values (mk-syntax/loc/props #'syntax)
              (mk-syntax/loc/props #'quasisyntax)))))

(require (for-syntax 'syntax/loc/props)
         (for-meta 2 'syntax/loc/props))

(define-syntax (splicing-local stx)
  (do-local stx (lambda (def-ctx expand-context sbindings vbindings bodys)
                  (if (eq? 'expression (syntax-local-context))
                      (quasisyntax/loc stx
                        (letrec-syntaxes+values
                         #,sbindings
                         #,vbindings
                         #,@bodys))
                      ;; Since we alerady have bindings for the current scopes,
                      ;; add an extra scope for re-binding:
                      (let ([i (make-syntax-introducer #t)])
                        (with-syntax ([([s-ids s-rhs] ...) (i sbindings)]
                                      [([(v-id ...) v-rhs] ...) (i vbindings)]
                                      [(body ...) (i bodys)]
                                      [(marked-id markless-id)
                                       (let ([id #'id])
                                         ;; The marked identifier should have both the extra
                                         ;; scope and the intdef scope, to be removed from
                                         ;; definitions expanded from `body`:
                                         (list (i (internal-definition-context-introduce def-ctx id))
                                               id))])
                          (with-syntax ([(top-decl ...)
                                         (if (equal? 'top-level (syntax-local-context))
                                             #'((define-syntaxes (v-id ... ...) (values)))
                                             null)])
                            (quasisyntax/loc stx
                              (begin
                                top-decl ...
                                (define-syntaxes s-ids s-rhs) ...
                                (define-values (v-id ...) v-rhs) ...
                                (splicing-let-start/body marked-id markless-id body)
                                ...)))))))))

(define-syntax (splicing-let-syntax stx)
  (do-let-syntax stx #f #f #'let-syntax #'define-syntaxes #f))

(define-syntax (splicing-let-syntaxes stx)
  (do-let-syntax stx #f #t #'let-syntaxes #'define-syntaxes #f))

(define-syntax (splicing-letrec-syntax stx)
  (do-let-syntax stx #t #f #'letrec-syntax #'define-syntaxes #f))

(define-syntax (splicing-letrec-syntaxes stx)
  (do-let-syntax stx #t #t #'letrec-syntaxes #'define-syntaxes #f))

(define-syntax (splicing-let stx)
  (do-let-syntax stx #f #f #'let #'define-values #f))

(define-syntax (splicing-let-values stx)
  (do-let-syntax stx #f #t #'let-values #'define-values #f))

(define-syntax (splicing-letrec stx)
  (do-let-syntax stx #t #f #'letrec #'define-values #t))

(define-syntax (splicing-letrec-values stx)
  (do-let-syntax stx #t #t #'letrec-values #'define-values #t))

(define-for-syntax (do-let-syntax stx rec? multi? let-id def-id need-top-decl?)
  (syntax-case stx ()
    [(_ ([ids expr] ...) body ...)
     (let ([all-ids (map ((if multi? check-ids check-id) stx)
                         (syntax->list #'(ids ...)))])
       (check-dup-binding stx all-ids)
       (if (eq? 'expression (syntax-local-context))
           (with-syntax ([LET let-id])
             (syntax/loc stx
               (LET ([ids expr] ...)
                 (#%expression body)
                 ...)))
           (with-syntax ([((id ...) ...)
                          (for/list ([ids (in-list all-ids)])
                            (for/list ([id (in-list ids)])
                              (syntax-property id 'definition-intended-as-local #t)))]
                         [DEF def-id]
                         [rec? rec?]
                         [(marked-id markless-id)
                          (let ([id #'id])
                            (list ((make-syntax-introducer #t) id)
                                  id))])
             (with-syntax ([(top-decl ...)
                            (if (and need-top-decl? (equal? 'top-level (syntax-local-context)))
                                #'((define-syntaxes (id ... ...) (values)))
                                null)])
               
               (syntax/loc stx
                 (begin
                   (splicing-let-start/def marked-id markless-id #f top-decl) ...
                   (splicing-let-start/def marked-id markless-id rec? (DEF (id ...) expr))
                   ...
                   (splicing-let-start/body marked-id markless-id body)
                   ...))))))]))

(define-syntax (splicing-let-start/def stx)
  (syntax-case stx ()
    [(_ marked-id markless-id rec? (DEF ids rhs))
     ;; Add the mark to every definition's identifiers; also
     ;; add to the body, if it's a recursively scoped binding:
     (let ([i (make-syntax-delta-introducer #'marked-id #'markless-id)])
       #`(DEF #,(i #'ids) #,(if (syntax-e #'rec?)
                                (i #'rhs)
                                #'rhs)))]))

(define-syntax (splicing-let-start/body stx)
  (syntax-case stx ()
    [(_ marked-id markless-id body)
     ;; Tenatively add the mark to the body,; we'll remove it on every
     ;; bit of syntax that turns out to be a binding:
     (let ([i (make-syntax-delta-introducer #'marked-id #'markless-id)])
       #`(splicing-let-body marked-id markless-id #,(i #'body)))]))

(define-for-syntax ((maybe unintro) form)
  (if (syntax-property form 'definition-intended-as-local)
      form
      (unintro form)))

(define-syntax (splicing-let-body stx)
  (syntax-case stx ()
    [(_ marked-id markless-id body)
     (let ([unintro (lambda (form)
                      ((make-syntax-delta-introducer #'marked-id #'markless-id) form 'remove))]
           [body (local-expand #'body (syntax-local-context) #f)])
       (syntax-case body (begin
                           define-values
                           define-syntaxes
                           begin-for-syntax
                           module
                           module*
                           #%require
                           #%provide
                           #%declare)
         [(begin form ...)
          (syntax/loc/props body
            (begin (splicing-let-body marked-id markless-id form) ...))]
         [(define-values ids rhs)
          (quasisyntax/loc/props body
            (define-values #,(map (maybe unintro) (syntax->list #'ids)) rhs))]
         [(define-syntaxes ids rhs)
          (quasisyntax/loc/props body
            (define-syntaxes #,(map (maybe unintro) (syntax->list #'ids)) rhs))]
         [(begin-for-syntax e ...)
          (syntax/loc/props body
            (begin-for-syntax (splicing-let-body/et marked-id markless-id e) ...))]
         [(module . _) (unintro body)]
         [(module* . _) body]
         [(#%require . _) (unintro body)]
         [(#%provide . _) body]
         [(#%declare . _) body]
         [_ body]))]))

(begin-for-syntax
  (define-for-syntax ((maybe unintro) form)
    (if (syntax-property form 'definition-intended-as-local)
        form
        (unintro form)))

  (define-syntax (splicing-let-body/et stx)
    (syntax-case stx ()
      [(_ marked-id markless-id body)
       (let* ([unintro (lambda (form)
                         ((make-syntax-delta-introducer #'marked-id #'markless-id) form 'remove))]
              [body (local-expand #'body (syntax-local-context) #f)])
         (syntax-case body (begin
                             define-values
                             define-syntaxes
                             begin-for-syntax
                             module
                             module*
                             #%require
                             #%provide
                             #%declare)
           [(begin form ...)
            (syntax/loc/props body
              (begin (splicing-let-body/et marked-id markless-id form) ...))]
           [(define-values ids rhs)
            (quasisyntax/loc/props body
              (define-values #,(map (maybe unintro) (syntax->list #'ids)) rhs))]
           [(define-syntaxes ids rhs)
            (quasisyntax/loc/props body
              (define-syntaxes #,(map (maybe unintro) (syntax->list #'ids)) rhs))]
           [(begin-for-syntax . es)
            ;; Give up on splicing definitions at phase level 2 and deeper:
            body]
           [(module . _) (unintro body)]
           [(module* . _) body]
           [(#%require . _) (unintro body)]
           [(#%provide . _) body]
           [(#%declare . _) body]
           [_ body]))])))

(define-for-syntax ((check-id stx) id-stx)
  (unless (identifier? id-stx)
    (raise-syntax-error #f "expected an identifier" stx id-stx))
  (list id-stx))

(define-for-syntax ((check-ids stx) ids-stx)
  (let ([ids (syntax->list ids-stx)])
    (unless ids
      (raise-syntax-error 
       #f
       "expected a parenthesized sequence of identifiers"
       stx
       ids-stx))
    (for-each (check-id stx) ids)
    ids))

(define-for-syntax (check-dup-binding stx idss)
  (let ([dup-id (check-duplicate-identifier (apply append idss))])
    (when dup-id
      (raise-syntax-error #f "duplicate binding" stx dup-id))))

;; ----------------------------------------

(define-syntax (splicing-letrec-syntaxes+values stx)
  (syntax-case stx ()
    [(_ ([sids sexpr] ...) ([vids vexpr] ...) body ...)
     (let* ([all-sids (map (check-ids stx)
                           (syntax->list #'(sids ...)))]
            [all-vids (map (check-ids stx)
                           (syntax->list #'(vids ...)))]
            [all-ids (append all-sids all-vids)])
       (check-dup-binding stx all-ids)
       (if (eq? 'expression (syntax-local-context))
           (syntax/loc stx
             (letrec-syntaxes+values ([sids sexpr] ...) ([vids vexpr] ...)
               (#%expression body) ...))
           (with-syntax ([((vid ...) ...) all-vids]
                         [(marked-id markless-id)
                          (let ([id #'id])
                            (list ((make-syntax-introducer #t) id)
                                  id))])
             (with-syntax ([(top-decl ...)
                            (if (equal? 'top-level (syntax-local-context))
                                #'((define-syntaxes (vid ... ...) (values)))
                                null)])
               (syntax/loc stx
                 (begin
                   (splicing-let-start/def marked-id markless-id #f top-decl) ...
                   (splicing-let-start/def marked-id markless-id #t (define-syntaxes sids sexpr))
                   ...
                   (splicing-let-start/def marked-id markless-id #t (define-values (vid ...) vexpr))
                   ...
                   (splicing-let-start/body marked-id markless-id body ...)))))))]))

;; ----------------------------------------

(define-syntax (splicing-syntax-parameterize stx)
  (if (eq? 'expression (syntax-local-context))
      ;; Splicing is no help in an expression context:
      (do-syntax-parameterize stx #'let-syntaxes #f)
      ;; Let `syntax-parameterize' check syntax, then continue
      (do-syntax-parameterize stx #'ssp-let-syntaxes #t)))

(define-syntax (ssp-let-syntaxes stx)
  (syntax-case stx ()
    [(_ ([(id) rhs] ...) (llk binds body ...))
     #'(begin
         ;; Evaluate each RHS only once:
         (define-syntax id rhs) ...
         ;; Partially expand `body' to push down `let-syntax':
         (expand-ssp-body binds body)
         ...)]))

(define-syntax (expand-ssp-body stx)
  (syntax-case stx ()
    [(_ binds body)
     (let ([ctx (syntax-local-make-definition-context #f #f)])
       (let ([body (parameterize ([current-parameter-environment
                                   (extend-parameter-environment (current-parameter-environment) #'binds)])
                     (local-expand #'(force-expand body)
                                   (syntax-local-context)
                                   null ;; `force-expand' actually determines stopping places
                                   ctx))])
         (let ([body
                ;; Extract expanded body out of `body':
                (syntax-case body (quote)
                  [(quote body) #'body])])
           (syntax-case body ( begin
                               define-values
                               define-syntaxes
                               begin-for-syntax
                               module
                               module*
                               #%require
                               #%provide
                               #%declare )
              [(begin expr ...)
               (syntax/loc/props body
                 (begin (expand-ssp-body binds expr) ...))]
              [(define-values (id ...) rhs)
               (syntax/loc/props body
                 (define-values (id ...)
                   (let-local-keys binds rhs)))]
              [(define-syntaxes ids rhs)
               (syntax/loc/props body
                 (define-syntaxes ids (wrap-param-et rhs binds)))]
              [(begin-for-syntax e ...)
               (syntax/loc/props body
                 (begin-for-syntax (wrap-param-et e binds) ...))]
              [(module . _) body]
              [(module* . _) body]
              [(#%require . _) body]
              [(#%provide . _) body]
              [(#%declare . _) body]
              [expr (syntax/loc body
                      (let-local-keys binds expr))]))))]))

(define-syntax (letrec-syntaxes/trans stx)
  (syntax-case stx ()
    [(_ bindings body)
     (syntax-property
      #'(letrec-syntaxes bindings body)
      'certify-mode
      'transparent)]))

(define-syntax (force-expand stx)
  (syntax-case stx ()
    [(_ stx)
     ;; Expand `stx' to reveal type of form, and then preserve it via
     ;; `quote':
     (syntax-property
      #`(quote #,(local-expand #'stx
                               'module
                               (kernel-form-identifier-list)
                               #f))
      'certify-mode
      'transparent)]))

(begin-for-syntax
 (define-syntax (wrap-param-et stx)
   (syntax-case stx ()
     [(_ e binds)
      (let ([as-expression
             (lambda ()
               #'(parameterize ([current-parameter-environment
                                 (extend-parameter-environment (current-parameter-environment) (quote-syntax binds))])
                   e))])
        (if (eq? (syntax-local-context) 'expression)
            (as-expression)
            (let ([e (local-expand #'e
                                   (syntax-local-context)
                                   (kernel-form-identifier-list)
                                   #f)])
              (syntax-case e (begin
                               define-syntaxes define-values
                               begin-for-syntax
                               module module*
                               #%require #%provide #%declare
                               quote-syntax)
                [(begin form ...)
                 (syntax/loc/props e
                   (begin (wrap-param-et form binds) ...))]
                [(define-syntaxes . _) e]
                [(begin-for-syntax . _) e]
                [(define-values ids rhs)
                 (syntax/loc/props e
                   (define-values ids (wrap-param-et rhs binds)))]
                [(module . _) e]
                [(module* . _) e]
                [(#%require . _) e]
                [(#%provide . _) e]
                [(#%declare . _) e]
                [(quote-syntax . _) e]
                [else (as-expression)]))))])))

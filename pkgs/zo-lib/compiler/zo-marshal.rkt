#lang racket/base
(require compiler/zo-structs
         racket/port
         racket/vector
         racket/match
         racket/contract
         racket/local
         racket/list
         racket/dict
         racket/function
         racket/pretty
         racket/path
         racket/set
         racket/extflonum)

(provide/contract
 [zo-marshal (hash? . -> . bytes?)]
 [zo-marshal-to (hash? output-port? . -> . void?)])

(struct not-ready ())

(struct encoded-scope (relative-id [content #:mutable]) #:prefab)

(define (zo-marshal top)
  (define bs (open-output-bytes))
  (zo-marshal-to top bs)
  (get-output-bytes bs))

(define (zo-marshal-to top outp) 
  (if (and (hash? top)
           (for/and ([(k v) (in-hash top)])
             (and (list? k)
                  (andmap symbol? k)
                  (hash? v))))
      ;; linklet directory:
      (zo-marshal-directory-to top outp)
      ;; single linklet bundle:
      (zo-marshal-bundle-to top outp)))

(define (zo-marshal-directory-to top outp)
  ;; Write the compiled form header
  (write-bytes #"#~" outp)
  ;; Write the version:
  (define version-bs (string->bytes/latin-1 (version)))
  (write-bytes (bytes (bytes-length version-bs)) outp)
  (write-bytes version-bs outp)

  (write-byte (char->integer #\D) outp)

  (struct bundle-bytes (code-bstr name-list name-bstr offset))
  ;; bytestring encodings of the bundles and bundle names
  (define unsorted-pre-bundle-bytess
    (for/list ([(name bundle) (in-hash top)])
      (define name-bstr
        (if (null? name)
            #""
            (apply bytes-append
                   (for/list ([sym (in-list name)])
                     (define b (string->bytes/utf-8 (symbol->string sym)))
                     (define len (bytes-length b))
                     (bytes-append (if (len . < . 255)
                                       (bytes len)
                                       (bytes-append
                                        (bytes 255)
                                        (integer->integer-bytes len 4 #f #f)))
                                   b)))))
      (define o (open-output-bytes))
      (zo-marshal-bundle-to bundle o)
      (bundle-bytes (get-output-bytes o)
                    name
                    name-bstr
                    0)))
  ;; Write order must correspond to a post-order traversal
  ;; of the tree, so write
  (define pre-bundle-bytess
    (sort unsorted-pre-bundle-bytess
          (lambda (a b)
            (let loop ([a a] [b b])
              (cond
               [(null? a) #f]
               [(null? b) #t]
               [(eq? (car a) (car b)) (loop (cdr a) (cdr b))]
               [(symbol<? (car a) (car b)) #t]
               [else #f])))))
  ;; Write count:
  (write-bytes (int->bytes (length pre-bundle-bytess)) outp)
  ;; Size of btree:
  (define header-size
    (+ 8
       (string-length (version))))
  (define btree-size
    (+ header-size
       (apply + (for/list ([mb (in-list pre-bundle-bytess)])
                  (+ (bytes-length (bundle-bytes-name-bstr mb))
                     20)))))
  ;; Add offsets to bundle-bytess:
  (define bundle-bytess (let loop ([offset btree-size] [bundle-bytess pre-bundle-bytess])
                       (if (null? bundle-bytess)
                           null
                           (let ([mb (car bundle-bytess)])
                             (cons (bundle-bytes (bundle-bytes-code-bstr mb)
                                                 (bundle-bytes-name-list mb)
                                                 (bundle-bytes-name-bstr mb)
                                                 offset)
                                   (loop (+ offset
                                            (bytes-length (bundle-bytes-code-bstr mb)))
                                         (cdr bundle-bytess)))))))
  ;; Sort by name for btree order:
  (define sorted-bundle-bytess 
    (list->vector (sort bundle-bytess bytes<? #:key bundle-bytes-name-bstr)))
  (define right-offsets (make-vector (vector-length sorted-bundle-bytess) 0))
  ;; Write out btree or compute offsets:
  (define (write-btree write-bytes)
    (let loop ([lo 0] [hi (vector-length sorted-bundle-bytess)] [pos header-size])
      (define mid (quotient (+ lo hi) 2))
      (define mb (vector-ref sorted-bundle-bytess mid))
      (define name-len (bytes-length (bundle-bytes-name-bstr mb)))
      (write-bytes (int->bytes name-len) outp)
      (write-bytes (bundle-bytes-name-bstr mb) outp)
      (write-bytes (int->bytes (bundle-bytes-offset mb)) outp)
      (write-bytes (int->bytes (bytes-length (bundle-bytes-code-bstr mb))) outp)
      (define left-pos (+ pos name-len 20))
      (write-bytes (int->bytes (if (= lo mid)
                                   0
                                   left-pos))
                   outp)
      (write-bytes (int->bytes (if (= (add1 mid) hi)
                                   0
                                   (vector-ref right-offsets mid)))
                   outp)
      (define right-pos (if (= lo mid)
                            left-pos
                            (loop lo mid left-pos)))
      (vector-set! right-offsets mid right-pos)
      (if (= (add1 mid) hi)
          right-pos
          (loop (add1 mid) hi right-pos))))
  (write-btree void) ; to fill `right-offsets'
  (write-btree write-bytes) ; to actually write the btree
  ;; Write bundles:
  (for ([mb (in-list bundle-bytess)])
    (write-bytes (bundle-bytes-code-bstr mb) outp)))

(define (zo-marshal-bundle-to top outp) 
  ; (obj -> (or pos #f)) output-port -> number
  ; writes top to outp using shared-obj-pos to determine symref
  ; returns the file position at the end of the compilation top
  (define (out-compilation-top shared-obj-pos shared-obj-pos-any counting? outp)
    (out-anything top (make-out outp shared-obj-pos shared-obj-pos-any counting?))
    (file-position outp))
  
  ; -> vector
  ; calculates what values show up in the compilation top more than once
  ; closures are always included even if they only show up once
  (define (create-symbol-table)
    (define encountered (make-hasheq))
    (define shared (make-hasheq))
    (define (encountered? v)
      ((hash-ref encountered v 0) . > . 0))
    (define (encounter! v)
      (hash-update! encountered v add1 0) 
      #f)
    (define (shared-obj-pos v #:error? [error? #f])
      (hash-ref shared v 
                (if error?
                    (λ () (error 'symref "~e not in symbol table" v))
                    #f)))
    (define (share! v)
      (or (shared-obj-pos v)
          (let ([pos (add1 (hash-count shared))])
            (hash-set! shared v pos) 
            pos)))
    
    (out-compilation-top 
     (λ (v #:error? [error? #f])
       (cond
         [(hash? v) (error 'create-symbol-table "current type trace: ~a" (current-type-trace))]
         [(closure? v)
          (let ([pos (share! v)])
            (if (encountered? v)
                pos
                (encounter! v)))]
         [error? ; If we would error if this were not present, then we must share it
          (encounter! v)
          (share! v)]
         [(encountered? v)
          (share! v)]
         [else
          (encounter! v)]))
     (lambda (v) #f)
     #t
     (open-output-nowhere))
    
    (define symbol-table (make-vector (hash-count shared) (not-ready)))
    (hash-map shared (λ (k v) (vector-set! symbol-table (sub1 v) k)))
    (values symbol-table shared-obj-pos))
  
  (define-values (symbol-table shared-obj-pos)
    (create-symbol-table))
  
  ; vector output-port -> (listof number) number
  ; writes symbol-table to outp
  ; returns the file positions of each value in the symbol table and the end of the symbol table
  (define (out-symbol-table symbol-table outp)
    (define (shared-obj-pos/modulo-v v)
      (define skip? #t)
      (λ (v2 #:error? [error? #f])
        (if (and skip? (eq? v v2))
            (begin
              (set! skip? #f)
              #f)
            (shared-obj-pos v2 
                            #:error? error?))))
    (values
     (for/list ([v (in-vector symbol-table)]
                [i (in-naturals)])
       (begin0
         (file-position outp)
         (out-anything v (make-out outp (shared-obj-pos/modulo-v v) shared-obj-pos #f))))
     (file-position outp)))
  
  ; Calculate file positions
  (define counting-port (open-output-nowhere))
  (define-values (offsets post-shared) (out-symbol-table symbol-table counting-port))
  (define all-forms-length (out-compilation-top shared-obj-pos shared-obj-pos #f counting-port))
  
  ; Write the compiled form header
  (write-bytes #"#~" outp)
  
  ; Write the version (notice that it isn't the same as out-string)
  (define version-bs (string->bytes/latin-1 (version)))
  (write-bytes (bytes (bytes-length version-bs)) outp)
  (write-bytes version-bs outp)

  ;; "B" is for linklet "bundle" (as opposed to a linklet directory)
  (write-byte (char->integer #\B) outp)

  ; Write empty hash code
  (write-bytes (make-bytes 20 0) outp)
  
  ; Write the symbol table information (size, offsets)
  (define symtabsize (add1 (vector-length symbol-table)))
  (write-bytes (int->bytes symtabsize) outp)
  (define all-short? (post-shared . < . #xFFFF))
  (write-bytes (bytes (if all-short? 1 0)) outp)
  (for ([o (in-list offsets)])
    (write-bytes (integer->integer-bytes o (if all-short? 2 4) #f #f) outp))
  ; Post-shared is where the top actually starts
  (write-bytes (int->bytes post-shared) outp)
  ; This is where the file should end
  (write-bytes (int->bytes all-forms-length) outp)
  ; Actually write the zo
  (out-symbol-table symbol-table outp)
  (out-compilation-top shared-obj-pos shared-obj-pos #f outp)
  (void))

;; ----------------------------------------

(define toplevel-type-num 0)
(define sequence-type-num 6)
(define unclosed-procedure-type-num 8)
(define let-value-type-num 9)
(define let-void-type-num 10)
(define letrec-type-num 11)
(define wcm-type-num 13)
(define define-values-type-num 14)
(define set-bang-type-num 15)
(define boxenv-type-num 16)
(define begin0-sequence-type-num 17)
(define varref-form-type-num 18)
(define apply-values-type-num 19)
(define with-immed-mark-type-num 20)
(define case-lambda-sequence-type-num 21)
(define inline-variants-type-num 22)
(define linklet-type-num 24)

(define-syntax define-enum
  (syntax-rules ()
    [(_ n) (begin)]
    [(_ n id . rest)
     (begin
       (define id n)
       (define-enum (add1 n) . rest))])) 

(define-enum
  0
  CPT_ESCAPE
  CPT_SYMBOL
  CPT_SYMREF
  CPT_WEIRD_SYMBOL
  CPT_KEYWORD
  CPT_BYTE_STRING
  CPT_CHAR_STRING
  CPT_CHAR
  CPT_INT
  CPT_NULL
  CPT_TRUE
  CPT_FALSE
  CPT_VOID
  CPT_BOX
  CPT_PAIR
  CPT_LIST
  CPT_VECTOR
  CPT_HASH_TABLE
  CPT_LET_ONE_TYPED
  CPT_MARSHALLED
  CPT_QUOTE
  CPT_REFERENCE
  CPT_LOCAL
  CPT_LOCAL_UNBOX
  CPT_SVECTOR
  CPT_APPLICATION
  CPT_LET_ONE
  CPT_BRANCH
  CPT_PATH
  CPT_CLOSURE
  CPT_DELAY_REF ; used to delay loading of syntax objects and lambda bodies
  CPT_PREFAB
  CPT_LET_ONE_UNUSED
  CPT_SHARED)

(define CPT_SMALL_NUMBER_START 34)
(define CPT_SMALL_NUMBER_END 62)

(define CPT_SMALL_SYMBOL_START 62)
(define CPT_SMALL_SYMBOL_END 80)

(define CPT_SMALL_MARSHALLED_START 80)
(define CPT_SMALL_MARSHALLED_END 92)

(define CPT_SMALL_LIST_MAX 50)
(define CPT_SMALL_PROPER_LIST_START 92)
(define CPT_SMALL_PROPER_LIST_END (+ CPT_SMALL_PROPER_LIST_START CPT_SMALL_LIST_MAX))

(define CPT_SMALL_LIST_START CPT_SMALL_PROPER_LIST_END)
(define CPT_SMALL_LIST_END 192)

(define CPT_SMALL_LOCAL_START 192)
(define CPT_SMALL_LOCAL_END 207)
(define CPT_SMALL_LOCAL_UNBOX_START 207)
(define CPT_SMALL_LOCAL_UNBOX_END 222)

(define CPT_SMALL_SVECTOR_START 222)
(define CPT_SMALL_SVECTOR_END 247)

(define CPT_SMALL_APPLICATION_START 247)
(define CPT_SMALL_APPLICATION_END 255)

(define CLOS_HAS_REST 1)
(define CLOS_HAS_REF_ARGS 2)
(define CLOS_PRESERVES_MARKS 4)
(define CLOS_NEED_REST_CLEAR 8)
(define CLOS_IS_METHOD 16)
(define CLOS_SINGLE_RESULT 32)

(define BITS_PER_MZSHORT 32)
(define BITS_PER_ARG 4)

(define (int->bytes x)
  (integer->integer-bytes x
                          4
                          #f
                          #f))

(define-struct protected-symref (val))

(define-struct out (s
                    ;; The output port for writing bytecode.
                    shared-index
                    ;; Takes a value and reports/record sharing.
                    ;; On the first pass, the number of times this function is
                    ;; called for a value determines whether sharing is needed
                    ;; for the value. That sharing is reported on later passes
                    ;; by returning a number (a slot in "symbol" table) instead
                    ;; of #f. On the symbol-table filling pass, the first call
                    ;; produces #f so that a value is written into the table.
                    shared-index-any
                    ;; Like `shared-index`, but doesn't record any sharing or
                    ;; produce #f for the immediate value of a symbol table.
                    counting?
                    ;; Set to #t for the first (sharing-finding pass), #f
                    ;; otherwise.
                    ))

(define (out-shared v out k)
  (if (shareable? v)
      (let ([n ((out-shared-index out) v)])
        (if n
            (begin
              (out-byte CPT_SYMREF out)
              (out-number n out))
            (k)))
      (k)))

(define (out-byte v out)
  (write-byte v (out-s out)))

(define (out-bytes b out)
  (write-bytes b (out-s out)))

(define (out-number n out)
  (cond
    [(n . < . 0)
     (if (n . > . -32)
         (out-byte (bitwise-ior #xC0 (- n)) out)
         (begin
           (out-byte #xE0 out)
           (out-bytes (int->bytes (- n)) out)))]
    [(n . < . 128)
     (out-byte n out)]
    [(n . < . #x4000)
     (out-byte (bitwise-ior #x80 (bitwise-and n #x3F)) out)
     (out-byte (bitwise-and #xFF (arithmetic-shift n -6)) out)]
    [else
     (out-byte #xF0 out)
     (out-bytes (int->bytes n) out)]))

(define (out-marshaled type-num val out)
  (if (type-num . < . (- CPT_SMALL_MARSHALLED_END CPT_SMALL_MARSHALLED_START))
      (out-byte (+ CPT_SMALL_MARSHALLED_START type-num) out)
      (begin
        (out-byte CPT_MARSHALLED out)
        (out-number type-num out)))
  (out-anything val out))

(define (or-pred? v . ps)
  (ormap (lambda (?) (? v)) ps))

(define quoting? (make-parameter #f))

(define (shareable? v)
  (define never-share-this?
    (or-pred? v char? maybe-same-as-fixnum? empty? boolean? void? hash?))
  (define always-share-this?
    (or-pred? v closure?))
  (or always-share-this?
      (if (quoting?) 
          #f
          (not never-share-this?))))

(define (maybe-same-as-fixnum? v)
  (and (exact-integer? v)
       (and (v . >= . -1073741824) (v . <= . 1073741823))))

(define (current-type-trace)
  (reverse (continuation-mark-set->list (current-continuation-marks) 'zo)))

(define (typeof v)
  (cond
    [(pair? v) 'cons]
    [(hash? v) 'hash]
    [(prefab-struct-key v) => (λ (key) key)]
    [(vector? v) 'vector]
    [else v]))

(define-syntax with-type-trace
  (syntax-rules ()
    [(_ v body ...)
     #;(begin body ...)
     (with-continuation-mark 'zo (typeof v)
       (begin0 (begin body ...) (void)))]))

(define (type->index type)
  (case type
    [(flonum) 1]
    [(fixnum) 2]
    [(extflonum) 3]
    [else (error 'type->index "unknown type: ~e" type)]))

(define (out-anything v out)
  (with-type-trace v
  (out-shared 
   v out
   (λ ()
     (match v
       [(? char?)
        (out-byte CPT_CHAR out)
        (out-number (char->integer v) out)]
       [(? maybe-same-as-fixnum?)
        (if (and (v . >= . 0)
                 (v . < . (- CPT_SMALL_NUMBER_END CPT_SMALL_NUMBER_START)))
            (out-byte (+ CPT_SMALL_NUMBER_START v) out)
            (begin
              (out-byte CPT_INT out)
              (out-number v out)))]
       [(list)
        (out-byte CPT_NULL out)]
       [#t
        (out-byte CPT_TRUE out)]
       [#f
        (out-byte CPT_FALSE out)]
       [(? void?)
        (out-byte CPT_VOID out)]
       [(struct closure (lam gen-id))
        (out-byte CPT_CLOSURE out)
        (let ([pos ((out-shared-index out) v #:error? #t)])
          (out-number pos out)
          (out-anything lam out))]
       [(? linkl?)
        (out-linklet v out)]
       [(struct def-values (ids rhs))
        (out-marshaled define-values-type-num
                       (list->vector (cons (protect-quote rhs) ids))
                       out)]
       [(struct beg0 (forms))
        (out-marshaled begin0-sequence-type-num (map protect-quote forms) out)]
       [(struct seq (forms))
        (out-marshaled sequence-type-num (map protect-quote forms) out)]
       [(struct toplevel (depth pos const? ready?))
        (out-marshaled toplevel-type-num
                       (cons
                        depth
                        (if (or const? ready?)
                            (cons pos
                                  (bitwise-ior 
                                   (if const? #x2 0)
                                   (if ready? #x1 0)))
                            pos))
                       out)]
       [(struct primval (id))
        (out-byte CPT_REFERENCE out)
        (out-number id out)]
       [(struct assign (id rhs undef-ok?))
        (out-marshaled set-bang-type-num
                       (cons undef-ok? (cons id (protect-quote rhs)))
                       out)]
       [(struct localref (unbox? offset clear? other-clears? type))
        (if (and (not clear?) (not other-clears?) (not flonum?)
                 (offset . < . (- CPT_SMALL_LOCAL_END CPT_SMALL_LOCAL_START)))
            (out-byte (+ (if unbox?
                             CPT_SMALL_LOCAL_UNBOX_START
                             CPT_SMALL_LOCAL_START)
                         offset)
                      out)
            (begin
              (out-byte (if unbox? CPT_LOCAL_UNBOX CPT_LOCAL) out)
              (if (not (or clear? other-clears? type))
                  (out-number offset out)
                  (begin
                    (out-number (- (add1 offset)) out)
                    (out-number (cond
                                 [clear? 1]
                                 [other-clears? 2]
                                 [else (+ 2 (type->index type))])
                                out)))))]
       [(? lam?)
        (out-lam v out)]
       [(struct case-lam (name lams))
        (out-marshaled case-lambda-sequence-type-num
                       (cons (or name null)
                             lams)
                       out)]
       [(struct let-one (rhs body type unused?))
        (out-byte (cond
                    [type CPT_LET_ONE_TYPED]
                    [unused? CPT_LET_ONE_UNUSED]
                    [else CPT_LET_ONE])
                  out)
        (out-anything (protect-quote rhs) out)
        (out-anything (protect-quote body) out)
        (when type
          (out-number (type->index type) out))]
       [(struct let-void (count boxes? body))
        (out-marshaled let-void-type-num
                       (list*
                        count
                        boxes?
                        (protect-quote body))
                       out)]
       [(struct let-rec (procs body))
        (out-marshaled letrec-type-num
                       (list*
                        (length procs)
                        (protect-quote body)
                        procs)
                       out)]
       [(struct install-value (count pos boxes? rhs body))
        (out-marshaled let-value-type-num
                       (list*
                        count
                        pos
                        boxes?
                        (protect-quote rhs)
                        (protect-quote body))
                       out)]
       [(struct boxenv (pos body))
        (out-marshaled boxenv-type-num
                       (cons
                        pos
                        (protect-quote body))
                       out)]
       [(struct branch (test then else))
        (out-byte CPT_BRANCH out)
        (out-anything (protect-quote test) out)
        (out-anything (protect-quote then) out)
        (out-anything (protect-quote else) out)]
       [(struct application (rator rands))
        (let ([len (length rands)]) 
          (if (len . < . (- CPT_SMALL_APPLICATION_END CPT_SMALL_APPLICATION_START))
              (out-byte (+ CPT_SMALL_APPLICATION_START (length rands)) out)
              (begin
                (out-byte CPT_APPLICATION out)
                (out-number len out)))
          (for-each (lambda (e)
                      (out-anything (protect-quote e) out))
                    (cons rator rands)))]
       [(struct apply-values (proc args-expr))
        (out-marshaled apply-values-type-num
                       (cons (protect-quote proc)
                             (protect-quote args-expr))
                       out)]
       [(struct with-immed-mark (key val body))
        (out-marshaled with-immed-mark-type-num
                       (vector
                        (protect-quote key)
                        (protect-quote val)
                        (protect-quote body))
                       out)]
       [(struct with-cont-mark (key val body))
        (out-marshaled wcm-type-num
                       (list*
                        (protect-quote key)
                        (protect-quote val)
                        (protect-quote body))
                       out)]
       [(struct varref (expr dummy))
        (out-marshaled varref-form-type-num
                       (cons expr dummy)
                       out)]
       [(protected-symref v)
        (out-anything ((out-shared-index out) v #:error? #t) out)]
       [(and (? symbol?) (not (? symbol-interned?)))
        (out-as-bytes v 
                      #:before-length (if (symbol-unreadable? v) 0 1)
                      (compose string->bytes/utf-8 symbol->string) 
                      CPT_WEIRD_SYMBOL
                      #f
                      out)]     
       [(? symbol?)
        (define bs (string->bytes/utf-8 (symbol->string v)))
        (define len (bytes-length bs))
        (if (len . < . (- CPT_SMALL_SYMBOL_END CPT_SMALL_SYMBOL_START))
            (out-byte (+ CPT_SMALL_SYMBOL_START len) out)
            (begin (out-byte CPT_SYMBOL out)
                   (out-number len out)))
        (out-bytes bs out)]
       [(? keyword?)
        (out-as-bytes v 
                      (compose string->bytes/utf-8 keyword->string) 
                      CPT_KEYWORD
                      #f
                      out)]
       [(? string?)
        (out-as-bytes v 
                      string->bytes/utf-8
                      CPT_CHAR_STRING
                      (string-length v)
                      out)]
       [(? bytes?)
        (out-as-bytes v 
                      values
                      CPT_BYTE_STRING
                      #f
                      out)]
       [(? box?)
        (out-byte CPT_BOX out)
        (out-anything (unbox v) out)]
       [(? pair?)
        (define (list-length-before-cycle/improper-end l)
          (let loop ([len 0] [l l])
            (cond 
              [(null? l)
               (values len #t)]
              [(pair? l)
               (if ((out-shared-index out) l)
                   (values len #f)
                   (loop (add1 len) (cdr l)))]
              [else
               (values len #f)])))

        (define-values (len-1 proper?)
          (if (out-counting? out)
              (values 0 #f)
              (list-length-before-cycle/improper-end (cdr v))))
        (define len (add1 len-1))
        
        (define (print-contents-as-proper)
          (for ([e (in-list v)])
            (out-anything e out)))
        (define (print-contents-as-improper)
          (let loop ([l v] [i len])
            (cond
              [(zero? i)
               (out-anything l out)]
              [else
               (out-anything (car l) out)
               (loop (cdr l) (sub1 i))])))
        (if proper?
            (if (len . < . (- CPT_SMALL_PROPER_LIST_END CPT_SMALL_PROPER_LIST_START))
                (begin (out-byte (+ CPT_SMALL_PROPER_LIST_START len) out)
                       (print-contents-as-proper))
                (begin (out-byte CPT_LIST out)
                       (out-number len out)
                       (print-contents-as-proper)
                       (out-anything null out)))
            (if (len . < . (- CPT_SMALL_LIST_END CPT_SMALL_LIST_START))
                ; XXX If len = 1 (or maybe = 2?) then this could by CPT_PAIR
                (begin (out-byte (+ CPT_SMALL_LIST_START len) out)
                       (print-contents-as-improper))
                (begin (out-byte CPT_LIST out)
                       (out-number len out)
                       (print-contents-as-improper))))]
       [(? vector?)
        (out-byte CPT_VECTOR out)
        (out-number (vector-length v) out)
        (for ([v (in-vector v)])
          (out-anything v out))]
       [(? hash?)
        (out-byte CPT_HASH_TABLE out)
        (out-number (cond
                      [(hash-eqv? v) 2]
                      [(hash-eq? v) 0]
                      [(hash-equal? v) 1])
                    out)
        (out-number (hash-count v) out)
        (for ([(k v) (in-hash v)])
          (out-anything k out)
          (out-anything v out))]
       [(svector vec)
        (let* ([len (vector-length vec)])
          (if (len . < . (- CPT_SMALL_SVECTOR_END CPT_SMALL_SVECTOR_START))
              (out-byte (+ CPT_SMALL_SVECTOR_START len) out)
              (begin (out-byte CPT_SVECTOR out)
                     (out-number len out)))
          (for ([n (in-range (sub1 len) -1 -1)])
            (out-number (vector-ref vec n) out)))]
       [(? prefab-struct-key)
        (define pre-v (struct->vector v))
        (vector-set! pre-v 0 (prefab-struct-key v))
        (out-byte CPT_PREFAB out)
        (out-anything pre-v out)]
       [(quoted qv)
        (out-byte CPT_QUOTE out)
        (parameterize ([quoting? #t])
          (out-anything qv out))]
       [(? path?)
        (out-byte CPT_PATH out)
        (define (within? p)
          (and (relative-path? p)
               (let loop ([p p])
                 (define-values (base name dir?) (split-path p))
                 (and (not (eq? name 'up))
                      (not (eq? name 'same))
                      (or (not (path? base))
                          (loop base))))))
        (define maybe-rel
          (and (current-write-relative-directory)
               (let ([dir (current-write-relative-directory)])
                 (and (or (not dir)
                          (within? (find-relative-path v
                                                       (if (pair? dir)
                                                           (cdr dir)
                                                           dir))))
                      (find-relative-path v
                                          (if (pair? dir)
                                              (car dir)
                                              dir))))))
        (cond
         [(not maybe-rel)
          (define bstr (path->bytes v))
          (out-number (bytes-length bstr) out)
          (out-bytes bstr out)]
         [else
          (out-number 0 out)
          (out-anything (for/list ([e (in-list (explode-path maybe-rel))])
                          (if (path? e)
                              (path-element->bytes e)
                              e))
                        out)])]
       [(or (? regexp?)
            (? byte-regexp?)
            (? number?)
            (? extflonum?))
        (out-byte CPT_QUOTE out)
        (define s (open-output-bytes))
        (parameterize 
            ([pretty-print-size-hook
              (lambda (v mode port)
                (and (path? v)
                     (let ([v (make-relative v)])
                       (+ 2 (let ([p (open-output-bytes)])
                              (write (path->bytes v) p)
                              (bytes-length (get-output-bytes p)))))))]
             [pretty-print-print-hook
              (lambda (v mode port)
                (display "#^" port)
                (write (path->bytes (make-relative v)) port))])
          (pretty-write v s))
        (out-byte CPT_ESCAPE out)
        (define bstr (get-output-bytes s))
        (out-number (bytes-length bstr) out)
        (out-bytes bstr out)]
       [else (error 'out-anything "~s" (current-type-trace))])))))

(define (out-linklet linklet-form out)
  (out-marshaled linklet-type-num
                 (convert-linklet linklet-form)
                 out))

(define (convert-linklet linklet-form)
  (match linklet-form
    [(struct linkl (name importss import-shapess exports internals lifts
                         source-names body max-let-depth))
     (define names-count (* 2 (hash-count source-names)))
     (list name
           max-let-depth
           (length lifts)
           (length exports)
           (list->vector body)
           (for*/vector #:length names-count ([(k v) (in-hash source-names)]
                                              [(n) (in-list (list k v))])
                        n)
           (list->vector (append exports internals lifts))
           (list->vector (map list->vector importss))
           (if (not (for*/or ([import-shapes (in-list import-shapess)]
                              [import-shape (in-list import-shapes)])
                      import-shape))
               #f
               (for/vector ([import-shapes (in-list import-shapess)])
                 (for/vector ([import-shape (in-list import-shapes)])
                   (encode-shape import-shape)))))]))

(define (out-lam expr out)  
  (match expr
    [(struct lam (name flags num-params param-types rest? closure-map closure-types toplevel-map max-let-depth body))
     (let* ([l (protect-quote body)]
            [any-refs? (or (not (andmap (lambda (t) (eq? t 'val)) param-types))
                           (not (andmap (lambda (t) (eq? t 'val/ref)) closure-types)))]
            [num-all-params (if (and rest? (not (memq 'only-rest-arg-not-used flags)))
                                (add1 num-params)
                                num-params)]
            [l (cons (make-svector (if any-refs?
                                       (list->vector
                                        (append
                                         (vector->list closure-map)
                                         (let* ([v (make-vector (ceiling 
                                                                 (/ (* BITS_PER_ARG (+ num-params (vector-length closure-map)))
                                                                    BITS_PER_MZSHORT)))]
                                                [set-bit! (lambda (i bit)
                                                            (let ([pos (quotient (* BITS_PER_ARG i) BITS_PER_MZSHORT)])
                                                              (vector-set! v pos
                                                                           (bitwise-ior (vector-ref v pos)
                                                                                        (arithmetic-shift 
                                                                                         bit
                                                                                         (modulo (* BITS_PER_ARG i) BITS_PER_MZSHORT))))))])
                                           (for ([t (in-list param-types)]
                                                 [i (in-naturals)])
                                             (case t
                                               [(val) (void)]
                                               [(ref) (set-bit! i 1)]
                                               [else (set-bit! i (+ 1 (type->index t)))]))
                                           (for ([t (in-list closure-types)]
                                                 [i (in-naturals num-all-params)])
                                             (case t
                                               [(val/ref) (void)]
                                               [else (set-bit! i (+ 1 (type->index t)))]))
                                           (vector->list v))))
                                       closure-map))
                     l)]
            [l (if any-refs?
                   (cons (vector-length closure-map) l)
                   l)]
            [tl-map (and toplevel-map
                         (for/fold ([v 0]) ([i (in-set toplevel-map)])
                           (bitwise-ior v (arithmetic-shift 1 i))))])
       (out-marshaled unclosed-procedure-type-num
                      (list*
                       (+ (if rest? CLOS_HAS_REST 0)
                          (if any-refs? CLOS_HAS_REF_ARGS 0)
                          (if (memq 'preserves-marks flags) CLOS_PRESERVES_MARKS 0)
                          (if (memq 'sfs-clear-rest-args flags) CLOS_NEED_REST_CLEAR 0)
                          (if (memq 'is-method flags) CLOS_IS_METHOD 0)
                          (if (memq 'single-result flags) CLOS_SINGLE_RESULT 0))
                       num-all-params
                       max-let-depth
                       (and tl-map
                            (if (tl-map . <= . #xFFFFFFF)
                                ;; Encode as a fixnum:
                                tl-map
                                ;; Encode as an even-sized vector of 16-bit integers:
                                (let ([len (* 2 (quotient (+ (integer-length tl-map) 31) 32))])
                                  (for/vector ([i (in-range len)])
                                    (let ([s (* i 16)])
                                      (bitwise-bit-field tl-map s (+ s 16)))))))
                       name
                       l)
                      out))]))

(define (out-as-bytes expr ->bytes CPT len2 out #:before-length [before-length #f])
  (define s (->bytes expr))
  (out-byte CPT out)
  (when before-length
    (out-number before-length out))
  (out-number (bytes-length s) out)
  (when len2 (out-number len2 out))
  (out-bytes s out))

(define-struct quoted (v))

(define (protect-quote v)
  (if (or (pair? v) (vector? v) (and (not (zo? v)) (prefab-struct-key v)) (box? v) (hash? v) (svector? v))
      (make-quoted v)
      v))

(define-struct svector (vec))

(define (make-relative v)
  (let ([r (current-write-relative-directory)])
    (if r
        (find-relative-path r v)
        v)))

(define (encode-shape constantness)
  (define (to-sym n) (string->symbol (format "struct~a" n)))
  (cond
   [(eq? constantness 'constant) #t]
   [(eq? constantness 'fixed) (void)]
   [(function-shape? constantness)
    (let ([a (function-shape-arity constantness)])
      (cond
       [(arity-at-least? a) 
        (bitwise-ior (arithmetic-shift (- (add1 (arity-at-least-value a))) 1)
                     (if (function-shape-preserves-marks? constantness) 1 0))]
       [(list? a)
        (string->symbol (apply
                         string-append
                         (add-between
                          (for/list ([a (in-list a)])
                            (define n (if (arity-at-least? a)
                                          (- (add1 (arity-at-least-value a)))
                                          a))
                            (number->string n))
                          ":")))]
       [else 
        (bitwise-ior (arithmetic-shift a 1) 
                     (if (function-shape-preserves-marks? constantness) 1 0))]))]
   [(struct-type-shape? constantness)
    (to-sym (arithmetic-shift (struct-type-shape-field-count constantness)
                              4))]
   [(constructor-shape? constantness)
    (to-sym (bitwise-ior 1 (arithmetic-shift (constructor-shape-arity constantness)
                                             4)))]
   [(predicate-shape? constantness) (to-sym 2)]
   [(accessor-shape? constantness)
    (to-sym (bitwise-ior 3 (arithmetic-shift (accessor-shape-field-count constantness)
                                             4)))]
   [(mutator-shape? constantness)
    (to-sym (bitwise-ior 4 (arithmetic-shift (mutator-shape-field-count constantness)
                                             4)))]
   [(struct-other-shape? constantness)
    (to-sym 5)]
   [else #f]))
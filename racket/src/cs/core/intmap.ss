;; Immutable maps represented as big-endian Patricia tries.
;; Based on Okasaki & Gill's "Fast Mergeable Integer Maps,"
;; (1998) with an added collision node.
;;
;; I also consulted Leijen and Palamarchuk's Haskell implementation
;; of Data.IntMap.

(define-record-type intmap
  [fields (immutable eqtype)
          (mutable root)]
  [nongenerative #{intmap pfwguidjcvqbvofiirp097jco-0}]
  [sealed #t])

(define-record-type Br
  [fields (immutable count)
          (immutable prefix)
          (immutable mask)
          (immutable left)
          (immutable right)]
  [nongenerative #{Br pfwguidjcvqbvofiirp097jco-1}]
  [sealed #t])

(define-record-type Leaf
  [fields (immutable hash)]
  [nongenerative #{Leaf pfwguidjcvqbvofiirp097jco-2}])

(define-record-type Lf
  [parent Leaf]
  [fields (immutable key)
          (immutable value)]
  [nongenerative #{Lf pfwguidjcvqbvofiirp097jco-3}]
  [sealed #t])

(define-record-type Co
  [parent Leaf]
  [fields (immutable pairs)]
  [nongenerative #{Co pfwguidjcvqbvofiirp097jco-4}]
  [sealed #t])

(define *nothing* (gensym))

(define immutable-hash? intmap?)

(define empty-hash (make-intmap 'equal #f))
(define empty-hasheqv (make-intmap 'eqv #f))
(define empty-hasheq (make-intmap 'eq #f))

(define (make-intmap-shell et)
  (make-intmap et #f))

(define (intmap-shell-sync! dst src)
  (intmap-root-set! dst (intmap-root src)))

(define (intmap-equal? t) (eq? 'equal (intmap-eqtype t)))
(define (intmap-eqv? t) (eq? 'eqv (intmap-eqtype t)))
(define (intmap-eq? t) (eq? 'eq (intmap-eqtype t)))

(define (intmap-count t)
  ($intmap-count (intmap-root t)))

(define (intmap-empty? t)
  (fx= 0 (intmap-count t)))

(define ($intmap-count t)
  (cond [(Br? t) (Br-count t)]
        [(Lf? t) 1]
        [(Co? t) (length (Co-pairs t))]
        [else 0]))

(define (intmap-ref t key def)
  (let ([et (intmap-eqtype t)]
        [root (intmap-root t)])
    (if root
        ($intmap-ref et root (hash-code et key) key def)
        ($fail def))))

(define ($intmap-ref et t h key def)
  (cond
   [(Br? t)
    (if (fx<= h (Br-prefix t))
        ($intmap-ref et (Br-left t) h key def)
        ($intmap-ref et (Br-right t) h key def))]

   [(Lf? t)
    (if (key=? et key (Lf-key t))
        (Lf-value t)
        ($fail def))]

   [(Co? t)
    (if (fx= h (Leaf-hash t))
        ($collision-ref et t key def)
        ($fail def))]

   [else
    ($fail def)]))

(define ($intmap-has-key? et t h key)
  (not (eq? *nothing* ($intmap-ref et t h key *nothing*))))

(define (intmap-set t key val)
  (let ([et (intmap-eqtype t)])
    (make-intmap
     et
     ($intmap-set et (intmap-root t) (hash-code et key) key val))))

(define ($intmap-set et t h key val)
  (cond
   [(Br? t)
    (let ([p (Br-prefix t)]
          [m (Br-mask t)])
      (cond
       [(not (match-prefix? h p m))
        (join h (make-Lf h key val) p t)]
       [(fx<= h p)
        (br p m ($intmap-set et (Br-left t) h key val) (Br-right t))]
       [else
        (br p m (Br-left t) ($intmap-set et (Br-right t) h key val))]))]

   [(Lf? t)
    (let ([j (Leaf-hash t)])
      (cond
       [(not (fx= h j))
        (join h (make-Lf h key val) j t)]
       [(key=? et key (Lf-key t))
        (let ([orig-val (Lf-value t)])
          (if (eq? val orig-val)
              t
              (make-Lf h key val)))]
       [else
        (make-Co h (list (cons key val) (cons (Lf-key t) (Lf-value t))))]))]

   [(Co? t)
    (let ([j (Leaf-hash t)])
      (if (fx= h j)
          (make-Co j ($collision-set et t key val))
          (join h (make-Lf h key val) j t)))]

   [else
    (make-Lf h key val)]))

(define (join p0 t0 p1 t1)
  (let ([m (branching-bit p0 p1)])
    (if (fx<= p0 p1)
        (br (mask p0 m) m t0 t1)
        (br (mask p0 m) m t1 t0))))

(define (intmap-remove t key)
  (let ([et (intmap-eqtype t)])
    (make-intmap
     et
     ($intmap-remove et (intmap-root t) (hash-code et key) key))))

(define ($intmap-remove et t h key)
  (cond
   [(Br? t)
    (let ([p (Br-prefix t)]
          [m (Br-mask t)])
      (cond
       [(not (match-prefix? h p m))
        t]
       [(fx<= h p)
        (br/check-left p m ($intmap-remove et (Br-left t) h key) (Br-right t))]
       [else
        (br/check-right p m (Br-left t) ($intmap-remove et (Br-right t) h key))]))]

   [(Lf? t)
    (if (key=? et key (Lf-key t))
        #f
        t)]

   [(Co? t)
    (cond
     [(fx=? h (Leaf-hash t))
      ;; A collision node always has at least 2 key-value pairs,
      ;; so when we remove one, we know the resulting list is non-empty.
      (let ([pairs ($collision-remove et t key)])
        (if (null? (cdr pairs))
            (make-Lf h (caar pairs) (cdar pairs))
            (make-Co h pairs)))]
     [else
      t])]

   [else
    #f]))

;; collision ops
(define ($collision-ref et t key def)
  (let loop ([xs (Co-pairs t)])
    (cond [(null? xs) ($fail def)]
          [(key=? et key (caar xs)) (cdar xs)]
          [else (loop (cdr xs))])))

(define ($collision-set et t key val)
  (cons (cons key val)
        (let loop ([xs (Co-pairs t)])
          (cond [(null? xs) '()]
                [(key=? et key (caar xs)) (loop (cdr xs))]
                [else (cons (car xs) (loop (cdr xs)))]))))

(define ($collision-remove et t key)
  (let loop ([xs (Co-pairs t)])
    (cond [(null? xs) '()]
          [(key=? et key (caar xs)) (loop (cdr xs))]
          [else (cons (car xs) (loop (cdr xs)))])))

(define ($collision-has-key? et t key)
  (let loop ([xs (Co-pairs t)])
    (cond [(null? xs) #f]
          [(key=? et key (caar xs)) #t]
          [else (loop (cdr xs))])))

;; bit twiddling
(define-syntax-rule (match-prefix? h p m)
  (fx= (mask h m) p))

(define-syntax-rule (mask h m)
  (fxand (fxior h (fx1- m)) (fxnot m)))

(define-syntax-rule (branching-bit p m)
  (highest-set-bit (fxxor p m)))

(define-syntax-rule (highest-set-bit x1)
  (let* ([x2 (fxior x1 (fxsrl x1 1))]
         [x3 (fxior x2 (fxsrl x2 2))]
         [x4 (fxior x3 (fxsrl x3 4))]
         [x5 (fxior x4 (fxsrl x4 8))]
         [x6 (fxior x5 (fxsrl x5 16))]
         [x7 (fxior x6 (fxsrl x6 32))])
    (fxxor x7 (fxsrl x7 1))))

;; basic utils
(define (br p m l r)
  (let ([c (fx+ ($intmap-count l) ($intmap-count r))])
    (make-Br c p m l r)))

(define (br* p m l r)
  (cond
   [(not r) l]
   [(not l) r]
   [else (br p m l r)]))

(define (br/check-left p m l r)
  (if l
      (br p m l r)
      r))

(define (br/check-right p m l r)
  (if r
      (br p m l r)
      l))

(define-syntax-rule (key=? et k1 k2)
  (case et
    [(eq) (eq? k1 k2)]
    [(eqv) (eqv? k1 k2)]
    [else (key-equal? k1 k2)]))

(define-syntax-rule (hash-code et k)
  (case et
    [(eq) (eq-hash-code k)]
    [(eqv) (eqv-hash-code k)]
    [else (key-equal-hash-code k)]))

(define ($fail default)
  (if (procedure? default)
      (default)
      default))

;; iteration
(define (intmap-iterate-first t)
  (and (fx> (intmap-count t) 0)
       0))

(define (intmap-iterate-next t pos)
  (let ([pos (fx1+ pos)])
    (and (fx< pos (intmap-count t))
         pos)))

(define (intmap-iterate-pair t pos fail)
  (or ($intmap-nth (intmap-root t) pos)
      fail))

(define (intmap-iterate-key t pos fail)
  (let ([p ($intmap-nth (intmap-root t) pos)])
    (if p (car p) fail)))

(define (intmap-iterate-value t pos fail)
  (let ([p ($intmap-nth (intmap-root t) pos)])
    (if p (cdr p) fail)))

(define (intmap-iterate-key+value t pos fail)
  (let ([p ($intmap-nth (intmap-root t) pos)])
    (if p
        (values (car p) (cdr p))
        fail)))

(define ($intmap-nth t n)
  (cond
   [(Br? t)
    (let* ([left (Br-left t)]
           [left-count ($intmap-count left)])
      (if (fx< n left-count)
          ($intmap-nth left n)
          ($intmap-nth (Br-right t) (fx- n left-count))))]

   [(Lf? t)
    (and (fx= 0 n)
         (cons (Lf-key t) (Lf-value t)))]

   [(Co? t)
    (let ([pairs (Co-pairs t)])
      (and (fx< n (length pairs))
           (list-ref pairs n)))]

   [else
    #f]))

(define (unsafe-intmap-iterate-first t)
  ($intmap-enum (intmap-root t) #f))

(define (unsafe-intmap-iterate-next t pos)
  (let ([next (cdr pos)])
    (and next
         ($intmap-enum (car next) (cdr next)))))

(define (unsafe-intmap-iterate-pair t pos)
  (car pos))

(define (unsafe-intmap-iterate-key t pos)
  (caar pos))

(define (unsafe-intmap-iterate-value t pos)
  (cdar pos))

(define (unsafe-intmap-iterate-key+value t pos)
  (values (caar pos) (cdar pos)))

(define ($intmap-enum t next)
  (cond
   [(Br? t)
    ($intmap-enum (Br-left t) (cons (Br-right t) next))]

   [(Lf? t)
    (cons (cons (Lf-key t) (Lf-value t)) next)]

   [(Co? t)
    (let ([pairs (Co-pairs t)])
      (let ([fst (car pairs)]
            [rst (cdr pairs)])
        (if (null? rst)
            (cons fst next)
            (cons fst (cons (make-Co #f rst) next)))))]

   [else
    next]))

(define (intmap-fold t nil proc)
  (let loop ([pos (unsafe-intmap-iterate-first t)] [nil nil])
    (cond
     [pos
      (let ([p (unsafe-intmap-iterate-pair t pos)])
        (loop (unsafe-intmap-iterate-next t pos)
              (proc (car p) (cdr p) nil)))]
     [else
      nil])))

(define (intmap-for-each t proc)
  (intmap-fold t (void) (lambda (k v _) (proc k v) (void))))

(define (intmap-map t proc)
  (intmap-fold t '() (lambda (k v xs) (cons (proc k v) xs))))

;; equality
(define (intmap=? a b eql?)
  (and (eq? (intmap-eqtype a) (intmap-eqtype b))
       ($intmap=? (intmap-eqtype a) (intmap-root a) (intmap-root b) eql?)))

(define ($intmap=? et a b eql?)
  (cond
   [(Br? a)
    (and (Br? b)
         (fx= (Br-count a) (Br-count b))
         (fx= (Br-prefix a) (Br-prefix b))
         (fx= (Br-mask a) (Br-mask b))
         ($intmap=? et (Br-left a) (Br-left b) eql?)
         ($intmap=? et (Br-right a) (Br-right b) eql?))]

   [(Lf? a)
    (and (Lf? b)
         (key=? et (Lf-key a) (Lf-key b))
         (eql? (Lf-value a) (Lf-value b)))]

   [(Co? a)
    (and (Co? b)
         (let ([xs (Co-pairs a)])
           (and (fx= (length xs) (length (Co-pairs b)))
                (let loop ([xs xs])
                  (cond [(null? xs) #t]
                        [($collision-has-key? et b (caar xs)) (loop (cdr xs))]
                        [else #f])))))]

   [else (and (not a) (not b))]))

;; hash code
(define (intmap-hash-code t hash)
  ($intmap-hash-code (intmap-root t) hash 0))

(define ($intmap-hash-code t hash hc)
  (cond
   [(Br? t)
    (let* ([hc (hash-code-combine hc (hash (Br-prefix t)))]
           [hc (hash-code-combine hc (hash (Br-mask t)))]
           [hc (hash-code-combine hc ($intmap-hash-code (Br-left t) hash hc))]
           [hc (hash-code-combine hc ($intmap-hash-code (Br-right t) hash hc))])
      hc)]

   [(Lf? t)
    (let* ([hc (hash-code-combine hc (Leaf-hash t))]
           [hc (hash-code-combine hc (hash (Lf-value t)))])
      hc)]

   [(Co? t)
    (hash-code-combine hc (Leaf-hash t))]

   [else
    (hash-code-combine hc (hash #f))]))

(define ignored/intmap
  (begin
    ;; Go through generic `hash` versions to support `a`
    ;; and `b` as impersonated hash tables
    (record-type-equal-procedure (record-type-descriptor intmap)
                                 (lambda (a b eql?)
                                   (hash=? a b eql?)))
    (record-type-hash-procedure (record-type-descriptor intmap)
                                (lambda (a hash)
                                  (hash-hash-code a hash)))))

;; subset
(define (intmap-keys-subset? a b)
  ($intmap-keys-subset? (intmap-eqtype a) (intmap-root a) (intmap-root b)))

(define ($intmap-keys-subset? et a b)
  (cond
   [(eq? a b)
    #t]

   [(Br? a)
    (and
     (Br? b)

     (let ([p1 (Br-prefix a)]
           [m1 (Br-mask a)]
           [p2 (Br-prefix b)]
           [m2 (Br-mask b)])
       (cond
        [(fx> m1 m2) #f]
        [(fx> m2 m1)
         (and (match-prefix? p1 p2 m2)
              (if (fx<= p1 p2)
                  ($intmap-keys-subset? et a (Br-left b))
                  ($intmap-keys-subset? et a (Br-right b))))]
        [else
         (and (fx= p1 p2)
              ($intmap-keys-subset? et (Br-left a) (Br-left b))
              ($intmap-keys-subset? et (Br-right a) (Br-right b)))])))]

   [(Lf? a)
    ($intmap-has-key? et b (Leaf-hash a) (Lf-key a))]

   [(Co? a)
    (let loop ([xs (Co-pairs a)])
      (cond [(null? xs) #t]
            [($intmap-has-key? et b (Leaf-hash a) (caar xs)) (loop (cdr xs))]
            [else #f]))]

   [else
    #t]))

;; merge
;; based on https://hackage.haskell.org/package/containers-0.5.10.2/docs/src/Data.IntMap.Internal.html#mergeWithKey%27
(define-syntax let-br
  (syntax-rules ()
    [(_ ([(p m l r) t] ...) exp ...)
     (let ([p (Br-prefix t)] ...
           [m (Br-mask t)] ...
           [l (Br-left t)] ...
           [r (Br-right t)] ...)
       exp ...)]))

(define (merge/key eqtype bin id f g1 g2 t1 t2)
  (define-syntax go
    (syntax-rules ()
      [(_ t1 t2) (merge/key eqtype bin id f g1 g2 t1 t2)]))

  (cond
   [(eq? t1 t2)
    (id t1)]

   [(Br? t1)
    (cond
     [(Br? t2)
      (let-br
       ([(p1 m1 l1 r1) t1] [(p2 m2 l2 r2) t2])
       (cond
        [(fx> m1 m2)
         (cond
          [(not (match-prefix? p2 p1 m1))
           (join* p1 (g1 t1) p2 (g2 t2))]
          [(fx<= p2 p1)
           (bin p1 m1 (go l1 t2) (g1 r1))]
          [else
           (bin p1 m1 (g1 l1) (go r1 t2))])]

        [(fx> m2 m1)
         (cond
          [(not (match-prefix? p1 p2 m2))
           (join* p1 (g1 t1) p2 (g2 t2))]
          [(fx<= p1 p2)
           (bin p2 m2 (go t1 l2) (g2 r2))]
          [else
           (bin p2 m2 (g2 l2) (go t1 r2))])]

        [(fx= p1 p2)
         (bin p1 m1 (go l1 l2) (go r1 r2))]

        [else
         (join* p1 (g1 t1) p2 (g2 t2))]))]

     [(Leaf? t2)
      (let merge0 ([t2 t2] [h2 (Leaf-hash t2)] [t1 t1])
        (cond
         [(eq? t1 t2)
          (id t1)]

         [(Br? t1)
          (let-br
           ([(p1 m1 l1 r1) t1])
           (cond
            [(not (match-prefix? h2 p1 m1))
             (join* p1 (g1 t1) h2 (g2 t2))]
            [(fx<= h2 p1)
             (bin p1 m1 (merge0 t2 h2 l1) (g1 r1))]
            [else
             (bin p1 m1 (g1 l1) (merge0 t2 h2 r1))]))]

         [(Leaf? t1)
          (let ([h1 (Leaf-hash t1)])
            (cond
             [(fx= h1 h2)
              (merge/collision eqtype f g1 g2 h1 t1 t2)]
             [else
              (join* h1 (g1 t1) h2 (g2 t2))]))]

         [else
          (g2 t2)]))]

     [else
      (g1 t1)])]

   [(Leaf? t1)
    (let merge0 ([t1 t1] [h1 (Leaf-hash t1)] [t2 t2])
      (cond
       [(eq? t1 t2)
        (id t1)]

       [(Br? t2)
        (let-br
         ([(p2 m2 l2 r2) t2])
         (cond
          [(not (match-prefix? h1 p2 m2))
           (join* h1 (g1 t1) p2 (g2 p2))]
          [(fx<= h1 p2)
           (bin p2 m2 (merge0 t1 h1 l2) (g2 r2))]
          [else
           (bin p2 m2 (g2 l2) (merge0 t1 h1 r2))]))]

       [(Leaf? t2)
        (let ([h2 (Leaf-hash t2)])
          (cond
           [(fx= h1 h2)
            (merge/collision eqtype f g1 g2 h1 t1 t2)]
           [else
            (join* h1 (g1 t1) h2 (g2 t2))]))]

       [else
        (g1 t2)]))]

   [else
    (g2 t2)]))

(define (find+rest p? xs)
  (let loop ([r #f] [ys '()] [xs xs])
    (cond [(null? xs)    (values r ys)]
          [(p? (car xs)) (loop (car xs) ys (cdr xs))]
          [else          (loop r (cons (car xs) ys) (cdr xs))])))

;; pre: t1 and t2 satisfy `Leaf?` and have the same hash code
(define (merge/collision eqtype f g1 g2 h t1 t2)
  (cond
   [(and (Lf? t1) (Lf? t2))
    (merge/lf-lf eqtype f g1 g2 h t1 t2)]
   [else
    ;; separate k-v pairs into
    ;; - those in both t1 and t2
    ;; - those in t1 only (left)
    ;; - those in t2 only (right)
    (let loop ([both '()] [left '()] [right (leaf->pairs t2)] [xs (leaf->pairs t1)])
      (cond
       [(null? xs)
        (let* ([l (g1 (pairs->leaf h left))]
               [r (g2 (pairs->leaf h right))]
               [pairs (append both (leaf->pairs l) (leaf->pairs r))])
          (pairs->leaf h pairs))]
       [else
        (let*-values
            ([(x)
              (car xs)]
             [(y ys)
              (find+rest (lambda (y)
                           (key=? eqtype (car x) (car y)))
                         right)])
          (cond
           [y
            (let* ([k1 (car x)]
                   [z (f k1 (cdr x) (cdr y) *nothing*)])
              (cond
               [(eq? *nothing* z)
                (loop both left ys (cdr xs))]
               [else
                (loop (cons (cons k1 z) both) left ys (cdr xs))]))]
           [else
            (loop both (cons x left) ys (cdr xs))]))]))]))

;; pre: t1 and t2 are both `Lf?` with the same hash code
(define (merge/lf-lf eqtype f g1 g2 h t1 t2)
  (let ([k1 (Lf-key t1)]
        [v1 (Lf-value t1)]
        [k2 (Lf-key t2)]
        [v2 (Lf-value t2)])
    (cond
     [(key=? eqtype k1 k2)
      (let ([x (f k1 v1 v2 *nothing*)])
        (cond
         [(eq? *nothing* x) #f]
         [(eq? v1 x) t1]
         [(eq? v2 x) t2]
         [else (make-Lf h k1 x)]))]
     [else
      (let ([s1 (g1 t1)]
            [s2 (g2 t2)])
        ;; Since g1 and g2 are only permitted to return nodes with a subset of the keys
        ;; they were given, s1 and s2 must both be either Lf? or #f. But g1 and g2 are
        ;; allowed to modify values.
        (cond
         [(not s1) s2]
         [(not s2) s1]
         [else (make-Co h
                        (list (cons k1 (Lf-value s1))
                              (cons k2 (Lf-value s2))))]))])))

(define (join* p1 t1 p2 t2)
  (cond
   [(not t1) t2]
   [(not t2) t1]
   [else (join p1 t1 p2 t2)]))

(define (leaf->pairs t)
  (cond
   [(Lf? t) (list (cons (Lf-key t) (Lf-value t)))]
   [(Co? t) (Co-pairs t)]
   [(not t) '()]))

(define (pairs->leaf h xs)
  (cond
   [(null? xs) #f]
   [(null? (cdr xs)) (make-Lf h (caar xs) (cdar xs))]
   [else (make-Co h xs)]))

(define ($union eqtype t1 t2)
  (merge/key eqtype
             br
             (lambda (t) t)
             (lambda (k v1 v2 nil) v1)
             (lambda (t) t)
             (lambda (t) t)
             t1
             t2))

(define ($intersection eqtype t1 t2)
  (merge/key eqtype
             br*
             (lambda (t) t)
             (lambda (k v1 v2 nil) v1)
             (lambda (t) #f)
             (lambda (t) #f)
             t1
             t2))

(define ($difference eqtype t1 t2)
  (merge/key eqtype
             br*
             (lambda (t) #f)
             (lambda (k v1 v2 nil) nil)
             (lambda (t) t)
             (lambda (t) #f)
             t1
             t2))

(define (hash-union t1 t2)
  (let* ([et (intmap-eqtype t1)]
         [root ($union et (intmap-root t1) (intmap-root t2))])
    (make-intmap et root)))

(define (hash-intersection t1 t2)
  (let* ([et (intmap-eqtype t1)]
         [root ($intersection et (intmap-root t1) (intmap-root t2))])
    (make-intmap et root)))

(define (hash-difference t1 t2)
  (let* ([et (intmap-eqtype t1)]
         [root ($difference et (intmap-root t1) (intmap-root t2))])
    (make-intmap et root)))

;; This implementation is a variation on the CHAMP encoding from
;; Steindorfer and Vinju, described here:
;;   https://michael.steindorfer.name/publications/oopsla15.pdf
;; and implemented here:
;;   https://github.com/usethesource/capsule
;;
;; The implementation in this file is similar to CHAMP insofar as it
;; separates the keys and children of a bitmap-indexed node and maintains
;; an almost canonical representation (modulo collision nodes and,
;; in our case, implicit/explicit values after key removals).
;;
;; The actual storage arrangement is different, however, since we elide
;; values altogether when they're all #t (which makes sets more efficient),
;; whereas the implementation cited above uses different specialized data
;; structures for maps and sets, duplicating most of the code between them.

(define-record-type hamt
  [fields (immutable eqtype)
          (mutable root)]
  [nongenerative #{hnode pfwh8wvaevt3r6pcwsqn90ry8-0}]
  [sealed #t])

(define *nothing* (gensym 'nothing))

;; 16-bit popcount
(define (popcount x)
  (let* ([x (fx- x (fxand (fxsrl x 1) #x5555))]
         [x (fx+ (fxand x #x3333) (fxand (fxsrl x 2) #x3333))]
         [x (fxand (fx+ x (fxsrl x 4)) #x0f0f)]
         [x (fx+ x (fxsrl x 8))])
    (fxand x #x1f)))

;; The number of bits in a hashcode = the number of bits in a fixnum.
(define *hashcode-bits* (fxbit-count (most-positive-fixnum)))

(define (key=? eqtype k1 k2)
  (case eqtype
    [(eq) (eq? k1 k2)]
    [(eqv) (eqv? k1 k2)]
    [else (equal? k1 k2)]))

(define (hash-code eqtype key)
  (case eqtype
    [(eq) (eq-hash-code key)]
    [(eqv) (eqv-hash-code key)]
    [else (equal-hash-code key)]))

;; On each level of the tree, we use a different portion of a key's hashcode.
;; At the root (level 0), we use the lowest *bnode-bits* bits of the hashcode.
;; At level 1, we right-shift the hashcode by *bnode-bits*, and so forth.
;; As we traverse the tree, we keep track of how many bits we're shifting the
;; hashcode by.
(define (down shift)
  (fx+ shift *bnode-bits*))

(meta-cond
 [(> (most-positive-fixnum) (expt 2 32))
  ;;
  ;; 64-bit bnode layout
  ;;
  ;; A bitmap-indexed node (bnode) is a vector with the following layout:
  ;;
  ;; [index 0]
  ;; ------------------------------------------------------------------\
  ;; | bitmaps | count | key_0 | ... | key_i | child_0 | ... | child_j /
  ;; ------------------------------------------------------------------\
  ;;   /--------------------------
  ;;   \ value_0 | ... | value_i |
  ;;   /--------------------------
  ;;
  ;; `count` is the number of keys mapped by the entire sub-tree rooted
  ;; at the current node.
  ;;
  ;; `bitmaps` is a 42-bit field with the following big-endian layout:
  ;;
  ;; -- 5 bits ---- 5 bits ------ 16 bits ------- 16 bits ----
  ;; | child-pop |  key-pop  |   child-map   |    key-map    |
  ;; ---------------------------------------------------------
  ;;
  ;; The `-pop` subfields are the population counts of the corresponsing
  ;; maps.
  ;;
  ;; Logically, there is one value per key. However, if every value in
  ;; the node is #t (as is the case when a HAMT is used as a set),
  ;; no values are actually stored.

  (define *bnode-bits* 4)
  (define *bnode-mask* #b1111)

  (define *bnode-count-index* 1)
  (define *bnode-key-base* 2)

  (define ($bnode-bitmaps n)
    (#%vector-ref n 0))

  (define (bnode-keymap n)
    (fxand #xffff ($bnode-bitmaps n)))

  (define (bnode-childmap n)
    (fxand #xffff (fxsrl ($bnode-bitmaps n) 16)))

  (define (bnode-keypop n)
    (fxand #b11111 (fxsrl ($bnode-bitmaps n) 32)))

  (define (bnode-childpop n)
    (fxsrl ($bnode-bitmaps n) 37))

  (define ($combine-bitmaps keymap childmap keypop childpop)
    (fxior keymap
           (fxsll childmap 16)
           (fxsll keypop 32)
           (fxsll childpop 37)))

  (define (bnode-set-bitmaps+pops! n keymap childmap keypop childpop)
    (let ([bitmaps ($combine-bitmaps keymap childmap keypop childpop)])
      (vector-set-fixnum! n 0 bitmaps)))

  (define-syntax make-bnode
    (syntax-rules ()
      [(_ kmap cmap kpop cpop count [elt ...])
       (vector ($combine-bitmaps kmap cmap kpop cpop)
               count
               elt ...)]))
  ]
 [else
  ;;
  ;; 32-bit bnode layout
  ;;
  ;; On a 32-bit build, a bnode has the following layout:
   ;;
  ;; [index 0]
  ;; ----------------------------------------------------------\
  ;; | keymap+pop | childmap+pop | count | key_0 | ... | key_i /
  ;; ----------------------------------------------------------\
  ;;   /----------------------------------------------------
  ;;   \ child_0 | ... | child_j | value_0 | ... | value_i |
  ;;   /----------------------------------------------------
  ;;
  ;; where `keymap+pop` are 21-bit fields with the following big-endian layout:
  ;;
  ;; -- 5 bits --- 16 bits----
  ;; | popcount |   bitmap   |
  ;; -------------------------
  (define *bnode-bits* 4)
  (define *bnode-mask* #b1111)

  (define *bnode-count-index* 2)
  (define *bnode-key-base* 3)

  (define (bnode-keymap n)
    (fxand #xffff (#%vector-ref n 0)))

  (define (bnode-childmap n)
    (fxand #xffff (#%vector-ref n 1)))

  (define (bnode-keypop n)
    (fxsrl (#%vector-ref n 0) 16))

  (define (bnode-childpop n)
    (fxsrl (#%vector-ref n 1) 16))

  (define (bnode-set-bitmaps+pops! n keymap childmap keypop childpop)
    (let ([kmp (fxior keymap (fxsll keypop 16))]
          [cmp (fxior childmap (fxsll childpop 16))])
      (vector-set-fixnum! n 0 kmp)
      (vector-set-fixnum! n 1 cmp)))

  (define-syntax make-bnode
    (syntax-rules ()
      [(_ kmap cmap kpop cpop count [elt ...])
       (vector (fxior keymap (fxsll keypop 16))
               (fxior childmap (fxsll childpop 16))
               count
               elt ...)]))
  ])

;;
(define bnode? #%vector?)

(define empty-bnode (make-bnode 0 0 0 0 0 []))

(define (bnode-count n)
  (#%vector-ref n *bnode-count-index*))

(define (bnode-set-count! n count)
  (vector-set-fixnum! n *bnode-count-index* count))

(define (bnode-maps-bit? bitmap bit)
  (not (fx= 0 (fxand bitmap bit))))

(define (bnode-maps-key? n bit)
  (bnode-maps-bit? (bnode-keymap n) bit))

(define (bnode-maps-child? n bit)
  (bnode-maps-bit? (bnode-childmap n) bit))

(define (bnode-index bitmap bit)
  (popcount (fxand bitmap (fx1- bit))))

(define (bnode-key-index n bit)
  (bnode-index (bnode-keymap n) bit))

(define (bnode-child-index n bit)
  (bnode-index (bnode-childmap n) bit))

(define (bnode-key-ref n idx)
  (#%vector-ref n (fx+ *bnode-key-base* idx)))

(define (bnode-child-base n)
  (fx+ *bnode-key-base*
       (bnode-keypop n)))

(define (bnode-child-ref n idx)
  (#%vector-ref n
                (fx+ (bnode-child-base n)
                     idx)))

(define (bnode-val-base n)
  (fx+ (bnode-child-base n)
       (bnode-childpop n)))

(define (bnode-val-ref n idx)
  (let ([val-phys-idx (fx+ (bnode-val-base n) idx)])
    (or (fx>= val-phys-idx (#%vector-length n))
        (#%vector-ref n val-phys-idx))))

(define (bnode-mask hash shift)
  (fxand (fxsrl hash shift) *bnode-mask*))

(define (bnode-bit-pos hash shift)
  (fxsll 1 (bnode-mask hash shift)))

(define (bnode-ref n key eqtype keyhash shift)
  (let ([bit (bnode-bit-pos keyhash shift)])

    (cond [(bnode-maps-key? n bit)
           (let* ([idx (bnode-key-index n bit)]
                  [k (bnode-key-ref n idx)])
             (if (key=? eqtype key k)
                 (bnode-val-ref n idx)
                 *nothing*))]

          [(bnode-maps-child? n bit)
           (let* ([idx (bnode-child-index n bit)]
                  [c (bnode-child-ref n idx)])
             (node-ref c key eqtype keyhash (down shift)))]

          [else
           *nothing*])))

(define (bnode-replace-val n idx val)
  (let* ([val-base (bnode-val-base n)]
         [cur-len (#%vector-length n)]
         [new-node
          (cond
           [(fx= val-base cur-len)
            ;; reify values
            (let ([v (make-vector (fx+ cur-len (bnode-keypop n)) #t)])
              (vector-copy! v 0 n 0 cur-len)
              v)]
           [else
            (#%vector-copy n)])])

    (#%vector-set! new-node (fx+ val-base idx) val)
    new-node))

(define (bnode-copy/base! dst dst-base dst-start src src-base src-start src-end)
  (vector-copy! dst
                (fx+ dst-base dst-start)
                src
                (fx+ src-base src-start)
                (fx+ src-base src-end)))

(define (bnode-copy/add! dst dst-base src src-base idx srcpop item)
  (bnode-copy/base! dst dst-base 0 src src-base 0 idx)
  (#%vector-set! dst (fx+ dst-base idx) item)
  (bnode-copy/base! dst dst-base (fx1+ idx) src src-base idx srcpop))

(define (bnode-copy/remove! dst dst-base src src-base idx srcpop)
  (bnode-copy/base! dst dst-base 0 src src-base 0 idx)
  (bnode-copy/base! dst dst-base idx src src-base (fx1+ idx) srcpop))

(define (bnode-add-child n child key-idx bit)
  (let* ([old-len (#%vector-length n)]
         [child-idx (bnode-child-index n bit)]
         [new-km (fxxor (bnode-keymap n) bit)]
         [new-cm (fxior (bnode-childmap n) bit)]
         [old-kp (bnode-keypop n)]
         [old-cp (bnode-childpop n)]
         [new-ct (fx1+ (bnode-count n))]
         [old-child-base (fx+ *bnode-key-base* old-kp)]
         [old-val-base (fx+ old-child-base old-cp)]
         [new-len
          ;; If we have reified values, we're removing 1 key and 1 value
          ;; and adding 1 child, so overall length decreases by 1.
          ;; If values are implicit, we're removing 1 key and adding 1
          ;; child, so overall length is the same.
          (if (fx= old-val-base old-len)
              old-len
              (fx1- old-len))]
         [new-node (make-vector new-len)])

    (bnode-set-bitmaps+pops! new-node new-km new-cm (fx1- old-kp) (fx1+ old-cp))
    (bnode-set-count! new-node new-ct)
    (bnode-copy/remove! new-node *bnode-key-base* n *bnode-key-base* key-idx old-kp)
    (bnode-copy/add! new-node (fx1- old-child-base) n old-child-base child-idx old-cp child)

    (when (fx< old-val-base old-len)
      (bnode-copy/remove! new-node old-val-base n old-val-base key-idx old-kp))

    new-node))

(define (merge-nodes k1 v1 h1 k2 v2 h2 shift)
  (cond
   [(and (fx< *hashcode-bits* shift)
         (fx= h1 h2))
    ;; hash collision
    (make-cnode h1 (vector (cons k1 v1) (cons k2 v2)))]

   [else
    (let ([m1 (bnode-mask h1 shift)]
          [m2 (bnode-mask h2 shift)])
      (cond
       [(fx= m1 m2)
        ;; partial collision: descend
        (let* ([child (merge-nodes k1 v1 h1 k2 v2 h2 (down shift))]
               [count (node-count child)]
               [childmap (bnode-bit-pos h1 shift)])
          (make-bnode 0 childmap 0 1 count [child]))]

       [else
        ;; no collision
        (let ([keymap (fxior (bnode-bit-pos h1 shift)
                             (bnode-bit-pos h2 shift))])
          (if (and (eq? v1 #t)
                   (eq? v2 #t))
              (if (fx< m1 m2)
                  (make-bnode keymap 0 2 0 2 [k1 k2])
                  (make-bnode keymap 0 2 0 2 [k2 k1]))
              (if (fx< m1 m2)
                  (make-bnode keymap 0 2 0 2 [k1 k2 v1 v2])
                  (make-bnode keymap 0 2 0 2 [k2 k1 v2 v1]))))]))]))

(define (bnode-replace-child n old-child new-child idx)
  (let ([count-diff (fx- (node-count new-child) (node-count old-child))]
        [child-base (bnode-child-base n)]
        [new-node (#%vector-copy n)])
    (bnode-set-count! new-node (fx+ (bnode-count n) count-diff))
    (#%vector-set! new-node (fx+ child-base idx) new-child)
    new-node))

(define (bnode-add-key n key val bit)
  (let* ([old-len (#%vector-length n)]
         [idx (bnode-key-index n bit)]
         [new-km (fxior (bnode-keymap n) bit)]
         [old-cm (bnode-childmap n)]
         [old-kp (bnode-keypop n)]
         [old-cp (bnode-childpop n)]
         [old-child-base (fx+ *bnode-key-base* old-kp)]
         [old-val-base (fx+ old-child-base old-cp)]
         [new-node
          (cond
           [(fx= old-len old-val-base) ; values are currently implicit
            (cond
             [(eq? val #t) ; values can stay implicit
              (make-vector (fx1+ old-len))]
             [else ; need to reify
              (let ([v (make-vector (fx+ old-len old-kp 2) #t)])
                (#%vector-set! v (fx+ old-val-base idx 1) val)
                v)])]
           [else ; values are already reified
            (let ([v (make-vector (fx+ old-len 2))])
              (bnode-copy/add! v (fx1+ old-val-base) n old-val-base idx old-kp val)
              v)])])

    (bnode-set-bitmaps+pops! new-node new-km old-cm (fx1+ old-kp) old-cp)
    (bnode-set-count! new-node (fx1+ (bnode-count n)))
    (bnode-copy/add! new-node *bnode-key-base* n *bnode-key-base* idx old-kp key)
    (bnode-copy/base! new-node (fx1+ old-child-base) 0 n old-child-base 0 old-cp)
    new-node))

(define (bnode-set n key val eqtype keyhash shift)
  (let ([bit (bnode-bit-pos keyhash shift)])

    (cond
     [(bnode-maps-key? n bit)
      (let* ([idx (bnode-key-index n bit)]
             [k (bnode-key-ref n idx)]
             [v (bnode-val-ref n idx)])
        (cond
         [(key=? eqtype key k)
          (if (eq? val v)
              n
              (bnode-replace-val n idx val))]
         [else
          (let* ([h (hash-code eqtype k)]
                 [child (merge-nodes k v h key val keyhash (down shift))])
            (bnode-add-child n child idx bit))]))]

     [(bnode-maps-child? n bit)
      (let* ([idx (bnode-child-index n bit)]
             [old-child (bnode-child-ref n idx)]
             [new-child (node-set old-child key val eqtype keyhash (down shift))])
        (if (eq? new-child old-child)
            n
            (bnode-replace-child n old-child new-child idx)))]

     [else
      (bnode-add-key n key val bit)])))

(define (bnode-singleton n idx bit keyhash shift)
  ;; `n` maps exactly two keys and no children. So `idx` must be
  ;; either 0 or 1.
  (let* ([old-km (bnode-keymap n)]
         [keep-idx (if (fx= 0 idx) 1 0)]
         [keep-key (bnode-key-ref n keep-idx)]
         [keep-val (bnode-val-ref n keep-idx)]
         [new-km
          ;; We can use `keyhash` -- the hash of the key we're *removing* --
          ;; to compute the keymap for a singleton node containing only
          ;; the key we're *not* removing, because the hash codes of both
          ;; keys share a common prefix, and we're constructing a keymap
          ;; that reflects the case where shift = 0. (That's because we
          ;; know that this singleton is going to become the new root node.)
          ;;
          ;; [Thanks to an author of the CHAMP paper,
          ;; Michael Steindorfer, for explaining this.]
          (if (fx= 0 shift)
              (fxxor old-km bit)
              (bnode-bit-pos keyhash 0))])
    (if (eq? keep-val #t)
        (make-bnode new-km 0 1 0 1 [keep-key])
        (make-bnode new-km 0 1 0 1 [keep-key keep-val]))))

(define (bnode-remove-key n idx bit)
  (let* ([new-km (fxxor (bnode-keymap n) bit)]
         [old-cm (bnode-childmap n)]
         [old-len (#%vector-length n)]
         [old-kp (bnode-keypop n)]
         [old-cp (bnode-childpop n)]
         [old-child-base (fx+ *bnode-key-base* old-kp)]
         [old-val-base (fx+ old-child-base old-cp)]
         [new-node
          (cond
           [(fx= old-val-base old-len)
            ;; implicit values
            (make-vector (fx1- old-len))]
           [else
            ;; explicit values
            (let ([v (make-vector (fx- old-len 2))])
              (bnode-copy/remove! v (fx1- old-val-base) n old-val-base idx old-kp)
              v)])])

    (bnode-set-bitmaps+pops! new-node new-km old-cm (fx1- old-kp) old-cp)
    (bnode-set-count! new-node (fx1- (bnode-count n)))
    (bnode-copy/remove! new-node *bnode-key-base* n *bnode-key-base* idx old-kp)
    (bnode-copy/base! new-node (fx1- old-child-base) 0 n old-child-base 0 old-cp)
    new-node))

(define (bnode-remove-child n singleton child-idx bit)
  ;; We're removing a child at `child-idx` and adding
  ;; a k-v pair extracted from `singleton`, which can
  ;; only be a bnode.
  (let* ([old-len (#%vector-length n)]
         [key-idx (bnode-key-index n bit)]
         [new-km (fxior (bnode-keymap n) bit)]
         [new-cm (fxxor (bnode-childmap n) bit)]
         [old-kp (bnode-keypop n)]
         [old-cp (bnode-childpop n)]
         [old-child-base (fx+ *bnode-key-base* old-kp)]
         [old-val-base (fx+ old-child-base old-cp)]
         [key (bnode-key-ref singleton 0)]
         [val (bnode-val-ref singleton 0)]
         [new-node
          (cond
           [(fx< old-val-base old-len)
            ;; explicit values
            (let ([v (make-vector (fx1+ old-len))])
              (bnode-copy/add! v old-val-base n old-val-base key-idx old-kp val)
              v)]
           [(eq? val #t)
            ;; keep implicit values
            (make-vector old-len)]
           [else
            ;; reify values
            (let ([v (make-vector (fx+ old-len old-kp 1) #t)])
              (#%vector-set! v (fx+ old-val-base key-idx) val)
              v)])])

    (bnode-set-bitmaps+pops! new-node new-km new-cm (fx1+ old-kp) (fx1- old-cp))
    (bnode-set-count! new-node (fx1- (bnode-count n)))
    (bnode-copy/add! new-node *bnode-key-base* n *bnode-key-base* key-idx old-kp key)
    (bnode-copy/remove! new-node (fx1+ old-child-base) n old-child-base child-idx old-cp)
    new-node))

(define (bnode-remove n key eqtype keyhash shift)
  (let ([bit (bnode-bit-pos keyhash shift)])

    (cond
     [(bnode-maps-key? n bit)
      (let* ([idx (bnode-key-index n bit)]
             [k (bnode-key-ref n idx)])
        (cond
         [(key=? eqtype key k)
          (if (and (fx= 2 (bnode-keypop n))
                   (fx= 0 (bnode-childpop n)))
              (bnode-singleton n idx bit keyhash shift)
              (bnode-remove-key n idx bit))]
         [else
          n]))]

     [(bnode-maps-child? n bit)
      (let* ([idx (bnode-child-index n bit)]
             [old-child (bnode-child-ref n idx)]
             [new-child (node-remove old-child key eqtype keyhash (down shift))])
        (cond
         [(eq? new-child old-child)
          n]
         [(fx= 1 (node-count new-child))
          (if (and (fx= 0 (bnode-childpop n))
                   (fx= 1 (bnode-keypop n)))
              new-child
              (bnode-remove-child n new-child idx bit))]
         [else
          (bnode-replace-child n old-child new-child idx)]))]

     [else
      n])))

(define (bnode=? a b eqtype val=?)
  (and
   (bnode? b)
   (fx= (bnode-count a) (bnode-count b))
   (fx= (bnode-keymap a) (bnode-keymap b))
   (fx= (bnode-childmap a) (bnode-childmap b))

   (let ([kpop (bnode-keypop a)])
     (let loop ([i 0])
       (or (fx= i kpop)
           (and (key=? eqtype (bnode-key-ref a i) (bnode-key-ref b i))
                (val=? (bnode-val-ref a i) (bnode-val-ref b i))
                (loop (fx1+ i))))))

   (let ([cpop (bnode-childpop a)])
     (let loop ([i 0])
       (or (fx= i cpop)
           (and (node=? (bnode-child-ref a i) (bnode-child-ref b i) eqtype val=?)
                (loop (fx1+ i))))))))

(define (bnode-keys-subset? a b eqtype shift)
  (cond
   [(bnode? b)
    (let* ([akm (bnode-keymap a)]
           [bkm (bnode-keymap b)]
           [acm (bnode-childmap a)]
           [bcm (bnode-childmap b)]
           [abm (fxior akm acm)]
           [bbm (fxior bkm bcm)])
      (and
       (fx= abm (fxand abm bbm))

       (let loop ([bit 0] [aki 0] [bki 0] [aci 0] [bci 0])
         (cond
          [(fx= 0 (fxsrl abm bit)) #t]
          [(fxbit-set? akm bit)
           (cond
            [(fxbit-set? bkm bit)
             (and (key=? eqtype (bnode-key-ref a aki) (bnode-key-ref b bki))
                  (loop (fx1+ bit) (fx1+ aki) (fx1+ bki) aci bci))]
            [else
             (let ([akey (bnode-key-ref a aki)]
                   [bchild (bnode-child-ref b bci)])
               (and (node-has-key? bchild akey eqtype (hash-code eqtype akey) (down shift))
                    (loop (fx1+ bit) (fx1+ aki) bki aci (fx1+ bci))))])]
          [(fxbit-set? acm bit)
           (cond
            [(fxbit-set? bkm bit) #f]
            [else
             (let ([achild (bnode-child-ref a aci)]
                   [bchild (bnode-child-ref b bci)])
               (and (node-keys-subset? achild bchild eqtype (down shift))
                    (loop (fx1+ bit) aki bki (fx1+ aci) (fx1+ bci))))])]
          [(fxbit-set? bkm bit)
           (loop (fx1+ bit) aki (fx1+ bki) aci bci)]
          [(fxbit-set? bcm bit)
           (loop (fx1+ bit) aki bki aci (fx1+ bci))]
          [else
           (loop (fx1+ bit) aki bki aci bci)]))))]
   [else
    (let ([kpop (bnode-keypop a)]
          [cpop (bnode-childpop a)])
      (and (fx= 1 (fx+ kpop cpop))
           (if (fx= kpop 1)
               (node-keys-subset? (bnode-child-ref a 0) b eqtype (down shift))
               (not (not (cnode-index b (bnode-key-ref a 0) eqtype))))))]))

(define (bnode-entry-at-position n pos)
  (let ([kpop (bnode-keypop n)])
    (cond
     [(fx< pos kpop)
      (cons (bnode-key-ref n pos) (bnode-val-ref n pos))]
     [else
      (let ([cpop (bnode-childpop n)])
        (let loop ([i 0] [pos (fx- pos kpop)])
          (cond [(fx= i cpop) #f]
                [else
                 (let* ([child (bnode-child-ref n i)]
                        [count (node-count child)])
                   (if (fx< pos count)
                       (node-entry-at-position child pos)
                       (loop (fx1+ i) (fx- pos count))))])))])))


;; cnodes
(define-record-type cnode
  [fields (immutable hash)
          (immutable pairs)]
  [nongenerative #{cnode pfwh0bwrq2nqlke97ikru0ds2-0}]
  [sealed #t])

(define (cnode-count n)
  (#%vector-length (cnode-pairs n)))

(define (cnode-pair-ref n i)
  (#%vector-ref (cnode-pairs n) i))

(define (cnode-key-ref n i)
  (car (cnode-pair-ref n i)))

(define (cnode-val-ref n i)
  (cdr (cnode-pair-ref n i)))

(define (cnode-index n key eqtype)
  (let loop ([i (cnode-count n)])
    (cond [(fx= 0 i) #f]
          [(key=? eqtype key (cnode-key-ref n (fx1- i))) (fx1- i)]
          [else (loop (fx1- i))])))

(define (cnode-ref n key eqtype)
  (let ([i (cnode-index n key eqtype)])
    (if i
        (cnode-val-ref n i)
        *nothing*)))

(define (cnode-set n key val eqtype)
  (let ([i (cnode-index n key eqtype)])
    (if i
        ;; replace existing value
        (let ([p (cnode-pair-ref n i)])
          (if (eq? val (cdr p))
              n
              (let ([v (#%vector-copy (cnode-pairs n))])
                (#%vector-set! v i (cons (car p) val))
                (make-cnode (cnode-hash n) v))))
        ;; add new k-v pair
        (let* ([len (cnode-count n)]
               [v (make-vector (fx1+ len))])
          (vector-copy! v 0 (cnode-pairs n) 0 len)
          (#%vector-set! v len (cons key val))
          (make-cnode (cnode-hash n) v)))))

(define (cnode-remove n key eqtype)
  (let ([i (cnode-index n key eqtype)])
    (cond
     [i
      (case (cnode-count n)
        [(1)
         empty-bnode]
        [(2)
         (let* ([idx (if (fx= i 0) 1 0)]
                [p (cnode-pair-ref n idx)])
           (bnode-set empty-bnode (car p) (cdr p) eqtype (cnode-hash n) 0))]
        [else
         (let* ([old-pairs (cnode-pairs n)]
                [old-len (#%vector-length old-pairs)]
                [new-pairs (make-vector (fx1- old-len))])
           ;; okay, maybe this is misnamed
           (bnode-copy/remove! new-pairs 0 old-pairs 0 i old-len)
           (make-cnode (cnode-hash n) new-pairs))])]
     [else
      n])))

(define (cnode=? a b eqtype val=?)
  (and
   (cnode? b)
   (fx= (cnode-hash a) (cnode-hash b))
   (fx= (cnode-count a) (cnode-count b))

   (let loop ([i (cnode-count a)])
     (or (fx= 0 i)
         (let* ([ap (cnode-pair-ref a (fx1- i))]
                [bval (cnode-ref b (car ap) eqtype)])
           (and (val=? (cdr ap) bval)
                (loop (fx1- i))))))))

(define (cnode-keys-subset? a b eqtype shift)
  (and
   (or (not (cnode? b))
       (fx= (cnode-hash a) (cnode-hash b)))

   (let loop ([i (cnode-count a)])
     (cond [(fx= 0 i) #t]
           [else
            (let ([key (cnode-key-ref a (fx1- i))])
              (and
               (node-has-key? b key eqtype (cnode-hash a) shift)
               (loop (fx1- i))))]))))

(define (cnode-entry-at-position n pos)
  ;; NOTE: verify this
  ;; Chez pairs are mutable, so can't just return
  ;; the node's own pair; I need to re-wrap.
  (and (fx< pos (cnode-count n))
       (let ([p (cnode-pair-ref n pos)])
         (cons (car p) (cdr p)))))


;; generic node operations
(define (node-key-ref n i)
  (if (bnode? n)
      (bnode-key-ref n i)
      (cnode-key-ref n i)))

(define (node-val-ref n i)
  (if (bnode? n)
      (bnode-val-ref n i)
      (cnode-val-ref n i)))

(define (node-count n)
  (if (bnode? n)
      (bnode-count n)
      (cnode-count n)))

(define (node-ref n key eqtype keyhash shift)
  (if (bnode? n)
      (bnode-ref n key eqtype keyhash shift)
      (cnode-ref n key eqtype)))

(define (node-has-key? n key eqtype keyhash shift)
  (not (eq? *nothing*
            (node-ref n key eqtype keyhash shift))))

(define (node-set n key val eqtype keyhash shift)
  (if (bnode? n)
      (bnode-set n key val eqtype keyhash shift)
      (cnode-set n key val eqtype)))

(define (node-remove n key eqtype keyhash shift)
  (if (bnode? n)
      (bnode-remove n key eqtype keyhash shift)
      (cnode-remove n key eqtype)))

(define (node=? a b eqtype val=?)
  (or
   (eq? a b)

   (if (bnode? a)
       (bnode=? a b eqtype val=?)
       (cnode=? a b eqtype val=?))))

(define (node-keys-subset? a b eqtype shift)
  (or
   (eq? a b)
   (and (fx<= (node-count a) (node-count b))
        (if (bnode? a)
            (bnode-keys-subset? a b eqtype shift)
            (cnode-keys-subset? a b eqtype shift)))))

(define (node-entry-at-position n pos)
  (if (bnode? n)
      (bnode-entry-at-position n pos)
      (cnode-entry-at-position n pos)))

(define (node-hash-code n hash hc)
  (cond
   [(bnode? n)
    (let ([km (bnode-keymap n)]
          [cm (bnode-childmap n)]
          [kpop (bnode-keypop n)]
          [cpop (bnode-childpop n)])
      (letrec
          ([cloop
            (lambda (i hc)
              (if (fx= i cpop)
                  hc
                  (cloop (fx1+ i)
                         (node-hash-code (bnode-child-ref n i) hash hc))))]
           [kloop
            (lambda (i hc)
              (if (fx= i kpop)
                  (cloop 0 hc)
                  (kloop (fx1+ i)
                         (hash-code-combine hc (hash (bnode-val-ref n i))))))])
        (kloop 0 (hash-code-combine hc (fxior km cm)))))]
   [else
    ;; Hash code needs to be order-independent, so
    ;; collision nodes are a problem; simplify by just
    ;; using the hash code and hope that collisions are
    ;; rare.
    (hash-code-combine hc (cnode-hash n))]))

(define (node-iterate-first n stack)
  ;; In node positions, all indices are represented as
  ;; key indices, even if they refer to childres. This
  ;; relies on the fact that children follow keys
  ;; immediately in the bnode representation.
  (cond
   [(bnode? n)
    (let* ([i (fx- (bnode-val-base n) *bnode-key-base* 1)]
           [stack (cons (cons n i) stack)])
      (if (fx>= i (bnode-keypop n))
          (node-iterate-first (bnode-key-ref n i) stack)
          stack))]
   [else
    (let ([i (fx1- (cnode-count n))])
      (cons (cons n i) stack))]))

(define (node-iterate-next pos)
  (cond
   [(null? pos)
    ;; Stack is empty, so we're done
    #f]
   [else
    (let* ([p (car pos)]
           [stack (cdr pos)]
           [n (car p)]
           [i (cdr p)])
      (cond
       [(bnode? n)
        (cond
         [(fx= 0 i)
          ;; Exhausted this node, so return to parent node
          (node-iterate-next stack)]
         [else
          ;; Move to next (lower) index in the current node
          (let* ([i (fx1- i)]
                 [stack (cons (cons n i) stack)])
            (if (fx>= i (bnode-keypop n))
                (node-iterate-first (bnode-key-ref n i) stack)
                stack))])]
       [else
        (cond
         [(fx= 0 i)
          ;; Exhausted this node, so return to parent node
          (node-iterate-next stack)]
         [else
          (cons (cons n (fx1- i)) stack)])]))]))


;; hamt interface
(define empty-hash (make-hamt 'equal empty-bnode))
(define empty-hasheqv (make-hamt 'eqv empty-bnode))
(define empty-hasheq (make-hamt 'eq empty-bnode))

;; shells need to be fresh instances
(define (make-hamt-shell eqtype)
  (make-hamt eqtype empty-bnode))

(define (hamt-shell-sync! dst src)
  (hamt-root-set! dst (hamt-root src)))

(define immutable-hash? hamt?)

(define (hamt-equal? h) (eq? 'equal (hamt-eqtype h)))
(define (hamt-eqv? h) (eq? 'eqv (hamt-eqtype h)))
(define (hamt-eq? h) (eq? 'eq (hamt-eqtype h)))

(define (hamt-count h)
  (bnode-count (hamt-root h)))

(define (hamt-empty? h)
  (fx= 0 (hamt-count h)))

(define (hamt-ref h key fail)
  (let* ([root (hamt-root h)]
         [eqtype (hamt-eqtype h)]
         [keyhash (hash-code eqtype key)]
         [res (bnode-ref root key eqtype keyhash 0)])
    (cond
     [(eq? *nothing* res)
      (if (procedure? fail)
          (fail)
          fail)]
     [else
      res])))

(define (hamt-set h key val)
  (let* ([old-root (hamt-root h)]
         [eqtype (hamt-eqtype h)]
         [keyhash (hash-code eqtype key)]
         [new-root (bnode-set old-root key val eqtype keyhash 0)])
    (if (eq? new-root old-root)
        h
        (make-hamt eqtype new-root))))

(define (hamt-remove h key)
  (let* ([old-root (hamt-root h)]
         [eqtype (hamt-eqtype h)]
         [keyhash (hash-code eqtype key)]
         [new-root (bnode-remove old-root key eqtype keyhash 0)])
    (if (eq? new-root old-root)
        h
        (make-hamt eqtype new-root))))

(define (hamt-keys-subset? a b)
  (bnode-keys-subset? (hamt-root a) (hamt-root b) (hamt-eqtype a) 0))

(define (hamt=? a b eql?)
  (bnode=? (hamt-root a) (hamt-root b) (hamt-eqtype a) eql?))

(define (hamt-hash-code n hash)
  (node-hash-code (hamt-root n) hash 0))

(define ignored/hamt
  (begin
    (record-type-equal-procedure (record-type-descriptor hamt)
                                 (lambda (a b eql?)
                                   (hamt=? a b eql?)))
    (record-type-hash-procedure (record-type-descriptor hamt)
                                (lambda (a hash)
                                  (hamt-hash-code a hash)))))

;; safe iteration
(define (hamt-iterate-first h)
  (and (not (hamt-empty? h))
       0))

(define (hamt-iterate-next h pos)
  (let ([pos (fx1+ pos)])
    (and (not (fx= pos (hamt-count h)))
         pos)))

(define (hamt-iterate-key h pos fail)
  (let ([p (node-entry-at-position (hamt-root h) pos)])
    (if p
        (car p)
        fail)))

(define (hamt-iterate-value h pos fail)
  (let ([p (node-entry-at-position (hamt-root h) pos)])
    (if p
        (cdr p)
        fail)))

(define (hamt-iterate-key+value h pos fail)
  (let ([p (node-entry-at-position (hamt-root h) pos)])
    (if p
        (values (car p) (cdr p))
        fail)))

(define (hamt-iterate-pair h pos fail)
  (let ([p (node-entry-at-position (hamt-root h) pos)])
    (or p fail)))

;; unsafe iteration; position is a stack
;; represented by a list of (cons node index)
(define (unsafe-hamt-iterate-first h)
  (and (not (hamt-empty? h))
       (node-iterate-first (hamt-root h) '())))

(define (unsafe-hamt-iterate-next h pos)
  (node-iterate-next pos))

(define (unsafe-hamt-iterate-key h pos)
  (let ([p (car pos)])
    (node-key-ref (car p) (cdr p))))

(define (unsafe-hamt-iterate-value h pos)
  (let ([p (car pos)])
    (node-val-ref (car p) (cdr p))))

(define (unsafe-hamt-iterate-key+value h pos)
  (let ([p (car pos)])
    (let ([n (car p)]
          [i (cdr p)])
      (values (node-key-ref n i)
              (node-val-ref n i)))))

(define (unsafe-hamt-iterate-pair h pos)
  (let ([p (car pos)])
    (let ([n (car p)]
          [i (cdr p)])
      (cons (node-key-ref n i)
            (node-val-ref n i)))))

(define (hamt-fold h nil fn)
  (let loop ([pos (unsafe-hamt-iterate-first h)] [nil nil])
    (cond
     [pos
      (let-values ([(k v) (unsafe-hamt-iterate-key+value h pos)])
        (loop (node-iterate-next pos) (fn k v nil)))]
     [else
      nil])))

(define (hamt-for-each h proc)
  (hamt-fold h (void) (lambda (k v _) (proc k v) (void))))

(define (hamt-map h proc)
  (hamt-fold h '() (lambda (k v xs) (cons (proc k v) xs))))

(define (hamt->list h)
  (hamt-fold h '() (lambda (k v xs) (cons (cons k v) xs))))

(define (hamt-keys h)
  (hamt-fold h '() (lambda (k _ xs) (cons k xs))))

(define (hamt-values h)
  (hamt-fold h '() (lambda (_ v xs) (cons v xs))))

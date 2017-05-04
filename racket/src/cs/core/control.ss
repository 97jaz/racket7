;; The full continuation is a chain of metacontinuations. Each
;; metacontinuation contains a host Scheme continuation, and
;; every prompt is on a boundary between metacontinuations. When
;; a composable continuation is applied, the composition boundary
;; is also a metacontinuation boundary.

;; "Continuation" as exported from the core is "metacontinuation"
;; here. So, `call-with-current-continuation` defined here and
;; exported captures the current metacontinuation (up to a prompt).
;; The `call/cc` function is the host's notion of continuation, which
;; corresponds to a single metacontinuation frame.

;; A picture where the continuation grows down:

;;                   [root empty continuation]
;;                    --- empty-k
;; metacontinuation  |
;;     frame         |
;;                   |--- resume-k & resume/no-wind
;;                   |<-- tag represents this point
;;                    --- empty-k
;; metacontinuation  |
;;     frame         |
;;                   |
;;                   |--- resume-k & resume/no-wind
;;                   |<-- tag represents this point
;;                    --- empty-k
;;   current host    |
;;   continuation    |
;;                   v

;; Concretely, the metacontinuation is the current host continuation
;; plus the frames in the list `*metacontinuation*`, where the
;; shallowest (= lowest in the picture above) frame is first in the
;; list. The `empty-k` value of the current host continuation is
;; in `*empty-k*`.

;; The host Scheme implementation takes care of winders from
;; `dynamic-wind`, which means that tings generally work if host
;; functions uses `dynamic-wind` (e.g., for `with-input-from-file`).
;; We assume that no host Scheme winders end up using continuations
;; (or calling client-provided code that can use continuations), so
;; that cross-frame jumps at the metacontinuation level are not
;; triggered by the host Scheme.

;; The continuation within a metacontinuation frame is kept in two
;; forms: one that has the frame's winders (from `dynamic-wind`)
;; attached, and one that doesn't. The one without winders is used to
;; reinstantiate the frame's continuation as the host continuation
;; when control returns to that frame. The one with winders is used to
;; compose a captured frame onto the current continuation. See
;; `call/cc-no-winders` for the way Chez internals are used to get a
;; continuation disconnected from winders. See also the use of
;; `#%$current-stack-link` to disconnect a fresh metacontinuation
;; frame's continuation from the formerly current continuation.

;; The shallowest metacontinuation frame's `empty-k` continuation is
;; used to detect when the current host continuation is empty (i.e.,
;; when it matches the `*empty-k*` value). When it's empty, then
;; calling a composable continuation doesn't need to add a new
;; metacontinuation frame, and the application gets the right "tail"
;; behavior.

;; A metacontinuation frame's `resume-k/no-wind` is called when
;; control returns or needs to escape through the frame:
;;
;; * When returning normally to a metacontinuation frame, the
;;   `resume-k/no-wind` continuation receives the values returned to the
;;   frame.
;;
;; * When aborting to a prompt tag, the `resume-k/no-wind`
;;   continination receives a special value that indicates an abort to a
;;   specific tag, and the frames will jump to the next metacontinuation
;;   frame (running the current frame's "out" winders) until a frame
;;   with the right tag is hit.
;;
;; * Calling a non-composable continuation is similar to aborting,
;;   except that the target prompt's abort handler is not called.
;;   In fact, the metacontinuation-frame unwinding process stops
;;   before the frame with the target prompt tag (since that prompt
;;   is meant to be preserved).
;;
;; * When composing a metacontinuation frame onto the current
;;   metacontinuation, `resume-k` is called instead of
;;   `resume-k/no-wind` so that the frame's "in" winders get run.

;; The continuation marks for the frame represented by the current
;; host continuation are kept in `*mark-stack*`. When a metacontinuation
;; frame is created, it takes the current `*mark-stack*` value and
;; `*mark-stack*` is set back to empty. To keep winders and the mark
;; stack in sync, `dynamic-wind` is wrapped to reset the mark stack on
;; entry to a pre or post thunk.

;; A metacontinuation frame has an extra cache slot to contain a list
;; of mark-stack lists down to the root continuation. When a delimited
;; sequence of metacontinuation frames are copied out of or into the
;; metacontinuation, the slot is flushed and will be reset on demand.

;; We're assuming for now that no handlers are installed during a
;; nested metacontinuation.

;; Continuations are used to implement engines, but it's important
;; that an engine doesn't get swapped out (or, more generally,
;; asynchronous signals are handled at the Racket level) while we're
;; manipulating the continuation representation. A bad time for a swap
;; is an "interrupted" region. The `begin-uninterrupted` and
;; `end-uninterrupted` functions bracket such regions dynamically. See
;; also "core-engine.ss" and "core-interrupt.ss"

;; ----------------------------------------

(define *metacontinuation* '())
(define *empty-k* #f)

(define-record metacontinuation-frame (tag          ; continuation prompt tag or #f
                                       resume-k     ; delivers values to the prompt
                                       resume-k/no-wind ; same, but doesn't run winders jumping in
                                       empty-k      ; deepest end of this frame
                                       mark-stack   ; mark stack to restore
                                       mark-chain)) ; #f or a cached list of mark-chain-frame or elem+cache

;; Messages to `resume-k[/no-wind]`:
(define-record appending (resume))  ; composing the frame, so run "in" winders
(define-record aborting (tag args)) ; aborting, so run "out" winders
(define-record applying (c args))   ; applying a non-composable continuation

(define-record-type (continuation-prompt-tag create-continuation-prompt-tag continuation-prompt-tag?)
  (fields (mutable name))) ; mutable => constructor generates fresh instances

(define the-default-continuation-prompt-tag (create-continuation-prompt-tag 'default))

;; Not actually set, but allows access to the full continuation:
(define the-root-continuation-prompt-tag (create-continuation-prompt-tag 'root))

;; Detected to prevent some jumps:
(define the-barrier-prompt-tag (create-continuation-prompt-tag 'barrier))

(define make-continuation-prompt-tag
  (case-lambda
    [() (create-continuation-prompt-tag #f)]
    [(name)
     (unless (symbol? name)
       (raise-argument-error 'make-continuation-prompt-tag "symbol?" name))
     (create-continuation-prompt-tag name)]))
     
(define (default-continuation-prompt-tag) the-default-continuation-prompt-tag)
(define (root-continuation-prompt-tag) the-root-continuation-prompt-tag)

;; To support special treatment of break parameterizations, and also
;; to initialize disabled breaks for `dynamic-wind` pre and post
;; thunks:
(define break-enabled-key (gensym 'break-enabled))

;; FIXME: add caching to avoid full traversal
(define (continuation-prompt-available? tag)
  (unless (continuation-prompt-tag? tag)
    (raise-argument-error 'continuation-prompt-tag-available? "continuation-prompt-tag?" tag))
  (or (eq? tag the-default-continuation-prompt-tag)
      (eq? tag the-root-continuation-prompt-tag)
      (let loop ([mc *metacontinuation*])
        (cond
         [(null? mc)
          #f]
         [(eq? tag (metacontinuation-frame-tag (car mc)))
          #t]
         [else (loop (cdr mc))]))))

(define call-with-continuation-prompt
  (case-lambda
    [(proc) (call-with-continuation-prompt proc the-default-continuation-prompt-tag #f)]
    [(proc tag) (call-with-continuation-prompt proc tag #f)]
    [(proc tag handler . args)
     (unless (procedure? proc)
       (raise-argument-error 'call-with-continuation-prompt "procedure?" proc))
     (unless (continuation-prompt-tag? tag)
       (raise-argument-error 'call-with-continuation-prompt "continuation-prompt-tag?" tag))
     (unless (or (not handler) (procedure? handler))
       (raise-argument-error 'call-with-continuation-prompt "(or/c #f procedure?)" handler))
     (start-uninterrupted 'prompt)
     (call-in-empty-metacontinuation-frame
      tag
      (or handler (make-default-abort-handler tag))
      (lambda ()
        (end-uninterrupted 'prompt)
        (apply proc args)))]))

(define (make-default-abort-handler tag)
  (lambda (abort-thunk)
    (unless (and (procedure? abort-thunk)
                 (procedure-arity-includes? abort-thunk 0))
      (raise-argument-error 'default-continuation-prompt-handler "(procedure-arity-includes/c 0)" abort-thunk))
    (call-with-continuation-prompt abort-thunk tag #f)))

(define (resume-metacontinuation results)
  ;; pop a metacontinuation frame
  (cond
   [(null? *metacontinuation*) (exit)]
   [else
    (start-uninterrupted 'resume-mc)
    (let ([mf (car *metacontinuation*)])
      (pop-metacontinuation-frame)
      ;; resume
      ((metacontinuation-frame-resume-k/no-wind mf) results))]))

(define (pop-metacontinuation-frame)
  (let ([mf (car *metacontinuation*)])
    (set! *metacontinuation* (cdr *metacontinuation*))
    (set! *mark-stack* (metacontinuation-frame-mark-stack mf))
    (set! *empty-k* (metacontinuation-frame-empty-k mf))))

(define (call-in-empty-metacontinuation-frame tag handler proc)
  ;; Call `proc` in an empty metacontinuation frame, reifying the
  ;; current metacontinuation as needed (i.e., if non-empty) as a new
  ;; frame on `*metacontinuations*`; if the tag is #f and the 
  ;; current metacontinuation frame is already empty, don't push more
  (assert-in-uninterrupted)
  (call/cc
   (lambda (k)
     (cond
      [(and (not tag)
            (pair? *metacontinuation*)
            (let ([current-mf (car *metacontinuation*)])
              (and (eq? tag (metacontinuation-frame-tag current-mf))
                   (eq? k *empty-k*)
                   current-mf)))
       =>
       (lambda (current-mf)
         ;; empty continuation in the current frame; don't push a
         ;; new metacontinuation frame --- and, in fact, keep the
         ;; current one if metadata hasn't changed; we assume that
         ;; there are no new winders and the handler is the same,
         ;; otherwise the continuation would be bigger
         (when *mark-stack*
           ;; update metacontinuation for new mark-stack elements:
           (set! *metacontinuation*
                 (cons (metacontinuation-frame-merge current-mf *mark-stack*)
                       (cdr *metacontinuation*))))
         (proc))]
      [else
       (let ([r ; a list of results, or a non-list for special handling
              (call/cc
               (lambda (k)
                 (call/cc-no-winders
                  ;; Not necessarily called in tail position, but that's ok:
                  (lambda (k/no-wind)
                    ;; At this point, the winders list is empty.
                    ;; Push another continuation frame so we can drop it's `next`
                    (call-as-non-tail
                     (lambda ()
                       ;; drop the rest of the current continuation from the
                       ;; new metacontinuation frame:
                       (#%$current-stack-link #%$null-continuation)
                       (let-values ([results
                                     (call/cc
                                      ;; remember the "empty" continuation frame
                                      ;; that just continues the metacontinuation:
                                      (lambda (empty-k)
                                        (let ([mf (make-metacontinuation-frame tag
                                                                               k
                                                                               k/no-wind
                                                                               *empty-k*
                                                                               *mark-stack*
                                                                               #f)])
                                          (set! *empty-k* empty-k)
                                          (set! *mark-stack* #f)
                                          ;; push the metacontinuation:
                                          (set! *metacontinuation* (cons mf *metacontinuation*))
                                          ;; ready:
                                          (proc))))])
                         ;; continue normally; the metacontinuation could be different
                         ;; than when we captured this metafunction frame, though:
                         (resume-metacontinuation results))))))))])
         (cond
          [(or (null? r) (pair? r))
           ;; We're returning normally; the metacontinuation frame has
           ;; been popped already by `resume-metacontinuation`
           (end-uninterrupted 'resume)
           (if (and (pair? r) (null? (cdr r)))
               (car r)
               (apply values r))]
          [(appending? r)
           ;; We applied this metacontinuation frame just to run its "in" winders
           ((appending-resume r))]
          [(aborting? r)
           ;; We're aborting to a given tag
           (cond
            [(eq? tag (aborting-tag r))
             ;; Found the right tag. Remove the prompt as we call the handler:
             (pop-metacontinuation-frame)
             (end-uninterrupted 'handle)
             (apply handler
                    (aborting-args r))]
            [else
             ;; Aborting to an enclosing prompt, so keep going:
             (set! *metacontinuation* (cdr *metacontinuation*))
             (do-abort-current-continuation (aborting-tag r)
                                            (aborting-args r))])]
          [(applying? r)
           ;; We're applying a non-composable continuation --- past
           ;; this prompt, or else we would have stopped.
           ;; Continue escaping to an encloding prompt:
           (set! *metacontinuation* (cdr *metacontinuation*))
           (apply-continuation (applying-c r)
                               (applying-args r))]))]))))

(define (call/cc-no-winders proc)
  (let ([prev-winders (#%$current-winders)])
    (cond
     [(null? prev-winders)
      (call/cc proc)]
     [else
      ;; drop winders before capturing continuation:
      (#%$current-winders '())
      (begin0
       (call/cc proc)
       (#%$current-winders prev-winders))])))

(define (call-as-non-tail proc)
  (proc)
  '(error 'call-as-non-tail "shouldn't get to frame that was meant to be discarded"))
  
;; Make a frame like `current-mf`, but with more of a mark stack appended
(define (metacontinuation-frame-merge current-mf mark-stack)
  (make-metacontinuation-frame (metacontinuation-frame-tag current-mf)
                               (metacontinuation-frame-resume-k current-mf)
                               (metacontinuation-frame-resume-k/no-wind current-mf)
                               (metacontinuation-frame-empty-k current-mf)
                               (mark-stack-append mark-stack
                                                  (metacontinuation-frame-mark-stack current-mf))
                               #f))

;; ----------------------------------------

(define (abort-current-continuation tag . args)
  (unless (continuation-prompt-tag? tag)
    (raise-argument-error 'abort-current-continuation "continuation-prompt-tag?" tag))
  (check-prompt-tag-available 'abort-current-continuation tag)
  (start-uninterrupted 'abort)
  (do-abort-current-continuation tag args))
  
(define (do-abort-current-continuation tag args)
  (assert-in-uninterrupted)
  (cond
   [(null? *metacontinuation*)
    ;; A reset handler must end the uninterrupted region:
    ((reset-handler))]
   [else
    ((metacontinuation-frame-resume-k/no-wind (car *metacontinuation*))
     (make-aborting tag args))]))

;; ----------------------------------------

(define (call-with-continuation-barrier p)
  (unless (and (procedure? p)
               (procedure-arity-includes? p 0))
    (raise-argument-error 'call-with-continuation-barrier "(procedure-arity-includes/c 0)" p))
  (start-uninterrupted 'barrier)
  (call-in-empty-metacontinuation-frame
   the-barrier-prompt-tag ; <- recognized as a barrier by continuation capture or call
   #f
   (lambda ()
     (end-uninterrupted 'barrier)
     (p))))

;; ----------------------------------------

(define-record continuation ())
(define-record full-continuation continuation (k mark-stack empty-k mc))
(define-record composable-continuation full-continuation ())
(define-record non-composable-continuation full-continuation (tag))
(define-record escape-continuation continuation (tag))

(define call-with-current-continuation
  (case-lambda
    [(proc) (call-with-current-continuation proc
                                            the-default-continuation-prompt-tag)]
    [(proc tag)
     (unless (and (procedure? proc)
                  (procedure-arity-includes? proc 1))
       (raise-argument-error 'call-with-current-continuation "(procedure-arity-includes/c 1)" proc))
     (unless (continuation-prompt-tag? tag)
       (raise-argument-error 'call-with-current-continuation "continuation-prompt-tag?" tag))
     (call-with-end-uninterrupted
      (lambda ()
        (call/cc
         (lambda (k)
           (proc
            (make-non-composable-continuation
             k
             *mark-stack*
             *empty-k*
             (extract-metacontinuation 'call-with-current-continuation tag #t)
             tag))))))]))

(define call-with-composable-continuation
  (case-lambda
    [(p) (call-with-composable-continuation p the-default-continuation-prompt-tag)]
    [(p tag)
     (unless (and (procedure? p)
                  (procedure-arity-includes? p 1))
       (raise-argument-error 'call-with-composable-continuation "(procedure-arity-includes/c 1)" p))
     (unless (continuation-prompt-tag? tag)
       (raise-argument-error 'call-with-composable-continuation "continuation-prompt-tag?" tag))
     (call-with-end-uninterrupted
      (lambda ()
        (call/cc
         (lambda (k)
           (p
            (make-composable-continuation
             k
             *mark-stack*
             *empty-k*
             (extract-metacontinuation 'call-with-composable-continuation tag #f)))))))]))

(define (call-with-escape-continuation p)
  (unless (and (procedure? p)
               (procedure-arity-includes? p 1))
    (raise-argument-error 'call-with-escape-continuation "(procedure-arity-includes/c 1)" p))
  (let ([tag (make-continuation-prompt-tag)])
    (call-with-continuation-prompt
     (lambda ()
       (p (make-escape-continuation tag)))
     tag
     values)))

;; Applying a continuation calls this internal function:
(define (apply-continuation c args)
  (assert-in-uninterrupted)
  (cond
   [(composable-continuation? c)
    ;; To compose the metacontinuation, first make sure the current
    ;; continuation is reified in `*metacontinuation*`:
    (call-in-empty-metacontinuation-frame
     #f
     fail-abort-to-delimit-continuation
     (lambda ()
       ;; The current metacontinuation frame has an
       ;; empty continuation, so we can "replace" that
       ;; with the composable one:
       (apply-immediate-continuation c args)))]
   [(non-composable-continuation? c)
    (let* ([tag (non-composable-continuation-tag c)]
           [common-mc
            ;; We check every time, just in case control operations
            ;; change the current continuation out from under us.
            (find-common-metacontinuation (full-continuation-mc c)
                                          *metacontinuation*
                                          tag)])
      (cond
       [(eq? common-mc *metacontinuation*)
        ;; Replace the current metacontinuation frame's continuation
        ;; with the saved one; this replacement will take care of any
        ;; shared winders within the frame:
        (apply-immediate-continuation c args)]
       [else
        ;; Jump back to the nearest prompt, then continue jumping
        ;; as needed from there:
        ((metacontinuation-frame-resume-k/no-wind (car *metacontinuation*))
         ;; An `applying` record tells the metacontinuation's continuation
         ;; to continue jumping:
         (make-applying c args))]))]
   [(escape-continuation? c)
    (let ([tag (escape-continuation-tag c)])
      (unless (continuation-prompt-available? tag)
        (raise-arguments-error '|continuation application|
                               "attempt to jump into an escape continuation"))
      (do-abort-current-continuation tag args))]))

;; Apply a continuation within the current metacontinuation frame:
(define (apply-immediate-continuation c args)
  (call-with-appended-metacontinuation
   (full-continuation-mc c)
   (lambda ()
     (set! *mark-stack* (full-continuation-mark-stack c))
     (set! *empty-k* (full-continuation-empty-k c))
     (apply (full-continuation-k c) args))))

;; Used as a "handler" for a prompt without a tag, which is used for
;; composable continuations
(define (fail-abort-to-delimit-continuation . args)
  (error 'abort "trying to abort to a delimiter continuation frame"))

;; Find common metacontinuation to keep due to a combination of:
;; the metacontinuation is beyond the relevant prompt, or the
;; metacontinuation fragment before the prompt is also shared
;; with the composable continuation's metacontinuation (so we
;; should not unwind and rewind those metacontinuation frames)
(define (find-common-metacontinuation mc current-mc tag)
  (define-values (rev-current ; (list (cons mf mc) ...)
                  base-current-mc)
    ;; Get the reversed prefix of `current-mc` that is to be
    ;; replaced by `mc`:
    (let loop ([current-mc current-mc] [accum null])
      (cond
       [(null? current-mc)
        (unless (or (eq? tag the-default-continuation-prompt-tag)
                    (eq? tag the-root-continuation-prompt-tag))
          (raise-arguments-error 'apply-continuation
                                 "continuation includes no prompt with the given tag"
                                 "tag" tag))
        (values accum null)]
       [(eq? tag (metacontinuation-frame-tag (car current-mc)))
        (values accum current-mc)]
       [else
        (loop (cdr current-mc)
              ;; Accumulate this frame plus the chain that
              ;; we should keep if this frame is shared:
              (cons (cons (car current-mc) current-mc)
                    accum))])))
  (define rev-mc (reverse mc))
  ;; Work from the tail backwards (which is forward in the reverse
  ;; lists): If the continuations are the same for the two frames,
  ;; then the metacontinuation frame should not be unwound
  (let loop ([rev-current rev-current]
             [rev-mc rev-mc]
             [base-current-mc base-current-mc])
    (cond
     [(null? rev-mc) base-current-mc]
     [(null? rev-current)
      (check-for-barriers rev-mc)
      base-current-mc]
     [(eq? (metacontinuation-frame-resume-k (car rev-mc))
           (metacontinuation-frame-resume-k (caar rev-current)))
      ;; Matches, so update base and look shallower
      (loop (cdr rev-current)
            (cdr rev-mc)
            (cdar rev-current))]
     [else
      ;; Doesn't match, so we've found the shared part;
      ;; check for barriers that we'd have to reintroduce
      (check-for-barriers rev-mc)
      ;; Return the shared part
      (cdar rev-current)])))

(define (check-for-barriers rev-mc)
  (let loop ([rev-mc rev-mc])
    (unless (null? rev-mc)
      (when (eq? (metacontinuation-frame-tag (car rev-mc))
                 the-barrier-prompt-tag)
        (end-uninterrupted 'hit-barrier)
        (raise-arguments-error '|continuation application|
                               "attempt to cross a continuation barrier"))
      (loop (cdr rev-mc)))))

(define (call-with-end-uninterrupted thunk)
  ;; Using `call/cm` with a key of `none` ensures that we have an
  ;; `(end-uninterrupted)` in the immediate continuation, but
  ;; keeping the illusion that `thunk` is called in tail position.
  (call/cm none #f thunk))

(define (set-continuation-applicables!)
  (let ([add (lambda (rtd)
               (struct-property-set! prop:procedure
                                     rtd
                                     (lambda (c . args)
                                       (start-uninterrupted 'continue)
                                       (apply-continuation c args))))])
    (add (record-type-descriptor composable-continuation))
    (add (record-type-descriptor non-composable-continuation))
    (add (record-type-descriptor escape-continuation))))

;; ----------------------------------------

;; Extract a prefix of `*metacontinuation*` up to `tag`
(define (extract-metacontinuation who tag barrier-ok?)
  (define (check-barrier-ok saw-barrier?)
    (when (and saw-barrier? (not barrier-ok?))
      (raise-arguments-error who "cannot capture past continuation barrier")))
  (let loop ([mc *metacontinuation*] [saw-barrier? #f])
    (cond
     [(null? mc)
      (unless (or (eq? tag the-root-continuation-prompt-tag)
                  (eq? tag the-default-continuation-prompt-tag))
        (raise-arguments-error who "continuation includes no prompt with the given tag"
                               "tag" tag))
      (check-barrier-ok saw-barrier?)
      '()]
     [else
      (let ([a-tag (metacontinuation-frame-tag (car mc))])
        (cond
         [(eq? a-tag tag)
          (check-barrier-ok saw-barrier?)
          '()]
         [else
          (cons (metacontinuation-frame-clear-cache (car mc))
                (loop (cdr mc) (or saw-barrier?
                                   (eq? a-tag the-barrier-prompt-tag))))]))])))

(define (check-prompt-tag-available who tag)
  (unless (continuation-prompt-available? tag)
    (raise-arguments-error who "continuation includes no prompt with the given tag"
                           "tag" tag)))

(define (call-with-appended-metacontinuation mc proc)
  ;; Assumes that the current metacontinuation frame is ready to be
  ;; replaced with `mc` plus `proc`.
  ;; In the simple case of no winders and an empty frame immediate
  ;;  metacontinuation fame, we could just
  ;;  (set! *metacontinuation* (append mc *metacontinuation*))
  ;; But, to run winders and replace anything in the current frame,
  ;; we proceed frame-by-frame in `mc`.
  (let loop ([rmc (reverse mc)])
    (cond
     [(null? rmc) (proc)]
     [else
      (let ([mf (metacontinuation-frame-clear-cache (car rmc))]
            [rmc (cdr rmc)])
        (cond
         [(eq? (metacontinuation-frame-resume-k mf)
               (metacontinuation-frame-resume-k/no-wind mf))
          ;; No winders in this metacontinuation frame, so take a shortcut
          (set! *metacontinuation* (cons mf *metacontinuation*))
          (loop rmc)]
         [else
          ((metacontinuation-frame-resume-k mf)
           (make-appending (lambda ()
                             ;; resuming appended winders, but we'll keep
                             ;; them in the metacontinuation, instead:
                             (#%$current-winders '())
                             ;; addend frame:
                             (set! *metacontinuation* (cons mf *metacontinuation*))
                             ;; next...
                             (loop rmc))))]))])))

(define (metacontinuation-frame-clear-cache mf)
  (metacontinuation-frame-merge mf #f))

;; Get/cache a converted list of marks for a metacontinuation
(define (metacontinuation-marks mc)
  (cond
   [(null? mc) null]
   [else (let ([mf (car mc)])
           (or (metacontinuation-frame-mark-chain mf)
               (let* ([r (metacontinuation-marks (cdr mc))]
                      [l (cons (make-mark-chain-frame
                                (metacontinuation-frame-tag mf)
                                (mark-stack-to-marks
                                 (metacontinuation-frame-mark-stack mf)))
                               r)])
                 (set-metacontinuation-frame-mark-chain! mf l)
                 l)))]))

;; ----------------------------------------

(define-record continuation-mark-set (mark-chain k))
(define-record mark-stack-frame (prev   ; prev frame
                                 k      ; continuation for this frame
                                 table  ; hamt mapping keys to values
                                 flat)) ; #f or cached list that contains only tables and elem+caches

;; A mark stack is made of marks-stack frames:
(define *mark-stack* #f)

(define-syntax with-continuation-mark
  (syntax-rules ()
    [(_ key val body)
     (call/cm key val (lambda () body))]))

;; Sets a continuation mark.
;; Using `none` as a key ensures that a
;; stack-restoring frame is pushed without
;; adding a key--value mapping.
(define (call/cm key val proc)
  (call/cc
   (lambda (k)
     (if (and *mark-stack*
              (eq? k (mark-stack-frame-k *mark-stack*)))
         (begin
           (unless (eq? key none)
             (set-mark-stack-frame-table! *mark-stack*
                                          (hamt-set (mark-stack-frame-table *mark-stack*)
                                                    key
                                                    val))
             (set-mark-stack-frame-flat! *mark-stack* #f))
           (proc))
         (begin0
          (call/cc
           (lambda (k)
             (set! *mark-stack*
                   (make-mark-stack-frame *mark-stack*
                                          k
                                          (if (eq? key none)
                                              empty-hasheq
                                              (hasheq key val))
                                          #f))
             (proc)))
          (set! *mark-stack* (mark-stack-frame-prev *mark-stack*))
          ;; To support existing a uninterrupted region on resumption of
          ;; a continuation (see `call-with-end-uninterrupted`):
          (when in-uninterrupted?
            (pariah (end-uninterrupted 'cm))))))))

;; For internal use, such as `dynamic-wind` pre thunks:
(define (call/cm/nontail key val proc)
  (set! *mark-stack*
        (make-mark-stack-frame *mark-stack*
                               #f
                               (hasheq key val)
                               #f))
  (proc)
  (set! *mark-stack* (mark-stack-frame-prev *mark-stack*)))

(define (current-mark-chain)
  (get-current-mark-chain *mark-stack* *metacontinuation*))

(define (mark-stack-to-marks mark-stack)
  (let loop ([mark-stack mark-stack])
    (cond
     [(not mark-stack) null]
     [(mark-stack-frame-flat mark-stack) => (lambda (l) l)]
     [else
      (let ([l (cons (mark-stack-frame-table mark-stack)
                     (loop (mark-stack-frame-prev mark-stack)))])
        (set-mark-stack-frame-flat! mark-stack l)
        l)])))

(define-record mark-chain-frame (tag marks))
  
(define (get-current-mark-chain mark-stack mc)
  (cons (make-mark-chain-frame
         #f ; no tag
         (mark-stack-to-marks mark-stack))
        (metacontinuation-marks mc)))

(define (prune-mark-chain-prefix tag mark-chain)
  (cond
   [(eq? tag (mark-chain-frame-tag (elem+cache-strip (car mark-chain))))
    mark-chain]
   [else
    (prune-mark-chain-prefix tag (cdr mark-chain))]))

(define (prune-mark-chain-suffix tag mark-chain)
  (cond
   [(null? mark-chain) null]
   [(eq? tag (mark-chain-frame-tag (elem+cache-strip (car mark-chain))))
    null]
   [else
    (let ([rest-mark-chain (prune-mark-chain-suffix tag (cdr mark-chain))])
      (if (eq? rest-mark-chain (cdr mark-chain))
          mark-chain
          (cons (car mark-chain)
                rest-mark-chain)))]))

;; ----------------------------------------

;; A `elem+cache` can replace a plain table in a "flat" variant of the
;; mark stack within a metacontinuation frame, or in a mark-stack
;; chain for a metacontinuation. The cache is a table that records
;; results found later in the list, which allows
;; `continuation-mark-set-first` to take amortized constant time.
(define-record elem+cache (elem cache))
(define (elem+cache-strip t) (if (elem+cache? t) (elem+cache-elem t) t))

(define call-with-immediate-continuation-mark
  (case-lambda
    [(key proc) (call-with-immediate-continuation-mark key proc #f)]
    [(key proc default-v)
     (unless (and (procedure? proc)
                  (procedure-arity-includes? proc 1))
       (raise-argument-error 'call-with-immediate-continuation-mark "(procedure-arity-includes/c 1)" proc))
     (cond
      [(not *mark-stack*) (proc default-v)]
      [else
       (call/cc (lambda (k)
                  (if (eq? k (mark-stack-frame-k *mark-stack*))
                      (proc (let ([v (hamt-ref (mark-stack-frame-table *mark-stack*)
                                               key
                                               none)])
                              (if (eq? v none)
                                  default-v
                                  v)))
                      (proc default-v))))])]))

(define continuation-mark-set-first
  (case-lambda
    [(marks key) (continuation-mark-set-first marks key #f)]
    [(marks key none-v)
     (continuation-mark-set-first marks key none-v
                                  ;; Treat `break-enabled-key` and `parameterization-key`, specially
                                  ;; so that things like `current-break-parameterization` work without
                                  ;; referencing the root continuation prompt tag
                                  (if (or (eq? key break-enabled-key)
                                          (eq? key parameterization-key))
                                      the-root-continuation-prompt-tag
                                      the-default-continuation-prompt-tag))]
    [(marks key none-v prompt-tag)
     (unless (or (not marks)
                 (continuation-mark-set? marks))
       (raise-argument-error 'continuation-mark-set-first "(or/c continuation-mark-set? #f)" marks))
     (unless (continuation-prompt-tag? prompt-tag)
       (raise-argument-error 'continuation-mark-set-first "continuation-prompt-tag?" prompt-tag))
     (let ([v (marks-search (or (and marks
                                     (continuation-mark-set-mark-chain marks))
                                (current-mark-chain))
                            key
                            ;; elem-stop?:
                            (lambda (mcf)
                              (eq? (mark-chain-frame-tag mcf) prompt-tag))
                            ;; elem-ref:
                            (lambda (mcf key none)
                              ;; Search within a metacontinuation frame
                              (let ([marks (mark-chain-frame-marks mcf)])
                                (marks-search marks
                                              key
                                              ;; elem-stop?:
                                              (lambda (t) #f)
                                              ;; elem-ref:
                                              hamt-ref
                                              ;; fail-k:
                                              (lambda () none)
                                              ;; strip & combine:
                                              (lambda (v) v)
                                              (lambda (v old) v))))
                            ;; fail-k:
                            (lambda () none)
                            ;; strip & combine --- cache results at the metafunction
                            ;; level should depend on the prompt tag, so make the cache
                            ;; value another table level mapping the prompt tag to the value:
                            (lambda (v) (hash-ref v prompt-tag none2))
                            (lambda (v old) (hamt-set (if (eq? old none2) empty-hasheq old) prompt-tag v)))])
       (cond
        [(eq? v none)
         ;; More special treatment of built-in keys
         (cond
          [(eq? key parameterization-key)
           empty-parameterization]
          [(eq? key break-enabled-key)
           (current-engine-init-break-enabled-cell none-v)]
          [else
           none-v])]
        [else v]))]))

;; To make `continuation-mark-set-first` constant-time, if we traverse
;; N elements to get an answer, then cache the answer at N/2 elements.
(define (marks-search elems key elem-stop? elem-ref fail-k
                      strip-cache-result combine-cache-result)
  (let loop ([elems elems] [elems/cache-pos elems] [cache-step? #f])
    (cond
     [(or (null? elems)
          (elem-stop? (elem+cache-strip (car elems))))
      ;; Not found
      (cache-result! elems elems/cache-pos key none combine-cache-result)
      (fail-k)]
     [else
      (let ([t (car elems)])
        (define (check-elem t)
          (let ([v (elem-ref t key none)])
            (cond
             [(eq? v none)
              ;; Not found at this point; keep looking
              (loop (cdr elems)
                    (if cache-step? (cdr elems/cache-pos) elems/cache-pos)
                    (not cache-step?))]
             [else
              ;; Found it
              (cache-result! elems elems/cache-pos key v combine-cache-result)
              v])))
        (cond
         [(elem+cache? t)
          (let ([v (hamt-ref (elem+cache-cache t) key none2)])
            (cond
             [(eq? v none2)
              ;; No mapping in cache, so try the element and continue:
              (check-elem (elem+cache-elem t))]
             [else
              (let ([v (strip-cache-result v)])
                (cond
                 [(eq? v none2)
                  ;; Strip filtered this cache entry away, so try the element:
                  (check-elem (elem+cache-elem t))]
                 [(eq? v none)
                  ;; The cache records that it's not in the rest:
                  (cache-result! elems elems/cache-pos key none combine-cache-result)
                  (fail-k)]
                 [else
                  ;; The cache provides a value from the rest:
                  (cache-result! elems elems/cache-pos key v combine-cache-result)
                  v]))]))]
         [else
          ;; Try the element:
          (check-elem t)]))])))

;; To make `continuation-mark-set-first` constant-time, cache
;; a key--value mapping at a point that's half-way in
(define (cache-result! marks marks/cache-pos key v combine-cache-result)
  (unless (eq? marks marks/cache-pos)
    (let* ([t (car marks/cache-pos)]
           [new-t (if (elem+cache? t)
                      t
                      (make-elem+cache t empty-hasheq))])
      (unless (eq? t new-t)
        (set-car! marks/cache-pos new-t))
      (let ([old (hamt-ref (elem+cache-cache new-t) key none2)])
        (set-elem+cache-cache! new-t (hamt-set (elem+cache-cache new-t)
                                               key
                                               (combine-cache-result v old)))))))

(define continuation-mark-set->list
  (case-lambda
    [(marks key) (continuation-mark-set->list marks key the-default-continuation-prompt-tag)]
    [(marks key prompt-tag)
     (unless (or (not marks)
                 (continuation-mark-set? marks))
       (raise-argument-error 'continuation-mark-set->list "(or/c continuation-mark-set? #f)" marks))
     (unless (continuation-prompt-tag? prompt-tag)
       (raise-argument-error 'continuation-mark-set->list "continuation-prompt-tag?" prompt-tag))
     (let chain-loop ([mark-chain (or (and marks
                                           (continuation-mark-set-mark-chain marks))
                                      (current-mark-chain))])
       (cond
        [(null? mark-chain)
         null]
        [else
         (let* ([mcf (elem+cache-strip (car mark-chain))])
           (cond
            [(eq? (mark-chain-frame-tag mcf) prompt-tag)
             null]
            [else
             (let loop ([marks (mark-chain-frame-marks mcf)])
               (cond
                [(null? marks)
                 (chain-loop (cdr mark-chain))]
                [else
                 (let* ([v (hamt-ref (elem+cache-strip (car marks)) key none)])
                   (if (eq? v none)
                       (loop (cdr marks))
                       (cons v (loop (cdr marks)))))]))]))]))]))

(define continuation-mark-set->list*
  (case-lambda
    [(marks keys) (continuation-mark-set->list* marks keys the-default-continuation-prompt-tag #f)]
    [(marks keys prompt-tag) (continuation-mark-set->list* marks keys prompt-tag #f)]
    [(marks keys prompt-tag none-v)
     (unless (or (not marks)
                 (continuation-mark-set? marks))
       (raise-argument-error 'continuation-mark-set->list "(or/c continuation-mark-set? #f)" marks))
     (unless (list? keys)
       (raise-argument-error 'continuation-mark-set->list "list?" keys))
     (unless (continuation-prompt-tag? prompt-tag)
       (raise-argument-error 'continuation-mark-set->list "continuation-prompt-tag?" prompt-tag))
     (let* ([n (length keys)]
            [tmp (make-vector n)])
       (let chain-loop ([mark-chain (or (and marks
                                             (continuation-mark-set-mark-chain marks))
                                        (current-mark-chain))])
         (cond
          [(null? mark-chain)
           null]
          [else
           (let* ([mcf (elem+cache-strip (car mark-chain))])
             (cond
              [(eq? (mark-chain-frame-tag mcf) prompt-tag)
               null]
              [else
               (let loop ([marks (mark-chain-frame-marks mcf)])
                 (cond
                  [(null? marks)
                   (chain-loop (cdr mark-chain))]
                  [else
                   (let ([t (elem+cache-strip (car marks))])
                     (let key-loop ([keys keys] [i 0] [found? #f])
                       (cond
                        [(null? keys)
                         (if found?
                             (let ([vec (vector-copy tmp)])
                               (cons vec (loop (cdr marks))))
                             (loop (cdr marks)))]
                        [else
                         (let ([v (hamt-ref t (car keys) none)])
                           (cond
                            [(eq? v none)
                             (vector-set! tmp i none-v)
                             (key-loop (cdr keys) (add1 i) found?)]
                            [else
                             (vector-set! tmp i v)
                             (key-loop (cdr keys) (add1 i) #t)]))])))]))]))])))]))

(define current-continuation-marks
  (case-lambda
    [() (current-continuation-marks the-default-continuation-prompt-tag)]
    [(tag)
     (unless (continuation-prompt-tag? tag)
       (raise-argument-error 'current-continuation-marks "continuation-prompt-tag?" tag))
     ;; For now, keep `k` for error context:
     (call/cc
      (lambda (k)
        (make-continuation-mark-set (prune-mark-chain-suffix tag (current-mark-chain)) k)))]))

(define continuation-marks
  (case-lambda
    [(k) (continuation-marks k (default-continuation-prompt-tag))]
    [(k tag)
     (unless (or (not k) (continuation? k))
       (raise-argument-error 'continuation-marks "(or/c continuation? #f)" k))
     (unless (continuation-prompt-tag? tag)
       (raise-argument-error 'continuation-marks "continuation-prompt-tag?" tag))
     (cond
      [(full-continuation? k)
       (make-continuation-mark-set
        (prune-mark-chain-suffix
         tag
         (get-current-mark-chain (full-continuation-mark-stack k)
                                 (full-continuation-mc k)))
        k)]
      [(escape-continuation? k)
       (unless (continuation-prompt-available? (escape-continuation-tag k))
         (raise-arguments-error '|continuation application|
                                "escape continuation not in the current continuation"))
       (make-continuation-mark-set
        (prune-mark-chain-suffix
         tag
         (prune-mark-chain-prefix (escape-continuation-tag k) (current-mark-chain)))
        k)]
      [else
       (make-continuation-mark-set null #f)])]))

(define (mark-stack-append a b)
  (cond
   [(not a) b]
   [(not b) a]
   [else
    (make-mark-stack-frame (mark-stack-append (mark-stack-frame-prev a) b)
                           (mark-stack-frame-k a)
                           (mark-stack-frame-table a)
                           #f)]))

;; ----------------------------------------

;; Wrap `dynamic-wind` for three tasks:

;; 1. set the mark stack on entry and exit to the saved mark stack.
;;    The saved mark stack is confined to the current continuation
;;    frame, so it's ok to use it if the current continuation is later
;;    applied to a different metacontinuation.

;; 2. Start and end uninterrupted regions on the boundaries of
;;    transitions between thunks.

;; 3. Perform a built-in `(parameterize-break #f ...)` around the pre
;;    and post thunks. This break parameterization needs to be built
;;    in so that it's put in place before exiting the uninterrupted region,
;;    but it assumes a particular implementation of break
;;    parameterizations.

(define (dynamic-wind pre thunk post)
  (let ([saved-mark-stack *mark-stack*])
    (define-syntax with-saved-mark-stack/non-break
      (syntax-rules ()
        [(_ who e ...)
         (let ([dest-mark-stack *mark-stack*])
           (set! *mark-stack* saved-mark-stack)
           (call/cm/nontail
            break-enabled-key (make-thread-cell #f #t)
            (lambda ()
              (end-uninterrupted who)
              e ...
              (start-uninterrupted who)))
           (set! *mark-stack* dest-mark-stack))]))
    (start-uninterrupted 'dw)
    (begin0
     (#%dynamic-wind
      (lambda ()
        (with-saved-mark-stack/non-break 'dw-pre
          (pre)))
      (lambda ()
        (end-uninterrupted 'dw-body)
        (begin0
         (thunk)
         (start-uninterrupted 'dw-body)))
      (lambda ()
        (with-saved-mark-stack/non-break 'dw-post
          (post))))
     (end-uninterrupted 'dw))))

;; ----------------------------------------

(define-record saved-metacontinuation (mc exn-state))

(define empty-metacontinuation (make-saved-metacontinuation '() (create-exception-state)))

;; Similar to `call-with-current-continuation` plus
;; applying an old continuation, but does not run winders;
;; this operation makes sense for thread or engine context
;; switches
(define (swap-metacontinuation saved proc)
  (call-in-empty-metacontinuation-frame
   #f
   fail-abort-to-delimit-continuation
   (lambda ()
     (let ([now-saved (make-saved-metacontinuation
                       *metacontinuation*
                       (current-exception-state))])
       (set! *metacontinuation* (saved-metacontinuation-mc saved))
       (current-exception-state (saved-metacontinuation-exn-state saved))
       (proc now-saved)))))

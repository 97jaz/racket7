(library (thread)
  (export)
  (import (chezpart)
          (rename (only (chezscheme)
                        sleep
                        printf)
                  [sleep chez:sleep])
          (rename (core)
                  [core:break-enabled-key break-enabled-key]
                  ;; These are extracted via `#%linklet`:
                  [make-engine core:make-engine]
                  [engine-block core:engine-block]
                  [engine-return core:engine-return]
                  [set-ctl-c-handler! core:set-ctl-c-handler!]
                  [root-continuation-prompt-tag core:root-continuation-prompt-tag]
                  [set-break-enabled-transition-hook! core:set-break-enabled-transition-hook!]))

  (define (exit n)
    (chez:exit n))

  (define (sleep secs)
    (define isecs (inexact->exact (floor secs)))
    (chez:sleep (make-time 'time-duration
                           (inexact->exact (floor (* (- secs isecs) 1e9)))
                           isecs)))

  (define (primitive-table key)
    (case key
      [(|#%engine|) (hash
                     'make-engine core:make-engine
                     'engine-block core:engine-block
                     'engine-return core:engine-return
                     'set-ctl-c-handler! core:set-ctl-c-handler!
                     'root-continuation-prompt-tag core:root-continuation-prompt-tag
                     'break-enabled-key break-enabled-key
                     'set-break-enabled-transition-hook! core:set-break-enabled-transition-hook!
                     'exn:break/non-engine exn:break
                     'exn:break:hang-up/non-engine exn:break:hang-up
                     'exn:break:terminate/non-engine exn:break:terminate
                     'current-process-milliseconds cpu-time)]
      [else #f]))

  ;; Tie knots:
  (define (check-for-break) (1/check-for-break))
  (define (break-enabled) (1/break-enabled))

  (include "compiled/thread.scm")

  (set-engine-exit-handler!
   (lambda (v)
     (|#%app| (|#%app| 1/exit-handler) v)))

  (set-scheduler-lock-callbacks! (lambda () (1/make-semaphore 1))
                                 1/semaphore-wait
                                 1/semaphore-post))

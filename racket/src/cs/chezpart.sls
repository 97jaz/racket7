;; Reexports from `chezscheme` bindings that won't be replaced
;; by Racket-specific implementations.

(library (chezpart)
  (export)
  (import (chezscheme))
  (export (import
           (rename (except (chezscheme)
                           sort vector-sort vector-sort!
                           force delay identifier?
                           memv memq
                           output-port-buffer-mode
                           read-char peek-char
                           make-input-port make-output-port
                           close-input-port close-output-port
                           list? input-port? output-port?
                           open-input-file open-output-file abort
                           current-output-port current-input-port current-directory
                           open-input-string open-output-string get-output-string
                           open-input-output-file
                           with-input-from-file with-output-to-file
                           call-with-input-file call-with-output-file
                           format printf
                           write display newline port-name
                           error
                           date? make-date
                           dynamic-wind
                           call-with-current-continuation
                           make-engine engine-block engine-return
                           current-eval load
                           sleep thread?)
                   [make-parameter chez:make-parameter]
                   [void chez:void]
                   [date-second chez:date-second]
                   [date-minute chez:date-minute]
                   [date-hour chez:date-hour]
                   [date-day chez:date-day]
                   [date-month chez:date-month]
                   [date-year chez:date-year]
                   [date-week-day chez:date-week-day]
                   [date-year-day chez:date-year-day]
                   [string-copy! chez:string-copy!]
                   [apply chez:apply]
                   [procedure? chez:procedure?]
                   [substring chez:substring]
                   [gensym chez:gensym]
                   [symbol->string chez:symbol->string]
                   [random chez:random]
                   [fprintf chez:fprintf]
                   [current-error-port chez:current-error-port]
                   [string->number chez:string->number]
                   [file-exists? chez:file-exists?]
                   [directory-list chez:directory-list]
                   [filter chez:filter]
                   [member chez:member]
                   [raise chez:raise]))))

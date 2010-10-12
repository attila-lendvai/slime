(eval-and-compile
  (require 'slime))

(define-slime-contrib slime-fancy-inspector
  "Fancy inspector for CLOS objects."
  (:authors "Marco Baringer <mb@bese.it> and others")
  (:license "GPL")
  (:slime-dependencies slime-parse slime-presentations)
  (:swank-dependencies swank-fancy-inspector)
  (:on-load
   (add-hook 'slime-edit-definition-hooks 'slime-edit-inspector-part))
  (:on-unload
   (remove-hook 'slime-edit-definition-hooks 'slime-edit-inspector-part)))

(defun slime-inspect-definition ()
  "Inspect definition at point"
  (interactive)
  (slime-inspect (slime-definition-at-point)))

(defun slime-disassemble-definition ()
  "Disassemble definition at point"
  (interactive)
  (slime-eval-describe `(swank:disassemble-form
                         ,(slime-definition-at-point t))))

(defun slime-edit-inspector-part (name &optional where)
  (and (eq major-mode 'slime-inspector-mode)
       (cl-destructuring-bind (&optional property value)
           (slime-inspector-property-at-point)
         (when (eq property 'slime-part-number)
           (let ((location (slime-eval `(swank:find-definition-for-thing
                                         (swank:inspector-nth-part ,value))))
                 (name (format "Inspector part %s" value)))
             (when (and (consp location)
                        (not (eq (car location) :error)))
               (slime-edit-definition-cont
                (list (make-slime-xref :dspec `(,name)
                                       :location location))
                name
                where)))))))

;; redefine the original
(defun* slime-inspect (form &key (reset t) (mode :dwim) thread
                            (package (slime-current-package)))
  "Take an expression FORM and inspect it.

The MODE argument controls behavior:
 - :dwim try to be smart about what was the user's intention
 - :eval evaluate FORM and inspect the result
 - :as-is inspect FORM"
  (interactive
   (multiple-value-bind (presentation start end)
       (slime-presentation-around-point (point))
     (if presentation
         ;; Point is within a presentation, so don't prompt, just
         ;; inspect the presented object; don't play DWIM.
         (cons (slime-presentation-expression presentation)
               '(:mode :eval))
         ;; Not in a presentation, read form from minibuffer.
         (cons (let ((sexp (slime-sexp-at-point)))
                 (if (and sexp
                          ;; an string with alphanumeric chars and hyphens only?
                          (and (string-match "\\([-|*.:0-9a-zA-Z]*\\)" sexp)
                               (= (match-end 0) (length sexp))))
                     sexp
                     (slime-read-from-minibuffer (format (if current-prefix-arg
                                                             "Inspect value (evaluated in %s): "
                                                             "Inspect value (dwim mode in %s): ")
                                                         (slime-current-package))
                                                 sexp)))
               (if current-prefix-arg
                   '(:mode :eval)
                   '(:mode :dwim))))))
  (slime-eval-async `(swank:init-inspector ,form
                                           :reset ,reset
                                           :mode ,mode)
                    (lexical-let ((thread thread)
                                  (package package)
                                  (form form))
                      (lambda (thing)
                        (if thing
                            (slime-open-inspector thing nil nil thread package)
                            (message "Couldn't read anything from '%s' (hint: prefix for debugger with details)" form))))))

(provide 'slime-fancy-inspector)

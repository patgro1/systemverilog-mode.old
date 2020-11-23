;;; systemverilog-mode --- A Systemverilog editing mode. -*- coding: utf-8; lexical-binding: t; -*-

;;; Commentary:
;;; Code:

(defvar systemverilog-mode-syntax-table nil "Syntax table for `systemverilog-mode'.")
(defvar systemverilog-mode-font-lock-keywords nil "Keywords for syntax highlighting for `systemverilog-mode'.")

(setq systemverilog-mode-syntax-table
      (let ( (synTable (make-syntax-table)))
      ;; C style comments
      (modify-syntax-entry ?/ ". 124" synTable)
      (modify-syntax-entry ?* ". 23b" synTable)
      (modify-syntax-entry ?\n ">" synTable)
      (modify-syntax-entry ?_ "w" synTable)
      synTable))

;; TODO: Check the way we are implementing this... there are a lot of keywords... would it be possible to have them all in a seperate file? We also need to
;;       add all keywords from verilog and make a distinction between types and keywords and functions.
(setq systemverilog-mode-font-lock-keywords
      (let* (
             (x-keywords '("accept_on" "export" "ref" "alias" "extends" "rict" "always_comb" "extern" "return" "always_ff" "final" "s_always" "always_latch"
                           "first_match" "s_eventually" "assert" "foreach" "s_nexttime" "assume" "forkjoin" "s_until" "before" "global" "s_until_with"
                           "bind" "iff" "sequence" "bins" "ignore_bins" "shortint" "binsof" "illegal_bins" "implies" "solve" "break"
                           "import" "static" "inside" "chandle" "strong" "checker" "interface" "struct" "class" "intersect" "super"
                           "clocking" "join_any" "sync_accept_on" "const" "join_none" "sync_reject_on" "constraint" "let" "tagged" "context" "local" "this"
                           "continue" "throughout" "cover" "timeprecision" "covergroup" "matches" "timeunit" "coverpoint" "modport" "type"
                           "cross" "new" "typedef" "dist" "nexttime" "union" "do" "null" "unique" "endchecker" "package" "unique0" "endclass" "packed" "until"
                           "endclocking" "priority" "until_with" "endgroup" "program" "untypted" "endinterface" "property" "var" "endpackage" "protected" "virtual"
                           "endprogram" "pure" "void" "endproperty" "rand" "wait_order" "endsequence" "randc" "weak" "enum" "randcase" "wildcard" "eventually"
                           "randsequence" "with" "expect" "reject_on" "within" "input" "output" "inout" "localparam" "for" "generate" "endgenerate"
                           "if" "begin" "else" "end"))
             (x-types '("logic" "shortreal" "bit" "byte" "string" "int" "longint" "wire" "reg"))
             (x-keywords-regexp (regexp-opt x-keywords 'words))
             (x-types-regexp (regexp-opt x-types 'words)))
        `(
          (,x-keywords-regexp . font-lock-keyword-face)
          (,x-types-regexp . font-lock-type-face)
          )))

;;;###autoload
(define-derived-mode systemverilog-mode prog-mode "systemverilog mode"
  "Major mode for editing systemverilog"
  (set-syntax-table systemverilog-mode-syntax-table)
  (setq font-lock-defaults '(systemverilog-mode-font-lock-keywords)))


(provide 'systemverilog-mode)

;;; systemverilog-mode.el ends here

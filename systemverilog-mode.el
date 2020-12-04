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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reserved keywords and standardized words
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst verilog-95-keywords
  '(
    "always" "assign" "begin" "case" "casex" "casez" "deassign" "default" "defparam"
    "disable" "edge" "else" "end" "endcase" "endfunction" "endmodule" "endprimitive"
    "endspecify" "endtable" "endtask" "event" "for" "force" "forever" "fork" "function"
    "if" "ifnone" "initial" "join" "macromodule" "module" "negedge" "parameter" "posedge"
    "primitive" "release" "repeat" "specify" "specparam" "table" "task" "wait" "while"
    )
  "List of all keywords from Verilog 95 specification.")
(defconst verilog-01-keywords
  '(
    "automatic" "incdir" "include" "cell" "pulsestyle_ondetect" "pulsestyle_onevent"
    "config" "endconfig" "liblist" "showcancelled" "endgenerate" "library" "generate"
    "localparam" "use" "noshowcancelled"
    )
  "List of all keywords from Verilog 2001 specification.")
(defconst systemverilog-05-keywords
  '(
    "accept_on" "alias" "always_comb" "always_ff" "always_latch" "assert" "assume"
    "before" "bind" "binsof" "break" "chandle" "checker" "class" "clocking" "const"
    "constraint" "context" "continue" "cover" "covergroup" "cross" "dist" "do"
    "endchecker" "endclass" "endclocking" "endgroup" "endinterface" "endpackage"
    "endprogram" "endproperty" "endsequence" "enum" "eventually" "expect" "export"
    "extends" "extern" "final" "first_match" "foreach" "forkjoin" "global" "iff"
    "ignore_bins" "illegal_bins" "implies" "import" "inside" "interface" "intersect"
    "join_any" "join_none" "let" "local" "matches" "modport" "new" "nexttime" "null"
    "package" "packed" "priority" "program" "property" "protected" "pure" "randcase"
    "ref" "reject_on" "restrict" "return" "s_always" "s_eventually" "s_nexttime"
    "s_until" "s_until_with" "solve" "static" "struct" "super" "sync_accept_on"
    "sync_reject_on" "tagged" "this" "throughout" "timeprecision" "timeunit" "type"
    "typedef" "union" "unique" "unique0" "until" "until_with" "untypted" "virtual"
    "void" "wait_order" "wildcard" "with" "within"
    )
  "List of all keywords from Systemverilog specification.")
(defconst verilog-95-types
  '(
    "highz0" "inout" "input" "integer" "large" "medium" "output" "real" "realtime"
    "reg" "scalared" "small" "supply0" "supply1" "time" "tri" "tri0" "tri1" "triand"
    "trior" "trireg" "vectored" "wand" "wire" "wor"
    )
  "List of all types from Verilog 95 specification.")
(defconst verilog-01-types
  '(
"signed" "unsigned" "genvar"
    )
  "List of all types from Verilog 2001 specification.")
(defconst systemverilog-05-types
  '(
    "bins" "bit" "byte" "coverpoint" "int" "logic" "longint" "rand" "randc"
    "randsequence" "sequence" "shortint" "shortreal" "string" "var"
    )
  "List of all types from Systemverilog specification.")
(defconst verilog-95-builtin-primitives
  '(
    "and" "buf" "bufif0" "bufif1" "cmos" "nand" "nmos" "nor" "not" "notif0" "notif1"
    "or" "pmos" "rcmos" "rnmos" "rpmos" "rtran" "rtranif0" "rtranif1" "tran" "tranif0"
    "tranif1" "xnor" "xor"
    )
  "List of all builtin primitives from Verilog 95 specification.")
(defconst verilog-95-strength
  '(
    "highz1" "pull0" "pull1" "pulldown" "pullup" "strong0" "strong1" "weak0" "weak1"
    )
  "List of all strength words from Verilog 95 specification.")
(defconst systemverilog-05-strength
  '(
    "strong" "weak"
    )
  "List of all strength from Systemverilog specification.")

(defun systemverilog-font-words-init ()
  "Create all reserved keywords/type list from the constants."
  (setq systemverilog-mode-font-lock-keywords
        (let* (
               (x-keywords (append verilog-95-keywords
                                   verilog-01-keywords
                                   systemverilog-05-keywords))
               (x-types (append verilog-95-types
                                verilog-01-types
                                systemverilog-05-types))
               (x-builtins (append verilog-95-builtin-primitives))
               (x-strength (append verilog-95-strength
                                   systemverilog-05-strength))
               (x-keywords-regexp (regexp-opt x-keywords 'words))
               (x-types-regexp (regexp-opt x-types 'words))
               (x-builtin-primitives-regexp (regexp-opt x-builtins 'words))
               (x-strength-regexp (regexp-opt x-strength 'words)))
          `(
            (,x-keywords-regexp . font-lock-keyword-face)
            (,x-types-regexp . font-lock-type-face)
            (,x-builtin-primitives-regexp . font-lock-builtin-face)
            (,x-strength-regexp . font-lock-type-face)
            ;Preprocessor
            ("`define\\|`ifdef\\|`else\\|`endif" . font-lock-preprocessor-face)
            ; Synthesizer directives
            ; TODO: Maybe we could redefine this per tool but for now lets be generic
            ("(\\* .* \\*)" . font-lock-comment-face)
            ; System calls, we could eventually make a list to only highlight systemcalls or not...)
            ; System calls always start with $ and finish at a whitespace or a opening parenthesis
            ("\\$.*\\( \\|(\\)" . font-lock-keyword-face))
          )))

;;;###autoload
(define-derived-mode systemverilog-mode prog-mode "systemverilog mode"
  "Major mode for editing systemverilog"
  (systemverilog-font-words-init)
  (set-syntax-table systemverilog-mode-syntax-table)
  (setq font-lock-defaults '(systemverilog-mode-font-lock-keywords)))


(provide 'systemverilog-mode)

;;; systemverilog-mode.el ends here

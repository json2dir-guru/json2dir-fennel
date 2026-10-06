;; json2dir: create the directory tree a JSON document describes, in the current directory.
;; Implements RFC J2D-1 (https://github.com/kitsunoff/awesome-json2dir/blob/main/spec/rfc-json2dir.md).
;; Pure Fennel on LuaJIT: hand-written JSON parser, file system access through the built-in FFI (libc).
;; Linux x86_64 only (struct stat layout and O_* constants below).

(local ffi (require :ffi))
(local bit (require :bit))
(local {: byte : sub : char : find} string)

(ffi.cdef "
typedef unsigned int mode_t;
typedef long ssize_t;
typedef unsigned long size_t;
struct j2d_stat {
  unsigned long st_dev, st_ino, st_nlink;
  unsigned int st_mode, st_uid, st_gid;
  int __pad0;
  unsigned long st_rdev;
  long st_size, st_blksize, st_blocks;
  long st_times[6];
  long __unused[3];
};
int lstat(const char *path, struct j2d_stat *buf);
int mkdir(const char *path, mode_t mode);
int symlink(const char *target, const char *linkpath);
int unlink(const char *path);
int open(const char *path, int flags, ...);
ssize_t write(int fd, const void *buf, size_t n);
int fchmod(int fd, mode_t mode);
int close(int fd);
mode_t umask(mode_t mask);
char *strerror(int errnum);
")
(local C ffi.C)

;; O_WRONLY|O_CREAT|O_EXCL|O_NOFOLLOW|O_CLOEXEC
(local open-flags (bit.bor 0x1 0x40 0x80 0x20000 0x80000))
(local (S_IFMT S_IFDIR ENOENT) (values 0xF000 0x4000 2))
(local NUL (char 0))

(fn fail [msg] (error {: msg} 0))

(macro check [condition msg]
  "Fail with msg unless condition holds."
  `(when (not ,condition) (fail ,msg)))

(fn syserr [what p]
  (fail (.. p ": " what ": " (ffi.string (C.strerror (ffi.errno))))))

(macro sys! [call what p]
  "Run a libc call that returns 0 on success; report errno otherwise."
  `(when (not= 0 ,call) (syserr ,what ,p)))

;;; §3: strict UTF-8

(local bad-utf8 "input is not valid UTF-8")
(local non-ascii (.. "[" (char 128) "-" (char 255) "]"))

(fn utf8-shape [c]
  "Sequence length and smallest code point for a lead byte."
  (if (<= 0xC2 c 0xDF) (values 2 0x80)
      (<= 0xE0 c 0xEF) (values 3 0x800)
      (<= 0xF0 c 0xF4) (values 4 0x10000)
      (fail bad-utf8)))

(fn check-utf8 [s]
  (let [n (length s)]
    (var i (find s non-ascii 1))
    (while i
      (let [(len min) (utf8-shape (byte s i))]
        (check (<= (+ i len -1) n) bad-utf8)
        (var cp (bit.band (byte s i) (bit.rshift 0x7F len)))
        (for [k 1 (- len 1)]
          (let [d (byte s (+ i k))]
            (check (<= 0x80 d 0xBF) bad-utf8)
            (set cp (+ (* cp 64) (- d 0x80)))))
        (check (and (<= min cp 0x10FFFF) (not (<= 0xD800 cp 0xDFFF))) bad-utf8)
        (set i (find s non-ascii (+ i len)))))))

(fn utf8-encode [cp]
  (let [cont #(+ 0x80 (bit.band (bit.rshift cp $) 0x3F))]
    (if (< cp 0x80) (char cp)
        (< cp 0x800) (char (+ 0xC0 (bit.rshift cp 6)) (cont 0))
        (< cp 0x10000) (char (+ 0xE0 (bit.rshift cp 12)) (cont 6) (cont 0))
        (char (+ 0xF0 (bit.rshift cp 18)) (cont 12) (cont 6) (cont 0)))))

;;; §3, §4: strict JSON parser.
;;; Objects become {:keys [...] :map {...}}, arrays {:items [...]}, strings stay Lua strings.
;;; Numbers, true, false and null are rejected right away (§4.5).

(local escapes {34 "\"" 92 "\\" 47 "/" 98 (char 8) 102 (char 12)
                110 "\n" 114 "\r" 116 "\t"})

(fn parse [s]
  (var pos 1)

  (fn bad [what]
    (fail (.. "input is not valid JSON: " what " at byte " pos)))

  (fn skip-ws []
    (set pos (or (find s "[^ \t\r\n]" pos) (+ (length s) 1))))

  (fn hex4 []
    (let [h (sub s pos (+ pos 3))]
      (check (h:match "^%x%x%x%x$") (bad "bad \\u escape"))
      (set pos (+ pos 4))
      (tonumber h 16)))

  (fn parse-unicode []
    (let [hi (hex4)]
      (if (<= 0xD800 hi 0xDBFF)
          (do
            (check (= (sub s pos (+ pos 1)) "\\u") (bad "unpaired surrogate"))
            (set pos (+ pos 2))
            (let [lo (hex4)]
              (check (<= 0xDC00 lo 0xDFFF) (bad "unpaired surrogate"))
              (+ 0x10000 (* (- hi 0xD800) 0x400) (- lo 0xDC00))))
          (<= 0xDC00 hi 0xDFFF) (bad "unpaired surrogate")
          hi)))

  (fn parse-escape []
    (let [e (byte s pos)]
      (set pos (+ pos 1))
      (case e
        117 (utf8-encode (parse-unicode))
        (where e (. escapes e)) (. escapes e)
        _ (bad "bad escape"))))

  (fn parse-string []
    (set pos (+ pos 1))
    (let [buf []]
      (var done false)
      (while (not done)
        (let [j (or (find s "[\"\\%c]" pos) (bad "unterminated string"))]
          (when (> j pos) (table.insert buf (sub s pos (- j 1))))
          (set pos (+ j 1))
          (case (byte s j)
            34 (set done true)
            92 (table.insert buf (parse-escape))
            127 (table.insert buf (char 127)) ; DEL is matched by %c but allowed in JSON
            _ (bad "control character in string"))))
      (table.concat buf)))

  (fn parse-seq [close item]
    "Parse '[' or '{' ... close, calling item for each element."
    (set pos (+ pos 1))
    (skip-ws)
    (if (= (byte s pos) close)
        (set pos (+ pos 1))
        (do
          (var more true)
          (while more
            (item)
            (skip-ws)
            (case (byte s pos)
              44 (set pos (+ pos 1))
              (where c (= c close)) (do (set pos (+ pos 1)) (set more false))
              _ (bad (.. "expected ',' or '" (char close) "'")))))))

  (var parse-value nil)

  (fn parse-object [depth]
    (let [obj {:keys [] :map {}}]
      (parse-seq 125
        #(do
           (skip-ws)
           (check (= (byte s pos) 34) (bad "expected member name"))
           (let [name (parse-string)]
             (skip-ws)
             (check (= (byte s pos) 58) (bad "expected ':'"))
             (set pos (+ pos 1))
             (let [v (parse-value (+ depth 1))]
               (when (= nil (. obj.map name)) (table.insert obj.keys name))
               (tset obj.map name v))))) ; duplicates: the last occurrence wins (§4.2)
      obj))

  (fn parse-array [depth]
    (let [arr {:items []}]
      (parse-seq 93 #(table.insert arr.items (parse-value (+ depth 1))))
      arr))

  (set parse-value
       (fn [depth]
         (check (<= depth 1000) (bad "nesting too deep"))
         (skip-ws)
         (let [c (byte s pos)]
           (if (= c nil) (bad "unexpected end of input")
               (case c
                 123 (parse-object depth)
                 91 (parse-array depth)
                 34 (parse-string)
                 (where _ (find s "^[-0-9tfn]" pos))
                 (bad "numbers, true, false and null are not allowed")
                 _ (bad "unexpected character"))))))

  (when (= (sub s 1 3) (.. (char 239) (char 187) (char 191))) ; optional BOM
    (set pos 4))
  (let [v (parse-value 0)]
    (skip-ws)
    (check (> pos (length s)) (bad "trailing data"))
    v))

;;; §4: validate the whole document before touching the file system

(fn bad-name? [name]
  (or (= name "") (= name ".") (= name "..")
      (find name "/" 1 true) (find name NUL 1 true)))

(fn validate [v path]
  (case v
    (where _ (= (type v) :string)) nil
    {: items}
    (case items
      (where [kind body] (= 2 (length items)) (= :string (type kind)) (= :string (type body)))
      (case kind
        :link (check (not (find body NUL 1 true)) (.. path ": a link target cannot contain NUL"))
        :script nil
        _ (fail (.. path ": unknown array kind " kind)))
      _ (fail (.. path ": an array must be [\"link\", target] or [\"script\", content]")))
    {: keys : map}
    (each [_ name (ipairs keys)]
      (let [child (if (= path ".") name (.. path "/" name))]
        (check (not (bad-name? name)) (.. child ": invalid name"))
        (validate (. map name) child)))))

;;; §5: file system, through libc

(local st (ffi.new "struct j2d_stat"))

(fn lstat-kind [p]
  "nil (missing), :dir or :other; never follows symlinks."
  (if (= 0 (C.lstat p st))
      (if (= S_IFDIR (bit.band st.st_mode S_IFMT)) :dir :other)
      (= ENOENT (ffi.errno)) nil
      (syserr "lstat" p)))

(fn remove-existing [p kind]
  (case kind
    :dir (fail (.. p ": a directory is in the way"))
    :other (sys! (C.unlink p) "unlink" p)))

(local mask (let [m (C.umask 0)] (C.umask m) m))

(fn write-file [p content executable?]
  ;; O_CREAT|O_EXCL|O_NOFOLLOW: never writes through an entry that appeared after remove-existing
  (let [fd (C.open p open-flags (ffi.cast "mode_t" 438)) ; 0666
        buf (ffi.cast "const char *" content)
        n (length content)]
    (when (< fd 0) (syserr "open" p))
    (var off 0)
    (while (< off n)
      (let [w (C.write fd (+ buf off) (- n off))]
        (when (< w 0) (C.close fd) (syserr "write" p))
        (set off (+ off (tonumber w)))))
    (when executable?
      (let [mode (bit.bor (bit.band 438 (bit.bnot mask)) 73)] ; (0666 & ~umask) | 0111
        (when (not= 0 (C.fchmod fd mode)) (C.close fd) (syserr "fchmod" p))))
    (sys! (C.close fd) "close" p)))

(fn apply [dir {: keys : map}]
  (let [names (icollect [_ k (ipairs keys)] k)]
    (table.sort names) ; LuaJIT compares strings bytewise: ascending UTF-8 byte order
    (each [_ name (ipairs names)]
      (let [p (.. dir "/" name)
            kind (lstat-kind p)]
        (case (. map name)
          (where content (= (type content) :string))
          (do (remove-existing p kind)
              (write-file p content false))
          {:items [:link target]}
          (do (remove-existing p kind)
              (sys! (C.symlink target p) "symlink" p))
          {:items [:script content]}
          (do (remove-existing p kind)
              (write-file p content true))
          subtree
          (do (when (not= kind :dir)
                (when kind (sys! (C.unlink p) "unlink" p))
                (sys! (C.mkdir p 511) "mkdir" p)) ; 0777
              (apply p subtree)))))))

;;; §7: command line

(fn main [args]
  (if (> (length args) 0)
      (do (io.stderr:write "usage: json2dir < document.json\n") 2)
      (case (pcall #(let [input (or (io.stdin:read "*a") "")]
                      (check-utf8 input)
                      (let [doc (parse input)]
                        (check (and (= (type doc) :table) doc.keys)
                               "the root of the document must be an object")
                        (validate doc ".")
                        (apply "." doc))))
        true 0
        (false err) (do (io.stderr:write
                          (.. "json2dir: " (if (= (type err) :table) err.msg (tostring err)) "\n"))
                        1))))

(os.exit (main (or arg [])))

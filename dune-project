(lang dune 2.2)
(using coq 0.1)
(name mechkat)

(generate_opam_files true)

(package 
 (name mechkat)
 (depends 
  (coq (>= 8.15))
 )
 (synopsis "Mechanization of NetKAT in Coq")
 (description  "Mechanization of NetKAT in Coq")
 (maintainers   "jtsarracino@gmail.com")
 (authors      "John Sarracino" "Karuna Grewal" "Ryan Doenges")
 (homepage     "https://github.com/jsarracino/mech-kat")
 (bug_reports  "https://github.com/jsarracino/mech-kat")
)

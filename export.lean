/- This file exports file and line information for use in LaTeX references. -/

import all

import tactic.core

open tactic

meta structure decl_info :=
(name : name)
(filename : string)
(line : ℕ)

meta def process_decl (e : environment) (d : declaration) : tactic (option decl_info) :=
do
  ff ← d.in_current_file | return none,
  let decl_name := d.to_name,
  -- allow linking to private names
  let (internal, short_name) := if (`_private).is_prefix_of decl_name
                    then (ff, decl_name.update_prefix decl_name.get_prefix.get_prefix)
                    else (decl_name.is_internal ∨ d.is_auto_generated e, decl_name),
  ff ← pure internal | return none,
  some filename ← return (e.decl_olean decl_name) | return none,
  let parts := filename.split (= '/'),
  some ⟨line, _⟩ ← return (e.decl_pos decl_name) | return none,
  return $ some ⟨short_name, filename, line⟩

/-- Split a path into an optional parent component and filename -/
def path_split (path : string) : option string × string :=
match (path.split (= '/')).reverse with
| [] := (none, "/")
| [a] := (none, a)
| (a :: as) := ("/".intercalate as.reverse, a)
end

/-- Split a lean path into a project/parent pair -/
def project_file_split (path : string) : io (option string × string) :=
do
  (parent, some rest, tt) ← (io.iterate (some path, (none : option string), ff) $ λ state, do {
    (some p, old_rest, ff) ← pure state | pure none,
    (parent, rest) ← pure (path_split p),
    let rest := (match old_rest with
    | some r := rest ++ "/" ++ r
    | none := rest
    end),
    some parent ← pure parent | pure (some (parent, old_rest, tt)),
    found ← io.fs.file_exists (parent ++ "/leanpkg.toml"),
    if !found && "/lib/lean/library".is_suffix_of p then
      pure (some (none, some rest, tt))
    else
      pure (some (parent, some rest, found)) }),
  pure (parent, rest)

/-- A version of `list.map` for `io` that does not consume the whole stack -/
def list.mmap_io {α β : Type*} (f : α → io β) (l : list α) : io (list β) :=
do
  (_, bs) ← io.iterate (l, ([] : list β)) (λ state, do {
    (a :: as, bs) ← pure state | return none,
    b ← f a,
    return (some (as, b :: bs))
  }),
  pure bs

/-- A version of `list.mfoldl` for `io` that does not consume the whole stack -/
def list.mfoldl_io {s α : Type*} (f : s → α → io s) (x : s) (l : list α) : io s :=
prod.snd <$> io.iterate (l, x) (λ state, do {
  (a :: as, x) ← pure state | return none,
  x' ← f x a,
  return (some (as, x'))
})

def project_map (α : Type*) := rbmap (with_bot string) α

meta def main : io unit :=
do
  let project_urls : project_map string := rbmap.from_list
  [ (some "lean-ga", "https://github.com/pygae/lean-ga")
  , (some "mathlib", "https://github.com/leanprover-community/mathlib")
   --, (⊥, "https://github.com/leanprover-community/lean")
    ],
  let project_shas : project_map string := rbmap.from_list [
    (⊥, lean.githash)
  ],

  infos ← io.run_tactic $ do
  { e ← get_env,
    e.get_decls.mmap (process_decl e) },
  io.put_str_ln "\\makeatletter",
  io.put_str_ln "",
  io.put_str_ln "\\newcommand\\@leandef[4]{%",
  io.put_str_ln "\\@namedef{lean-ref-proj@#1}{#2}%",
  io.put_str_ln "\\@namedef{lean-ref-file@#1}{#3}%",
  io.put_str_ln "\\@namedef{lean-ref-line@#1}{#4}%",
  io.put_str_ln "}",
  io.put_str_ln "",
  project_shas ← infos.mfoldl_io (λ (shas : project_map string) (di : option decl_info), do
  { some di ← pure di | pure shas,
    (some p_dir, file) ← project_file_split di.filename | pure shas,
    (_, p) ← pure (path_split p_dir),
    -- skip projects without urls
    some url ← pure (project_urls.find p) | pure shas,
    io.put_str_ln (format!"\\@leandef{{{di.name}}}{{{p}}}{{{file}}}{{{di.line}}}").to_string,
    none ← pure (shas.find p) | pure shas,
    sha ← io.cmd { cmd := "git", args := ["rev-parse", "HEAD"], cwd := p_dir },
    let sha := sha.pop_back,  -- remove trailing newline
    pure (shas.insert p sha) })
    project_shas,

  io.put_str_ln "",
  project_shas.to_list.mmap_io (λ sha : option string × string, do
    some url ← pure (project_urls.find sha.1) | pure (),
    some p ← pure sha.1 | pure (),
    io.put_str_ln (format!"\\@namedef{{lean-ref-url@{p}}}{{{url}}}").to_string,
    io.put_str_ln (format!"\\@namedef{{lean-ref-sha@{p}}}{{{sha.2}}}").to_string),

  io.put_str_ln "",
  io.put_str_ln "\\makeatother"

/- Copyright 2025 François G. Dorais -/

import HTPILib.HTPIDefs
namespace HTPI

scoped syntax "truth_table" colGt "["term,*"]" : tactic

macro_rules
  | `(tactic| truth_table []) =>
    `(tactic| simp [*])
  | `(tactic| truth_table [$p]) =>
    `(tactic| cases Classical.prop_complete $p <;> truth_table [])
  | `(tactic| truth_table [$p, $ps,*]) =>
    `(tactic| cases Classical.prop_complete $p <;> truth_table [$ps,*])

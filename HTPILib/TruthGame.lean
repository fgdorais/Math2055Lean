/- Copyright 2025 François G. Dorais -/

import HTPILib.HTPIDefs
namespace HTPI

inductive TruthGame : Bool → Prop → Type
| is_true : TruthGame true True
| neg_false : TruthGame false P → TruthGame true (¬ P)
| or_left : TruthGame true P → TruthGame true (P ∨ Q)
| or_right : TruthGame true Q → TruthGame true (P ∨ Q)
| and_cases : TruthGame true P → TruthGame true Q → TruthGame true (P ∧ Q)
| is_false : TruthGame false False
| neg_true : TruthGame true P → TruthGame false (¬ P)
| or_cases : TruthGame false P → TruthGame false Q → TruthGame false (P ∨ Q)
| and_left : TruthGame false P → TruthGame false (P ∧ Q)
| and_right : TruthGame false Q → TruthGame false (P ∧ Q)

namespace TruthGame

mutual

theorem of_true : TruthGame true P → P
  | is_true => trivial
  | neg_false h => of_false h
  | or_left h => Or.inl (of_true h)
  | or_right h => Or.inr (of_true h)
  | and_cases hp hq => And.intro (of_true hp) (of_true hq)

theorem of_false : TruthGame false P → ¬ P
  | is_false => id
  | neg_true h => not_not_intro <| of_true h
  | and_left h => fun ⟨hp, _⟩ => of_false h hp
  | and_right h => fun ⟨_, hq⟩ => of_false h hq
  | or_cases hp hq => fun | .inl h => of_false hp h | .inr h => of_false hq h

end

syntax "by_game" colGt term,+ : tactic

macro_rules
| `(tactic| by_game $p) =>
  `(tactic| cases Classical.prop_complete $p <;> refine TruthGame.of_true ?_)
| `(tactic| by_game $p, $ps,*) =>
  `(tactic| cases Classical.prop_complete $p <;> by_game $ps,*)

macro "go_left" : tactic => `(tactic| first | refine TruthGame.or_left ?_ | refine TruthGame.and_left ?_ | fail "invalid play")
macro "go_right" : tactic => `(tactic| first | refine TruthGame.or_right ?_ | refine TruthGame.and_right ?_ | fail "invalid play")
macro "do_cases" : tactic => `(tactic| first | refine TruthGame.and_cases ?_ ?_ | refine TruthGame.or_cases ?_ ?_ | fail "invalid play")
macro "do_swap" : tactic => `(tactic| first | refine TruthGame.neg_true ?_ | refine TruthGame.neg_false ?_ | fail "invalid play")
macro "win!" : tactic => `(tactic | subst_vars <;> first | exact TruthGame.is_true | exact TruthGame.is_false | fail "invalid play")

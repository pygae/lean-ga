/-
This file will be changed drastically all the time, it's only for reproduce the problem as 
a [minimal working example](https://leanprover-community.github.io/mwe.html) to ask on 
[Zulip](http://leanprover.zulipchat.com/)
-/

import ring_theory.algebra
import tactic

example (A : Type) [add_comm_group A] (a b c : A) :
a = -b - c + (a + b + c) :=
begin
  abel,
end

example (A : Type) [ring A] (a b c : A) :
a = -b - c + (a + b + c) :=
begin
  ring,
  /-
  ring failed to simplify
  state:
  A : Type,
  _inst_1 : ring A,
  a b c : A
  ⊢ a = -b - c + (a + b + c)
  -/
end
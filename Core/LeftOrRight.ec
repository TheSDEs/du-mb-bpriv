(* ---------------------------------------------------------------------- *)
(* Modules parameterized by left or right choice. *)

module type LorR = {
  proc* l_or_r() : bool
}.

module Left : LorR = {
  proc l_or_r() : bool = { return true; }
}.

module Right : LorR = {
  proc l_or_r() : bool = { return false; }
}.

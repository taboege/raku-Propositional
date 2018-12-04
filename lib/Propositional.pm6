unit module Propositional;

role Formula is export {
    method Str { … }

    method variables { … }
    method compile { -> \α { self.eval: α } }
    method eval (Set \α) { … }

    method truth-table {
        my &eval = self.compile;
        gather for self.variables.combinations».Set -> \α {
            take (α) => eval α;
        }
    }

    multi method satisfiable   { so  any self.truth-table».value }
    multi method tautology     { so  all self.truth-table».value }
    multi method contradiction { not self.satisfiable            }
}

role Variable does Formula is export {
    method Str { … }

    method Propositional::AST { self }
    method Propositional::CNF { self }
    method variables          { set self }

    method compile { -> \α { α{self}:exists } }
    method eval (Set \α) { α{self}:exists }
}

sub truth-table (Formula:D \φ) is export { φ.truth-table }

# FIXME: https://github.com/rakudo/rakudo/issues/2147
# TODO: This is tighter than the infixes.
#multi prefix:<¬> (Bool $p)          is export                 { not $p        }
#multi  infix:<∧> (Bool $p, Bool $q) is export                 {     $p and $q }
#multi  infix:<∨> (Bool $p, Bool $q) is export                 {     $p or  $q }
#multi  infix:<⇒> (Bool $p, Bool $q) is export is assoc<right> { not $p or  $q }
#multi  infix:<⇔> (Bool $p, Bool $q) is export                 {     $p === $q }
sub bnot   (Bool $p)          is export                 { not $p }
sub band   (Bool $p, Bool $q) is export                 {     $p and $q }
sub bor    (Bool $p, Bool $q) is export                 {     $p or  $q }
sub bimply (Bool $p, Bool $q) is export is assoc<right> { not $p or  $q }
sub bequiv (Bool $p, Bool $q) is export                 {     $p === $q }

use OO::Monitors;

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

role Variable does Formula {
    method Str { … }

    method Propositional::AST { self }
    method Propositional::CNF { self }
    method variables          { set self }

    method compile { -> \α { α{self}:exists } }
    method eval (Set \α) { α{self}:exists }
}

sub truth-table (Formula:D \φ) is export { φ.truth-table }

#|« Lookup structure to serialize and deserialize variables.

This structure is required to convert a Formula into C<DIMACS cnf>
format which is the input accepted by SAT solvers. You can make a
standalone Variable::Lookup structure for your variables or mix
this role into your Variable class.

To implement this role correctly, variables must be uniquely
numbered by integers starting from 1 and form a continuous
range 1..(# of vars). Only then it can be expected that #SAT
and AllSAT solvers work on the problem you intended to pose.
»
role Variable::Lookup {
    #| Return a unique integer identifying the variable.
    multi method get-int (Variable: --> Int)   { self.get-index(self) }
    multi method get-int (Variable $v --> Int) { … }
    #| Return a variable object from its integer.
    multi method get-var (Int $n --> Variable)   { … }
}

# Needs to be a monitor because we are non-atomically updating a hash
# which may be shared among threads (many SAT instances being created
# in an all junction, for example).
#|« Default implementation of a Variable::Lookup: caches all variables
it is queried about and returns consistent, unique numbers for each.

This is what you will want to use most of the time, unless your variables
permit a specialized, more efficient lookup.
»
monitor Variable::Cache does Variable::Lookup {
    has %!to-int;
    has @!to-var;

    multi method get-int (Variable $v --> Int) {
        if %!to-int{$v}:exists {
            return %!to-int{$v};
        }
        push @!to-var, $v;
        %!to-int{$v} = +@!to-var
    }

    multi method get-var (Int $n --> Variable) {
        @!to-var[$n - 1]
    }
}

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

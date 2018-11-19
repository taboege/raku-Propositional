use Test;

use Propositional;
# Can't include this, R#2147
#use Propositional::AST;

# Quick and dirty variable space.
# We convert the pairs to something else behind the scenes
# because pairs are special-cased in a bunch of core Perl 6
# structures, like Set() and generally operators that can
# take adverbs.
class Var does Propositional::Variable {
    has $.name;

    multi method new (Pair:D $p) {
        self.new: :name($p.key)
    }

    method Str  { $!name }
    method gist { $!name }
}

multi prefix:<`> (Pair $p) is export {
    state %VARS;
    %VARS{$p.key} //= Var.new($p)
}

multi infix:<eqv> (Formula \φ, Formula \ψ) is export {
    set(φ.truth-table) eqv set(ψ.truth-table)
}

# Return a Seq of operator symbol strings, one for each path down the AST.
multi sub operator-traces (\φ) {
    multi sub operator-traces (Propositional::Variable \φ,      $so-far is copy) {
        take $so-far
    }
    # FIXME: see above for why we can't use Propositional::AST
    #multi sub operator-traces (Propositional::AST::Operator \φ, $so-far is copy) {
    multi sub operator-traces (\φ where { .^name ~~ /'Propositional::AST::Operator'/ }, $so-far is copy) {
        $so-far ~= φ.sym;
        operator-traces $_, $so-far for φ.operands
    }

    gather operator-traces φ, ''
}

sub ok-normalform(\φ, \φ-nf, $path-pattern) {
    subtest (~φ) => {
        like operator-traces(φ-nf).all, $path-pattern, "correct syntax";
        ok φ eqv φ-nf, "truth tables match";
    }
}

sub ok-NNF (\φ) is export {
    ok-normalform φ, φ.NNF, rx/^ <-[¬]>* '¬'? $/
}

sub ok-CNF (\φ) is export {
    ok-normalform φ, φ.CNF, rx/^ '∧'? '∨'? '¬'? $/
}

sub ok-DNF (\φ) is export {
    ok-normalform φ, φ.DNF, rx/^ '∨'? '∧'? '¬'? $/
}

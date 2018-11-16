use Propositional;

unit module Propositional::AST;

role Operator[$sym, &impl] does Propositional::Formula {
    has $.sym = $sym;
    has @.operands;
    has $!variables;

#    method Propositional::CNF {
#        self.rewrite() # NNF
#            .rewrite() # CNF
#        # Convert to CNF object
#    }

    method squish {
        return self unless &impl.arity == 2;
        @!operands».squish;
        my @new-operands;
        for @!operands {
            @new-operands.push: quietly .?sym eq $!sym ?? |.operands !! $_;
        }
        @!operands = @new-operands;
        self
    }

    method variables {
        # Maintain a cache.
        # TODO: This cache should be evicted sometime too.
        # In a running program, you will have a directed acyclic
        # graph of active formulas. Only the roots in this graph
        # and sporadically other formulas that the user has a
        # reference to should keep the cache.
        $!variables //= [∪] @!operands».variables
    }

    #| Return an S-expression of the formula
    method Str { "($!sym {@!operands})" }
    method compile { -> \α { self.eval: α } }
    method eval (Set \α) { [[&impl]] @!operands».eval(α) }
}

class Operator::Not   does Operator["¬", &bnot]   { }
class Operator::And   does Operator["∧", &band]   { }
class Operator::Or    does Operator["∨", &bor]    { }
# FIXME: This has the wrong associativity.
class Operator::Imply does Operator["⇒", &bimply] { }
class Operator::Equiv does Operator["⇔", &bequiv] { }

# TODO: This is tighter than the infixes.
multi prefix:<¬> (Formula \φ) is export {
    Operator::Not.new: :operands(φ)
        andthen .squish
}

multi infix:<∧> (Formula \φ, Formula \ψ) is export {
    Operator::And.new: :operands(φ, ψ)
        andthen .squish
}

multi infix:<∨> (Formula \φ, Formula \ψ) is export {
    Operator::Or.new: :operands(φ, ψ)
        andthen .squish
}

multi infix:<⇒> (Formula \φ, Formula \ψ) is export {
    Operator::Imply.new: :operands(φ, ψ)
        andthen .squish
}

multi infix:<⇔> (Formula \φ, Formula \ψ) is export {
    Operator::Equiv.new: :operands(φ, ψ)
        andthen .squish
}

use Propositional;

unit module Propositional::AST;

#
# Forwards and operators because the Operator role already needs them.
#

class RewriteCapture { … }

# Mnemonic: cap-ture
multi prefix:<^> (Pair $p --> RewriteCapture) is export {
    new RewriteCapture: :name($p.key), :matcher($p.value)
}

class Operator::Not   { … }
class Operator::And   { … }
class Operator::Or    { … }
class Operator::Imply { … }
class Operator::Equiv { … }

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

role Rewritable {
    method rewrite (*@rules, :ce(:$times)? is copy = Inf) {
        my $cur = self;
        loop {
            my $*REWRITTEN = 0;
            $cur .= rewrite-once: $_ for @rules;
            last if --$times ≤ 0 or not $*REWRITTEN or $cur !~~ Rewritable;
        }
        $cur
    }

    method rewrite-once ($rule (:key($pattern), :value(&replacement))) { … }
}

# FIXME: A role for AST-specific variable functionality is tempting but
# it shouldn't exist because the AST type will survive conversions to
# non-AST representations. Maybe the best solution is to add the variable
# part into Operator.rewrite-once. It has to examine its operands more
# closely then, and re-dispatch rewrite-once for Operator operands, and
# special-case Variable operands.
role Variable does Propositional::Variable does Rewritable {
    method rewrite-once ($rule (:key($pattern), :value(&replacement))) {
        my %*REWRITE-CAPTURES;
        if self ~~ $pattern {
            try $*REWRITTEN++;
            return replacement |%*REWRITE-CAPTURES;
        }
        self
    }
}

role Operator[$sym, &impl] does Propositional::Formula does Rewritable {
    has $.sym = $sym;
    has @.operands;
    has $!variables;

    method NNF {
        self.rewrite(
            (  ^:p ⇔ ^:q)  => { ($:p ⇒  $:q) ∧ ($:q ⇒ $:p) },
            (  ^:p ⇒ ^:q)  => { ¬$:p ∨  $:q },
            (¬(^:p ∨ ^:q)) => { ¬$:p ∧ ¬$:q },
            (¬(^:p ∧ ^:q)) => { ¬$:p ∨ ¬$:q },
            (¬¬^:p)        => {  $:p        },
        )
        andthen .squish
    }

    method CNF {
        # TODO: Add a truth-table-based candidate for situations with few variables.
        # Then just add ¬ in front of assignments evaluating to False.
        # TODO: Tseitin transformation allows to obtain a CNF formula which
        # is not equivalent but equisatisfiable and with guaranteed polynomial-
        # bounded increase in size.
        self.NNF.rewrite(
            (^:p ∨ (^:q ∧ ^:r)) => { ($:p ∨ $:q) ∧ ($:p ∨ $:r) },
            ((^:q ∧ ^:r) ∨ ^:p) => { ($:p ∨ $:q) ∧ ($:p ∨ $:r) },
        )
        andthen .squish
    }

    method DNF {
        self.NNF.rewrite(
            (^:p ∧ (^:q ∨ ^:r)) => { ($:p ∧ $:q) ∨ ($:p ∧ $:r) },
            ((^:q ∨ ^:r) ∧ ^:p) => { ($:p ∧ $:q) ∨ ($:p ∧ $:r) },
        )
        andthen .squish
    }

#    method Propositional::CNF {
#        my $cnf = self.CNF;
#        new Propositional::CNF: :clauses(
#            new Propositional::CNF::Clause(
#                vars => ...
#                nars => ...
#            )
#            for $cnf.operands
#        )
#    }

    method rewrite-once ($rule (:key($pattern), :value(&replacement))) {
        my %*REWRITE-CAPTURES;
        if self !~~ $pattern {
            my @operands = do .?rewrite-once($rule) // $_ for @!operands;
            # Do not create a new Operator unless necessary.
            return all(@operands Z=== @!operands) ??
                self !!
                new self: :@operands;
        }
        try $*REWRITTEN++;
        replacement |%*REWRITE-CAPTURES
    }

    multi method ACCEPTS (Operator:D: Operator:D $lhs) {
        $lhs.sym eqv $!sym and
        # XXX: Will this lead to trouble with squish?
        # E.g. ^:p ∧ ^:q will not match `:p ∧ `:q ∧ `:r
        $lhs.operands == @!operands and
        all($lhs.operands Z~~ @!operands)
    }

    method squish {
        @!operands».squish;
        return self unless &impl.arity == 2;
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
    method eval (Set \α) { [[&impl]] @!operands».eval(α) }
}

class Operator::Not   does Operator["¬", &bnot]   { }
class Operator::And   does Operator["∧", &band]   { }
class Operator::Or    does Operator["∨", &bor]    { }
# FIXME: This has the wrong associativity.
class Operator::Imply does Operator["⇒", &bimply] { }
class Operator::Equiv does Operator["⇔", &bequiv] { }

class RewriteCapture does Propositional::Variable does Rewritable {
    has $.name;
    has $.matcher;

    method rewrite-once ($rule (:key($pattern), :value(&replacement))) {
        my %*REWRITE-CAPTURES;
        if self ~~ $pattern {
            try $*REWRITTEN++;
            return replacement |%*REWRITE-CAPTURES;
        }
        self
    }

    multi method ACCEPTS (RewriteCapture:D: $lhs) {
        my $res = $lhs ~~ $!matcher;
        # TODO: Maybe throw if :exists?
        try %*REWRITE-CAPTURES{$!name} = $lhs if $res;
        $res
    }

    method Str { "^$!name" }
}

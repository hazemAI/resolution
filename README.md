# resolution


● This assignment will involve working in groups of two members.

● Write Python code to apply resolution procedure in predicate logic.

● Upload your code to GitHub and then add the link to the discussion sheet to check for plagiarism.

● It should contain the functions that cover the following steps (resolution steps):

1. Eliminate implication
2. Move negation inward (Demorgan Law)
3. Remove double-not.
4. Standardize variable scope.
5. The prenex form (obtained by moving all quantifiers to the left of the
formula.)
6. Skolemization for existential quantifiers.
7. Eliminate universal quantifiers.
8. Convert to conjunctive normal form
9. Turn conjunctions into clauses in a set, and rename variables so that no
clause shares the same variable name.
10.Rename variables in clauses so that each clause has a unique variable
name.

`
from nltk.inference.resolution import ResolutionProverCommand
from nltk.sem.logic import *
from nltk.sem import logic

def implications_elemination(expr):
    if isinstance(expr, ImpExpression):
        return implications_elemination(
            OrExpression(-expr.first, expr.second)
        )
    elif isinstance(expr, (AllExpression, ExistsExpression)):
        return type(expr)(
            expr.variable,
            implications_elemination(expr.term)
        )
    elif isinstance(expr, (AndExpression, OrExpression)):
        return type(expr)(
            implications_elemination(expr.first),
            implications_elemination(expr.second)
        )
    elif isinstance(expr, NegatedExpression):
        return NegatedExpression(
            implications_elemination(expr.term)
        )
    else:
        return expr


def demorgan(expr):
    if isinstance(expr, NegatedExpression):
        if isinstance(expr.term, AndExpression):
            return OrExpression(
                demorgan(
                    NegatedExpression(expr.term.first)
                ),
                demorgan(
                    NegatedExpression(expr.term.second)
                )
            )
        elif isinstance(expr.term, OrExpression):
            return AndExpression(
                demorgan(
                    NegatedExpression(expr.term.first)
                ),
                demorgan(
                    NegatedExpression(expr.term.second)
                )
            )
        elif isinstance(expr.term, AllExpression):
            return ExistsExpression(
                expr.term.variable,
                demorgan(
                    NegatedExpression(expr.term.term)
                )
            )
        elif isinstance(expr.term, ExistsExpression):
            return AllExpression(
                expr.term.variable,
                demorgan(
                    NegatedExpression(expr.term.term)
                )
            )
        else:
            return expr
    elif isinstance(expr, (AndExpression, OrExpression)):
        return type(expr)(
            demorgan(expr.first),
            demorgan(expr.second)
        )
    elif isinstance(expr, (AllExpression, ExistsExpression)):
        return type(expr)(
            expr.variable,
            demorgan(expr.term)
        )
    else:
        return expr


def remove_double_negation(expr):
    if isinstance(expr, NegatedExpression):
        if isinstance(expr.term, NegatedExpression):
            return remove_double_negation(expr.term.term)
        else:
            return NegatedExpression(remove_double_negation(expr.term))
    elif isinstance(expr, (AndExpression, OrExpression)):
        return type(expr)(
            remove_double_negation(expr.first),
            remove_double_negation(expr.second)
        )
    elif isinstance(expr, (AllExpression, ExistsExpression)):
        return type(expr)(
            expr.variable,
            remove_double_negation(expr.term)
        )
    else:
        return expr

def variable_standardization(expr, variable_set=None):
    if variable_set is None:
        variable_set = set()
    if isinstance(expr, AllExpression):
        new_var = expr.variable
        while new_var in variable_set:
            ascii_value = (ord(new_var.name) - 96) % 26 + 97
            new_var = Variable(chr(ascii_value))
        variable_set.add(new_var)
        if new_var != expr.variable:
            expr = expr.alpha_convert(new_var)
        return AllExpression(
            expr.variable,
            variable_standardization(expr.term, variable_set)
        )
    elif isinstance(expr, ExistsExpression):
        new_var = expr.variable
        while new_var in variable_set:
            ascii_value = (ord(new_var.name) - 96) % 26 + 97
            new_var = Variable(chr(ascii_value))
        variable_set.add(new_var)
        if new_var != expr.variable:
            expr = expr.alpha_convert(new_var)
        return ExistsExpression(
            expr.variable,
            variable_standardization(expr.term, variable_set)
        )
    elif isinstance(expr, NegatedExpression):
        return NegatedExpression(
            variable_standardization(expr.term, variable_set)
        )
    elif isinstance(expr, (AndExpression, OrExpression)):
        return type(expr)(
            variable_standardization(expr.first, variable_set),
            variable_standardization(expr.second, variable_set)
        )
    else:
        return expr


def to_pnf(expr):
    def get_quantifiers(expr):
        if isinstance(expr, AllExpression):
            term = get_quantifiers(expr.term)
            return term[0], term[1] + [AllExpression], term[2] + [expr.variable]
        elif isinstance(expr, ExistsExpression):
            term = get_quantifiers(expr.term)
            return term[0], term[1] + [ExistsExpression], term[2] + [expr.variable]
        elif isinstance(expr, NegatedExpression):
            term = get_quantifiers(expr.term)
            return NegatedExpression(term[0]), term[1], term[2]
        elif isinstance(expr, (AndExpression, OrExpression)):
            first = get_quantifiers(expr.first)
            second = get_quantifiers(expr.second)
            return type(expr)(first[0], second[0]), first[1] + second[1], first[2] + second[2]
        else:
            return expr, [], []

    expr, quantifiers, variables = get_quantifiers(expr)
    for quantifier, variable in sorted(zip(quantifiers, variables), key=lambda x: 1 if x[0] == AllExpression else 0):
        expr = quantifier(variable, expr)
    return expr


def skolemization(expr, variable_set=None):
    if variable_set is None:
        variable_set = set()
    if isinstance(expr, ExistsExpression):
        return skolemization(
            expr.term.replace(expr.variable, skolem_function(variable_set)),
            variable_set
        )
    elif isinstance(expr, AllExpression):
        return AllExpression(
            expr.variable,
            skolemization(expr.term, variable_set.add(expr.variable))
        )
    elif isinstance(expr, (AndExpression, OrExpression)):
        return type(expr)(
            skolemization(expr.first, variable_set),
            skolemization(expr.second, variable_set)
        )
    elif isinstance(expr, NegatedExpression):
        return NegatedExpression(
            skolemization(expr.term, variable_set)
        )
    else:
        return expr

def universal_quantifier_elemination(expr):
    if isinstance(expr, AllExpression):
        return universal_quantifier_elemination(expr.term)
    else:
        return expr


def to_cnf(expr):
    if isinstance(expr, OrExpression):
        if isinstance(expr.first, AndExpression):
            return AndExpression(
                to_cnf(
                    OrExpression(expr.first.first, expr.second)
                ),
                to_cnf(
                    OrExpression(expr.first.second, expr.second)
                )
            )
        elif isinstance(expr.second, AndExpression):
            return AndExpression(
                to_cnf(
                    OrExpression(expr.first, expr.second.first)
                ),
                to_cnf(
                    OrExpression(expr.first, expr.second.second)
                )
            )
        else:
            return OrExpression(
                to_cnf(expr.first),
                to_cnf(expr.second)
            )
    elif isinstance(expr, AndExpression):
        return AndExpression(
            to_cnf(expr.first),
            to_cnf(expr.second)
        )
    else:
        return expr


def to_clauses(expr):
    if isinstance(expr, AndExpression):
        return to_clauses(expr.first) + to_clauses(expr.second)
    elif isinstance(expr, OrExpression):
        return [to_clauses(expr.first)] + [to_clauses(expr.second)]
    else:
        return [expr]
    
def unique_var_name(exprs, variable_set=None):
    if variable_set is None:
        variable_set = set()

    def rename(expr):
        if isinstance(expr, AllExpression):
            new_var = expr.variable
            while new_var in variable_set:
                ascii_value = (ord(new_var.name) - 96) % 26 + 97
                new_var = Variable(chr(ascii_value))
            variable_set.add(new_var)
            if new_var != expr.variable:
                expr = expr.alpha_convert(new_var)
            return AllExpression(
                expr.variable,
                rename(expr.term)
            )
        else:
            return expr

    return [rename(expr) for expr in exprs]

def resolution(kb, goal=None):
    kb = [implications_elemination(e) for e in kb]
    print('\n**************** KB after implications elemination ****************\n')
    for i in kb:
        print(i)
        
    kb = [demorgan(e) for e in kb]
    print('\n**************** KB after moving negation inwards ****************\n')
    for i in kb:
        print(i)
        
    kb = [remove_double_negation(e) for e in kb]
    print('\n**************** KB after removing double negation ****************\n')
    for i in kb:
        print(i)
    
    kb = [variable_standardization(e) for e in kb]
    print('\n**************** KB after variable standardization ****************\n')
    for i in kb:
        print(i)
                
    kb = [to_pnf(e) for e in kb]
    print('\n**************** KB after converting to prenext normal form ****************\n')
    for i in kb:
        print(i)
        
    kb = [skolemization(e) for e in kb]
    print('\n**************** KB after skolemization ****************\n')
    for i in kb:
        print(i)
        
    kb = [universal_quantifier_elemination(e) for e in kb]
    print('\n**************** KB after universal quantifier elemination ****************\n')
    for i in kb:
        print(i)
        
    kb = [to_cnf(e) for e in kb]
    print('\n**************** KB after converting to conjunction normal form ****************\n')
    for i in kb:
        print(i)
        
    kb = [to_clauses(e) for e in kb]
    print('\n**************** KB after converting into clauses ****************\n')
    for i in kb:
        print(i)
    return kb


read_expr = logic.Expression.fromstring

kb = ['exists x.(Dog(x) & Owns(Jack, x))',
      'all x.((exists y.Dog(y) & all y.Owns(x, y)) -> AnimalLover(x))',
      'all x.AnimalLover(x) -> (all y.Animal(y) -> -Kills(x, y))',
      'Kills(Jack, Tuna) | Kills(Curiosity, Tuna)',
      'Cat(Tuna)',
      'all x.Cat(x) -> Animal(x)',]

goal = 'Kills(Curiosity, Tuna)'

kb = [read_expr(i) for i in kb]

kb = resolution(kb)

# # 1. Eliminate implication
# # 2. Move negation inward (Demorgan Law)
# # 3. Remove double-not.
# # 4. Standardize variable scope.
# # 5. The prenex form (obtained by moving all quantifiers to the left of the formula.)
# # 6. Skolemization for existential quantifiers.
# # 7. Eliminate universal quantifiers.
# # 8. Convert to conjunctive normal form
# # 9. Turn conjunctions into clauses in a set, and rename variables so that no clause shares the same variable name.
# # 10. Rename variables in clauses so that each clause has a unique variable name.

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


def move_negation_inwards(expr):
    if isinstance(expr, NegatedExpression):
        if isinstance(expr.term, AndExpression):
            return OrExpression(
                move_negation_inwards(
                    NegatedExpression(expr.term.first)
                ),
                move_negation_inwards(
                    NegatedExpression(expr.term.second)
                )
            )
        elif isinstance(expr.term, OrExpression):
            return AndExpression(
                move_negation_inwards(
                    NegatedExpression(expr.term.first)
                ),
                move_negation_inwards(
                    NegatedExpression(expr.term.second)
                )
            )
        elif isinstance(expr.term, AllExpression):
            return ExistsExpression(
                expr.term.variable,
                move_negation_inwards(
                    NegatedExpression(expr.term.term)
                )
            )
        elif isinstance(expr.term, ExistsExpression):
            return AllExpression(
                expr.term.variable,
                move_negation_inwards(
                    NegatedExpression(expr.term.term)
                )
            )
        else:
            return expr
    elif isinstance(expr, (AndExpression, OrExpression)):
        return type(expr)(
            move_negation_inwards(expr.first),
            move_negation_inwards(expr.second)
        )
    elif isinstance(expr, (AllExpression, ExistsExpression)):
        return type(expr)(
            expr.variable,
            move_negation_inwards(expr.term)
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

def standardize_variables(expr, variable_set=None):
    if variable_set is None:
        variable_set = set()
    if isinstance(expr, AllExpression):
        new_var = expr.variable
        while new_var in variable_set:
            new_val = (ord(new_var.name) - 96) % 26 + 97
            new_var = Variable(chr(new_val))
        variable_set.add(new_var)
        if new_var != expr.variable:
            expr = expr.alpha_convert(new_var)
        return AllExpression(
            expr.variable,
            standardize_variables(expr.term, variable_set)
        )
    elif isinstance(expr, ExistsExpression):
        new_var = expr.variable
        while new_var in variable_set:
            new_val = (ord(new_var.name) - 96) % 26 + 97
            new_var = Variable(chr(new_val))
        variable_set.add(new_var)
        if new_var != expr.variable:
            expr = expr.alpha_convert(new_var)
        return ExistsExpression(
            expr.variable,
            standardize_variables(expr.term, variable_set)
        )
    elif isinstance(expr, NegatedExpression):
        return NegatedExpression(
            standardize_variables(expr.term, variable_set)
        )
    elif isinstance(expr, (AndExpression, OrExpression)):
        return type(expr)(
            standardize_variables(expr.first, variable_set),
            standardize_variables(expr.second, variable_set)
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


def to_clause(expr):
    def convert(expr):
        if isinstance(expr, AndExpression):
            return convert(expr.first) + convert(expr.second)
        elif isinstance(expr, OrExpression):
            return [convert(expr.first), convert(expr.second)]
        else:
            return [expr]

    def flatten(clauses):
        flatten_lists = []
        for clause in clauses:
            if isinstance(clause, list) and isinstance(clause[0], list):
                flatten_lists.extend(flatten(clause))
            elif isinstance(clause, list):
                flatten_lists.extend(clause)
            else:
                flatten_lists.append(clause)
        return flatten_lists

    return flatten(convert(expr))

def rename_variables(exprs, variable_set=None):
    if variable_set is None:
        variable_set = set()

    def rename(expr):
        if isinstance(expr, AllExpression):
            new_var = expr.variable
            while new_var in variable_set:
                new_val = (ord(new_var.name) - 96) % 26 + 97
                new_var = Variable(chr(new_val))
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
    print('\n**************** KB after implications elemination****************:')
    for i in kb:
        print('\n', i)
        
    kb = [move_negation_inwards(e) for e in kb]
    print('\n**************** KB after moving negation inwards:')
    for i in kb:
        print('\n', i)
        
    kb = [remove_double_negation(e) for e in kb]
    print('\n**************** KB after remove double negation:')
    for i in kb:
        print('\n', i)
    
    kb = [standardize_variables(e) for e in kb]
    print('\n****************KB after standardize variables:')
    for i in kb:
        print('\n', i)
                
    kb = [to_pnf(e) for e in kb]
    print('\n**************** KB after to pnf:')
    for i in kb:
        print('\n', i)
        
    kb = [skolemization(e) for e in kb]
    print('\n**************** KB after skolemization:')
    for i in kb:
        print('\n', i)
        
    kb = [universal_quantifier_elemination(e) for e in kb]
    print('\n**************** KB after universal quantifier elemination:')
    for i in kb:
        print('\n', i)
        
    kb = [to_cnf(e) for e in kb]
    print('\n**************** KB after converting to CNF:')
    for i in kb:
        print('\n', i)
        
    kb = [to_clause(e) for e in kb]
    print('\n**************** KB after converting to clauses:')
    for i in kb:
        print('\n', i)
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
# goal = read_expr(goal)

kb = resolution(kb)

# p = ResolutionProverCommand(read_expr(goal), kb)
# print(p.prove())
# print(p.proof())

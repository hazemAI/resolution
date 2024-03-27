# RKR Assignment 1 - resolution


● This assignment will involve working in groups of two members.

● Write Python code to apply resolution procedure in predicate logic.

● Upload your code to GitHub and then add the link to the discussion sheet to check for plagiarism.

● It should contain the functions that cover the following steps (resolution steps):

1. Eliminate implication
2. Move negation inward (Demorgan Law)
3. Remove double-not.
4. Standardize variable scope.
5. The prenex form (obtained by moving all quantifiers to the left of the formula.)
6. Skolemization for existential quantifiers.
7. Eliminate universal quantifiers.
8. Convert to conjunctive normal form
9. Turn conjunctions into clauses in a set, and rename variables so that no clause shares the same variable name.
10. Rename variables in clauses so that each clause has a unique variable
name.

```
from nltk.sem.logic import *
from nltk.sem import logic



def implications_elemination(expr):
    if type(expr) == ImpExpression:
        return implications_elemination(OrExpression(-expr.first, expr.second))
    
    elif type(expr) in [AllExpression, ExistsExpression]:
        return type(expr)(expr.variable, implications_elemination(expr.term))
    
    elif type(expr) == NegatedExpression:
        return NegatedExpression(implications_elemination(expr.term))
    
    elif type(expr) in [AndExpression, OrExpression]:
        return type(expr)(implications_elemination(expr.first), implications_elemination(expr.second))
    else:
        return expr

def demorgan(expr):
    expression_map = {
        AndExpression: OrExpression,
        OrExpression: AndExpression,
        AllExpression: ExistsExpression,
        ExistsExpression: AllExpression
    }
    if type(expr) == NegatedExpression:
        if type(expr.term) in [AndExpression, OrExpression]:
            return expression_map[type(expr.term)](
                demorgan(NegatedExpression(expr.term.first)),
                demorgan(NegatedExpression(expr.term.second))
            )
        elif type(expr.term) in [AllExpression, ExistsExpression]:
            return expression_map[type(expr.term)](
                expr.term.variable,
                demorgan(NegatedExpression(expr.term.term))
            )
        else:
            return expr
    elif type(expr) in [AndExpression, OrExpression]:
        return type(expr)(demorgan(expr.first), demorgan(expr.second))
    
    elif type(expr) in [AllExpression, ExistsExpression]:
        return type(expr)(expr.variable, demorgan(expr.term))
    else:
        return expr


def remove_double_negation(expr):
    if type(expr) == NegatedExpression:
        if type(expr.term) == NegatedExpression:
            return remove_double_negation(expr.term.term)
        else:
            return NegatedExpression(remove_double_negation(expr.term))
    elif type(expr) in [AndExpression, OrExpression]:
        return type(expr)(
            remove_double_negation(expr.first),
            remove_double_negation(expr.second)
        )
    elif type(expr) in [AllExpression, ExistsExpression]:
        return type(expr)(
            expr.variable,
            remove_double_negation(expr.term)
        )
    else:
        return expr

def variable_standardization(expr, variable_list=None):
    variable_list = variable_list or []
    alphabet = 'abcdefghijklmnopqrstuvwxyz'
    
    if type(expr) in [AllExpression, ExistsExpression]:
        new_var = expr.variable
        while new_var in variable_list:
            new_var = Variable(alphabet[(alphabet.index(new_var.name) + 1) % 26])
        if new_var not in variable_list:
            variable_list.append(new_var)
        if new_var != expr.variable:
            expr = expr.alpha_convert(new_var)
        return type(expr)(
            expr.variable,
            variable_standardization(expr.term, variable_list)
        )
    elif type(expr) == NegatedExpression:
        return NegatedExpression(
            variable_standardization(expr.term, variable_list)
        )
    elif type(expr) in [AndExpression, OrExpression]:
        return type(expr)(
            variable_standardization(expr.first, variable_list),
            variable_standardization(expr.second, variable_list)
        )
    else:
        return expr


def to_pnf(expr):
    def get_quantifiers(expr):
        if type(expr) in [AllExpression, ExistsExpression]:
            sub_term = get_quantifiers(expr.term)
            # Append current quantifier and variable to the lists
            return sub_term[0], sub_term[1] + [type(expr)], sub_term[2] + [expr.variable]
        elif type(expr) == NegatedExpression:
            sub_term = get_quantifiers(expr.term)
            # Negate the sub_term (expression part) and return the quantifiers and variables
            return NegatedExpression(sub_term[0]), sub_term[1], sub_term[2]
        elif type(expr) in [AndExpression, OrExpression]:
            left = get_quantifiers(expr.first)
            right = get_quantifiers(expr.second)
            # Merge the terms and lists from both sides of the expression
            return type(expr)(left[0], right[0]), left[1] + right[1], left[2] + right[2]
        else:
            # Return the expression and empty lists for base case
            return expr, [], []

    expr, quantifiers, variables = get_quantifiers(expr)
    # Sort the quantifiers so that all universal quantifiers come before existential quantifiers
    for quantifier, variable in sorted(zip(quantifiers, variables),
                                       key=lambda x: 1 if x[0] == AllExpression else 0):
        expr = quantifier(variable, expr)
    return expr


def skolemization(expr, variable_list=None):
    variable_list = variable_list or []
    if type(expr) == ExistsExpression:
        return skolemization(
            expr.term.replace(expr.variable, skolem_function(variable_list)), variable_list)
    elif type(expr) == AllExpression:
        return AllExpression(expr.variable,skolemization(expr.term, variable_list.append(expr.variable)))
    
    elif type(expr) in [AndExpression, OrExpression]:
        return type(expr)(skolemization(expr.first, variable_list), skolemization(expr.second, variable_list))
    
    elif type(expr) == NegatedExpression:
        return NegatedExpression(skolemization(expr.term, variable_list))
    else:
        return expr

def universal_quantifier_elemination(expr):
    if type(expr) == AllExpression:
        return universal_quantifier_elemination(expr.term)
    else:
        return expr


def to_cnf(expr):
    if type(expr) == OrExpression:
        sub_exprs = [expr.first, expr.second]
        for i, sub_expr in enumerate(sub_exprs):
            if type(sub_expr) == AndExpression:
                other = sub_exprs[1 - i] # A or (B and C) | (B and C) or A
                return AndExpression(
                    to_cnf(OrExpression(sub_expr.first, other)), 
                    to_cnf(OrExpression(sub_expr.second, other))
                )
        return OrExpression(to_cnf(expr.first), to_cnf(expr.second))
    elif type(expr) == AndExpression:
        return AndExpression(to_cnf(expr.first), to_cnf(expr.second))
    else:
        return expr


# convertion to clauses is like seperating the lists with ands like (a and b) becomes [a], [b] and seperating the ors with commas like (a or b) becomes [a, b]
def to_clauses(expr):
    if type(expr) == AndExpression:
        return to_clauses(expr.first) + to_clauses(expr.second)
    elif type(expr) == OrExpression:
        return [to_clauses(expr.first)] + [to_clauses(expr.second)]
    else:
        return [expr]
    

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
    print('\n**************** KB after converting to prenex normal form ****************\n')
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
```

# Write Python code to apply resolution procedure in predicate logic (you can use nlkt)
# It should contain the functions that cover the following steps (resolution steps): 

# Given the following FOL statements:

# forall x. forall y. (CScourse(x) and Test(y, x) implies exists z. Fail(z, y))
# forall y. ((exists x. Test(y, x)) and Easy(y) implies forall z. Pass(z, y))
# not exists x. exists y. (Pass(x, y) and Fail(x, y))
# Test(Exam1, Class1)
# Easy (Exam1)

['forall x. forall y. (CScourse(x) and Test(y, x) -> exists z. Fail(z, y))',
      'forall y. ((exists x. Test(y, x)) and Easy(y) -> forall z. Pass(z, y))',
      'not exists x. exists y. (Pass(x, y) and Fail(x, y))',
      'Test(Exam1, Class1)',
      'Easy(Exam1)']

# Use resolution to procedure to prove: not CScourse(Class1)

# Answer:
# The Knowledge base becomes:

# not CScourse(x) or not Test(y, x) or Fail(f(z), y)
# *not Test(y, x)* or not Easy(y) or Pass(z, y) # we remove *not Test(y, x)* because it is a duplicate from statement 1
# not Pass(x, y) or not Fail(x, y)
# Test(Exam1, Class1)
# Easy (Exam1)

# kb = {not CScourse(x) or not Test(y, x) or Fail(f(z), y),
# not Easy(y) or Pass(z, y),
# not Pass(x, y) or not Fail(x, y),
# Test(Exam1, Class1),
# Easy(Exam1)}

# We start with Negate our goal then add to our set as follow:
# 1. CScourse(Class1)
# 2. not CScourse(Class1) or not Test(y, Class1) or Fail(f(z), y) x/Class1
# 3. not Easy(y) or Pass(z, y)
# 4. not Pass(x, y) or not Fail(x, y)
# 5. Test(Exam1, Class1)
# 6. Easy (Exam1)

# from 1,2
# 7. not Test(y, Class1) or Fail(f(z), y)
# from 3,6 y/Examl
# 8. Pass(z, Exam1)
# from 4
# 9. not Pass(z, Exam1) or not Fail(z, Exam1) x/z, y/Exam1
# from 8,9
# 10. not Fail(z, Exam1) y/Exam1
# from 5,7,10
# z/f(z), y/Exam1
# {}


from nltk import ResolutionProver
from nltk.sem import Expression
from nltk.sem import logic


# Eliminate implications.
def eliminate_implication(expression):
    if expression.is_atomic():
        return expression
    elif expression.op == '->':
        return logic.AndExpression(eliminate_implication(logic.NotExpression(expression.first)), eliminate_implication(expression.second))
    else:
        return logic.AndExpression(eliminate_implication(expression.first), eliminate_implication(expression.second))
    
    
# Move negation inward (Demorgan Law).
def move_negation_inward(expression):
    if expression.is_atomic():
        return expression
    elif expression.op == 'not':
        if expression.first.op == 'and':
            return logic.OrExpression(move_negation_inward(logic.NotExpression(expression.first.first)), move_negation_inward(logic.NotExpression(expression.first.second)))
        elif expression.first.op == 'or':
            return logic.AndExpression(move_negation_inward(logic.NotExpression(expression.first.first)), move_negation_inward(logic.NotExpression(expression.first.second)))
        else:
            return expression
    else:
        return logic.AndExpression(move_negation_inward(expression.first), move_negation_inward(expression.second))
    
    
# Standardize variable scope. 
def standardize_variable_scope(expression, variables):
    if expression.is_atomic():
        return expression
    elif expression.op == 'all':
        new_variable = logic.Variable(variables.pop())
        return standardize_variable_scope(expression.first.substitute(expression.variable, new_variable), variables)
    else:
        return logic.AndExpression(standardize_variable_scope(expression.first, variables), standardize_variable_scope(expression.second, variables))
    
# Eliminate universal quantifiers. 
def eliminate_universal_quantifiers(expression):
    if expression.is_atomic():
        return expression
    elif expression.op == 'all':
        return eliminate_universal_quantifiers(expression.first)
    else:
        return logic.AndExpression(eliminate_universal_quantifiers(expression.first), eliminate_universal_quantifiers(expression.second))

# The prenex normal form (obtained by moving all quantifiers to the front of the formula.) 
def prenex_normal_form(expression):
    if expression.is_atomic():
        return expression
    elif expression.op == 'and':
        return logic.AndExpression(prenex_normal_form(expression.first), prenex_normal_form(expression.second))
    elif expression.op == 'or':
        return logic.OrExpression(prenex_normal_form(expression.first), prenex_normal_form(expression.second))
    elif expression.op == 'all':
        return logic.AllExpression(expression.variable, prenex_normal_form(expression.first))
    elif expression.op == 'exists':
        return logic.ExistsExpression(expression.variable, prenex_normal_form(expression.first))
    else:
        return expression
    
# Convert to conjunctive normal form 
def conjunctive_normal_form(expression):
    if expression.is_atomic():
        return expression
    elif expression.op == 'and':
        return logic.AndExpression(conjunctive_normal_form(expression.first), conjunctive_normal_form(expression.second))
    elif expression.op == 'or':
        return logic.OrExpression(conjunctive_normal_form(expression.first), conjunctive_normal_form(expression.second))
    else:
        return expression
# Turn conjunctions into clauses in a set, and rename variables so that no clause shares the same variable name.
def clauses(expression):
    if expression.is_atomic():
        return {expression}
    elif expression.op == 'and':
        return clauses(expression.first) | clauses(expression.second)
    else:
        return {expression}

# Rename variables in clauses so that each clause has a unique variable name.
def rename_variables(clauses):
    new_clauses = set()
    for clause in clauses:
        new_clause = set()
        for literal in clause:
            new_literal = literal
            if literal.op == 'not':
                new_literal = logic.NotExpression(logic.Variable(literal.first.variable + str(len(new_clauses))))
            elif literal.op == 'all':
                new_literal = logic.AllExpression(logic.Variable(literal.variable + str(len(new_clauses))), new_literal.first)
            elif literal.op == 'exists':
                new_literal = logic.ExistsExpression(logic.Variable(literal.variable + str(len(new_clauses))), new_literal.first)
            new_clause.add(new_literal)
        new_clauses.add(new_clause)
    return new_clauses

# Resolution
def resolution(knowledge_base, goal):
    # Eliminate implications.
    knowledge_base = eliminate_implication(knowledge_base)
    goal = eliminate_implication(goal)
    # Move negation inward.
    knowledge_base = move_negation_inward(knowledge_base)
    goal = move_negation_inward(goal)
    # Standardize variable scope.
    knowledge_base = standardize_variable_scope(knowledge_base, ['x', 'y', 'z', 'f'])
    goal = standardize_variable_scope(goal, ['x', 'y', 'z', 'f'])
    # Eliminate universal quantifiers.
    knowledge_base = eliminate_universal_quantifiers(knowledge_base)
    goal = eliminate_universal_quantifiers(goal)
    # The prenex normal form.
    knowledge_base = prenex_normal_form(knowledge_base)
    goal = prenex_normal_form(goal)
    # Convert to conjunctive normal form.
    knowledge_base = conjunctive_normal_form(knowledge_base)
    goal = conjunctive_normal_form(goal)
    # Turn conjunctions into clauses in a set, and rename variables so that no clause shares the same variable name.
    knowledge_base = clauses(knowledge_base)
    goal = clauses(goal)
    knowledge_base = rename_variables(knowledge_base)
    goal = rename_variables(goal)
    # Resolution
    prover = ResolutionProver()
    return prover.prove(goal, knowledge_base)


# kb without cnf
kb = ['forall x. forall y. (CScourse(x) and Test(y, x) -> exists z. Fail(z, y))',
      'forall y. ((exists x. Test(y, x)) and Easy(y) -> forall z. Pass(z, y))',
      'not exists x. exists y. (Pass(x, y) and Fail(x, y))',
      'Test(Exam1, Class1)',
      'Easy(Exam1)']


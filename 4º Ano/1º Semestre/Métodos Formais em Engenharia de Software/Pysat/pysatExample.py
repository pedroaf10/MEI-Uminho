from pysat.solvers import Minisat22

s = Minisat22()                # cria o solver s

s.add_clause([-1, 2])          # acrescenta uma cláusula
s.add_clause([-1, -2, 3])

if s.solve():                  # testa a satisfatibilidade
    print("SAT")
    print(s.get_model())       # imprime o modelo
else: 
    print("UNSAT")

s.delete()                     # apaga o solver adsa
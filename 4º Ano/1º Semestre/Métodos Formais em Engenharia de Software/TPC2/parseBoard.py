import re
from z3 import *

x = {}
s = Solver()
f = open(r"C:\Users\Pedro\Documents\Uminho\Uminho\4ano\1Semestre\MFES\TPC2\Board.txt")
N = 0

lines = f.readlines()
cont = -1
i = 0
for line in lines:
    if cont == -1 :
        N = int(line)
        for i in range(N):
            x[i] = {}
        for j in range(N):
            x[i][j] = Int('x'+str(i)+str(j))       # declaração de variáveis
            s.add(And(1<= x[i][j], x[i][j]<=N))    # restrições de valor

    else :
        if ((cont % 2) == 0) :

            if res := re.findall(r'[^\|\n\s\b]', line):
                print("!",res)

                for j in range(N*2-1):
                    print(res[j])
 
                    if(res[j].isdigit()):
                        print(x[i][j])
                        #x[i][j] = int(res[j])

                    elif(res[j] == '<'):
                       # print(x[i][j-1], " menor ", x[i][j])
                        print(j)

                    elif(res[j] == '>'):
                        print(" maior ")
                    

            i += 1
        else:
            if res := re.findall(r'[^\|\n\s\b]', line):
                #print(res)
                f = 2
    cont += 1

print(x)
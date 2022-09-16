// Modelo Circuito Euleriano num grafo não-orientado e ligado

var sig Proximo in Nodo {}

sig Nodo {
    var vizinhos : set Nodo
}

// Algumas das propriedades desejadas para o sistema

assert noMaximoUmProximo {
	always (one Proximo)
}

// Especifique as condições iniciais do sistema

fact Init {
    all n: Nodo | n.vizinhos in Nodo-n
    all n1, n2: Nodo | n1 in n2.vizinhos implies n2 in n1.vizinhos
    all n: Nodo | Nodo in n.^vizinhos
	all n: Nodo | rem[#n.vizinhos, 2] = 0
	one Proximo
	all n: Nodo | Nodo-n in n.vizinhos
}

// Operação de remover uma aresta
pred removeAresta [n1, n2: Nodo] {
	// guard
	Proximo = n1
	#n1.vizinhos > 1
	n1 in n2.vizinhos
	n2 in n1.vizinhos

	//efects
	n1.vizinhos' = n1.vizinhos-n2
    n2.vizinhos' = n2.vizinhos-n1
	Proximo' = n2	

	//frame condition
	all n: Nodo-(n1+n2) | n.vizinhos' = n.vizinhos
	all n: Nodo | Nodo in n.^vizinhos'
}

// Operação de remover uma aresta e um nodo
pred removeNodo [n1, n2: Nodo] {
	// guard
	Proximo = n1
	#n1.vizinhos = 1
	n1 in n2.vizinhos
	n2 in n1.vizinhos

	//efects
	n1.vizinhos' = n1.vizinhos-n2
    n2.vizinhos' = n2.vizinhos-n1
	Proximo' = n2

	//frame condition
	all n: Nodo-(n1+n2) | n.vizinhos' = n.vizinhos
}

pred nop {
    Nodo' = Nodo
    vizinhos' = vizinhos
    Proximo' = Proximo
}

fact Traces {
    always (nop or some n1, n2: Nodo | removeAresta[n1 , n2]
			    or some n1, n2: Nodo | removeNodo[n1 , n2])
}

run Exemplo {
	eventually (all n: Nodo | no n.vizinhos)
	
} for exactly 5 Nodo, 20 steps

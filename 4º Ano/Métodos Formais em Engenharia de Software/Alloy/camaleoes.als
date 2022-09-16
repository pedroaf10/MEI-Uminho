/* 
Complete o seguinte modelo de uma colónia de camaleões onde o número de 
camaleões é fixo mas onde a cor de cada camaleão pode mudar de acordo com
as seguintes regras: 
- As cores possíveis são Verde, Azul e Amarelo
- Se 2 camaleões de cores diferentes se encontram mudam ambos para a terceira cor
- As cores só se alteram na situação acima 
*/

abstract sig Cor {}
one sig Verde, Azul, Amarelo extends Cor {}

sig Camaleao {
	var cor : one Cor
}

pred nop {	
	cor' = cor
}

pred encontro[x,y : Camaleao] {
	// guards
	x != y
	x.cor != y.cor

	// effect
	(x.cor != Verde and y.cor != Verde) implies 
		(x.cor' = Verde and y.cor' = Verde)
	(x.cor != Amarelo and y.cor != Amarelo) implies 
		(x.cor' = Amarelo and y.cor' = Amarelo)
	(x.cor != Azul and y.cor != Azul) implies 
		(x.cor' = Azul and y.cor' = Azul)

	// frame conditions
	all c : Camaleao - (x + y) | c.cor' = c.cor
}

fact Comportamento {
	always (nop or some x,y : Camaleao | encontro[x,y])
}

// Especifique as seguintes propriedades desta colónia

assert Estabilidade {
	// Se os camaleoes ficarem todos da mesma cor, as cores nunca mais mudam
	always Camaleao.cor in Amarelo implies always Camaleao.cor in Amarelo
	always Camaleao.cor in Verde implies always Camaleao.cor in Verde
	always Camaleao.cor in Azul implies always Camaleao.cor in Azul
}

check Estabilidade for 5

assert NaoConvergencia {
	// Se inicialmente há um camaleao verde e nenhum azul então não é possível
	// que a colónia fique toda amarela
	(one c : Camaleao | c.cor = Verde and no Verde & (Camaleao-c).cor) and no Azul & Camaleao.cor implies always not Camaleao.cor in Amarelo
}

check NaoConvergencia for 5

// Especifique um cenário onde existe um camaleao que não para de mudar de cor
// tomando recorrentemente todas as cores possíveis

run Exemplo {
	 one c : Camaleao | always c.cor' != c.cor
}

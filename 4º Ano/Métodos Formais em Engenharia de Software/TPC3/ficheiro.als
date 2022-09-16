sig Object {}

sig Name {}

sig Dir extends Object {
    entries : set Entry
}

sig File extends Object {}

sig Root extends Dir {}

sig Entry {
    object : one Object,
    name : one Name

}
fact {
    entries in Dir one -> set Entry
}


sig Hash {}
abstract sig Object {
	hash : one Hash
}

sig Blob extends Object {}

sig Name {}
sig Tree extends Object {
	objects : Hash -> Name
}

sig Commit extends Object {
	tree : one Hash,
	parent : set Hash
}

pred Invs {
	// Specify the properties of the git object model inside this predicate

	// The number of points you will get is proportional to the number of correct properties.
	// To check how many points you have so far you can use the different commands. The maximum is 5 points.
	// Be careful to not overspecify! 
	// If not all possible git object models are allowed by your spec you get 0 points, even if you have some correct properties.
	// To check if you are not overspecifying you can use command AllModelsArePossible. 
	// If you are overspecifying this command will return a git object model that should be possible 
	// but that you spec is not currently accepting.
  
  	//1-Uma arvore não pode ter 2 objetos diferentes com o mesmo nome.
  	//t: Tree, o: Object | lone n: Name | o in t.
  	all n1, n2: Name| n1 in ~(Tree.objects).Hash and n2 in ~(Tree.objects).Hash implies n1 != n2 or 
  
	//2-Cada hash é correspondente a um único objeto
  	all o1, o2: Object | o1 != o2 implies o1.hash != o2.hash // correta
  
	//3.1-Os objetos de uma tree são outras tree ou um blob.
  	all t: Tree | t.objects.Name in (Object-Commit).hash // correta
  
	//3.2-O Commit, em tree aponta para uma hash de um objeto tipo tree.
  	all c: Commit | c.tree in Tree.hash // correta
  
	//3.3-O Commit em parent aponta para hashs de objetos tipo Commit.
    all c: Commit | c.parent in Commit.hash // correta
  
	//4.1-Um Commit não pode estar contido nos seus parent.
  	//all c: Commit | c.hash not in c.parent
  
	//4.2-Uma Tree nao pode estar contida nos seus objetos.
  	//all t: Tree | t.hash not in t.objects.Name 
  
	//5.1-Se 2 Trees tem os mesmos objetos então são a mesma Tree.
  	//all t1, t2: Tree | t1.objects.Name = t2.objects.Name and t1.hash = t2.hash implies t1 = t2
  
	//5.2-Se 2 Commit tem a mesma tree, e os mesmos parents então são o mesmo Commit
	//all c1, c2: Commit | c1.tree = c2.tree and c1.parent = c2.parent implies c1 = c2
}

all t1, t2: Tree | t1.^(objects.Name.~hash) = t2.^(objects.Name.~hash) and t1.hash = t2.hash implies t1 = t2

all c1, c2: Commit | c1.^(tree.~hash) = c2.^(tree.~hash) and c1.parent = c2.parent implies c1 = c2

// tpc 3

sig Hash {}
abstract sig Object {
	hash : one Hash
}

sig Blob extends Object {}

sig Name {}
sig Tree extends Object {
	objects : Hash -> Name
}

sig Commit extends Object {
	tree : one Hash,
	parent : set Hash
}

pred Invs {
  
  	// Cada Objeto é identificado por uma Hash
  	all o1, o2: Object | o1 != o2 implies o1.hash != o2.hash // check 1
  
  	// Não podem haver 2 objetos na mesma Tree com o mesmo 2
  	all n: Name, t: Tree | n in ~(t.objects).Hash implies one t.objects.n // check 2
  
  	// Um Commit não pode estar contido na suscessão dos seus parents.
  	all c : Commit | c not in c.^(parent.~hash) // check 3
  
	// Uma Tree nao pode estar contida nos seus objects nem nos objects destes.
    all t : Tree | t not in t.^(objects.Name.~hash) // check 3
  
	// Os objetos de uma tree correspondem a Tree ou Blob.
  	all t: Tree | t.objects.Name in Tree.hash + Blob.hash // check 4
  
	// O campo tree em Commit é uma Tree.
  	all c: Commit | c.tree in Tree.hash // check 4
  
  	// O campo parent em Commit é um Commit.
    all c: Commit | c.parent in Commit.hash // check 4
  
	// Se 2 Trees tem os mesmos objetos implica que são a mesma Tree.
	all t1, t2: Tree | t1.objects = t2.objects implies t1=t2 // check 5
  
	// Se 2 Commit tem a mesma tree e os mesmos parents implica que são o mesmo Commit.
	all c1, c2: Commit | c1.tree = c2.tree and c1.parent = c2.parent implies c1=c2 // check 5
}
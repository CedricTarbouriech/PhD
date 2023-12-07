sig Entity {
	part_of: set Entity
}

/**************
 * Predicates *
 **************/
pred P(x, y : Entity) {
	x->y in part_of
}

pred PP(x, y : Entity) {
	P[x, y] and x != y
}

pred O(x, y : Entity) {
	some z : Entity | P[z, x] and P[z, y]
}

/**********
 * Axioms *
 **********/
// Reflexivity
pred Refl { 
	all x : Entity | P[x, x]
}
fact { Refl }

// Transitivity
pred Trans {
	all x, y, z : Entity |
		P[x, y] and P[y, z] implies P[x, z]
}

// Antisymmetry
pred Antis {
	all x, y : Entity |
		P[x, y] and P[y, x] implies x = y
}

// Supplementation
pred WSup {
	all x, y : Entity |
		PP[x, y] implies (some z : Entity | P[z, y] and not O[z, x])
}

// Strong Supplementation
pred SSup {
	all x, y : Entity |
		not P[y, x] implies (some z : Entity | P[z, y] and not O[z, x])
}

/***********
 * Sandbox *
 ***********/

assert T1 {
	no x : Entity | not P[x, x]
}

fact { Refl Trans Antis SSup }
check { 
	all x, y : Entity |
		PP[x, y] implies (some z : Entity |
			P[z, y] and not O[z, x])
} for 30

run {
	Refl Trans Antis
	some disj x, y, z : Entity |
		P[x, y] and P[y, z]
} for 3

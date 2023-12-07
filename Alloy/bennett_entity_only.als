sig Entity {
	slot_of : set Entity,
	fills : set Entity
}

/***************
 * Definitions *
 ***************/
pred F(x, s : Entity) { x->s in fills }
pred Ps(s, x : Entity) { s->x in slot_of }
pred P(x, y : Entity) { some z : Entity | Ps[z, y] and F[x, z] }
pred PP(x, y : Entity) { P[x, y] and not P[y, x] }
pred O(x, y : Entity) { some z : Entity | P[z, x] and P[z, y] }
pred Os(x, y : Entity) { some z : Entity | Ps[z, x] and Ps[z, y] }
pred PPs(x, y : Entity) { Ps[x, y] and not F[y, x] }

/**********
 * Axioms *
 **********/
// Only Slots are Filled
pred A1 {
	all x, y : Entity |
		(F[x, y] implies (some z : Entity | Ps[y, z]))
}

// Slots Cannot Fill
pred A2 {
	all x, y : Entity |
		F[x, y] implies (no z : Entity | Ps[x, z])
}

// Slots Don’t Have Slots
pred A3 {
	all x, y : Entity |
		Ps[x, y] implies (no z : Entity | Ps[z, x])
}

// Improper Parthood Slots
pred A4 {
	all x : Entity |
		(some y : Entity | Ps[y, x]) implies
			(some z : Entity | Ps[z, x] and F[x, z])
}

// Slot Inheritance
pred A5 {
	all x, y, z1, z2 : Entity |
		(Ps[z1, y] and F[x, z1] and Ps[z2, x]) implies (Ps[z2, y])
}

// Mutual Occupancy is Identity
pred A6 {
	all x, y, z1, z2 : Entity |
		((Ps[z1, y] and F[x, z1]) and (Ps[z2, x] and F[y, z2])) implies (x = y)
}

// Single Occupancy
pred A7 {
	all x, y : Entity |
		(Ps[x, y]) implies (one z : Entity | F[z, x])
}

// Slot Strong Supplementation
pred A8 {
	all x, y : Entity |
		((some z : Entity | Ps[z, x]) and (some z : Entity | Ps[z, y])) implies
			((no z : Entity | Ps[z, x] and F[y, z]) implies
				(some z: Entity | Ps[z, y] and not Ps[z, x]))
}

/************
 * Theorems *
 ************/
// Filler Irreflexivity
assert T1 {
	all x : Entity | not F[x, x]
}

// Filler Asymmetry
assert T2 {
	all x, y : Entity |
		F[x, y] implies not F[y, x]
}

// Filler Transitivity
assert T3 {
	all x, y, z : Entity |
		F[x, y] and F[y, z] implies F[x, z]
}

// Slot Irreflexivity
assert T4 {
	all x : Entity | not Ps[x, x]
}

// Slot Asymmetry
assert T5 {
	all x, y : Entity |
		Ps[x, y] implies not Ps[y, x]
}

// Slot Transitivity
assert T6 {
	all x, y, z : Entity |
		Ps[x, y] and Ps[y, z] implies Ps[x, z]
}

// Transitivity
assert T7 {
	all x, y, z : Entity |
		P[x, y] and P[y, z] implies P[x, z]
}

// Anti-Symmetry
assert T8 {
	all x, y : Entity |
		P[x, y] and P[y, x] implies x = y
}

// Conditional Reflexivity
assert T9 {
	all x : Entity |
		((some z : Entity | Ps[z, x]) implies P[x, x])
}

// Parts <-> Slots
assert T11 {
	all y : Entity |
		((some x : Entity | P[x, y]) iff (some z : Entity | Ps[z, y]))
}

// Composites <-> Slot-Composites
assert T12 {
	all y : Entity |
		((some x : Entity | PP[x, y]) iff (some z : Entity | PPs[z, y]))
}

// Slot Weak Supplementation
assert T13 {
	all x, y : Entity |
		PP[x, y] implies (some z : Entity | Ps[z, y] and not Ps[z, x])
}

// Slot Extensionality
assert T14 {
	all x, y : Entity |
		(((some z : Entity | PP[z, x]) or (some z : Entity | PP[z, y])) implies
			(x = y iff (all z : Entity | PPs[z, x] iff PPs[z, y])))
}

fact {  }

check T1 for 5 // OK : A1 et A2
check T2 for 5 // OK : A1 et A2
check T3 for 5 // OK : A1 et A2
check T4 for 5 // OK : A3
check T5 for 5 // OK : A3
check T6 for 5 // OK : A3
check T7 for 5 // Seulement besoin de A5, et non de A7
check T8 for 5 // OK : A6
check T9 for 5 // OK : A4
check T11 for 5 // Aussi prouvable avec A4 (y est sa partie)
check T12 for 5 // Ok : A6 et A7
check T13 for 5 // A8 et aussi par A4
check T14 for 6 // Axiomes insuffisants

/***********
 * Sandbox *
 ***********/

run { some disj x, y, z : Entity | P[x, y] and P[y, z] } for 6

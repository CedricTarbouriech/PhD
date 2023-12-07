// BA2 and BA3 are implemented by the types of content and slots.
// BA7 is implemented by the multiplicity of content.

open util/relation as rel

sig Slot {
	content : one Filler,
	copied_through : set Slot,
	copied_from : set Slot
}

sig Filler {
	slots : set Slot
}

/***************
 * Definitions *
 ***************/
pred F(x : Filler, s : Slot) { x = s.content }
pred Ps(s : Slot, x : Filler) { s in x.slots }
pred P(x, y : Filler) { some z : Slot | Ps[z, y] and F[x, z] }
pred PP(x, y : Filler) { P[x, y] and not P[y, x] }
pred O(x, y : Filler) { some z : Filler | P[z, x] and P[z, y] }
pred Os(x, y : Filler) { some z : Slot | Ps[z, x] and Ps[z, y] }
pred PPs(s : Slot, x : Filler) { Ps[s, x] and not F[x, s] }
pred IPs(s : Slot, x : Filler) { Ps[s, x] and F[x, s] }
pred CT(s, t : Slot) { s->t in copied_through }
pred CF(s, t : Slot) { s->t in copied_from }

/**********
 * Axioms *
 **********/
// Only Slots are Filled
pred BA1 {
	Slot in Filler.slots
}

// Improper Parthood Slots
pred BA4 {
	all x : Filler | ((#x.slots > 0) implies (some z: Slot | F[x, z] and Ps[z, x]))
}

// Slot Inheritance
pred BA5 {
	all x, y : Filler, z : Slot |
		(P[x, y] and Ps[z, x]) implies (Ps[z, y])
}

// Mutual Occupancy is Identity
pred BA6 {
	all x, y : Filler |
		(P[x, y] and P[y, x]) implies (x = y)
}

// Slot Strong Supplementation
pred BA8 {
	all x, y : Filler |
		(#x.slots > 0 and #y.slots > 0) implies
			(not P[y, x] implies (#(y.slots - x.slots) > 0))
}

/** Our Axioms **/
// Improper Slots are only owned by their Filler
pred A1 {
	all x : Filler, s : Slot |
		(Ps[s, x] and F[x, s]) implies
			(all y : Filler | (Ps[s, y] implies x = y))
}

// Proper Slot Inheritance
pred A2 {
	all x, y : Filler, s : Slot |
		(P[x, y] and PPs[s, x]) implies (Ps[s, y])
}

// Additional Improper Parthood Slots
pred A3 {
	all x : Filler, s : Slot |
		(F[x, s]) implies (some t : Slot | Ps[t, x] and F[x, t])
}

// Only One Improper Slot per Filler
pred A4 {
	all x : Filler, s, t : Slot |
		(Ps[s, x] and F[x, s] and Ps[t, x] and F[x, t]) implies
			(s = t)
}

// Anti-inheritance
pred A5 {
	all disj x, y : Filler | 
		(all t : Slot | 
			(P[x, y] and Ps[t, x]) implies (not Ps[t, y])
		)
}

// Existence of a Unique Copy-Slot for each Whole and Path-Slot, Source-Slot Pair
pred A6 {
	all x, y : Filler, s, t : Slot |
		(PPs[s, x] and F[y, s] and PPs[t, y]) implies 
			(one u : Slot | Ps[u, x] and CT[u, s] and CF[u, t])
}

// Copied Slot has the Same Filler as its Source
pred A7 {
	all s, t : Slot |
		(CF[t, s]) implies (some x : Filler | F[x, s] and F[x, t])
}

// Same Owner
pred A8 {
	all x : Filler, s, t : Slot |
		(PPs[t, x] and CT[t, s]) implies (PPs[s, x])
}

// Path and Source are Related
pred A9 {
	all s, t, u : Slot |
		(CT[u, s] and CF[u, t]) implies
			(some x : Filler | F[x, s] and PPs[t, x])
}

pred A10 {
	all s, t, u : Slot | (CF[s, t] and CF[s, u]) implies (t = u)
}

pred A11 {
	all s, t, u : Slot | (CT[s, t] and CT[s, u]) implies (t = u)
}


/************
 * Theorems *
 ************/
// Transitivity
assert BT7 {
	all x, y, z : Filler |
		P[x, y] and P[y, z] implies P[x, z]
}

// Anti-Symmetry
assert BT8 {
	all x, y : Filler |
		P[x, y] and P[y, x] implies x = y
}

// Conditional Reflexivity
assert BT9 {
	all x : Filler |
		((some z : Slot | Ps[z, x]) implies P[x, x])
}

// Parts <-> Slots
assert BT11 {
	all y : Filler |
		((some x : Filler | P[x, y]) iff (some z : Slot | Ps[z, y]))
}

// Composites <-> Slot-Composites
assert BT12 {
	all y : Filler |
		((some x : Filler | PP[x, y]) iff (some z : Slot | PPs[z, y]))
}

// Slot Weak Supplementation
assert BT13 {
	all x, y : Filler |
		PP[x, y] implies (some z : Slot | Ps[z, y] and not Ps[z, x])
}

// Slot Extensionality
assert BT14 {
	all x, y : Filler |
		((some z : Filler | PP[z, x]) or (some z : Filler | PP[z, y])) implies
			((x = y) iff (some z : Slot | (PPs[z, x] iff PPs[z, y])))
}

assert T1 {
	all x, y : Filler |
		(PP[y, x]) implies
			(some s: Slot | Ps[s, x] and F[y, s] and not Ps[s, y])
}

assert T3 {
	all x : Filler |
		(some s : Slot | Ps[s, x] or F[x, s]) implies (P[x, x])
}

fact {
	BA1 BA6 BA4 BA8 A1 A3 A4 A5 A6 A7 A8 A9 A10 A11
	rel/irreflexive[copied_through]
	rel/irreflexive[copied_from]
}

check BT7 for 10
check BT8 for 10
check BT9 for 10
check BT11 for 10
check BT12 for 10
check BT13 for 10
check BT14 for 3 but exactly 2 Filler
check T1 for 10
check T3 for 10

/***********
 * Sandbox *
 ***********/
run { Filler in (slots.Slot + Slot.content) } for 5

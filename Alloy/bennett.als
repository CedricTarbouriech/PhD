/**
  Bennett, Having a Part Twice Over, 2013.

  Some axioms are not implemented as facts:
  - (BA2) "Slots Cannot Fill" is implemented by the signature Slot;
  - (BA3) "Slots Don’t Have Slots" is implemented by the signature Filler;
*/

sig Slot {
  slot_of : set Filler
}

sig Filler {
  fills : set Slot
} 

pred F(a : Filler, s: Slot) { s in a.fills }
pred Ps(s : Slot, a: Filler) { a in s.slot_of }
pred P(a, b : Filler) { some s : Slot | Ps[s, b] and F[a, s] }
pred PP(a, b : Filler) { P[a, b] and not P[b, a] }
pred O(a, b : Filler) { some c : Filler | P[c, a] and P[c, b] }
pred Os(a, b : Filler) { some s : Slot | Ps[s, a] and Ps[s, b] }
pred PPs(s : Slot, a : Filler) { Ps[s, a] and not F[a, s] }

/* (A1) Only Slots are Filled */
fact {
	all a : Filler, s : Slot |
		(F[a, s] implies (some b : Filler | Ps[s, b]))
}

/* (A4) Improper Parthood Slots */
fact {
	all a : Filler | (some s : Slot | Ps[s, a])
		implies (some s : Slot | Ps[s, a] and F[a, s])
}

/* (A5) Slot Inheritance */
fact A5 {
	all a, b : Filler, s, t : Slot |
		(Ps[s, b] and F[a, s] and Ps[t, a]) implies Ps[t, b]
}

/* (A6) Mutual Occupancy is Identity */
fact {
	all a, b : Filler, s, t : Slot |
		(Ps[s, b] and F[a, s] and Ps[t, a] and F[b, t]) implies a = b
}

/* (A7) Single Occupancy */
fact {
	all a : Filler, s : Slot |
		Ps[s, a] implies (one b : Filler | F[b, s])
}

/* (T7) Transitivity */
check T7 {
	all a, b, c : Filler |
		P[a, b] and P[b, c] implies P[a, c]
} for 10

/* (T8) Anti-Symmetry */
check T8 {
	all a, b : Filler |
		P[a, b] and P[b, a] implies a = b
} for 10

/* (T9) Conditional Reflexivity */
check T9 {
	all a : Filler | (some s : Slot | Ps[s, a]) implies P[a, a]
} for 10

/* (T11) Parts <-> Slots */
check T11 {
	all a : Filler | (some b : Filler | P[b, a]) iff (some s : Slot | Ps[s, a])
} for 10

/* (T12) Composites <-> Slot-Composites */
check T12 {
	all a : Filler | (some b : Filler | PP[b, a]) iff (some s : Slot | PPs[s, a])
} for 10

/* (A8) Slot Stong Supplementation */
check A8 {
	all a, b : Filler |
		((some s : Slot | Ps[s, a]) and (some s : Slot | Ps[s, b])) implies
			((no s : Slot | Ps[s, a] and F[b, s]) implies
				(some s : Slot | Ps[s, b] and not Ps[s, a]))
} for 20

// As A8 is in fact a theorem, this serves as a way to activate/deactivate
// A8 as an axiom to see the consequences of performances.
fact {
	 //A8
}

/* (T13) Slot Weak Supplementation */
check T13 {
	all a, b : Filler | PP[a, b] implies
		(some s : Slot | Ps[s, b] and not Ps[s, a])
} for 15

/* (T14) Slot Extensionality */
/* Counter-example found! */
check T14 {
	all a, b : Filler |
		((some c : Filler | PP[c, a]) or (some c : Filler | PP[c, b])) implies
			((a = b) iff (all s : Slot | PPs[s, a] iff PPs[s, b]))
} for 3

check {
	no s : Slot | some disj a, b : Filler | F[a, s] and F[b, s]
} for 5

run {
  some disj a, b, c : Filler | P[a, c] and P[b, c]
} for 3 

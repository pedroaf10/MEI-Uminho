sig Track {
	succs : set Track,
	signals : set Signal
}
sig Junction, Entry, Exit in Track {}

sig Signal {}
sig Semaphore, Speed extends Signal {}

// Specify the following properties
// You can check their correctness with the different commands and
// when specifying each property you can assume all the previous ones to be true

pred inv1 {
	// The station has at least one entry and one exit
    some Entry and some Exit
}


pred inv2 {
	// Signals belong to one track
    all s : Signal | one signals.s

}


pred inv3 {
	// Exit tracks are those without successor
    all t : Track |t in Exit iff no t.succs
}


pred inv4 {
	// Entry tracks are those without predecessors
    all t: Track | t in Entry iff t not in Track.succs
}


pred inv5 {
	// Junctions are the tracks with more than one predecessor
    all j : Track | #succs.j > 1 iff j in Junction
}


pred inv6 {
	// Entry tracks must have a speed signal
    all t: Track | t in Entry implies some t.signals&Speed
}


pred inv7 {
	// The station has no cycles
    all t : Track | t not in t.^succs
}


pred inv8 {
	// It should be possible to reach every exit from every entry
    all e : Entry | all ex : Exit | ex in e.^succs or e=ex
}

pred inv9 {
	// Tracks not followed by junctions do not have semaphores
    all t : Track | no t.succs&Junction implies t.signals in Signal-Semaphore
}


pred inv10 {
	// Every track before a junction has a semaphore
    all t : Track | some t.succs&Junction implies some t.signals&Semaphore
}
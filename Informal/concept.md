<H1>Clock Model: Concept</H1>

# Motivation

# Clocks

Here, we consider **clocks** as names of entities that cause events.

These entities provide a tool for distinguishing events concerning the possibility of being guaranteed to order ones in time namely if the same clock triggered two events, then one of them was guaranteed to happen before the other.

In other words, any set of events occurring in a system is the disjunctive union of totally ordered event sets.
Each of these event sets is uniquely related to one and only one system clock.

More detailed,
- each system is related to a finite set of clocks;
- the event set caused by a system clock is finite or enumerable.

A set of events occurring in a system can be called an **event log**.

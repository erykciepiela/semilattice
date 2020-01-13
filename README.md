# semilattice

## Problems

* Out of order events delivery - state depends on events delivery order
* Duplicate events delivery - state gets currupted by duplicates
* Network partitioning - ?
  * Remote writes - writes affected by unavailability/latency/failure of remote central storage
  * Squashing events - events can be squashed anytime anywhere
  * Replicas
* Original events not persisted, only state 

## Presentation

1. Conflict-Free Replicated Data Types
    1. Distributed state replicas instead of central state
        1. Fast local reads
        1. Fast local writes - temporary inconsistencies
        1. Not blocking local read/writes - network partitioning tolerance
        1. Replica synchronisation at arbitrary times - eventual consistency
    1. Advatageous even with single replica
        1. Irrefutable writes - accepting writes as undeniable facts
        1. Append-only writes - data can only grow
        1. Transaction-less - consequence of the above
        1. Contradictory writes - possible but explicitly modeled
    1. New ACID
        1. Associativity - `a \/ (b \/ c) == (a \/ b) \/ c` - handling
        1. Commutativity - `a \/ b == b \/ a` - handling out-of-order writes
        1. Idempotence - `a \/ a == a` - handling duplicate writes
        1. Distributed
    1. Bounded join semilattice
        1. Algebra `(S, \/, 0)` where
            1. `S` is set of all possible values
            1. `\/` (called *join*) is associative, commutative, idempotent binary operator
            1. `0` (called *neutral element*) is an element of `S` such that for all `a` in `S`, `0 \/ a == a == a \/ 0`
            1. `S` is closed under `\/`: for all `a` and `b` in `S`, `a \/ b` also in `S` - we can always join values
        1. Associativity lets us skip parenths: `a \/ (b \/ c) == a \/ b \/ c`
        1. Associativity+commutativity+idempotence+neutral element in action: `a \/ (b \/ c) == 0 \/ (b \/ a) \/ (c \/ c)`
    1. Bounded join semilattice examples
        1. `GrowingSet`
            1. Set that can only grow in time
            1. `S` is a set of values of arbitrary type
            1. `\/` is sum
            1. `0` is an empty set
        1. `ShrinkingSet` - set that can only shrink in time
        1. `IncreasingValue` - value that can only increase in time
        1. `DecreasingValue` - value that can only decrease in time
        1. `PredAnd a` - functions `a -> Bool`, `Bool`s anded
        1. `PredOr a` - functions `a -> Bool`, `Bool`s ored
        1. Time-stamped values - pairs `(a, Time)` (under some assumptions about `a` and `Time` types and clocks synchronization, what assumptions?)
    1. Higher-kinded bounded join semilattices
        1. If `v` is a BJS then `GrowingMap k s` is BJS as well
            1. `GrowingMap` is a map where we can only add entries or join existing ones
        1. If `e` is a BJS then `GrowingList w` is BJS as well
            1. `GrowingList` is a list where we can only append values or join existing ones
        1. If `a` and `b` are BJSs than `(a, b)` is BJS as well
        1. If `a` and `b` are BJSs than `Either a b` is BJS as well (what are `\/` and `0`?)
        1. We can combine the above: `GrowingMap A (GrowingMap B ((GrowingList (DecreasingValue C), (Either (IncreasingValue D) (GrowingSet E)))))` is a BJS as long as
            1. `instance Bounded C` so that we know maximum value of `C`
            1. `instance Bounded D` so that we know minimum value of `D`
            1. `instance Ord E` so that we can compare values of `E`s
    1. Modeling contradictions
        1. Assume a value that we expect to be set at some time and should stay the same since then, what if we get different values?
        1. `Same a` is a (union) type that can have value `Unknown`, `Unambiguous a` or `Ambiguous`
        1. `Same a` is BJS as long as we can compare `a`s - `instance Eq a`
        1. Note we can get the same `Unambiguous a` multiple times without contradiction (what are `\/` and `0`?)
    

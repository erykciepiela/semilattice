# Order, Lattices and Conflict-Free Replicated Data Types

1. Conflict-Free Replicated Data Types
    1. Instead of shared central state, shared state in distributed replicas
        1. Fast, not blocking local reads
        1. Fast, not blocking local writes - temporary inconsistencies between replicas
        1. Conflict-free replica synchronisation at arbitrary times - eventual consistency
        1. No central state - no single point of failure
        1. Replacement for RPC-like APIs
    1. Advatageous even when single replica
        1. Irrefutable writes - accepting writes as undeniable facts
        1. Append-only writes - data can only "grow"
        1. Transaction-less - consequence of the above
        1. Contradictory writes - possible but explicitly modeled
    1. New ACID
        1. Let `a`, `b`, and `c` be replicas and `+` be a replicat "merge" operation
        1. Associativity - `a + (b + c) == (a + b) + c`, handles arbitrary grouping of merges
        1. Commutativity - `a + b == b + a` - handles out-of-order merges
        1. Idempotence - `a + a == a` - handles duplicate merges
        1. Distributed - remote replicas merges
1. Maths behind CRDTs
    1. *Type* - a collection of values
    1. *Partial order* - values of type can be compared with `+>` (a kind of "greater or equal")
        1. `a +> a` - reflexivity
        1. `a +> b, b +> a => a == b` - antisymmetry
        1. `a +> b +> c => a +> c` - transitivity
        1. note that there might be that neither `a +> b` nor `b +> a`, `a` and `b` not comparable, that's why "partial"
    1. *Lattice*
        1. Algebra `(S, \/, /\)` where
            1. `S` is a type
            1. `\/` (*join*) is a binary operator
                1. closed under `S` - if `a` and `b` belongs to `S` then `a \/ b` also belongs to `S`
                1. associative - `a \/ (b \/ c) = (a \/ b) \/ c`
                1. commutative - `a \/ b = b \/ a`
                1. idempotent - `a \/ a = a`
                1. `a \/ b +> a`
            1. `/\` (*meet*) is a binary operator
                1. closed under `S`
                1. associative - `a /\ (b /\ c) = (a /\ b) /\ c`
                1. commutative - `a /\ b = b /\ a`
                1. idempotent -  `a /\ a = a`
                1. `a +> a /\ b`
    1. *Bounded lattice*
        1. Algebra `(S, /\, \/, 0, 1)`
            1. `0` (*bottom*) is a value belonging to `S`
                1. for all `a` in `S`, `0 \/ a == a == a \/ 0`
            1. `1` (*top*) is a value belonging to `S`
                1. for all `a` in `S`, `1 /\ a == a == a /\ 1`
    1. *Finite lattice*
        1. Lattice `(S, \/, /\)` where `S` is finite
    1. *Distributive lattice*
        1. `a /\ (b \/ c) = (a /\ b) \/ (a \/ c)`
    1. *Dual*
        1. 
    1. (Bounded) join semilattices examples
        1. `GrowingSet` is BJS
            1. Set that can only grow in time
            1. `S` is a set of values of arbitrary type
            1. `\/` is sum
            1. `0` is an empty set
        1. `ShrinkingSet` is JS - set that can only shrink in time
        1. `ShrinkingSet` is BJS if we know the largest possible set
        1. `IncreasingValue` is JS - value that can only increase in time
        1. `IncreasingValue` is BJS if we know minimal possible value
        1. `DecreasingValue` is JS - value that can only decrease in time
        1. `DecreasingValue` is BJS if we know maximal possible value
        1. `PredAnd a` is BJS - functions `a -> Bool`, `Bool`s anded
        1. `PredOr a` is BJS - functions `a -> Bool`, `Bool`s ored
        1. Time-stamped value is JS - pairs `(a, Time)` (under assumptions about clocks synchronization)
    1. Higher-kinded (bounded) join semilattices
        1. If `v` is a JS then `GrowingMap k s` is BJS
            1. `GrowingMap` is a map where we can only add entries or join existing ones
        1. If `e` is a JS then `GrowingList w` is BJS
            1. `GrowingList` is a list where we can only append values or join existing ones
        1. If `a` and `b` are BJSs than `(a, b)` is BJS
        1. If `a` and `b` are BJSs than `Either a b` is BJS (what are `\/` and `0`?)
        1. If `a` is JS than `Maybe a` is BJS (equivalent to `Either () a`)
        1. We can combine the above: `GrowingMap A (GrowingMap B ((GrowingList (DecreasingValue C), (Either (IncreasingValue D) (GrowingSet E)))))` is a BJS as long as
            1. `instance Bounded C` so that we know maximum value of `C`
            1. `instance Bounded D` so that we know minimum value of `D`
            1. `instance Ord E` so that we can compare values of `E`s
    1. Modeling contradictions
        1. Assume a value that we expect to be set at some time and should stay the same since then, what if we get different values?
        1. `Same a` is a (union) type that can have value `Unknown`, `Unambiguous a` or `Ambiguous`
        1. `Same a` is BJS as long as we can compare `a`s - `instance Eq a`
        1. Note we can get the same `Unambiguous a` multiple times without contradiction (what are `\/` and `0`?)
    1. Order in join semilattice
        1. If `a \/ b == a` then we say `a +> b`, `b <+ a`, `a` is greater or equal to `b`, `b` is lesser or equal to `a`
        1. In particular, as `a \/ a == a` because of idempotence, indeed, `a` is greater or equal to itself and `a` is lesser or equal to itself, therefore `a` is equal to itself.
        1. Intuitively, when `a +> b` then joining `a` with `b` will not introduce anything new than `a`, `a` already contains `b`, `a` has already contained `b`
        1. Checking if `a +> b` is a kind of read operation: it checkes whether `b` is already contained in `a`
        1. Example:
        ```
        isPersonOlderThan :: Person -> Age -> GrowingMap Person (Increasing Age) -> Bool
        isPersonOlderThan person age personMap = personMap +> singleton person (Increasing age)
        ```
    1. Mappings between join semilattices
        1. Let's analyse more useful read operation:
        ```
        personsAge :: Person -> GrowingMap Person (Increasing Age) -> Maybe (Increasing Age)
        personsAge personMap person = lookup person personMap
        ```
        1. Notice this is a function from one BJS to another BJS
        1. Left-hand side BJS will only grow, so will the right-hand side BJS
        1. As left-hand side BJS grows, so will the right-hand side BJS - it's a *monotonic* function
            1. Monotonic mappings between JSs are a category
        1. If `f (a \/ b) = f a \/ f b` and `f 0 = 0` then `f` it's not only *monotonic* but *homomorphic*
            1. Homomorphic mappings between JSs are a category
        1. Propagators concept
    1. References
        1. *Introduction to Lattices and Order*, 2nd edition, 2012, B. A. Davey, H. A. Priestley
        1. [Edward Kmett: Propagators - Boston Haskell](https://www.youtube.com/watch?v=DyPzPeOPgUE)
        1. [Edward Kmett: Propagators - YOW! Lambda Jam 2016](https://www.youtube.com/watch?v=acZkF6Q2XKs)
        1. [John Mumm: A CRDT Primer: Defanging Order Theory](https://www.youtube.com/watch?v=OOlnp2bZVRs&t=1478s)
        1. [Marc Shapiro: Strong Eventual Consistency and Conflict-free Replicated Data Types](https://www.youtube.com/watch?v=ebWVLVhiaiY&t=1018s)    

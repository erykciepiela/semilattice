# semilattice

## Problems

* Out of order events delivery - state depends on events delivery order
* Duplicate events delivery - state gets currupted by duplicates
* Network partitioning - ?
  * Remote writes - writes affected by unavailability/latency/failure of remote central storage
  * Squashing events - events can be squashed anytime anywhere
  * Replicas
* Original events not persisted, only state 

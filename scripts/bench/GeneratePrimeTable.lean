/- The settled prime-table generator invocation.  Its stdout is the two
generated regions in `HexPrimality/Table.lean`. -/
import HexPrimality.SieveElab

#rebuild_primeTable 10000 100 4

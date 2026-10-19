/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Init.System.IO

/-! # Interruptible process pipes

The optional PARI protocol uses fresh, exclusively owned process pipes. Polling
their descriptors permits cooperative reader cancellation even if a descendant
escapes the process group and keeps a pipe open. These IO operations produce no
proofs and do not participate in certificate replay.
-/

public section

namespace Hex.ECPP.Pari.IO

/-- Read at most 4096 bytes from a fresh process pipe, polling for at most 25 ms.
`none` means no data is ready; an empty byte array means EOF. The descriptor is
made nonblocking. Do not mix this operation with buffered handle reads. -/
@[extern "hex_ecpp_poll_read"]
opaque pollRead (handle : @& _root_.IO.FS.Handle) : _root_.IO (Option ByteArray)

/-- Send SIGKILL to the owned, unreaped child's process group. If the group does
not yet exist, kill its leader. Never call this operation after reaping the child.
The PID must be positive and representable as a POSIX process ID. -/
@[extern "hex_ecpp_kill_group"]
opaque killGroup (pid : UInt32) : _root_.IO Unit

end Hex.ECPP.Pari.IO

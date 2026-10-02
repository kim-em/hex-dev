/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet.Codec.Value

/-! Conformance for the total integer-only JSON byte backend.
Oracle: Python's standard JSON parser, required, via JsonBytesDriver.
Covered operations: actual UTF-8 parsing/printing, string escape handling,
integer tokens, nested arrays/objects and complete-input consumption.
Covered properties: universal byte roundtrips checked by the ordinary kernel,
and rejection of malformed syntax, invalid UTF-8 and lone surrogates.
This does not assert roundtrips for the existing Dag byte codec. -/
namespace Hex.SignDet.JsonBytes
open Codec.Json

example (value : Value) : readBytes value.writeBytes = some value := readBytes_write value

#guard readBytes "[1,]".toUTF8 == none
#guard readBytes "{\"a\":1,}".toUTF8 == none
#guard readBytes "[01]".toUTF8 == none
#guard readBytes "[1e2]".toUTF8 == none
#guard readBytes "[1.0]".toUTF8 == none
#guard readBytes "\"\\ud800\"".toUTF8 == none
#guard readBytes "[] null".toUTF8 == none
#guard readBytes (ByteArray.mk #[0xc0, 0xaf]) == none
#guard readBytes "{\"x\":1,\"x\":2}".toUTF8 ==
    some (.object (.cons "x" (.number 1) (.cons "x" (.number 2) .nil)))
#guard readBytes "\"\\ud83d\\ude00\"".toUTF8 == some (.string "😀")

/-- A deliberately non-tail call tests the executable's stack configuration.
This is only a native test canary, never part of parsing or certificate replay. -/
@[noinline] def stackCanary : Nat → IO Nat
  | 0 => pure 0
  | n + 1 => do
    let result ← stackCanary n
    if result == n then pure (result + 1)
    else throw (IO.userError "stack canary result changed")

end Hex.SignDet.JsonBytes

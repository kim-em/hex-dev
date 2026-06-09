import HexLLL.Basic

namespace Hex
namespace LLLProviderProbe

def main (args : List String) : IO UInt32 := do
  let expected ←
    match args with
    | ["absent"] => pure false
    | ["present"] => pure true
    | _ =>
        IO.eprintln "usage: hexlll_provider_probe absent|present"
        return 2
  let actual := LLLProvider.providerAvailable ()
  if actual = expected then
    if !expected then
      match LLLProvider.providerReduce 0 0 #[] 0.75 0.55 0 false with
      | .error _ => return 0
      | .ok _ =>
          IO.eprintln "providerReduce unexpectedly succeeded while provider is absent"
          return 1
    return 0
  else
    IO.eprintln s!"providerAvailable = {actual}, expected {expected}"
    return 1

end LLLProviderProbe
end Hex

def main (args : List String) : IO UInt32 :=
  Hex.LLLProviderProbe.main args

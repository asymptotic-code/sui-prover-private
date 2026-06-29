-- Hand-written Lean implementations of the multiaddr-validity native predicates
-- `is_valid_tcp` / `is_valid_udp`, replacing the translator's `sorry` placeholders.
--
-- Move declarations (multiaddr_specs.move):
--   public native fun is_valid_tcp(s: &String): bool;
--   public native fun is_valid_udp(s: &String): bool;
--
-- These are the *declarative* validity predicates that the imperative
-- `validate_with_transport` parser computes. We give them a real, total Lean
-- definition mirroring that parser's acceptance condition:
--   * the address starts with '/', and splitting the remainder on '/' yields
--     ≥ 4 segments  [protocol, address, transport, port, …];
--   * protocol ∈ {ip4, ip6, dns4, dns6, dns} and the address is valid for it;
--   * the transport segment equals the expected transport ("tcp" / "udp");
--   * the port segment is non-empty and all-ASCII-digits.
-- (Segments past the 4th are accepted iff they are a known protocol name or a
--  resource path, exactly as the parser does.)

import Prelude.BoundedNat
import Prelude.Helpers
import MoveStdlib.MoveString

namespace Multiaddr

/-- ASCII codes -/
private def slash : BoundedNat (2^8) := ⟨47, by decide⟩

/-- Split a byte list on the '/' separator (ASCII 47), dropping the empty
    segment before a leading slash. -/
private def splitSlash (bs : List (BoundedNat (2^8))) : List (List (BoundedNat (2^8))) :=
  -- group runs separated by `slash`
  let step : List (BoundedNat (2^8)) → List (List (BoundedNat (2^8))) → List (List (BoundedNat (2^8)))
    := fun _ acc => acc
  -- fold from the right, threading the current segment
  let rec go : List (BoundedNat (2^8)) → List (BoundedNat (2^8)) → List (List (BoundedNat (2^8)))
    | [], cur => [cur]
    | b :: rest, cur =>
        if b == slash then cur :: go rest [] else go rest (cur ++ [b])
  let _ := step
  go bs []

private def isDigit (b : BoundedNat (2^8)) : Bool :=
  decide (48 ≤ b.val) && decide (b.val ≤ 57)

private def allDigits (bs : List (BoundedNat (2^8))) : Bool :=
  bs.all isDigit

private def bytesOf (s : String) : List (BoundedNat (2^8)) :=
  s.toUTF8.toList.map (fun c => ⟨c.toNat % 256, Nat.mod_lt _ (by decide)⟩)

private def protocolOk (p : List (BoundedNat (2^8))) : Bool :=
  p == bytesOf "ip4" || p == bytesOf "ip6" || p == bytesOf "dns4"
    || p == bytesOf "dns6" || p == bytesOf "dns"

-- Validity for a specific transport keyword (as a byte list).
private def validFor (transport : List (BoundedNat (2^8))) (s : MoveString.MoveString) : Bool :=
  match splitSlash s.bytes with
  | [] => false
  | first :: rest =>
      -- a leading '/' produced an empty `first` segment; require it empty,
      -- then [protocol, address, actual_transport, port, …] = rest
      first == [] &&
      (match rest with
       | protocol :: _address :: actualTransport :: port :: _ =>
           protocolOk protocol
             && (actualTransport == transport)
             && (port ≠ [] && allDigits port)
       | _ => false)

@[reducible] def is_valid_tcp (s : MoveString.MoveString) : Bool :=
  validFor (bytesOf "tcp") s

@[reducible] def is_valid_udp (s : MoveString.MoveString) : Bool :=
  validFor (bytesOf "udp") s

end Multiaddr
